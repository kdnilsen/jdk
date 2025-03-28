/*
 * Copyright (c) 2018, 2019, Red Hat, Inc. All rights reserved.
 * Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
 * Copyright (c) 2025, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

#include "precompiled.hpp"

#include "gc/shared/gcCause.hpp"
#include "gc/shenandoah/heuristics/shenandoahHeuristics.hpp"
#include "gc/shenandoah/heuristics/shenandoahSpaceInfo.hpp"
#include "gc/shenandoah/heuristics/shenandoahAdaptiveHeuristics.hpp"
#include "gc/shenandoah/shenandoahCollectionSet.hpp"
#include "gc/shenandoah/shenandoahCollectorPolicy.hpp"
#include "gc/shenandoah/shenandoahFreeSet.hpp"
#include "gc/shenandoah/shenandoahHeap.inline.hpp"
#include "gc/shenandoah/shenandoahHeapRegion.inline.hpp"
#include "logging/log.hpp"
#include "logging/logTag.hpp"
#include "runtime/globals.hpp"
#include "utilities/quickSort.hpp"

// These constants are used to adjust the margin of error for the moving
// average of the allocation rate and cycle time. The units are standard
// deviations.
const double ShenandoahAdaptiveHeuristics::FULL_PENALTY_SD = 0.2;
const double ShenandoahAdaptiveHeuristics::DEGENERATE_PENALTY_SD = 0.1;

// These are used to decide if we want to make any adjustments at all
// at the end of a successful concurrent cycle.
const double ShenandoahAdaptiveHeuristics::LOWEST_EXPECTED_AVAILABLE_AT_END = -0.5;
const double ShenandoahAdaptiveHeuristics::HIGHEST_EXPECTED_AVAILABLE_AT_END = 0.5;

// These values are the confidence interval expressed as standard deviations.
// At the minimum confidence level, there is a 25% chance that the true value of
// the estimate (average cycle time or allocation rate) is not more than
// MINIMUM_CONFIDENCE standard deviations away from our estimate. Similarly, the
// MAXIMUM_CONFIDENCE interval here means there is a one in a thousand chance
// that the true value of our estimate is outside the interval. These are used
// as bounds on the adjustments applied at the outcome of a GC cycle.
const double ShenandoahAdaptiveHeuristics::MINIMUM_CONFIDENCE = 0.319; // 25%
const double ShenandoahAdaptiveHeuristics::MAXIMUM_CONFIDENCE = 3.291; // 99.9%

ShenandoahAdaptiveHeuristics::ShenandoahAdaptiveHeuristics(ShenandoahSpaceInfo* space_info) :
  ShenandoahHeuristics(space_info),
  _margin_of_error_sd(ShenandoahAdaptiveInitialConfidence),
  _spike_threshold_sd(ShenandoahAdaptiveInitialSpikeThreshold),
  _last_trigger(OTHER),
  _available(Moving_Average_Samples, ShenandoahAdaptiveDecayFactor) { }

ShenandoahAdaptiveHeuristics::~ShenandoahAdaptiveHeuristics() {}

void ShenandoahAdaptiveHeuristics::choose_collection_set_from_regiondata(ShenandoahCollectionSet* cset,
                                                                         RegionData* data, size_t size,
                                                                         size_t actual_free) {
  size_t garbage_threshold = ShenandoahHeapRegion::region_size_bytes() * ShenandoahGarbageThreshold / 100;

  // The logic for cset selection in adaptive is as follows:
  //
  //   1. We cannot get cset larger than available free space. Otherwise we guarantee OOME
  //      during evacuation, and thus guarantee full GC. In practice, we also want to let
  //      application to allocate something. This is why we limit CSet to some fraction of
  //      available space. In non-overloaded heap, max_cset would contain all plausible candidates
  //      over garbage threshold.
  //
  //   2. We should not get cset too low so that free threshold would not be met right
  //      after the cycle. Otherwise we get back-to-back cycles for no reason if heap is
  //      too fragmented. In non-overloaded non-fragmented heap min_garbage would be around zero.
  //
  // Therefore, we start by sorting the regions by garbage. Then we unconditionally add the best candidates
  // before we meet min_garbage. Then we add all candidates that fit with a garbage threshold before
  // we hit max_cset. When max_cset is hit, we terminate the cset selection. Note that in this scheme,
  // ShenandoahGarbageThreshold is the soft threshold which would be ignored until min_garbage is hit.

  size_t capacity    = _space_info->soft_max_capacity();
  size_t max_cset    = (size_t)((1.0 * capacity / 100 * ShenandoahEvacReserve) / ShenandoahEvacWaste);
  size_t free_target = (capacity / 100 * ShenandoahMinFreeThreshold) + max_cset;
  size_t min_garbage = (free_target > actual_free ? (free_target - actual_free) : 0);

  log_info(gc, ergo)("Adaptive CSet Selection. Target Free: %zu%s, Actual Free: "
                     "%zu%s, Max Evacuation: %zu%s, Min Garbage: %zu%s",
                     byte_size_in_proper_unit(free_target), proper_unit_for_byte_size(free_target),
                     byte_size_in_proper_unit(actual_free), proper_unit_for_byte_size(actual_free),
                     byte_size_in_proper_unit(max_cset),    proper_unit_for_byte_size(max_cset),
                     byte_size_in_proper_unit(min_garbage), proper_unit_for_byte_size(min_garbage));

  // Better select garbage-first regions
  QuickSort::sort(data, size, compare_by_garbage);

  size_t cur_cset = 0;
  size_t cur_garbage = 0;

  for (size_t idx = 0; idx < size; idx++) {
    ShenandoahHeapRegion* r = data[idx].get_region();

    size_t new_cset    = cur_cset + r->get_live_data_bytes();
    size_t new_garbage = cur_garbage + r->garbage();

    if (new_cset > max_cset) {
      break;
    }

    if ((new_garbage < min_garbage) || (r->garbage() > garbage_threshold)) {
      cset->add_region(r);
      cur_cset = new_cset;
      cur_garbage = new_garbage;
    }
  }
}

#undef KELVIN_DEVELOPMENT
#ifdef KELVIN_DEVELOPMENT
const char* stage_name(ShenandoahGCStage stage) {
  switch (stage) {
    case ShenandoahGCStage::_num_phases:
      return "<num-phases>";
    case ShenandoahGCStage::_final_roots:
      return "final_roots";
    case ShenandoahGCStage::_mark:
      return "mark";
    case ShenandoahGCStage::_evac:
      return "evac";
    case ShenandoahGCStage::_update:
      return "update";
    default:
      return "<unknown>";
  }
}
#endif

uint ShenandoahAdaptiveHeuristics::should_surge_phase(ShenandoahGCStage stage, double now) {
  _phase_stats[stage].set_most_recent_start_time(now);

  // If we're already surging within this cycle, do not reduce the surge level
  uint surge = _surge_level;
  size_t allocatable = ShenandoahHeap::heap()->free_set()->available();
  double time_to_finish_gc = 0.0;

  assert (ConcGCThreads * 2 == ParallelGCThreads, "Assume ConcurrentGCThreads is half ParallelGCThreads");
  if (_previous_cycle_max_surge_level > 1) {
    // If we required more than minimal surge in previous cycle, continue with a small surge now.  We may still be
    // catching up
    if (surge < 1) {
      surge = 1;
    }
  }

  size_t bytes_allocated = _space_info->bytes_allocated_since_gc_start();
  _phase_stats[stage].set_most_recent_bytes_allocated(bytes_allocated);
  double alloc_rate = _allocation_rate.average_rate(_margin_of_error_sd);

#ifdef KELVIN_DEVELOPMENT
  log_info(gc)(" bytes_allocated: %zu, avg_alloc_rate: %.3f MB/s, _margin_of_error_sd: %.3f",
               bytes_allocated, alloc_rate / (1024 * 1024), _margin_of_error_sd);
#endif

  switch (stage) {
    case ShenandoahGCStage::_num_phases:
      assert(false, "Should not happen");
      break;
    case ShenandoahGCStage::_final_roots:
    {
      // May happen after _mark, in case this is an abbreviated cycle
      time_to_finish_gc += _phase_stats[_final_roots].predict_next();

      // final_roots is preceded by mark, no evac or update
      double alloc_rate_since_gc_start = bytes_allocated / (now - _phase_stats[_mark].get_most_recent_start_time());
      if (alloc_rate_since_gc_start > alloc_rate) {
        alloc_rate = alloc_rate_since_gc_start;
#ifdef KELVIN_DEVELOPMENT
        log_info(gc)(" increasing alloc rate to %.3f MB/s in final_roots: %zu / %.3f",
                     alloc_rate / (1024 * 1024), bytes_allocated, now - _phase_stats[_mark].get_most_recent_start_time());
#endif
      }
    }
    break;

    case ShenandoahGCStage::_mark:
      time_to_finish_gc += _phase_stats[_mark].predict_next();
    case ShenandoahGCStage::_evac:
    {
      if (stage == _evac) {
        double alloc_rate_since_gc_start = bytes_allocated / (now - _phase_stats[_mark].get_most_recent_start_time());
        if (alloc_rate_since_gc_start > alloc_rate) {
          alloc_rate = alloc_rate_since_gc_start;
#ifdef KELVIN_DEVELOPMENT
          log_info(gc)(" increasing alloc rate to %.3f MB/s in evac: %zu / %.3f",
                       alloc_rate / (1024 * 1024), bytes_allocated, now - _phase_stats[_mark].get_most_recent_start_time());
#endif
        }
      }
      time_to_finish_gc += _phase_stats[_evac].predict_next();
    }
    case ShenandoahGCStage::_update:
    {
      if (stage == _update) {
        double alloc_rate_since_gc_start = bytes_allocated / (now - _phase_stats[_mark].get_most_recent_start_time());
        if (alloc_rate_since_gc_start > alloc_rate) {
          alloc_rate = alloc_rate_since_gc_start;
#ifdef KELVIN_DEVELOPMENT
          log_info(gc)(" increasing alloc rate to %.3f MB/s in update: %zu / %.3f",
                       alloc_rate / (1024 * 1024), bytes_allocated, now - _phase_stats[_mark].get_most_recent_start_time());
#endif
        }
        double alloc_rate_since_evac_start = ((bytes_allocated - _phase_stats[_evac].get_most_recent_bytes_allocated())/
                                              (now - _phase_stats[_evac].get_most_recent_start_time()));
        if (alloc_rate_since_evac_start > alloc_rate) {
          alloc_rate = alloc_rate_since_evac_start;
#ifdef KELVIN_DEVELOPMENT
          log_info(gc)(" increasing alloc rate to %.3f MB/s in update since evac: %zu / %.3f",
                       alloc_rate / (1024 * 1024), bytes_allocated - _phase_stats[_evac].get_most_recent_bytes_allocated(),
                       (now - _phase_stats[_evac].get_most_recent_start_time()));
#endif
        }
      }
      time_to_finish_gc += _phase_stats[_update].predict_next();
    }
  }

  double race_odds;

  if (allocatable == 0) {
    // Avoid divide by zero, and force high surge if we are out of memory
    race_odds = 1000.0;
  } else {
    race_odds = (alloc_rate * time_to_finish_gc) / allocatable;
  }

  // To Do: Also consider accelerating consumption of memory. Use/race_odds = MAX(avg_odds, accelerated_odds)

  if (race_odds > 1.75) {
    surge = 4;
  } else if (race_odds > 1.5) {
    if (surge < 3) {
      surge = 3;
    }
  } else if (race_odds > 1.25) {
    if (surge < 2) {
      surge = 2;
    }
  } else if (race_odds > 1.0) {
    if (surge < 1) {
      surge = 1;
    }
  }

#undef KELVIN_DEVELOPMENT
#ifdef KELVIN_DEVELOPMENT
  const char* phase_name = stage_name(stage);
  log_info(gc)("ShouldSurge(%s), allocatable: %zu, alloc_rate: %.3f MB/s, time_to_finish_gc: %.3fs, race_odds: %.3f returns %u",
               phase_name, allocatable, alloc_rate / (1024 * 1024), time_to_finish_gc, race_odds, surge);
#endif
  _surge_level = surge;
  if (surge > 0) {
    log_info(gc)("Surging GC worker threads at level %u", surge);
  }
  if ((stage == ShenandoahGCStage::_update) || (stage == ShenandoahGCStage::_final_roots)) {
    _previous_cycle_max_surge_level = surge;
  }
  return surge;
}

void ShenandoahAdaptiveHeuristics::record_phase_end(ShenandoahGCStage phase, double now) {
  double duration = now - _phase_stats[phase].get_most_recent_start_time();
  switch (_surge_level) {
    case 4:
      duration *= 2.0;          // If we had half the workers, assume we would have required twice the time
      break;
    case 3:
      duration *= 1.75;         // If we had 4/7 the workers, assume we would have required 7/4 the time
      break;
    case 2:
      duration *= 1.5;          // If we had 4/6 the workers, assume we would have required 6/4 the time
      break;
    case 1:
      duration *= 1.25;         // If we had 4/5 the workers, assume we would have required 5/4 the time
      break;
    case 0:
    default:
      // No adjustment to duration necessary
      break;
  }
#undef KELVIN_DEVELOPMENT
#ifdef KELVIN_DEVELOPMENT
  const char* phase_name = stage_name(phase);
  log_info(gc)("Recording duration of phase %s, adjusted by surge_level %u: %.3f", phase_name, _surge_level, duration);
#endif
  _phase_stats[phase].add_sample(duration);
}

void ShenandoahAdaptiveHeuristics::record_cycle_start() {
  ShenandoahHeuristics::record_cycle_start();
  _allocation_rate.allocation_counter_reset();
}

void ShenandoahAdaptiveHeuristics::record_success_concurrent() {
  ShenandoahHeuristics::record_success_concurrent();

  size_t available = _space_info->available();

  double z_score = 0.0;
  double available_sd = _available.sd();
  if (available_sd > 0) {
    double available_avg = _available.avg();
    z_score = (double(available) - available_avg) / available_sd;
    log_debug(gc, ergo)("Available: %zu %sB, z-score=%.3f. Average available: %.1f %sB +/- %.1f %sB.",
                        byte_size_in_proper_unit(available), proper_unit_for_byte_size(available),
                        z_score,
                        byte_size_in_proper_unit(available_avg), proper_unit_for_byte_size(available_avg),
                        byte_size_in_proper_unit(available_sd), proper_unit_for_byte_size(available_sd));
    
  }

  _previous_cycle_max_surge_level = _surge_level;
  _surge_level = 0;

  _available.add(double(available));

  // In the case when a concurrent GC cycle completes successfully but with an
  // unusually small amount of available memory we will adjust our trigger
  // parameters so that they are more likely to initiate a new cycle.
  // Conversely, when a GC cycle results in an above average amount of available
  // memory, we will adjust the trigger parameters to be less likely to initiate
  // a GC cycle.
  //
  // The z-score we've computed is in no way statistically related to the
  // trigger parameters, but it has the nice property that worse z-scores for
  // available memory indicate making larger adjustments to the trigger
  // parameters. It also results in fewer adjustments as the application
  // stabilizes.
  //
  // In order to avoid making endless and likely unnecessary adjustments to the
  // trigger parameters, the change in available memory (with respect to the
  // average) at the end of a cycle must be beyond these threshold values.
  if (z_score < LOWEST_EXPECTED_AVAILABLE_AT_END ||
      z_score > HIGHEST_EXPECTED_AVAILABLE_AT_END) {
    // The sign is flipped because a negative z-score indicates that the
    // available memory at the end of the cycle is below average. Positive
    // adjustments make the triggers more sensitive (i.e., more likely to fire).
    // The z-score also gives us a measure of just how far below normal. This
    // property allows us to adjust the trigger parameters proportionally.
    //
    // The `100` here is used to attenuate the size of our adjustments. This
    // number was chosen empirically. It also means the adjustments at the end of
    // a concurrent cycle are an order of magnitude smaller than the adjustments
    // made for a degenerated or full GC cycle (which themselves were also
    // chosen empirically).
    adjust_last_trigger_parameters(z_score / -100);
  }
}

void ShenandoahAdaptiveHeuristics::record_success_degenerated() {
  ShenandoahHeuristics::record_success_degenerated();
  // Adjust both trigger's parameters in the case of a degenerated GC because
  // either of them should have triggered earlier to avoid this case.
  adjust_margin_of_error(DEGENERATE_PENALTY_SD);
  adjust_spike_threshold(DEGENERATE_PENALTY_SD);

  // If we had to degenerate, that's as if we were surging at max level
  _previous_cycle_max_surge_level = 4;
  _surge_level = 0;
}

void ShenandoahAdaptiveHeuristics::record_success_full() {
  ShenandoahHeuristics::record_success_full();
  // Adjust both trigger's parameters in the case of a full GC because
  // either of them should have triggered earlier to avoid this case.
  adjust_margin_of_error(FULL_PENALTY_SD);
  adjust_spike_threshold(FULL_PENALTY_SD);

  // If we escalated to full gc, that's as if we were surging at max level
  _previous_cycle_max_surge_level = 4;
  _surge_level = 0;
}

static double saturate(double value, double min, double max) {
  return MAX2(MIN2(value, max), min);
}

//  Rationale:
//    The idea is that there is an average allocation rate and there are occasional abnormal bursts (or spikes) of
//    allocations that exceed the average allocation rate.  What do these spikes look like?
//
//    1. At certain phase changes, we may discard large amounts of data and replace it with large numbers of newly
//       allocated objects.  This "spike" looks more like a phase change.  We were in steady state at M bytes/sec
//       allocation rate and now we're in a "reinitialization phase" that looks like N bytes/sec.  We need the "spike"
//       accommodation to give us enough runway to recalibrate our "average allocation rate".
//
//   2. The typical workload changes.  "Suddenly", our typical workload of N TPS increases to N+delta TPS.  This means
//       our average allocation rate needs to be adjusted.  Once again, we need the "spike" accomodation to give us
//       enough runway to recalibrate our "average allocation rate".
//
//    3. Though there is an "average" allocation rate, a given workload's demand for allocation may be very bursty.  We
//       allocate a bunch of LABs during the 5 ms that follow completion of a GC, then we perform no more allocations for
//       the next 150 ms.  It seems we want the "spike" to represent the maximum divergence from average within the
//       period of time between consecutive evaluation of the should_start_gc() service.  Here's the thinking:
//
//       a) Between now and the next time I ask whether should_start_gc(), we might experience a spike representing
//          the anticipated burst of allocations.  If that would put us over budget, then we should start GC immediately.
//       b) Between now and the anticipated depletion of allocation pool, there may be two or more bursts of allocations.
//          If there are more than one of these bursts, we can "approximate" that these will be separated by spans of
//          time with very little or no allocations so the "average" allocation rate should be a suitable approximation
//          of how this will behave.
//
//    For cases 1 and 2, we need to "quickly" recalibrate the average allocation rate whenever we detect a change
//    in operation mode.  We want some way to decide that the average rate has changed, while keeping average
//    allocation rate computation independent.
bool ShenandoahAdaptiveHeuristics::should_start_gc() {
  size_t capacity = _space_info->soft_max_capacity();
  size_t available = _space_info->soft_available();
  size_t allocated = _space_info->bytes_allocated_since_gc_start();

  log_debug(gc)("should_start_gc? available: %zu, soft_max_capacity: %zu"
                ", allocated: %zu", available, capacity, allocated);

  // Track allocation rate even if we decide to start a cycle for other reasons.
  double rate = _allocation_rate.sample(allocated);
  _last_trigger = OTHER;

  size_t min_threshold = min_free_threshold();
  if (available < min_threshold) {
    log_trigger("Free (%zu%s) is below minimum threshold (%zu%s)",
                 byte_size_in_proper_unit(available), proper_unit_for_byte_size(available),
                 byte_size_in_proper_unit(min_threshold), proper_unit_for_byte_size(min_threshold));
    return true;
  }

  // Check if we need to learn a bit about the application
  const size_t max_learn = ShenandoahLearningSteps;
  if (_gc_times_learned < max_learn) {
    size_t init_threshold = capacity / 100 * ShenandoahInitFreeThreshold;
    if (available < init_threshold) {
      log_trigger("Learning %zu of %zu. Free (%zu%s) is below initial threshold (%zu%s)",
                   _gc_times_learned + 1, max_learn,
                   byte_size_in_proper_unit(available), proper_unit_for_byte_size(available),
                   byte_size_in_proper_unit(init_threshold), proper_unit_for_byte_size(init_threshold));
      return true;
    }
  }
  // Check if allocation headroom is still okay. This also factors in:
  //   1. Some space to absorb allocation spikes (ShenandoahAllocSpikeFactor)
  //   2. Accumulated penalties from Degenerated and Full GC
  size_t allocation_headroom = available;

  size_t spike_headroom = capacity / 100 * ShenandoahAllocSpikeFactor;
  size_t penalties      = capacity / 100 * _gc_time_penalties;

  allocation_headroom -= MIN2(allocation_headroom, spike_headroom);
  allocation_headroom -= MIN2(allocation_headroom, penalties);

  double avg_cycle_time = _gc_cycle_time_history->davg() + (_margin_of_error_sd * _gc_cycle_time_history->dsd());
  double avg_alloc_rate = _allocation_rate.upper_bound(_margin_of_error_sd);

  log_debug(gc)("average GC time: %.2f ms, allocation rate: %.0f %s/s",
          avg_cycle_time * 1000, byte_size_in_proper_unit(avg_alloc_rate), proper_unit_for_byte_size(avg_alloc_rate));
  if (avg_cycle_time * avg_alloc_rate > allocation_headroom) {
    log_trigger("Average GC time (%.2f ms) is above the time for average allocation rate (%.0f %sB/s)"
                 " to deplete free headroom (%zu%s) (margin of error = %.2f)",
                 avg_cycle_time * 1000,
                 byte_size_in_proper_unit(avg_alloc_rate), proper_unit_for_byte_size(avg_alloc_rate),
                 byte_size_in_proper_unit(allocation_headroom), proper_unit_for_byte_size(allocation_headroom),
                 _margin_of_error_sd);
    log_info(gc, ergo)("Free headroom: %zu%s (free) - %zu%s (spike) - %zu%s (penalties) = %zu%s",
                       byte_size_in_proper_unit(available),           proper_unit_for_byte_size(available),
                       byte_size_in_proper_unit(spike_headroom),      proper_unit_for_byte_size(spike_headroom),
                       byte_size_in_proper_unit(penalties),           proper_unit_for_byte_size(penalties),
                       byte_size_in_proper_unit(allocation_headroom), proper_unit_for_byte_size(allocation_headroom));
    _last_trigger = RATE;
    return true;
  }

  bool is_spiking = _allocation_rate.is_spiking(rate, _spike_threshold_sd);
  if (is_spiking && avg_cycle_time > allocation_headroom / rate) {
    log_trigger("Average GC time (%.2f ms) is above the time for instantaneous allocation rate (%.0f %sB/s) to deplete free headroom (%zu%s) (spike threshold = %.2f)",
                 avg_cycle_time * 1000,
                 byte_size_in_proper_unit(rate), proper_unit_for_byte_size(rate),
                 byte_size_in_proper_unit(allocation_headroom), proper_unit_for_byte_size(allocation_headroom),
                 _spike_threshold_sd);
    _last_trigger = SPIKE;
    return true;
  }

  return ShenandoahHeuristics::should_start_gc();
}

void ShenandoahAdaptiveHeuristics::adjust_last_trigger_parameters(double amount) {
  switch (_last_trigger) {
    case RATE:
      adjust_margin_of_error(amount);
      break;
    case SPIKE:
      adjust_spike_threshold(amount);
      break;
    case OTHER:
      // nothing to adjust here.
      break;
    default:
      ShouldNotReachHere();
  }
}

void ShenandoahAdaptiveHeuristics::adjust_margin_of_error(double amount) {
  _margin_of_error_sd = saturate(_margin_of_error_sd + amount, MINIMUM_CONFIDENCE, MAXIMUM_CONFIDENCE);
  log_debug(gc, ergo)("Margin of error now %.2f", _margin_of_error_sd);
}

void ShenandoahAdaptiveHeuristics::adjust_spike_threshold(double amount) {
  _spike_threshold_sd = saturate(_spike_threshold_sd - amount, MINIMUM_CONFIDENCE, MAXIMUM_CONFIDENCE);
  log_debug(gc, ergo)("Spike threshold now: %.2f", _spike_threshold_sd);
}

size_t ShenandoahAdaptiveHeuristics::min_free_threshold() {
  // Note that soft_max_capacity() / 100 * min_free_threshold is smaller than max_capacity() / 100 * min_free_threshold.
  // We want to behave conservatively here, so use max_capacity().  By returning a larger value, we cause the GC to
  // trigger when the remaining amount of free shrinks below the larger threshold.
  return _space_info->max_capacity() / 100 * ShenandoahMinFreeThreshold;
}

ShenandoahAllocationRate::ShenandoahAllocationRate() :
  _last_sample_time(os::elapsedTime()),
  _last_sample_value(0),
  _interval_sec(1.0 / ShenandoahAdaptiveSampleFrequencyHz),
  _rate(int(ShenandoahAdaptiveSampleSizeSeconds * ShenandoahAdaptiveSampleFrequencyHz), ShenandoahAdaptiveDecayFactor),
  _rate_avg(int(ShenandoahAdaptiveSampleSizeSeconds * ShenandoahAdaptiveSampleFrequencyHz), ShenandoahAdaptiveDecayFactor) {
}

double ShenandoahAllocationRate::average_rate(double sds) const {
  double avg = _rate_avg.avg();
  double computed_sd = _rate_avg.sd();
#ifdef KELVIN_DEVELOPMENT
  log_info(gc)("average_rate computed from prediction: %.3f, computed_sd: %.3f, sds: %.3f, result: %.3f",
               avg, computed_sd, sds, avg + (sds * computed_sd));
#endif
  return avg + (sds * computed_sd);
}

double ShenandoahAllocationRate::sample(size_t allocated) {
  double now = os::elapsedTime();
  double rate = 0.0;
  if (now - _last_sample_time > _interval_sec) {
    if (allocated >= _last_sample_value) {
      rate = instantaneous_rate(now, allocated);
      _rate.add(rate);
      _rate_avg.add(_rate.avg());
    }

    _last_sample_time = now;
    _last_sample_value = allocated;
  }
  return rate;
}

double ShenandoahAllocationRate::upper_bound(double sds) const {
  // Here we are using the standard deviation of the computed running
  // average, rather than the standard deviation of the samples that went
  // into the moving average. This is a much more stable value and is tied
  // to the actual statistic in use (moving average over samples of averages).
  return _rate.davg() + (sds * _rate_avg.dsd());
}

void ShenandoahAllocationRate::allocation_counter_reset() {
  _last_sample_time = os::elapsedTime();
  _last_sample_value = 0;
}

bool ShenandoahAllocationRate::is_spiking(double rate, double threshold) const {
  if (rate <= 0.0) {
    return false;
  }

  double sd = _rate.sd();
  if (sd > 0) {
    // There is a small chance that that rate has already been sampled, but it
    // seems not to matter in practice.
    double z_score = (rate - _rate.avg()) / sd;
    if (z_score > threshold) {
      return true;
    }
  }
  return false;
}

double ShenandoahAllocationRate::instantaneous_rate(double time, size_t allocated) const {
  size_t last_value = _last_sample_value;
  double last_time = _last_sample_time;
  size_t allocation_delta = (allocated > last_value) ? (allocated - last_value) : 0;
  double time_delta_sec = time - last_time;
  return (time_delta_sec > 0)  ? (allocation_delta / time_delta_sec) : 0;
}

ShenandoahPhaseTimeEstimator::ShenandoahPhaseTimeEstimator() :
  _changed(true),
  _first_index(0),
  _num_samples(0),
  _sum_of_samples(0.0),
  _sum_of_x(0.0),
  _sum_of_xx(0.0) { }

void ShenandoahPhaseTimeEstimator::add_sample(double sample) {
  if (_num_samples >= Samples) {
    _sum_of_samples -= _sample_array[_first_index];
    _num_samples--;
    _first_index++;
    if (_first_index == Samples) {
      _first_index = 0;
    }
  } else {
    _sum_of_x += _num_samples;
    double xx = _num_samples * _num_samples;
    _sum_of_xx += xx;
  }
  assert(_num_samples < Samples, "Unexpected overflow of ShenandoahPhaseTimeEstimator samples");
  assert(_first_index < Samples, "Unexpected overflow");

  _sum_of_samples += sample;
  _sample_array[(_first_index + _num_samples++) % Samples] = sample;
  _changed = true;
}

double ShenandoahPhaseTimeEstimator::predict_next() {
  if (!_changed) {
    return _next_prediction;
  } else if (_num_samples > 0) {
    double samples[Samples];
    double mean = _sum_of_samples / _num_samples;
    double sum_of_squared_deviations = 0.0;
    double sum_of_xy = 0.0;
    for (uint i = 0; i < _num_samples; i++) {
      uint index = (_first_index + i) % Samples;
      double sample = _sample_array[index];
      samples[i] = sample;
      sum_of_xy = i * sample;
      double delta = mean - sample;
      sum_of_squared_deviations += delta * delta;
    }
    double standard_deviation = sqrt(sum_of_squared_deviations / _num_samples);
    double prediction_by_average = mean + standard_deviation;
    double prediction_by_trend = prediction_by_average;
    
    if (_num_samples > 2) {
      double m = (_num_samples * sum_of_xy - _sum_of_x * _sum_of_samples) / (_num_samples * _sum_of_xx - _sum_of_x * _sum_of_x);
      double b = (_sum_of_samples - m * _sum_of_x) / _num_samples;
      sum_of_squared_deviations = 0;
      for (uint i = 0; i < _num_samples; i++) {
        double estimated_y = b + m * i;
        double delta = estimated_y - samples[i];
        sum_of_squared_deviations = delta * delta;
      }
      standard_deviation = sqrt(sum_of_squared_deviations / _num_samples);
      prediction_by_trend = b + m * _num_samples + standard_deviation;;
    }
    _next_prediction = MAX2(prediction_by_average, prediction_by_trend);
    _changed = false;
    return _next_prediction;
  } else {
    return 0.0;
  }
}
