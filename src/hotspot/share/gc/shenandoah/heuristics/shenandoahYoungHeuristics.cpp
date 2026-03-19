/*
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

#include "gc/shenandoah/heuristics/shenandoahOldHeuristics.hpp"
#include "gc/shenandoah/heuristics/shenandoahYoungHeuristics.hpp"
#include "gc/shenandoah/shenandoahCollectorPolicy.hpp"
#include "gc/shenandoah/shenandoahFreeSet.hpp"
#include "gc/shenandoah/shenandoahGenerationalHeap.inline.hpp"
#include "gc/shenandoah/shenandoahHeapRegion.inline.hpp"
#include "gc/shenandoah/shenandoahOldGeneration.hpp"
#include "gc/shenandoah/shenandoahYoungGeneration.hpp"
#include "utilities/quickSort.hpp"

ShenandoahYoungHeuristics::ShenandoahYoungHeuristics(ShenandoahYoungGeneration* generation)
    : ShenandoahGenerationalHeuristics(generation),
      _young_live_words_not_in_most_recent_cset(0),
      _old_live_words_not_in_most_recent_cset(0),
      _remset_words_in_most_recent_mark_scan(0),
      _young_live_words_after_most_recent_mark(0),
      _young_words_most_recently_evacuated(0),
      _old_words_most_recently_evacuated(0),
      _words_most_recently_promoted(0),
      _regions_most_recently_promoted_in_place(0),
      _live_words_most_recently_promoted_in_place(0),
      _anticipated_pip_words(0) {
}

void ShenandoahYoungHeuristics::choose_collection_set_from_regiondata(ShenandoahCollectionSet* cset,
                                                                      RegionData* data, size_t size,
                                                                      size_t actual_free) {
  // See comments in ShenandoahAdaptiveHeuristics::choose_collection_set_from_regiondata():
  // we do the same here, but with the following adjustments for generational mode:
  //
  // In generational mode, the sort order within the data array is not strictly descending amounts
  // of garbage. In particular, regions that have reached tenure age will be sorted into this
  // array before younger regions that typically contain more garbage. This is one reason why,
  // for example, we continue examining regions even after rejecting a region that has
  // more live data than we can evacuate.
  ShenandoahGenerationalHeap* heap = ShenandoahGenerationalHeap::heap();
  bool need_to_finalize_mixed = heap->old_generation()->heuristics()->prime_collection_set(cset);

  // Better select garbage-first regions
  QuickSort::sort<RegionData>(data, size, compare_by_garbage);

  size_t cur_young_garbage = add_preselected_regions_to_collection_set(cset, data, size);

  choose_young_collection_set(cset, data, size, actual_free, cur_young_garbage);

  // Especially when young-gen trigger is expedited in order to finish mixed evacuations, there may not be
  // enough consolidated garbage to make effective use of young-gen evacuation reserve.  If there is still
  // young-gen reserve available following selection of the young-gen collection set, see if we can use
  // this memory to expand the old-gen evacuation collection set.
  need_to_finalize_mixed |= heap->old_generation()->heuristics()->top_off_collection_set(_add_regions_to_old);
  if (need_to_finalize_mixed) {
    heap->old_generation()->heuristics()->finalize_mixed_evacs();
  }

  size_t young_words_evacuated = cset->get_young_bytes_reserved_for_evacuation() / HeapWordSize;
  size_t old_words_evacuated = cset->get_old_bytes_reserved_for_evacuation() / HeapWordSize;
  set_young_words_most_recently_evacuated(young_words_evacuated);
  set_old_words_most_recently_evacuated(old_words_evacuated);

  // This memory will be updated in young
  size_t young_live_at_mark = get_young_live_words_after_most_recent_mark();
  size_t young_live_not_in_cset = young_live_at_mark - young_words_evacuated;
  set_young_live_words_not_in_most_recent_cset(young_live_not_in_cset);

  ShenandoahOldGeneration* old_gen = ShenandoahGenerationalHeap::heap()->old_generation();
  if (cset->has_old_regions()) {
    // This is a mixed collection.  We will need to update all of the old live that is not in the cset.
    // Treat all old-gen memory that was not placed into the mixed-candidates as live. Some of this will eventually
    // be coalesced and filled, but it is all going to be "updated". Consider any promotions following most recent
    // old mark to be "live" (now known to be dead, so must be updated). Note that there have not been any promotions
    // yet during this cycle, as we are just beginning to evacuate.
    size_t old_gen_used = old_gen->used() / HeapWordSize;
    size_t mixed_candidates_known_garbage = old_gen->unprocessed_collection_candidates_garbage() / HeapWordSize;
    size_t old_live_in_cset = cset->get_old_bytes_reserved_for_evacuation();
    size_t old_garbage_in_cset = cset->get_old_garbage();
    size_t old_live_not_in_cset = old_gen_used - (old_garbage_in_cset + old_live_in_cset + mixed_candidates_known_garbage);
    set_old_live_words_not_in_most_recent_cset(old_live_not_in_cset);
  }

  if (old_gen->has_in_place_promotions()) {
    size_t pip_words = old_gen->get_expected_in_place_promotable_live_words();
    set_live_words_most_recently_promoted_in_place(pip_words);
  } else {
    set_live_words_most_recently_promoted_in_place(0);
  }
}

void ShenandoahYoungHeuristics::choose_young_collection_set(ShenandoahCollectionSet* cset,
                                                            const RegionData* data,
                                                            size_t size, size_t actual_free,
                                                            size_t cur_young_garbage) const {

  const auto heap = ShenandoahGenerationalHeap::heap();

  const size_t capacity = heap->soft_max_capacity();
  const size_t garbage_threshold = ShenandoahHeapRegion::region_size_bytes() * ShenandoahGarbageThreshold / 100;
  const size_t ignore_threshold = ShenandoahHeapRegion::region_size_bytes() * ShenandoahIgnoreGarbageThreshold / 100;

  // This is young-gen collection or a mixed evacuation.
  // If this is mixed evacuation, the old-gen candidate regions have already been added.
  size_t cur_cset = 0;
  const size_t max_cset = (size_t) (heap->young_generation()->get_evacuation_reserve() / ShenandoahEvacWaste);
  const size_t free_target = (capacity * ShenandoahMinFreeThreshold) / 100 + max_cset;
  const size_t min_garbage = (free_target > actual_free) ? (free_target - actual_free) : 0;


  log_info(gc, ergo)(
          "Adaptive CSet Selection for YOUNG. Max Evacuation: %zu%s, Actual Free: %zu%s.",
          byte_size_in_proper_unit(max_cset), proper_unit_for_byte_size(max_cset),
          byte_size_in_proper_unit(actual_free), proper_unit_for_byte_size(actual_free));

  for (size_t idx = 0; idx < size; idx++) {
    ShenandoahHeapRegion* r = data[idx].get_region();
    if (cset->is_preselected(r->index())) {
      continue;
    }

    // Note that we do not add tenurable regions if they were not pre-selected.  They were not preselected
    // because there is insufficient room in old-gen to hold their to-be-promoted live objects or because
    // they are to be promoted in place.
    if (!heap->is_tenurable(r)) {
      const size_t new_cset = cur_cset + r->get_live_data_bytes();
      const size_t region_garbage = r->garbage();
      const size_t new_garbage = cur_young_garbage + region_garbage;
      const bool add_regardless = (region_garbage > ignore_threshold) && (new_garbage < min_garbage);
      assert(r->is_young(), "Only young candidates expected in the data array");
      if ((new_cset <= max_cset) && (add_regardless || (region_garbage > garbage_threshold))) {
        cur_cset = new_cset;
        cur_young_garbage = new_garbage;
        cset->add_region(r);
      }
    }
  }
}


bool ShenandoahYoungHeuristics::should_start_gc() {
  auto heap = ShenandoahGenerationalHeap::heap();
  ShenandoahOldGeneration* old_generation = heap->old_generation();
  ShenandoahOldHeuristics* old_heuristics = old_generation->heuristics();

  // Checks that an old cycle has run for at least ShenandoahMinimumOldTimeMs before allowing a young cycle.
  if (ShenandoahMinimumOldTimeMs > 0) {
    if (old_generation->is_preparing_for_mark() || old_generation->is_concurrent_mark_in_progress()) {
      size_t old_time_elapsed = size_t(old_heuristics->elapsed_cycle_time() * 1000);
      if (old_time_elapsed < ShenandoahMinimumOldTimeMs) {
        // Do not decline_trigger() when waiting for minimum quantum of Old-gen marking.  It is not at our discretion
        // to trigger at this time.
        log_debug(gc)("Young heuristics declines to trigger because old_time_elapsed < ShenandoahMinimumOldTimeMs");
        return false;
      }
    }
  }

  // inherited triggers have already decided to start a cycle, so no further evaluation is required
  if (ShenandoahAdaptiveHeuristics::should_start_gc()) {
    // ShenandoahAdaptiveHeuristics::should_start_gc() has already accepted trigger, or declined it.
    return true;
  }

#ifdef KELVIN_ORIGINAL_EXPEDITE_PROMO
  // Get through promotions and mixed evacuations as quickly as possible.  These cycles sometimes require significantly
  // more time than traditional young-generation cycles so start them up as soon as possible.  This is a "mitigation"
  // for the reality that old-gen and young-gen activities are not truly "concurrent".  If there is old-gen work to
  // be done, we start up the young-gen GC threads so they can do some of this old-gen work.  As implemented, promotion
  // gets priority over old-gen marking.
  size_t promo_expedite_threshold = percent_of(heap->young_generation()->max_capacity(), ShenandoahExpeditePromotionsThreshold);
  size_t promo_potential = old_generation->get_promotion_potential();
  if (promo_potential > promo_expedite_threshold) {
    // Detect unsigned arithmetic underflow
    assert(promo_potential < heap->capacity(), "Sanity");
    log_trigger("Expedite promotion of " PROPERFMT, PROPERFMTARGS(promo_potential));
    accept_trigger();
    return true;
  }
#endif

#ifdef KELVIN_ORIGINAL_EXPEDITE_MIXED
  size_t mixed_candidates = old_heuristics->unprocessed_old_collection_candidates();
  if (mixed_candidates > ShenandoahExpediteMixedThreshold && !heap->is_concurrent_weak_root_in_progress()) {
    // We need to run young GC in order to open up some free heap regions so we can finish mixed evacuations.
    // If concurrent weak root processing is in progress, it means the old cycle has chosen mixed collection
    // candidates, but has not completed. There is no point in trying to start the young cycle before the old
    // cycle completes.
    log_trigger("Expedite mixed evacuation of %zu regions", mixed_candidates);
    accept_trigger();
    return true;
  }
#endif

  // Don't decline_trigger() here  That was done in ShenandoahAdaptiveHeuristics::should_start_gc()
  return false;
}

// Return a conservative estimate of how much memory can be allocated before we need to start GC. The estimate is based
// on memory that is currently available within young generation plus all of the memory that will be added to the young
// generation at the end of the current cycle (as represented by young_regions_to_be_reclaimed) and on the anticipated
// amount of time required to perform a GC.
size_t ShenandoahYoungHeuristics::bytes_of_allocation_runway_before_gc_trigger(size_t young_regions_to_be_reclaimed) {
  size_t capacity = _space_info->max_capacity();
  size_t usage = _space_info->used();
  size_t available = (capacity > usage)? capacity - usage: 0;
  size_t allocated = _free_set->get_bytes_allocated_since_gc_start();

  size_t available_young_collected = ShenandoahHeap::heap()->collection_set()->get_young_available_bytes_collected();
  size_t anticipated_available =
          available + young_regions_to_be_reclaimed * ShenandoahHeapRegion::region_size_bytes() - available_young_collected;
  size_t spike_headroom = capacity * ShenandoahAllocSpikeFactor / 100;
  size_t penalties      = capacity * _gc_time_penalties / 100;

  double rate = _allocation_rate.sample(allocated);

  // At what value of available, would avg and spike triggers occur?
  //  if allocation_headroom < avg_cycle_time * avg_alloc_rate, then we experience avg trigger
  //  if allocation_headroom < avg_cycle_time * rate, then we experience spike trigger if is_spiking
  //
  // allocation_headroom =
  //     0, if penalties > available or if penalties + spike_headroom > available
  //     available - penalties - spike_headroom, otherwise
  //
  // so we trigger if available - penalties - spike_headroom < avg_cycle_time * avg_alloc_rate, which is to say
  //                  available < avg_cycle_time * avg_alloc_rate + penalties + spike_headroom
  //            or if available < penalties + spike_headroom
  //
  // since avg_cycle_time * avg_alloc_rate > 0, the first test is sufficient to test both conditions
  //
  // thus, evac_slack_avg is MIN2(0,  available - avg_cycle_time * avg_alloc_rate + penalties + spike_headroom)
  //
  // similarly, evac_slack_spiking is MIN2(0, available - avg_cycle_time * rate + penalties + spike_headroom)
  // but evac_slack_spiking is only relevant if is_spiking, as defined below.

  double avg_cycle_time = _gc_cycle_time_history->davg() + (_margin_of_error_sd * _gc_cycle_time_history->dsd());
  double avg_alloc_rate = _allocation_rate.upper_bound(_margin_of_error_sd);
  size_t evac_slack_avg;
  if (anticipated_available > avg_cycle_time * avg_alloc_rate + penalties + spike_headroom) {
    evac_slack_avg = anticipated_available - (avg_cycle_time * avg_alloc_rate + penalties + spike_headroom);
  } else {
    // we have no slack because it's already time to trigger
    evac_slack_avg = 0;
  }

  bool is_spiking = _allocation_rate.is_spiking(rate, _spike_threshold_sd);
  size_t evac_slack_spiking;
  if (is_spiking) {
    if (anticipated_available > avg_cycle_time * rate + penalties + spike_headroom) {
      evac_slack_spiking = anticipated_available - (avg_cycle_time * rate + penalties + spike_headroom);
    } else {
      // we have no slack because it's already time to trigger
      evac_slack_spiking = 0;
    }
  } else {
    evac_slack_spiking = evac_slack_avg;
  }

  size_t threshold = min_free_threshold();
  size_t evac_min_threshold = (anticipated_available > threshold)? anticipated_available - threshold: 0;
  return MIN3(evac_slack_spiking, evac_slack_avg, evac_min_threshold);
}

double ShenandoahYoungHeuristics::predict_gc_time(size_t mark_words) {
  assert(mark_words != 0, "(mark_words == 0) implies linear prediction of gc time");
  double mark_time = predict_mark_time(mark_words);
  double evac_time = predict_evac_time(get_anticipated_evac_words(), get_anticipated_pip_words());
  double update_time = predict_update_time(get_anticipated_update_words());
  if ((mark_time == 0.0) || (evac_time == 0.0) || (update_time == 0.0)) {
#undef KELVIN_PREDICT
#ifdef KELVIN_PREDICT
    log_info(gc)("YH(" PTR_FORMAT ")::predict_gc(%zu): %.3f from short circuit", p2i(this), mark_words, 0.0);
#endif
    return 0.0;
  } else {
    double result = mark_time + evac_time + update_time;
#ifdef KELVIN_PREDICT
    log_info(gc)("YH(" PTR_FORMAT ")::predict_gc(%zu): %.3f from mark(): %.3f, evac(%zu, %zu): %.3f, update(%zu): %.3f returns %.3f",
                 p2i(this), mark_words, result, mark_time, get_anticipated_evac_words(), get_anticipated_pip_words(),
                 evac_time, get_anticipated_update_words(), update_time, result);
#endif
    return result;
  }
}

double ShenandoahYoungHeuristics::predict_evac_time(size_t anticipated_evac_words, size_t anticipated_pip_words) {
  return _phase_stats[ShenandoahMajorGCPhase::_evac].predict_at((double) (5 * anticipated_evac_words + anticipated_pip_words));
}

double ShenandoahYoungHeuristics::predict_final_roots_time(size_t anticipated_pip_words) {
  return _phase_stats[ShenandoahMajorGCPhase::_final_roots].predict_at((double) anticipated_pip_words);
}

void ShenandoahYoungHeuristics:: update_anticipated_after_completed_gc(size_t old_cset_regions, size_t young_cset_regions,
                                                                       ShenandoahOldGeneration* old_gen,
                                                                       ShenandoahYoungGeneration* young_gen,
                                                                       size_t promo_potential_words, size_t pip_potential_words,
                                                                       size_t mixed_candidate_live_words,
                                                                       size_t mixed_candidate_garbage_words)
{
  if ((mixed_candidate_live_words + promo_potential_words == 0)) {
    // No need for any reserve in old.  Setting anticipated_mark_words to zero denotes that we use pre-existing linear
    // predictor for gc-time estimates.
#undef KELVIN_MARK_WORDS
#ifdef KELVIN_MARK_WORDS
    log_info(gc)("SYH(" PTR_FORMAT ")::set_anticipated_after_completed_gc() zeros mark_words because mixed: %zu, promo: %zu",
                 p2i(this), mixed_candidate_live_words, promo_potential_words);
#endif
    set_anticipated_mark_words(0);
    return;
  } else {
    // Assume the memory is available to perform "maximal" GC cycles.  As such, we'll be planning "large" efforts.
    // If memory supply is constrained, we'll want to trigger early so we can catch up. Triggering early is reinforced
    // by overestimating how long the GC cycle will take.
    size_t proposed_young_reserve_words = (young_gen->max_capacity() * ShenandoahEvacReserve) / (100 * HeapWordSize);

    // Note that proposed_old_reserve = (size_t) ((proposed_total_reserve * ShenandoahOldEvacPercent) / 100);
    //           proposed_total_reserve = 100 * proposed_old_reserve / ShenandoahOldEvacPercent
    //           proposed_total_reserve = proposed_old_reserve + proposed_young_reserve
    //           proposed_old_reserve + proposed_young_reserve = 100 * proposed_old_reserve / ShenandoahOldEvacPercent
    //           proposed_old_reserve * (1 - 100 / ShenandoahOldEvacPercent) = - proposed_young_reserve;
    //           proposed_old_reserve = ((100 / ShenandoahOldEvacPercent) - 1) * proposed_young_reserve
    //           proposed_old_reserve = proposed_young_reserve / ((100 - ShenandoahOldEvacPercent) / ShenandoahOldEvacPercent)
    //           proposed_old_reserve = proposed_young_reserve * ShenandoahOldEvacPercent / (100 - ShenandoahOldEvacPercent);
    size_t proposed_old_reserve_words = proposed_young_reserve_words * ShenandoahOldEvacPercent / (100 - ShenandoahOldEvacPercent);
    size_t proposed_total_reserve_words = proposed_old_reserve_words + proposed_young_reserve_words;

    // Anticipate that we will share collector reserves between old and young.  Usually, this allows us to evacuate more
    // old than was "proposed".
    size_t anticipated_young_evac_words = get_young_words_most_recently_evacuated();
    size_t anticipated_young_reserve_words = (size_t) (anticipated_young_evac_words * ShenandoahEvacWaste);
    size_t anticipated_old_reserve_words = proposed_total_reserve_words - anticipated_young_reserve_words;
    size_t anticipated_old_evac_words = (size_t) (anticipated_old_reserve_words / ShenandoahOldEvacWaste);

    // Remember the total potential mixed candidate live.  We use this to estimate update burden.
    size_t mixed_candidate_live_potential = mixed_candidate_live_words;
    size_t old_evac_potential_words = promo_potential_words + mixed_candidate_live_words;
    if (anticipated_old_evac_words < old_evac_potential_words) {
      size_t old_evac_overflow_words = old_evac_potential_words - anticipated_old_evac_words;
      old_evac_potential_words = anticipated_old_evac_words;
      if (old_evac_overflow_words < promo_potential_words) {
        promo_potential_words -= old_evac_overflow_words;
        // dead_code: old_evac_overflow_words = 0;
      } else {
        old_evac_overflow_words -= promo_potential_words;
        promo_potential_words = 0;
        if (old_evac_overflow_words < mixed_candidate_live_words) {
          mixed_candidate_live_words -= old_evac_overflow_words;
          // dead code: old_evac_overflow_words = 0;
        } else {
          // dead_code: old_evac_overflow_words -= mixed_candidate_live_words;
          mixed_candidate_live_words = 0;
        }
      }
    }
    anticipated_old_evac_words = promo_potential_words + mixed_candidate_live_words;
    size_t anticipated_young_update = get_young_live_words_not_in_most_recent_cset();
    size_t anticipated_old_update;
    if (mixed_candidate_live_words > 0) {
      anticipated_old_update = old_gen->used() / HeapWordSize - mixed_candidate_live_words;
    } else {
      anticipated_old_update = get_remset_words_in_most_recent_mark_scan();
    }

#ifdef KELVIN_MARK_WORDS
    log_info(gc)("SYH(" PTR_FORMAT ")::set_anticipated_after_completed_gc() non-zero mark_words because mixed: %zu, promo: %zu",
                 p2i(this), mixed_candidate_live_words, promo_potential_words);
#endif
    // We'll assume all promotion is by evacuation.  If we find out following mark that some of the promotion will be
    // in place, we will adjust anticipation there.
    set_anticipated_pip_words(0);
    set_anticipated_mark_words(get_young_live_words_after_most_recent_mark());
    set_anticipated_evac_words(anticipated_young_evac_words + anticipated_old_evac_words);
    set_anticipated_update_words(anticipated_old_update + anticipated_young_update);
  }
}
