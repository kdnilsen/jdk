/*
 * Copyright (c) 2002, 2025, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
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
 */

/**
 * <p>Interfaces for remote access to
 * JMX MBean servers.
 * This package defines the essential interfaces for making a JMX
 * MBean server manageable remotely.</p>
 *
 * <p>JMX defines the notion of <b>connectors</b>.
 * A connector is attached to a JMX API MBean server and makes it
 * accessible to remote Java clients. The client end of a
 * connector exports essentially the same interface as the MBean
 * server, specifically the {@link
 * javax.management.MBeanServerConnection MBeanServerConnection}
 * interface.</p>
 *
 * <p>A connector makes an MBean server remotely accessible through
 * a given protocol.
 *
 *      <ul>
 *        <li>The JMX Remote API defines a standard connector,
 *     the <b>RMI Connector</b>, which provides remote access to an
 *     MBeanServer through RMI.
 *
 *        <li>Other connector protocols are also possible using the
 *     {@link javax.management.remote.JMXConnectorFactory
 *     JMXConnectorFactory}.
 *     </ul>
 *
 *       <h2>Connector addresses</h2>
 *
 *       <p>Typically, a connector server has an address, represented by the
 *     class {@link javax.management.remote.JMXServiceURL
 *     JMXServiceURL}.  An address for the RMI Connector can look
 *     like this:</p>
 *
 *       <pre>
 *       service:jmx:rmi:///jndi/rmi://myhost:1099/myname
 *       </pre>
 *
 *       <p>In this <code>JMXServiceURL</code>, the first <code>rmi:</code>
 *         specifies the RMI connector, while the second <code>rmi:</code>
 *         specifies the RMI registry into which the RMI connector server
 *         has stored its stub.
 *
 *       <p>The example above shows only one form of address.
 *         An address for the RMI Connector can take several forms,
 *     as detailed in the documentation for the package
 *     <code><a href="{@docRoot}/java.management.rmi/javax/management/remote/rmi/package-summary.html">javax.management.remote.rmi</a></code>.</p>
 *
 *       <h2>Creating a connector server</h2>
 *
 *       <p>A connector server is created by constructing an instance of
 *     a subclass of {@link
 *     javax.management.remote.JMXConnectorServer
 *     JMXConnectorServer}.  Usually, this instance is created
 *         using the method {@link
 *         javax.management.remote.JMXConnectorServerFactory#newJMXConnectorServer(JMXServiceURL,
 *         java.util.Map, javax.management.MBeanServer)
 *     JMXConnectorServerFactory.newJMXConnectorServer}.</p>
 *
 *       <p>Typically, a connector server is associated with an MBean
 *     server either by registering it in that MBean server, or by
 *     supplying the MBean server as a parameter when creating the
 *     connector server.</p>
 *
 *       <h2>Creating a connector client</h2>
 *
 *       <p>A connector client is usually created by supplying the
 *     <code>JMXServiceURL</code> of the connector server to connect to
 *         to the {@link
 *     javax.management.remote.JMXConnectorFactory#connect(JMXServiceURL)
 *     JMXConnectorFactory.connect} method.</p>
 *
 *       <p>For more specialized uses, a connector client can be created
 *     by directly instantiating a class that implements the {@link
 *     javax.management.remote.JMXConnector JMXConnector} interface,
 *     for example the class <a href="{@docRoot}/java.management.rmi/javax/management/remote/rmi/RMIConnector.html">RMIConnector</a>.</p>
 *
 *       <h2>Additional client or server parameters</h2>
 *
 *       <p>When creating a connector client or server, it is possible to
 *     supply an object of type {@link java.util.Map Map} that defines
 *     additional parameters.  Each entry in this Map has a key that is
 *     a string and an associated value whose type is appropriate for
 *     that key.  The standard keys defined by the JMX Remote API all
 *     begin with the string "<code>jmx.remote.</code>".  The document
 *     <em>JMX Remote API</em> lists these standard keys.</p>
 *
 *       <h2>Connection identifiers</h2>
 *
 *       <p>Every connection opened by a connector server has a string
 *     identifier, called its <b>connection id</b>.  This identifier
 *     appears in the {@link
 *     javax.management.remote.JMXConnectionNotification
 *     JMXConnectionNotification} events emitted by the connector
 *     server, in the list returned by {@link
 *     javax.management.remote.JMXConnectorServerMBean#getConnectionIds()
 *     getConnectionIds()}, and in the value
 *     returned by the client's {@link
 *     javax.management.remote.JMXConnector#getConnectionId()
 *     getConnectionId()} method.</p>
 *
 *       <p>As an example, a connection ID can look something like this:</p>
 *
 *       <pre>
 * rmi://192.18.1.9 username 1
 *       </pre>
 *
 *       <p>The formal grammar for connection ids that follow this
 *          convention is as follows (using the grammar notation from section 2.4 of
 *          <em>The Java Language Specification</em>):</p>
 *       <pre>
 * <em>ConnectionId:</em>
 *     <em>Protocol</em> : <em>ClientAddress<sub>opt</sub></em> Space <em>ClientId<sub>opt</sub></em> Space <em>ArbitraryText</em>
 *
 * <em>ClientAddress:</em>
 *     // <em>HostAddress</em> <em>ClientPort<sub>opt</sub></em>
 *
 * <em>ClientPort</em>
 *     : <em>HostPort</em>
 *       </pre>
 *
 *       <p>The <code><em>Protocol</em></code> is a protocol that would
 *     be recognized by {@link
 *     javax.management.remote.JMXConnectorFactory
 *     JMXConnectorFactory}.</p>
 *
 *       <p>The <code><em>ClientAddress</em></code> is the
 *     address and port of the connecting client, if these can be
 *     determined, otherwise nothing.  The
 *     <code><em>HostAddress</em></code> is the Internet address of
 *     the host that the client is connecting from, in numeric or DNS
 *     form.  Numeric IPv6 addresses are enclosed in square brackets
 *     <code>[]</code>.  The <code><em>HostPort</em></code> is the
 *     decimal port number that the client is connecting from.</p>
 *
 *       <p>The <code><em>ClientId</em></code> is the identity of the
 *     client entity, typically a string returned by {@link
 *     javax.management.remote.JMXPrincipal#getName()
 *     JMXPrincipal.getName()}.  This string must not contain
 *     spaces.</p>
 *
 *       <p>The <code><em>ArbitraryText</em></code> is any additional
 *     text that the connector server adds when creating the client id.
 *     At a minimum, it must be enough to distinguish this connection
 *     ID from the ID of any other connection currently opened by this
 *     connector server.</p>
 *
 *
 *     @see <a href="https://jcp.org/aboutJava/communityprocess/mrel/jsr160/index2.html">
 *       JMX Specification, version 1.4</a>
 *
 *     @since 1.5
 */
package javax.management.remote;
