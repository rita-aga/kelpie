//! Simulated RPC Transport for DST
//!
//! TigerStyle: Bridge between SimNetwork and RpcTransport for testing production
//! cluster code under simulated network conditions (partitions, delays, faults).
//!
//! This allows running production `Cluster` code with:
//! - Network partitions (bidirectional and one-way)
//! - Message delays and jitter
//! - Packet loss and corruption
//! - Deterministic message delivery

use crate::clock::SimClock;
use crate::network::SimNetwork;
use crate::rng::DeterministicRng;
use async_trait::async_trait;
use bytes::Bytes;
use kelpie_cluster::{
    ClusterError, ClusterResult, RequestId, RpcHandler, RpcMessage, RpcTransport,
};
use kelpie_registry::NodeId;
use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;

/// Simulated RPC transport for DST
///
/// Implements `RpcTransport` trait using `SimNetwork` underneath.
/// Allows testing production Cluster code with network partitions.
///
/// # Example
///
/// ```rust,ignore
/// use kelpie_dst::{SimClock, SimNetwork, SimRpcTransport, DeterministicRng, FaultInjectorBuilder};
/// use kelpie_cluster::{Cluster, ClusterConfig};
///
/// let clock = SimClock::from_millis(1000);
/// let rng = DeterministicRng::new(42);
/// let fault_injector = FaultInjectorBuilder::new(rng.fork()).build();
/// let network = SimNetwork::new(clock.clone(), rng, Arc::new(fault_injector));
///
/// let transport = SimRpcTransport::new(
///     NodeId::new("node-1").unwrap(),
///     "127.0.0.1:8001".parse().unwrap(),
///     Arc::new(network),
///     clock,
/// );
///
/// // Use with production Cluster
/// let cluster = Cluster::with_time_provider(
///     node, config, registry, Arc::new(transport), runtime, clock,
/// );
/// ```
pub struct SimRpcTransport {
    /// Local node ID
    node_id: NodeId,
    /// Local address (for interface compatibility)
    local_addr: SocketAddr,
    /// Shared simulated network
    network: Arc<SimNetwork>,
    /// Simulation clock for timeouts
    clock: SimClock,
    /// Handler for incoming messages
    handler: Arc<RwLock<Option<Box<dyn RpcHandler>>>>,
    /// Node ID to address mapping (for address lookups)
    node_addrs: Arc<RwLock<HashMap<NodeId, SocketAddr>>>,
    /// Pending requests waiting for responses
    pending: Arc<RwLock<HashMap<RequestId, tokio::sync::oneshot::Sender<RpcMessage>>>>,
    /// Next request ID
    next_request_id: AtomicU64,
    /// Whether the transport is running
    running: AtomicBool,
    /// Message processing task handle (for receive loop)
    _processing: Arc<RwLock<Option<()>>>,
}

impl SimRpcTransport {
    /// Create a new simulated RPC transport
    pub fn new(
        node_id: NodeId,
        local_addr: SocketAddr,
        network: Arc<SimNetwork>,
        clock: SimClock,
    ) -> Self {
        Self {
            node_id,
            local_addr,
            network,
            clock,
            handler: Arc::new(RwLock::new(None)),
            node_addrs: Arc::new(RwLock::new(HashMap::new())),
            pending: Arc::new(RwLock::new(HashMap::new())),
            next_request_id: AtomicU64::new(1),
            running: AtomicBool::new(false),
            _processing: Arc::new(RwLock::new(None)),
        }
    }

    /// Register a node's address
    pub async fn register_node(&self, node_id: NodeId, addr: SocketAddr) {
        let mut addrs = self.node_addrs.write().await;
        addrs.insert(node_id, addr);
    }

    /// Get next request ID
    pub fn next_request_id(&self) -> RequestId {
        self.next_request_id.fetch_add(1, Ordering::SeqCst)
    }

    /// Get access to the underlying SimNetwork for partition control
    pub fn network(&self) -> &SimNetwork {
        &self.network
    }

    /// Process incoming messages (called in receive loop)
    async fn process_incoming(&self) {
        let messages = self.network.receive(self.node_id.as_str()).await;

        for msg in messages {
            // Deserialize the RPC message
            let rpc_msg: RpcMessage = match serde_json::from_slice(&msg.payload) {
                Ok(m) => m,
                Err(e) => {
                    tracing::warn!(
                        node = %self.node_id,
                        error = %e,
                        "Failed to deserialize RPC message"
                    );
                    continue;
                }
            };

            // Check if this is a response to a pending request
            if rpc_msg.is_response() {
                if let Some(request_id) = rpc_msg.request_id() {
                    let mut pending = self.pending.write().await;
                    if let Some(sender) = pending.remove(&request_id) {
                        let _ = sender.send(rpc_msg);
                        continue;
                    }
                }
            }

            // Handle incoming request via RpcHandler
            let handler_guard = self.handler.read().await;
            if let Some(ref h) = *handler_guard {
                let from_node = match NodeId::new(&msg.from) {
                    Ok(id) => id,
                    Err(_) => continue,
                };

                if let Some(response) = h.handle(&from_node, rpc_msg).await {
                    // Send response back
                    if let Ok(response_bytes) = serde_json::to_vec(&response) {
                        self.network
                            .send(
                                self.node_id.as_str(),
                                &msg.from,
                                Bytes::from(response_bytes),
                            )
                            .await;
                    }
                }
            }
        }
    }
}

#[async_trait]
impl RpcTransport for SimRpcTransport {
    async fn send(&self, target: &NodeId, message: RpcMessage) -> ClusterResult<()> {
        // Serialize message
        let payload = serde_json::to_vec(&message).map_err(|e| ClusterError::Internal {
            message: format!("Failed to serialize message: {}", e),
        })?;

        // Send through SimNetwork
        let sent = self
            .network
            .send(self.node_id.as_str(), target.as_str(), Bytes::from(payload))
            .await;

        if sent {
            Ok(())
        } else {
            Err(ClusterError::node_unreachable(target, "network partition"))
        }
    }

    async fn send_and_recv(
        &self,
        target: &NodeId,
        message: RpcMessage,
        timeout: Duration,
    ) -> ClusterResult<RpcMessage> {
        let request_id = message.request_id().ok_or_else(|| ClusterError::Internal {
            message: "message has no request ID".into(),
        })?;

        // Set up response channel
        let (tx, mut rx) = tokio::sync::oneshot::channel();
        {
            let mut pending = self.pending.write().await;
            pending.insert(request_id, tx);
        }

        // Send the message
        if let Err(e) = self.send(target, message).await {
            let mut pending = self.pending.write().await;
            pending.remove(&request_id);
            return Err(e);
        }

        // Wait for response with simulated timeout
        // In DST, we advance clock and poll for messages
        let start_time = self.clock.now_ms();
        let timeout_ms = timeout.as_millis() as u64;

        loop {
            // Process any incoming messages
            self.process_incoming().await;

            // Check if response arrived
            match rx.try_recv() {
                Ok(response) => return Ok(response),
                Err(tokio::sync::oneshot::error::TryRecvError::Empty) => {
                    // Not yet, check timeout
                    if self.clock.now_ms() - start_time >= timeout_ms {
                        let mut pending = self.pending.write().await;
                        pending.remove(&request_id);
                        return Err(ClusterError::rpc_timeout(target, timeout_ms));
                    }
                    // Yield to allow other tasks
                    tokio::task::yield_now().await;
                }
                Err(tokio::sync::oneshot::error::TryRecvError::Closed) => {
                    let mut pending = self.pending.write().await;
                    pending.remove(&request_id);
                    return Err(ClusterError::rpc_failed(target, "response channel closed"));
                }
            }
        }
    }

    async fn broadcast(&self, message: RpcMessage) -> ClusterResult<()> {
        let addrs = self.node_addrs.read().await;
        for (node_id, _) in addrs.iter() {
            if node_id != &self.node_id {
                // Ignore send failures during broadcast
                let _ = self.send(node_id, message.clone()).await;
            }
        }
        Ok(())
    }

    async fn set_handler(&self, handler: Box<dyn RpcHandler>) -> ClusterResult<()> {
        let mut h = self.handler.write().await;
        *h = Some(handler);
        Ok(())
    }

    async fn start(&self) -> ClusterResult<()> {
        if self.running.swap(true, Ordering::SeqCst) {
            return Err(ClusterError::AlreadyStarted);
        }
        tracing::info!(
            node = %self.node_id,
            addr = %self.local_addr,
            "SimRpcTransport started"
        );
        Ok(())
    }

    async fn stop(&self) -> ClusterResult<()> {
        self.running.store(false, Ordering::SeqCst);
        tracing::info!(node = %self.node_id, "SimRpcTransport stopped");
        Ok(())
    }

    fn local_addr(&self) -> SocketAddr {
        self.local_addr
    }
}

/// Builder for creating multiple SimRpcTransport instances sharing the same SimNetwork
///
/// This is useful for creating multi-node cluster tests with partition simulation.
pub struct SimRpcTransportBuilder {
    network: Arc<SimNetwork>,
    clock: SimClock,
}

impl SimRpcTransportBuilder {
    /// Create a new builder with shared network and clock
    pub fn new(network: Arc<SimNetwork>, clock: SimClock) -> Self {
        Self { network, clock }
    }

    /// Create a new builder from individual components
    pub fn from_components(clock: SimClock, rng: DeterministicRng) -> Self {
        use crate::fault::FaultInjectorBuilder;
        let fault_injector = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        let network = Arc::new(SimNetwork::new(clock.clone(), rng, fault_injector));
        Self::new(network, clock)
    }

    /// Build a transport for a specific node
    pub fn build(&self, node_id: NodeId, addr: SocketAddr) -> SimRpcTransport {
        SimRpcTransport::new(node_id, addr, self.network.clone(), self.clock.clone())
    }

    /// Get access to the shared network for partition control
    pub fn network(&self) -> &SimNetwork {
        &self.network
    }

    /// Get access to the shared clock
    pub fn clock(&self) -> &SimClock {
        &self.clock
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fault::FaultInjectorBuilder;

    fn test_node_id(n: u32) -> NodeId {
        NodeId::new(format!("node-{}", n)).unwrap()
    }

    fn test_addr(port: u16) -> SocketAddr {
        use std::net::{IpAddr, Ipv4Addr};
        SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), port)
    }

    fn create_test_network(clock: SimClock) -> Arc<SimNetwork> {
        let rng = DeterministicRng::new(42);
        let fault_injector = Arc::new(FaultInjectorBuilder::new(rng.fork()).build());
        Arc::new(SimNetwork::new(clock, rng, fault_injector).with_latency(0, 0))
    }

    #[tokio::test]
    async fn test_sim_rpc_transport_create() {
        let clock = SimClock::from_millis(0);
        let network = create_test_network(clock.clone());
        let transport = SimRpcTransport::new(test_node_id(1), test_addr(8001), network, clock);

        assert_eq!(transport.local_addr(), test_addr(8001));
    }

    #[tokio::test]
    async fn test_sim_rpc_transport_start_stop() {
        let clock = SimClock::from_millis(0);
        let network = create_test_network(clock.clone());
        let transport = SimRpcTransport::new(test_node_id(1), test_addr(8001), network, clock);

        // Start
        transport.start().await.unwrap();

        // Double start should fail
        let result = transport.start().await;
        assert!(matches!(result, Err(ClusterError::AlreadyStarted)));

        // Stop
        transport.stop().await.unwrap();
    }

    #[tokio::test]
    async fn test_sim_rpc_transport_send_with_partition() {
        use kelpie_registry::NodeStatus;

        let clock = SimClock::from_millis(0);
        let network = create_test_network(clock.clone());

        let transport1 = SimRpcTransport::new(
            test_node_id(1),
            test_addr(8001),
            network.clone(),
            clock.clone(),
        );
        let transport2 =
            SimRpcTransport::new(test_node_id(2), test_addr(8002), network.clone(), clock);

        // Start both
        transport1.start().await.unwrap();
        transport2.start().await.unwrap();

        // Register addresses
        transport1
            .register_node(test_node_id(2), test_addr(8002))
            .await;
        transport2
            .register_node(test_node_id(1), test_addr(8001))
            .await;

        // Send without partition - should succeed
        let heartbeat = RpcMessage::Heartbeat(kelpie_registry::Heartbeat::new(
            test_node_id(1),
            1000,
            NodeStatus::Active,
            0,
            100,
            1,
        ));
        let result = transport1.send(&test_node_id(2), heartbeat.clone()).await;
        assert!(result.is_ok(), "Send should succeed without partition");

        // Create partition
        network.partition("node-1", "node-2").await;

        // Send with partition - should fail
        let result = transport1.send(&test_node_id(2), heartbeat).await;
        assert!(result.is_err(), "Send should fail with partition");
        assert!(matches!(result, Err(ClusterError::NodeUnreachable { .. })));

        // Heal partition
        network.heal("node-1", "node-2").await;

        // Send after heal - should succeed
        let heartbeat = RpcMessage::Heartbeat(kelpie_registry::Heartbeat::new(
            test_node_id(1),
            1000,
            NodeStatus::Active,
            0,
            100,
            2,
        ));
        let result = transport1.send(&test_node_id(2), heartbeat).await;
        assert!(result.is_ok(), "Send should succeed after heal");
    }

    #[tokio::test]
    async fn test_sim_rpc_transport_builder() {
        let clock = SimClock::from_millis(0);
        let rng = DeterministicRng::new(42);
        let builder = SimRpcTransportBuilder::from_components(clock, rng);

        let _transport1 = builder.build(test_node_id(1), test_addr(8001));
        let _transport2 = builder.build(test_node_id(2), test_addr(8002));

        // Both should share the same network
        // Create partition via builder's network
        builder.network().partition("node-1", "node-2").await;

        // Verify partition affects both transports
        assert!(builder.network().is_partitioned("node-1", "node-2").await);
    }
}
