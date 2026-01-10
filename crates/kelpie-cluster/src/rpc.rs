//! Inter-node RPC
//!
//! TigerStyle: Explicit message types with bounded payloads.

use crate::error::{ClusterError, ClusterResult};
use async_trait::async_trait;
use bytes::Bytes;
use kelpie_core::actor::ActorId;
// For future: RPC_MESSAGE_SIZE_BYTES_MAX for message validation
use kelpie_registry::{Heartbeat, NodeId};
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;
use std::time::Duration;

/// RPC request ID
pub type RequestId = u64;

/// RPC message types
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum RpcMessage {
    // =========================================================================
    // Heartbeat
    // =========================================================================
    /// Heartbeat message
    Heartbeat(Heartbeat),

    /// Heartbeat acknowledgement
    HeartbeatAck { node_id: NodeId, sequence: u64 },

    // =========================================================================
    // Actor Operations
    // =========================================================================
    /// Forward an actor invocation to another node
    ActorInvoke {
        request_id: RequestId,
        actor_id: ActorId,
        operation: String,
        payload: Bytes,
    },

    /// Response to actor invocation
    ActorInvokeResponse {
        request_id: RequestId,
        result: Result<Bytes, String>,
    },

    /// Prepare to migrate an actor (pre-migration check)
    MigratePrepare {
        request_id: RequestId,
        actor_id: ActorId,
        from_node: NodeId,
    },

    /// Confirm migration readiness
    MigratePrepareResponse {
        request_id: RequestId,
        ready: bool,
        reason: Option<String>,
    },

    /// Transfer actor state during migration
    MigrateTransfer {
        request_id: RequestId,
        actor_id: ActorId,
        state: Bytes,
        from_node: NodeId,
    },

    /// Confirm state received
    MigrateTransferResponse {
        request_id: RequestId,
        success: bool,
        reason: Option<String>,
    },

    /// Complete migration (activate on new node)
    MigrateComplete {
        request_id: RequestId,
        actor_id: ActorId,
    },

    /// Confirm migration complete
    MigrateCompleteResponse {
        request_id: RequestId,
        success: bool,
        reason: Option<String>,
    },

    // =========================================================================
    // Cluster Management
    // =========================================================================
    /// Join request from a new node
    JoinRequest {
        request_id: RequestId,
        node_id: NodeId,
        rpc_addr: SocketAddr,
    },

    /// Join response with cluster info
    JoinResponse {
        request_id: RequestId,
        accepted: bool,
        cluster_nodes: Vec<(NodeId, SocketAddr)>,
        reason: Option<String>,
    },

    /// Leave notification
    LeaveNotification { node_id: NodeId },

    /// Request cluster state
    ClusterStateRequest { request_id: RequestId },

    /// Cluster state response
    ClusterStateResponse {
        request_id: RequestId,
        nodes: Vec<(NodeId, SocketAddr)>,
        leader: Option<NodeId>,
    },
}

impl RpcMessage {
    /// Get the request ID if this message has one
    pub fn request_id(&self) -> Option<RequestId> {
        match self {
            Self::Heartbeat(_) => None,
            Self::HeartbeatAck { .. } => None,
            Self::LeaveNotification { .. } => None,
            Self::ActorInvoke { request_id, .. } => Some(*request_id),
            Self::ActorInvokeResponse { request_id, .. } => Some(*request_id),
            Self::MigratePrepare { request_id, .. } => Some(*request_id),
            Self::MigratePrepareResponse { request_id, .. } => Some(*request_id),
            Self::MigrateTransfer { request_id, .. } => Some(*request_id),
            Self::MigrateTransferResponse { request_id, .. } => Some(*request_id),
            Self::MigrateComplete { request_id, .. } => Some(*request_id),
            Self::MigrateCompleteResponse { request_id, .. } => Some(*request_id),
            Self::JoinRequest { request_id, .. } => Some(*request_id),
            Self::JoinResponse { request_id, .. } => Some(*request_id),
            Self::ClusterStateRequest { request_id, .. } => Some(*request_id),
            Self::ClusterStateResponse { request_id, .. } => Some(*request_id),
        }
    }

    /// Check if this is a response message
    pub fn is_response(&self) -> bool {
        matches!(
            self,
            Self::HeartbeatAck { .. }
                | Self::ActorInvokeResponse { .. }
                | Self::MigratePrepareResponse { .. }
                | Self::MigrateTransferResponse { .. }
                | Self::MigrateCompleteResponse { .. }
                | Self::JoinResponse { .. }
                | Self::ClusterStateResponse { .. }
        )
    }

    /// Get the actor ID if this message involves an actor
    pub fn actor_id(&self) -> Option<&ActorId> {
        match self {
            Self::ActorInvoke { actor_id, .. } => Some(actor_id),
            Self::MigratePrepare { actor_id, .. } => Some(actor_id),
            Self::MigrateTransfer { actor_id, .. } => Some(actor_id),
            Self::MigrateComplete { actor_id, .. } => Some(actor_id),
            _ => None,
        }
    }
}

/// RPC transport trait
///
/// Abstracts the underlying transport mechanism (TCP, in-memory, etc.)
#[async_trait]
pub trait RpcTransport: Send + Sync {
    /// Send a message to a specific node
    async fn send(&self, target: &NodeId, message: RpcMessage) -> ClusterResult<()>;

    /// Send a message and wait for response
    async fn send_and_recv(
        &self,
        target: &NodeId,
        message: RpcMessage,
        timeout: Duration,
    ) -> ClusterResult<RpcMessage>;

    /// Broadcast a message to all known nodes
    async fn broadcast(&self, message: RpcMessage) -> ClusterResult<()>;

    /// Register a handler for incoming messages
    async fn set_handler(&self, handler: Box<dyn RpcHandler>) -> ClusterResult<()>;

    /// Start listening for connections
    async fn start(&self) -> ClusterResult<()>;

    /// Stop the transport
    async fn stop(&self) -> ClusterResult<()>;

    /// Get the local address
    fn local_addr(&self) -> SocketAddr;
}

/// Handler for incoming RPC messages
#[async_trait]
pub trait RpcHandler: Send + Sync {
    /// Handle an incoming message
    ///
    /// Returns an optional response message.
    async fn handle(&self, from: &NodeId, message: RpcMessage) -> Option<RpcMessage>;
}

/// In-memory RPC transport for testing
///
/// Messages are delivered directly through channels, simulating network behavior.
pub struct MemoryTransport {
    /// Local node ID
    node_id: NodeId,
    /// Local address
    addr: SocketAddr,
    /// Sender channels to other nodes
    senders: tokio::sync::RwLock<
        std::collections::HashMap<NodeId, tokio::sync::mpsc::Sender<(NodeId, RpcMessage)>>,
    >,
    /// Receiver for incoming messages
    receiver: tokio::sync::Mutex<Option<tokio::sync::mpsc::Receiver<(NodeId, RpcMessage)>>>,
    /// Handler for incoming messages
    handler: tokio::sync::RwLock<Option<Box<dyn RpcHandler>>>,
    /// Pending requests waiting for responses
    pending: tokio::sync::RwLock<
        std::collections::HashMap<RequestId, tokio::sync::oneshot::Sender<RpcMessage>>,
    >,
    /// Next request ID
    next_request_id: std::sync::atomic::AtomicU64,
    /// Whether the transport is running
    running: std::sync::atomic::AtomicBool,
}

impl MemoryTransport {
    /// Create a new in-memory transport
    pub fn new(node_id: NodeId, addr: SocketAddr) -> Self {
        let (tx, rx) = tokio::sync::mpsc::channel(1000);

        Self {
            node_id: node_id.clone(),
            addr,
            senders: tokio::sync::RwLock::new({
                let mut map = std::collections::HashMap::new();
                map.insert(node_id, tx);
                map
            }),
            receiver: tokio::sync::Mutex::new(Some(rx)),
            handler: tokio::sync::RwLock::new(None),
            pending: tokio::sync::RwLock::new(std::collections::HashMap::new()),
            next_request_id: std::sync::atomic::AtomicU64::new(1),
            running: std::sync::atomic::AtomicBool::new(false),
        }
    }

    /// Connect to another transport
    ///
    /// Note: This is a simplified implementation for testing.
    /// In production, actual TCP connections would be established.
    #[allow(dead_code)]
    pub async fn connect(&self, other: &MemoryTransport) {
        let mut senders = self.senders.write().await;
        let mut other_senders = other.senders.write().await;

        // Create channel from self to other
        let (tx_to_other, _rx_to_other) = tokio::sync::mpsc::channel(1000);
        senders.insert(other.node_id.clone(), tx_to_other);

        // Create channel from other to self
        let (tx_to_self, _rx_to_self) = tokio::sync::mpsc::channel(1000);
        other_senders.insert(self.node_id.clone(), tx_to_self);
    }

    /// Get next request ID
    pub fn next_request_id(&self) -> RequestId {
        self.next_request_id
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
    }

    /// Process incoming messages
    async fn process_messages(
        mut receiver: tokio::sync::mpsc::Receiver<(NodeId, RpcMessage)>,
        handler: std::sync::Arc<tokio::sync::RwLock<Option<Box<dyn RpcHandler>>>>,
        pending: std::sync::Arc<
            tokio::sync::RwLock<
                std::collections::HashMap<RequestId, tokio::sync::oneshot::Sender<RpcMessage>>,
            >,
        >,
    ) {
        while let Some((from, message)) = receiver.recv().await {
            // Check if this is a response to a pending request
            if message.is_response() {
                if let Some(request_id) = message.request_id() {
                    let mut pending = pending.write().await;
                    if let Some(sender) = pending.remove(&request_id) {
                        let _ = sender.send(message);
                        continue;
                    }
                }
            }

            // Handle as incoming message
            let handler = handler.read().await;
            if let Some(ref h) = *handler {
                if let Some(_response) = h.handle(&from, message).await {
                    // In a full implementation, we'd send the response back
                }
            }
        }
    }
}

#[async_trait]
impl RpcTransport for MemoryTransport {
    async fn send(&self, target: &NodeId, message: RpcMessage) -> ClusterResult<()> {
        let senders = self.senders.read().await;
        let sender = senders
            .get(target)
            .ok_or_else(|| ClusterError::node_unreachable(target, "no connection"))?;

        sender
            .send((self.node_id.clone(), message))
            .await
            .map_err(|_| ClusterError::node_unreachable(target, "channel closed"))?;

        Ok(())
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
        let (tx, rx) = tokio::sync::oneshot::channel();
        {
            let mut pending = self.pending.write().await;
            pending.insert(request_id, tx);
        }

        // Send the message
        self.send(target, message).await?;

        // Wait for response with timeout
        match tokio::time::timeout(timeout, rx).await {
            Ok(Ok(response)) => Ok(response),
            Ok(Err(_)) => Err(ClusterError::rpc_failed(target, "response channel closed")),
            Err(_) => {
                // Remove pending request
                let mut pending = self.pending.write().await;
                pending.remove(&request_id);
                Err(ClusterError::rpc_timeout(
                    target,
                    timeout.as_millis() as u64,
                ))
            }
        }
    }

    async fn broadcast(&self, message: RpcMessage) -> ClusterResult<()> {
        let senders = self.senders.read().await;
        for (node_id, sender) in senders.iter() {
            if node_id != &self.node_id {
                let _ = sender.send((self.node_id.clone(), message.clone())).await;
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
        if self.running.swap(true, std::sync::atomic::Ordering::SeqCst) {
            return Err(ClusterError::AlreadyStarted);
        }

        // Start message processing task
        let receiver = {
            let mut rx = self.receiver.lock().await;
            rx.take().ok_or_else(|| ClusterError::Internal {
                message: "receiver already taken".into(),
            })?
        };

        let handler = std::sync::Arc::new(
            self.handler
                .write()
                .await
                .take()
                .map(|h| tokio::sync::RwLock::new(Some(h)))
                .unwrap_or_else(|| tokio::sync::RwLock::new(None)),
        );

        let pending =
            std::sync::Arc::new(tokio::sync::RwLock::new(std::collections::HashMap::new()));

        tokio::spawn(Self::process_messages(receiver, handler, pending));

        Ok(())
    }

    async fn stop(&self) -> ClusterResult<()> {
        self.running
            .store(false, std::sync::atomic::Ordering::SeqCst);
        Ok(())
    }

    fn local_addr(&self) -> SocketAddr {
        self.addr
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kelpie_registry::NodeStatus;

    fn test_node_id(n: u32) -> NodeId {
        NodeId::new(format!("node-{}", n)).unwrap()
    }

    fn test_addr(port: u16) -> SocketAddr {
        use std::net::{IpAddr, Ipv4Addr};
        SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), port)
    }

    #[test]
    fn test_rpc_message_request_id() {
        let actor_id = ActorId::new("test", "actor-1").unwrap();
        let msg = RpcMessage::ActorInvoke {
            request_id: 42,
            actor_id,
            operation: "test".into(),
            payload: Bytes::new(),
        };
        assert_eq!(msg.request_id(), Some(42));

        let hb = RpcMessage::Heartbeat(Heartbeat::new(
            test_node_id(1),
            1000,
            NodeStatus::Active,
            0,
            100,
            1,
        ));
        assert_eq!(hb.request_id(), None);
    }

    #[test]
    fn test_rpc_message_is_response() {
        let resp = RpcMessage::ActorInvokeResponse {
            request_id: 1,
            result: Ok(Bytes::new()),
        };
        assert!(resp.is_response());

        let req = RpcMessage::ActorInvoke {
            request_id: 1,
            actor_id: ActorId::new("test", "a").unwrap(),
            operation: "op".into(),
            payload: Bytes::new(),
        };
        assert!(!req.is_response());
    }

    #[test]
    fn test_rpc_message_actor_id() {
        let actor_id = ActorId::new("test", "actor-1").unwrap();
        let msg = RpcMessage::ActorInvoke {
            request_id: 1,
            actor_id: actor_id.clone(),
            operation: "test".into(),
            payload: Bytes::new(),
        };
        assert_eq!(msg.actor_id(), Some(&actor_id));

        let hb = RpcMessage::HeartbeatAck {
            node_id: test_node_id(1),
            sequence: 1,
        };
        assert!(hb.actor_id().is_none());
    }

    #[tokio::test]
    async fn test_memory_transport_create() {
        let transport = MemoryTransport::new(test_node_id(1), test_addr(9001));
        assert_eq!(transport.local_addr(), test_addr(9001));
    }

    #[tokio::test]
    async fn test_memory_transport_request_id() {
        let transport = MemoryTransport::new(test_node_id(1), test_addr(9001));
        let id1 = transport.next_request_id();
        let id2 = transport.next_request_id();
        assert_eq!(id1 + 1, id2);
    }
}
