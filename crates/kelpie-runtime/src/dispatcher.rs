//! Message dispatcher for actor runtime
//!
//! TigerStyle: Single-threaded per-actor execution, explicit message routing.

use crate::activation::ActiveActor;
use bytes::Bytes;
use kelpie_core::actor::{Actor, ActorId};
use kelpie_core::constants::{ACTOR_CONCURRENT_COUNT_MAX, INVOCATION_PENDING_COUNT_MAX};
use kelpie_core::error::{Error, Result};
use kelpie_core::metrics;
use kelpie_storage::ActorKV;
use serde::{de::DeserializeOwned, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Instant;
use tokio::sync::{mpsc, oneshot};
use tracing::{debug, error, info, instrument};

/// Configuration for the dispatcher
#[derive(Debug, Clone)]
pub struct DispatcherConfig {
    /// Maximum number of concurrent actors
    pub max_actors: usize,
    /// Maximum pending messages per actor
    pub max_pending_per_actor: usize,
    /// Channel buffer size for dispatcher commands
    pub command_buffer_size: usize,
}

impl Default for DispatcherConfig {
    fn default() -> Self {
        Self {
            max_actors: ACTOR_CONCURRENT_COUNT_MAX,
            max_pending_per_actor: INVOCATION_PENDING_COUNT_MAX,
            command_buffer_size: 1024,
        }
    }
}

/// Commands sent to the dispatcher
#[derive(Debug)]
pub enum DispatcherCommand {
    /// Invoke an actor
    Invoke {
        actor_id: ActorId,
        operation: String,
        payload: Bytes,
        reply_tx: oneshot::Sender<Result<Bytes>>,
    },
    /// Deactivate an actor
    Deactivate { actor_id: ActorId },
    /// Shutdown the dispatcher
    Shutdown,
}

/// Handle to send commands to the dispatcher
#[derive(Clone)]
pub struct DispatcherHandle {
    command_tx: mpsc::Sender<DispatcherCommand>,
}

impl DispatcherHandle {
    /// Invoke an actor
    pub async fn invoke(
        &self,
        actor_id: ActorId,
        operation: String,
        payload: Bytes,
    ) -> Result<Bytes> {
        let (reply_tx, reply_rx) = oneshot::channel();

        self.command_tx
            .send(DispatcherCommand::Invoke {
                actor_id: actor_id.clone(),
                operation,
                payload,
                reply_tx,
            })
            .await
            .map_err(|_| Error::Internal {
                message: "dispatcher channel closed".into(),
            })?;

        reply_rx.await.map_err(|_| Error::Internal {
            message: "reply channel closed".into(),
        })?
    }

    /// Deactivate an actor
    pub async fn deactivate(&self, actor_id: ActorId) -> Result<()> {
        self.command_tx
            .send(DispatcherCommand::Deactivate { actor_id })
            .await
            .map_err(|_| Error::Internal {
                message: "dispatcher channel closed".into(),
            })
    }

    /// Shutdown the dispatcher
    pub async fn shutdown(&self) -> Result<()> {
        self.command_tx
            .send(DispatcherCommand::Shutdown)
            .await
            .map_err(|_| Error::Internal {
                message: "dispatcher channel closed".into(),
            })
    }
}

/// Factory for creating actors
pub trait ActorFactory<A>: Send + Sync + 'static
where
    A: Actor,
{
    /// Create a new actor instance
    fn create(&self, id: &ActorId) -> A;
}

/// Simple factory that clones a prototype actor
pub struct CloneFactory<A: Clone + Send + Sync + 'static> {
    prototype: A,
}

impl<A: Clone + Send + Sync + 'static> CloneFactory<A> {
    /// Create a new clone factory
    pub fn new(prototype: A) -> Self {
        Self { prototype }
    }
}

impl<A> ActorFactory<A> for CloneFactory<A>
where
    A: Actor + Clone,
{
    fn create(&self, _id: &ActorId) -> A {
        self.prototype.clone()
    }
}

/// Dispatcher for routing messages to actors
///
/// Manages actor lifecycle and message routing.
pub struct Dispatcher<A, S>
where
    A: Actor<State = S>,
    S: Serialize + DeserializeOwned + Default + Send + Sync,
{
    /// Actor factory
    factory: Arc<dyn ActorFactory<A>>,
    /// KV store for persistence
    kv: Arc<dyn ActorKV>,
    /// Configuration
    config: DispatcherConfig,
    /// Active actors
    actors: HashMap<String, ActiveActor<A, S>>,
    /// Command receiver
    command_rx: mpsc::Receiver<DispatcherCommand>,
    /// Command sender (for creating handles)
    command_tx: mpsc::Sender<DispatcherCommand>,
}

impl<A, S> Dispatcher<A, S>
where
    A: Actor<State = S>,
    S: Serialize + DeserializeOwned + Default + Send + Sync + Clone + 'static,
{
    /// Create a new dispatcher
    pub fn new(
        factory: Arc<dyn ActorFactory<A>>,
        kv: Arc<dyn ActorKV>,
        config: DispatcherConfig,
    ) -> Self {
        let (command_tx, command_rx) = mpsc::channel(config.command_buffer_size);

        Self {
            factory,
            kv,
            config,
            actors: HashMap::new(),
            command_rx,
            command_tx,
        }
    }

    /// Get a handle to the dispatcher
    pub fn handle(&self) -> DispatcherHandle {
        DispatcherHandle {
            command_tx: self.command_tx.clone(),
        }
    }

    /// Run the dispatcher loop
    #[instrument(skip(self), level = "info")]
    pub async fn run(&mut self) {
        info!("Dispatcher starting");

        while let Some(command) = self.command_rx.recv().await {
            match command {
                DispatcherCommand::Invoke {
                    actor_id,
                    operation,
                    payload,
                    reply_tx,
                } => {
                    let result = self
                        .handle_invoke(actor_id.clone(), &operation, payload)
                        .await;
                    let _ = reply_tx.send(result);
                }
                DispatcherCommand::Deactivate { actor_id } => {
                    self.handle_deactivate(&actor_id).await;
                }
                DispatcherCommand::Shutdown => {
                    info!("Dispatcher shutting down");
                    self.shutdown().await;
                    break;
                }
            }
        }

        info!("Dispatcher stopped");
    }

    /// Handle an invoke command
    #[instrument(skip(self, payload), fields(actor_id = %actor_id, operation), level = "debug")]
    async fn handle_invoke(
        &mut self,
        actor_id: ActorId,
        operation: &str,
        payload: Bytes,
    ) -> Result<Bytes> {
        let start = Instant::now();
        let key = actor_id.qualified_name();

        // Ensure actor is active
        if !self.actors.contains_key(&key) {
            self.activate_actor(actor_id.clone()).await?;
        }

        // Get the active actor
        let active = self.actors.get_mut(&key).ok_or_else(|| Error::Internal {
            message: "actor not found after activation".into(),
        })?;

        // Process the invocation
        let result = active.process_invocation(operation, payload).await;

        // Record metrics
        let duration = start.elapsed().as_secs_f64();
        let status = if result.is_ok() { "success" } else { "error" };
        metrics::record_invocation(operation, status, duration);

        result
    }

    /// Activate an actor
    async fn activate_actor(&mut self, actor_id: ActorId) -> Result<()> {
        let key = actor_id.qualified_name();

        // Check capacity
        if self.actors.len() >= self.config.max_actors {
            return Err(Error::Internal {
                message: format!("maximum actor count reached: {}", self.config.max_actors),
            });
        }

        // Create and activate the actor
        let actor = self.factory.create(&actor_id);
        let active = ActiveActor::activate(actor_id.clone(), actor, self.kv.clone()).await?;

        self.actors.insert(key, active);
        debug!(actor_id = %actor_id, "Actor activated");

        // Record activation metric
        metrics::record_agent_activated();

        Ok(())
    }

    /// Handle a deactivate command
    async fn handle_deactivate(&mut self, actor_id: &ActorId) {
        let key = actor_id.qualified_name();

        if let Some(mut active) = self.actors.remove(&key) {
            if let Err(e) = active.deactivate().await {
                error!(actor_id = %actor_id, error = %e, "Failed to deactivate actor");
            } else {
                debug!(actor_id = %actor_id, "Actor deactivated");
                // Record deactivation metric
                metrics::record_agent_deactivated();
            }
        }
    }

    /// Shutdown all actors
    async fn shutdown(&mut self) {
        let actor_ids: Vec<_> = self.actors.keys().cloned().collect();

        for key in actor_ids {
            if let Some(mut active) = self.actors.remove(&key) {
                if let Err(e) = active.deactivate().await {
                    error!(error = %e, "Failed to deactivate actor during shutdown");
                }
            }
        }
    }

    /// Get the number of active actors
    pub fn active_actor_count(&self) -> usize {
        self.actors.len()
    }

    /// Check if an actor is active
    pub fn is_active(&self, actor_id: &ActorId) -> bool {
        self.actors.contains_key(&actor_id.qualified_name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use async_trait::async_trait;
    use kelpie_core::actor::ActorContext;
    use kelpie_storage::MemoryKV;

    #[derive(Debug, Default, Clone, serde::Serialize, serde::Deserialize)]
    struct CounterState {
        count: i64,
    }

    #[derive(Clone)]
    struct CounterActor;

    #[async_trait]
    impl Actor for CounterActor {
        type State = CounterState;

        async fn invoke(
            &self,
            ctx: &mut ActorContext<Self::State>,
            operation: &str,
            _payload: Bytes,
        ) -> Result<Bytes> {
            match operation {
                "increment" => {
                    ctx.state.count += 1;
                    Ok(Bytes::from(ctx.state.count.to_string()))
                }
                "get" => Ok(Bytes::from(ctx.state.count.to_string())),
                _ => Err(Error::InvalidOperation {
                    operation: operation.to_string(),
                }),
            }
        }
    }

    #[tokio::test]
    async fn test_dispatcher_basic() {
        let factory = Arc::new(CloneFactory::new(CounterActor));
        let kv = Arc::new(MemoryKV::new());
        let config = DispatcherConfig::default();

        let mut dispatcher = Dispatcher::new(factory, kv, config);
        let handle = dispatcher.handle();

        // Run dispatcher in background
        let dispatcher_task = tokio::spawn(async move {
            dispatcher.run().await;
        });

        // Invoke actor
        let actor_id = ActorId::new("test", "counter-1").unwrap();
        let result = handle
            .invoke(actor_id.clone(), "increment".to_string(), Bytes::new())
            .await
            .unwrap();
        assert_eq!(result, Bytes::from("1"));

        let result = handle
            .invoke(actor_id.clone(), "get".to_string(), Bytes::new())
            .await
            .unwrap();
        assert_eq!(result, Bytes::from("1"));

        // Shutdown
        handle.shutdown().await.unwrap();
        dispatcher_task.await.unwrap();
    }

    #[tokio::test]
    async fn test_dispatcher_multiple_actors() {
        let factory = Arc::new(CloneFactory::new(CounterActor));
        let kv = Arc::new(MemoryKV::new());
        let config = DispatcherConfig::default();

        let mut dispatcher = Dispatcher::new(factory, kv, config);
        let handle = dispatcher.handle();

        let dispatcher_task = tokio::spawn(async move {
            dispatcher.run().await;
        });

        let actor1 = ActorId::new("test", "counter-1").unwrap();
        let actor2 = ActorId::new("test", "counter-2").unwrap();

        // Increment actor1 twice
        handle
            .invoke(actor1.clone(), "increment".to_string(), Bytes::new())
            .await
            .unwrap();
        handle
            .invoke(actor1.clone(), "increment".to_string(), Bytes::new())
            .await
            .unwrap();

        // Increment actor2 once
        handle
            .invoke(actor2.clone(), "increment".to_string(), Bytes::new())
            .await
            .unwrap();

        // Verify counts are independent
        let result1 = handle
            .invoke(actor1.clone(), "get".to_string(), Bytes::new())
            .await
            .unwrap();
        assert_eq!(result1, Bytes::from("2"));

        let result2 = handle
            .invoke(actor2.clone(), "get".to_string(), Bytes::new())
            .await
            .unwrap();
        assert_eq!(result2, Bytes::from("1"));

        handle.shutdown().await.unwrap();
        dispatcher_task.await.unwrap();
    }

    #[tokio::test]
    async fn test_dispatcher_deactivate() {
        let factory = Arc::new(CloneFactory::new(CounterActor));
        let kv = Arc::new(MemoryKV::new());
        let config = DispatcherConfig::default();

        let mut dispatcher = Dispatcher::new(factory, kv.clone(), config);
        let handle = dispatcher.handle();

        let dispatcher_task = tokio::spawn(async move {
            dispatcher.run().await;
        });

        let actor_id = ActorId::new("test", "counter-deactivate").unwrap();

        // Increment
        handle
            .invoke(actor_id.clone(), "increment".to_string(), Bytes::new())
            .await
            .unwrap();
        handle
            .invoke(actor_id.clone(), "increment".to_string(), Bytes::new())
            .await
            .unwrap();

        // Deactivate
        handle.deactivate(actor_id.clone()).await.unwrap();

        // Allow time for deactivation
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;

        // Invoke again - should reactivate with persisted state
        let result = handle
            .invoke(actor_id.clone(), "get".to_string(), Bytes::new())
            .await
            .unwrap();
        assert_eq!(result, Bytes::from("2"));

        handle.shutdown().await.unwrap();
        dispatcher_task.await.unwrap();
    }
}
