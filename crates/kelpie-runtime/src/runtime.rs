//! Main runtime coordinator
//!
//! TigerStyle: Single entry point, explicit configuration, clean shutdown.

use crate::dispatcher::{
    ActorFactory, CloneFactory, Dispatcher, DispatcherConfig, DispatcherHandle,
};
use crate::handle::{ActorHandle, ActorHandleBuilder};
use kelpie_core::actor::{Actor, ActorId, ActorRef};
use kelpie_core::error::{Error, Result};
use kelpie_storage::ActorKV;
use serde::{de::DeserializeOwned, Serialize};
use std::sync::Arc;
use tokio::task::JoinHandle;
use tracing::info;

/// Configuration for the runtime
#[derive(Debug, Clone, Default)]
pub struct RuntimeConfig {
    /// Dispatcher configuration
    pub dispatcher: DispatcherConfig,
}

/// Builder for creating a runtime
pub struct RuntimeBuilder<A, S>
where
    A: Actor<State = S>,
    S: Serialize + DeserializeOwned + Default + Send + Sync + 'static,
{
    factory: Option<Arc<dyn ActorFactory<A>>>,
    kv: Option<Arc<dyn ActorKV>>,
    config: RuntimeConfig,
    _phantom: std::marker::PhantomData<S>,
}

impl<A, S> RuntimeBuilder<A, S>
where
    A: Actor<State = S>,
    S: Serialize + DeserializeOwned + Default + Send + Sync + Clone + 'static,
{
    /// Create a new runtime builder
    pub fn new() -> Self {
        Self {
            factory: None,
            kv: None,
            config: RuntimeConfig::default(),
            _phantom: std::marker::PhantomData,
        }
    }

    /// Set the actor factory
    pub fn with_factory(mut self, factory: Arc<dyn ActorFactory<A>>) -> Self {
        self.factory = Some(factory);
        self
    }

    /// Set the KV store
    pub fn with_kv(mut self, kv: Arc<dyn ActorKV>) -> Self {
        self.kv = Some(kv);
        self
    }

    /// Set the configuration
    pub fn with_config(mut self, config: RuntimeConfig) -> Self {
        self.config = config;
        self
    }

    /// Build the runtime
    pub fn build(self) -> Result<Runtime<A, S>> {
        let factory = self.factory.ok_or_else(|| Error::Internal {
            message: "factory is required".into(),
        })?;

        let kv = self.kv.ok_or_else(|| Error::Internal {
            message: "kv store is required".into(),
        })?;

        Ok(Runtime::new(factory, kv, self.config))
    }
}

impl<A, S> Default for RuntimeBuilder<A, S>
where
    A: Actor<State = S>,
    S: Serialize + DeserializeOwned + Default + Send + Sync + Clone + 'static,
{
    fn default() -> Self {
        Self::new()
    }
}

/// Convenience method to create runtime for cloneable actors
impl<A, S> RuntimeBuilder<A, S>
where
    A: Actor<State = S> + Clone,
    S: Serialize + DeserializeOwned + Default + Send + Sync + Clone + 'static,
{
    /// Set a prototype actor (will be cloned for each activation)
    pub fn with_actor(self, actor: A) -> Self {
        self.with_factory(Arc::new(CloneFactory::new(actor)))
    }
}

/// The main Kelpie runtime
///
/// Manages actor lifecycle, message routing, and coordination.
pub struct Runtime<A, S>
where
    A: Actor<State = S>,
    S: Serialize + DeserializeOwned + Default + Send + Sync + Clone + 'static,
{
    /// The dispatcher
    dispatcher: Option<Dispatcher<A, S>>,
    /// Handle for sending commands
    handle: DispatcherHandle,
    /// Background task handle
    task: Option<JoinHandle<()>>,
    /// Configuration
    config: RuntimeConfig,
}

impl<A, S> Runtime<A, S>
where
    A: Actor<State = S>,
    S: Serialize + DeserializeOwned + Default + Send + Sync + Clone + 'static,
{
    /// Create a new runtime
    pub fn new(
        factory: Arc<dyn ActorFactory<A>>,
        kv: Arc<dyn ActorKV>,
        config: RuntimeConfig,
    ) -> Self {
        let dispatcher = Dispatcher::new(factory, kv, config.dispatcher.clone());
        let handle = dispatcher.handle();

        Self {
            dispatcher: Some(dispatcher),
            handle,
            task: None,
            config,
        }
    }

    /// Start the runtime
    ///
    /// Spawns the dispatcher loop in a background task.
    pub fn start(&mut self) -> Result<()> {
        if self.task.is_some() {
            return Err(Error::Internal {
                message: "runtime already started".into(),
            });
        }

        let mut dispatcher = self.dispatcher.take().ok_or_else(|| Error::Internal {
            message: "runtime already started".into(),
        })?;

        info!("Starting Kelpie runtime");

        self.task = Some(tokio::spawn(async move {
            dispatcher.run().await;
        }));

        Ok(())
    }

    /// Stop the runtime
    pub async fn stop(&mut self) -> Result<()> {
        if let Some(task) = self.task.take() {
            info!("Stopping Kelpie runtime");
            self.handle.shutdown().await?;
            task.await.map_err(|e| Error::Internal {
                message: format!("dispatcher task failed: {}", e),
            })?;
        }
        Ok(())
    }

    /// Get a handle to the dispatcher
    pub fn dispatcher_handle(&self) -> DispatcherHandle {
        self.handle.clone()
    }

    /// Get an actor handle builder
    pub fn actor_handles(&self) -> ActorHandleBuilder {
        ActorHandleBuilder::new(self.handle.clone())
    }

    /// Get a handle to a specific actor
    pub fn actor(&self, actor_id: ActorId) -> ActorHandle {
        ActorHandle::new(ActorRef::new(actor_id), self.handle.clone())
    }

    /// Get a handle to a specific actor by namespace and id
    pub fn actor_by_parts(
        &self,
        namespace: impl Into<String>,
        id: impl Into<String>,
    ) -> Result<ActorHandle> {
        let actor_id = ActorId::new(namespace, id)?;
        Ok(self.actor(actor_id))
    }

    /// Check if the runtime is running
    pub fn is_running(&self) -> bool {
        self.task.as_ref().is_some_and(|t| !t.is_finished())
    }

    /// Get the runtime configuration
    pub fn config(&self) -> &RuntimeConfig {
        &self.config
    }
}

impl<A, S> Drop for Runtime<A, S>
where
    A: Actor<State = S>,
    S: Serialize + DeserializeOwned + Default + Send + Sync + Clone + 'static,
{
    fn drop(&mut self) {
        if self.task.is_some() {
            // Can't await in drop, so we just abort the task
            if let Some(task) = self.task.take() {
                task.abort();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use async_trait::async_trait;
    use bytes::Bytes;
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
    async fn test_runtime_basic() {
        let kv = Arc::new(MemoryKV::new());

        let mut runtime = RuntimeBuilder::new()
            .with_actor(CounterActor)
            .with_kv(kv)
            .build()
            .unwrap();

        runtime.start().unwrap();
        assert!(runtime.is_running());

        let actor = runtime.actor_by_parts("test", "counter-1").unwrap();

        let result = actor.invoke("increment", Bytes::new()).await.unwrap();
        assert_eq!(result, Bytes::from("1"));

        let result = actor.invoke("increment", Bytes::new()).await.unwrap();
        assert_eq!(result, Bytes::from("2"));

        runtime.stop().await.unwrap();
        assert!(!runtime.is_running());
    }

    #[tokio::test]
    async fn test_runtime_multiple_actors() {
        let kv = Arc::new(MemoryKV::new());

        let mut runtime = RuntimeBuilder::new()
            .with_actor(CounterActor)
            .with_kv(kv)
            .build()
            .unwrap();

        runtime.start().unwrap();

        let handles = runtime.actor_handles();
        let actor1 = handles.for_parts("test", "counter-a").unwrap();
        let actor2 = handles.for_parts("test", "counter-b").unwrap();

        // Independent state
        actor1.invoke("increment", Bytes::new()).await.unwrap();
        actor1.invoke("increment", Bytes::new()).await.unwrap();
        actor2.invoke("increment", Bytes::new()).await.unwrap();

        let result1 = actor1.invoke("get", Bytes::new()).await.unwrap();
        let result2 = actor2.invoke("get", Bytes::new()).await.unwrap();

        assert_eq!(result1, Bytes::from("2"));
        assert_eq!(result2, Bytes::from("1"));

        runtime.stop().await.unwrap();
    }

    #[tokio::test]
    async fn test_runtime_state_persistence() {
        let kv = Arc::new(MemoryKV::new());

        // First runtime instance
        {
            let mut runtime = RuntimeBuilder::new()
                .with_actor(CounterActor)
                .with_kv(kv.clone())
                .build()
                .unwrap();

            runtime.start().unwrap();

            let actor = runtime.actor_by_parts("test", "persistent").unwrap();
            actor.invoke("increment", Bytes::new()).await.unwrap();
            actor.invoke("increment", Bytes::new()).await.unwrap();

            // Deactivate to persist state
            actor.deactivate().await.unwrap();
            tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;

            runtime.stop().await.unwrap();
        }

        // Second runtime instance - state should be restored
        {
            let mut runtime = RuntimeBuilder::new()
                .with_actor(CounterActor)
                .with_kv(kv)
                .build()
                .unwrap();

            runtime.start().unwrap();

            let actor = runtime.actor_by_parts("test", "persistent").unwrap();
            let result = actor.invoke("get", Bytes::new()).await.unwrap();
            assert_eq!(result, Bytes::from("2"));

            runtime.stop().await.unwrap();
        }
    }
}
