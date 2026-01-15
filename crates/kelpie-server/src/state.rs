//! Server state management
//!
//! TigerStyle: Thread-safe shared state with explicit locking.
//!
//! DST Support: Optional fault injection for deterministic simulation testing.
//!
//! Storage Integration: Optional AgentStorage backend for persistence.
//! When storage is configured, state is persisted to durable backend (FDB/Sim).
//! In-memory HashMaps serve as hot cache, storage is source of truth.

use crate::actor::{AgentActor, RealLlmAdapter};
use crate::llm::LlmClient;
use crate::models::ArchivalEntry;
use crate::models::{AgentState, Block, Job, Message};
use crate::service::AgentService;
use crate::storage::{AgentStorage, StorageError};
use crate::tools::UnifiedToolRegistry;
use chrono::Utc;
use kelpie_runtime::{CloneFactory, Dispatcher, DispatcherConfig, DispatcherHandle};
use kelpie_storage::memory::MemoryKV;
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};
use uuid::Uuid;

#[cfg(feature = "dst")]
use kelpie_dst::fault::FaultInjector;

/// Maximum agents per server instance
pub const AGENTS_COUNT_MAX: usize = 100_000;

/// Maximum messages per agent
pub const MESSAGES_PER_AGENT_MAX: usize = 10_000;

/// Maximum archival entries per agent
pub const ARCHIVAL_ENTRIES_PER_AGENT_MAX: usize = 100_000;

/// Maximum standalone blocks
pub const BLOCKS_COUNT_MAX: usize = 100_000;

/// Tool information for API responses
#[derive(Debug, Clone)]
pub struct ToolInfo {
    pub name: String,
    pub description: String,
    pub input_schema: serde_json::Value,
    pub source: Option<String>,
}

/// Server-wide shared state
#[derive(Clone)]
pub struct AppState {
    inner: Arc<AppStateInner>,
}

struct AppStateInner {
    /// NEW Phase 5: Actor-based agent service (None for backward compat)
    agent_service: Option<AgentService>,
    /// NEW Phase 5: Actor runtime dispatcher handle (None for backward compat)
    dispatcher: Option<DispatcherHandle>,
    /// NEW Phase 5: Shutdown coordination channel
    shutdown_tx: Option<tokio::sync::broadcast::Sender<()>>,

    /// Agent storage by ID (in-memory hot cache)
    /// TODO Phase 6: Remove after HTTP handlers migrated to agent_service
    agents: RwLock<HashMap<String, AgentState>>,
    /// Messages by agent ID (in-memory hot cache)
    messages: RwLock<HashMap<String, Vec<Message>>>,
    /// Tool definitions by name (legacy, for API compatibility)
    tools: RwLock<HashMap<String, ToolInfo>>,
    /// Unified tool registry for execution
    tool_registry: Arc<UnifiedToolRegistry>,
    /// Archival memory entries by agent ID
    archival: RwLock<HashMap<String, Vec<ArchivalEntry>>>,
    /// Standalone blocks by ID (for letta-code compatibility)
    blocks: RwLock<HashMap<String, Block>>,
    /// Scheduled jobs by ID (Phase 5: Scheduling)
    jobs: RwLock<HashMap<String, Job>>,
    /// Server start time for uptime calculation
    start_time: Instant,
    /// LLM client (None if no API key configured)
    llm: Option<LlmClient>,
    /// Durable storage backend (None = in-memory only)
    /// When present, state is persisted to storage (FDB/Sim)
    storage: Option<Arc<dyn AgentStorage>>,
    /// Prometheus metrics registry (None if metrics disabled or otel feature not enabled)
    #[cfg(feature = "otel")]
    prometheus_registry: Option<Arc<prometheus::Registry>>,
    /// Fault injector for DST testing (None in production)
    #[cfg(feature = "dst")]
    fault_injector: Option<Arc<FaultInjector>>,
}

impl AppState {
    /// Create new server state
    pub fn new() -> Self {
        Self::with_registry(None)
    }

    /// Create new server state with optional Prometheus registry
    #[cfg(feature = "otel")]
    pub fn with_registry(registry: Option<&prometheus::Registry>) -> Self {
        let llm = LlmClient::from_env();
        if llm.is_some() {
            tracing::info!("LLM integration enabled");
        } else {
            tracing::warn!(
                "No LLM API key found. Set ANTHROPIC_API_KEY or OPENAI_API_KEY for real responses."
            );
        }

        let tool_registry = Arc::new(UnifiedToolRegistry::new());

        // Phase 6.4: Create AgentService and Dispatcher for production
        let (agent_service, dispatcher, shutdown_tx) = if let Some(ref llm_client) = llm {
            tracing::info!("Initializing actor-based agent service");

            // Create LLM adapter for actor
            let llm_adapter: Arc<dyn crate::actor::LlmClient> =
                Arc::new(RealLlmAdapter::new(llm_client.clone()));

            // Create AgentActor
            let actor = AgentActor::new(llm_adapter);

            // Create CloneFactory for dispatcher
            let factory = Arc::new(CloneFactory::new(actor));

            // Use MemoryKV for actor storage (TODO: production will use FDB)
            let kv = Arc::new(MemoryKV::new());

            // Create Dispatcher
            let mut dispatcher = Dispatcher::new(factory, kv, DispatcherConfig::default());
            let handle = dispatcher.handle();

            // Spawn dispatcher runtime
            tokio::spawn(async move {
                dispatcher.run().await;
            });

            // Create service
            let service = AgentService::new(handle.clone());

            // Create shutdown channel
            let (tx, _rx) = tokio::sync::broadcast::channel(1);

            (Some(service), Some(handle), Some(tx))
        } else {
            tracing::warn!("Actor service disabled - no LLM client configured");
            (None, None, None)
        };

        Self {
            inner: Arc::new(AppStateInner {
                agent_service,
                dispatcher,
                shutdown_tx,
                agents: RwLock::new(HashMap::new()),
                messages: RwLock::new(HashMap::new()),
                tools: RwLock::new(HashMap::new()),
                tool_registry,
                archival: RwLock::new(HashMap::new()),
                blocks: RwLock::new(HashMap::new()),
                jobs: RwLock::new(HashMap::new()),
                start_time: Instant::now(),
                llm,
                storage: None,
                prometheus_registry: registry.map(|r| Arc::new(r.clone())),
                #[cfg(feature = "dst")]
                fault_injector: None,
            }),
        }
    }

    /// Create new server state without Prometheus registry (when otel feature not enabled)
    #[cfg(not(feature = "otel"))]
    pub fn with_registry(_registry: Option<()>) -> Self {
        let llm = LlmClient::from_env();
        if llm.is_some() {
            tracing::info!("LLM integration enabled");
        } else {
            tracing::warn!(
                "No LLM API key found. Set ANTHROPIC_API_KEY or OPENAI_API_KEY for real responses."
            );
        }

        let tool_registry = Arc::new(UnifiedToolRegistry::new());

        // Phase 6.4: Create AgentService and Dispatcher for production
        let (agent_service, dispatcher, shutdown_tx) = if let Some(ref llm_client) = llm {
            tracing::info!("Initializing actor-based agent service");

            // Create LLM adapter for actor
            let llm_adapter: Arc<dyn crate::actor::LlmClient> =
                Arc::new(RealLlmAdapter::new(llm_client.clone()));

            // Create AgentActor
            let actor = AgentActor::new(llm_adapter);

            // Create CloneFactory for dispatcher
            let factory = Arc::new(CloneFactory::new(actor));

            // Use MemoryKV for actor storage (TODO: production will use FDB)
            let kv = Arc::new(MemoryKV::new());

            // Create Dispatcher
            let mut dispatcher = Dispatcher::new(factory, kv, DispatcherConfig::default());
            let handle = dispatcher.handle();

            // Spawn dispatcher runtime
            tokio::spawn(async move {
                dispatcher.run().await;
            });

            // Create service
            let service = AgentService::new(handle.clone());

            // Create shutdown channel
            let (tx, _rx) = tokio::sync::broadcast::channel(1);

            (Some(service), Some(handle), Some(tx))
        } else {
            tracing::warn!("Actor service disabled - no LLM client configured");
            (None, None, None)
        };

        Self {
            inner: Arc::new(AppStateInner {
                agent_service,
                dispatcher,
                shutdown_tx,
                agents: RwLock::new(HashMap::new()),
                messages: RwLock::new(HashMap::new()),
                tools: RwLock::new(HashMap::new()),
                tool_registry,
                archival: RwLock::new(HashMap::new()),
                blocks: RwLock::new(HashMap::new()),
                jobs: RwLock::new(HashMap::new()),
                start_time: Instant::now(),
                llm,
                storage: None,
                #[cfg(feature = "dst")]
                fault_injector: None,
            }),
        }
    }

    /// Create server state with durable storage backend
    ///
    /// TigerStyle: Storage enables persistence for crash recovery.
    pub fn with_storage(storage: Arc<dyn AgentStorage>) -> Self {
        let llm = LlmClient::from_env();
        let tool_registry = Arc::new(UnifiedToolRegistry::new());

        Self {
            inner: Arc::new(AppStateInner {
                agent_service: None,
                dispatcher: None,
                shutdown_tx: None,
                agents: RwLock::new(HashMap::new()),
                messages: RwLock::new(HashMap::new()),
                tools: RwLock::new(HashMap::new()),
                tool_registry,
                archival: RwLock::new(HashMap::new()),
                blocks: RwLock::new(HashMap::new()),
                jobs: RwLock::new(HashMap::new()),
                start_time: Instant::now(),
                llm,
                storage: Some(storage),
                #[cfg(feature = "otel")]
                prometheus_registry: None,
                #[cfg(feature = "dst")]
                fault_injector: None,
            }),
        }
    }

    /// Create server state with fault injector for DST testing
    #[cfg(feature = "dst")]
    pub fn with_fault_injector(fault_injector: Arc<FaultInjector>) -> Self {
        let tool_registry = Arc::new(UnifiedToolRegistry::new());

        Self {
            inner: Arc::new(AppStateInner {
                agent_service: None,
                dispatcher: None,
                shutdown_tx: None,
                agents: RwLock::new(HashMap::new()),
                messages: RwLock::new(HashMap::new()),
                tools: RwLock::new(HashMap::new()),
                tool_registry,
                archival: RwLock::new(HashMap::new()),
                blocks: RwLock::new(HashMap::new()),
                jobs: RwLock::new(HashMap::new()),
                start_time: Instant::now(),
                llm: None,
                storage: None,
                #[cfg(feature = "otel")]
                prometheus_registry: None,
                fault_injector: Some(fault_injector),
            }),
        }
    }

    /// Create server state with both storage and fault injector for DST testing
    #[cfg(feature = "dst")]
    pub fn with_storage_and_faults(
        storage: Arc<dyn AgentStorage>,
        fault_injector: Arc<FaultInjector>,
    ) -> Self {
        let tool_registry = Arc::new(UnifiedToolRegistry::new());

        Self {
            inner: Arc::new(AppStateInner {
                agent_service: None,
                dispatcher: None,
                shutdown_tx: None,
                agents: RwLock::new(HashMap::new()),
                messages: RwLock::new(HashMap::new()),
                tools: RwLock::new(HashMap::new()),
                tool_registry,
                archival: RwLock::new(HashMap::new()),
                blocks: RwLock::new(HashMap::new()),
                jobs: RwLock::new(HashMap::new()),
                start_time: Instant::now(),
                llm: None,
                storage: Some(storage),
                #[cfg(feature = "otel")]
                prometheus_registry: None,
                fault_injector: Some(fault_injector),
            }),
        }
    }

    /// Create AppState with AgentService and Dispatcher integration
    ///
    /// TigerStyle: This constructor enables actor-based agent management (Phase 5).
    ///
    /// # Arguments
    /// * `agent_service` - Service layer for agent operations
    /// * `dispatcher` - Dispatcher handle for shutdown coordination
    ///
    /// Note: This constructor is used for DST testing and will eventually
    /// replace the HashMap-based constructors after Phase 6 migration.
    pub fn with_agent_service(agent_service: AgentService, dispatcher: DispatcherHandle) -> Self {
        let tool_registry = Arc::new(UnifiedToolRegistry::new());
        let (shutdown_tx, _rx) = tokio::sync::broadcast::channel(1);

        Self {
            inner: Arc::new(AppStateInner {
                agent_service: Some(agent_service),
                dispatcher: Some(dispatcher),
                shutdown_tx: Some(shutdown_tx),
                agents: RwLock::new(HashMap::new()),
                messages: RwLock::new(HashMap::new()),
                tools: RwLock::new(HashMap::new()),
                tool_registry,
                archival: RwLock::new(HashMap::new()),
                blocks: RwLock::new(HashMap::new()),
                jobs: RwLock::new(HashMap::new()),
                start_time: Instant::now(),
                llm: None,
                storage: None,
                #[cfg(feature = "otel")]
                prometheus_registry: None,
                #[cfg(feature = "dst")]
                fault_injector: None,
            }),
        }
    }

    /// Get reference to the agent service (if configured)
    ///
    /// Returns None if AppState was created without actor-based service.
    /// After Phase 6 migration, this will always return Some.
    pub fn agent_service(&self) -> Option<&AgentService> {
        self.inner.agent_service.as_ref()
    }

    /// Gracefully shutdown the actor system
    ///
    /// TigerStyle: Waits for in-flight requests to complete (up to timeout).
    ///
    /// # Arguments
    /// * `timeout` - Maximum time to wait for in-flight requests
    ///
    /// # Errors
    /// Returns error if dispatcher shutdown fails
    pub async fn shutdown(&self, timeout: Duration) -> kelpie_core::Result<()> {
        // Signal shutdown to any listeners
        if let Some(tx) = &self.inner.shutdown_tx {
            let _ = tx.send(());
        }

        // Wait for in-flight requests (up to timeout)
        tokio::time::sleep(timeout).await;

        // Shutdown dispatcher if present
        if let Some(dispatcher) = &self.inner.dispatcher {
            dispatcher.shutdown().await?;
        }

        Ok(())
    }

    /// Check if fault should be injected for an operation
    #[cfg(feature = "dst")]
    fn should_inject_fault(&self, operation: &str) -> Option<kelpie_dst::fault::FaultType> {
        self.inner
            .fault_injector
            .as_ref()
            .and_then(|fi| fi.should_inject(operation))
    }

    /// No fault injection in non-DST builds
    #[cfg(not(feature = "dst"))]
    fn should_inject_fault(&self, _operation: &str) -> Option<()> {
        None
    }

    /// Get reference to the LLM client (if configured)
    pub fn llm(&self) -> Option<&LlmClient> {
        self.inner.llm.as_ref()
    }

    /// Get reference to the unified tool registry
    pub fn tool_registry(&self) -> &UnifiedToolRegistry {
        &self.inner.tool_registry
    }

    /// Get server uptime in seconds
    pub fn uptime_seconds(&self) -> u64 {
        self.inner.start_time.elapsed().as_secs()
    }

    /// Get reference to the Prometheus registry (if configured)
    #[cfg(feature = "otel")]
    pub fn prometheus_registry(&self) -> Option<&prometheus::Registry> {
        self.inner.prometheus_registry.as_ref().map(|r| r.as_ref())
    }

    /// Check if durable storage is configured
    pub fn has_storage(&self) -> bool {
        self.inner.storage.is_some()
    }

    /// Get reference to the storage backend (if configured)
    pub fn storage(&self) -> Option<&dyn AgentStorage> {
        self.inner.storage.as_ref().map(|s| s.as_ref())
    }

    // =========================================================================
    // Dual-Mode Agent Operations (Phase 6.1)
    // =========================================================================
    //
    // These methods delegate to AgentService if available, otherwise fall back
    // to HashMap. This enables incremental migration of HTTP handlers.
    //
    // After Phase 6 migration completes, these will be removed and handlers
    // will call agent_service() directly.

    /// Get an agent by ID (dual-mode)
    ///
    /// Phase 6.11: Prefers AgentService if available, falls back to HashMap.
    pub async fn get_agent_async(&self, id: &str) -> Result<Option<AgentState>, StateError> {
        if let Some(service) = self.agent_service() {
            match service.get_agent(id).await {
                Ok(agent) => Ok(Some(agent)),
                Err(kelpie_core::Error::ActorNotFound { .. }) => {
                    // Actor not found is not an error, just means agent doesn't exist
                    Ok(None)
                }
                Err(kelpie_core::Error::Internal { message })
                    if message.contains("Agent not created") =>
                {
                    // Actor was activated but has no agent state (never called create)
                    Ok(None)
                }
                Err(e) => Err(StateError::Internal {
                    message: format!("Service error: {}", e),
                }),
            }
        } else {
            // Fallback to HashMap for backward compatibility
            self.get_agent(id)
        }
    }

    /// Create an agent (dual-mode)
    ///
    /// Phase 6.11: Prefers AgentService if available, falls back to HashMap.
    pub async fn create_agent_async(
        &self,
        request: crate::models::CreateAgentRequest,
    ) -> Result<AgentState, StateError> {
        if let Some(service) = self.agent_service() {
            service
                .create_agent(request)
                .await
                .map_err(|e| StateError::Internal {
                    message: format!("Service error: {}", e),
                })
        } else {
            // Fallback to HashMap for backward compatibility
            // Use from_request to convert CreateAgentRequest to AgentState
            #[allow(deprecated)]
            let agent = AgentState::from_request(request);
            #[allow(deprecated)]
            self.create_agent(agent)
        }
    }

    /// Update an agent (dual-mode)
    ///
    /// Phase 6.11: Prefers AgentService if available, falls back to HashMap.
    pub async fn update_agent_async(
        &self,
        id: &str,
        update: serde_json::Value,
    ) -> Result<AgentState, StateError> {
        if let Some(service) = self.agent_service() {
            service
                .update_agent(id, update)
                .await
                .map_err(|e| StateError::Internal {
                    message: format!("Service error: {}", e),
                })
        } else {
            // Fallback: For HashMap mode, parse update and apply manually
            let update_req: crate::models::UpdateAgentRequest = serde_json::from_value(update)
                .map_err(|e| StateError::Internal {
                    message: format!("Failed to parse update: {}", e),
                })?;

            // Apply update using closure-based update_agent
            #[allow(deprecated)]
            self.update_agent(id, |agent| {
                if let Some(name) = update_req.name {
                    agent.name = name;
                }
                if let Some(system) = update_req.system {
                    agent.system = Some(system);
                }
                if let Some(description) = update_req.description {
                    agent.description = Some(description);
                }
                if let Some(tags) = update_req.tags {
                    agent.tags = tags;
                }
                if let Some(metadata) = update_req.metadata {
                    agent.metadata = metadata;
                }
            })
        }
    }

    /// Delete an agent (dual-mode)
    ///
    /// Phase 6.11: Prefers AgentService if available, falls back to HashMap.
    pub async fn delete_agent_async(&self, id: &str) -> Result<(), StateError> {
        if let Some(service) = self.agent_service() {
            service
                .delete_agent(id)
                .await
                .map_err(|e| StateError::Internal {
                    message: format!("Service error: {}", e),
                })
        } else {
            // Fallback to HashMap for backward compatibility
            self.delete_agent(id)
        }
    }

    /// List agents (dual-mode)
    ///
    /// Phase 6.5: Currently always uses HashMap since AgentService doesn't have list support yet.
    /// TODO: Implement registry/index infrastructure for actor-based list operations.
    pub async fn list_agents_async(
        &self,
        limit: usize,
        cursor: Option<&str>,
    ) -> Result<(Vec<AgentState>, Option<String>), StateError> {
        // TODO: When AgentService supports list operations (requires registry):
        // if let Some(service) = self.agent_service() {
        //     service.list_agents(limit, cursor).await...
        // } else {
        //     self.list_agents(limit, cursor)
        // }

        // For now, always use HashMap (works in both modes)
        self.list_agents(limit, cursor)
    }

    // Note: list_agents not yet implemented in AgentService
    // For now, list handler will continue using HashMap directly

    // =========================================================================
    // Async Persistence Operations (for durable storage)
    // =========================================================================

    /// Persist agent metadata to durable storage
    ///
    /// TigerStyle: Async operation for storage backend writes.
    /// Returns Ok(()) if no storage configured (in-memory only mode).
    pub async fn persist_agent(&self, agent: &AgentState) -> Result<(), StorageError> {
        if let Some(storage) = &self.inner.storage {
            use crate::storage::AgentMetadata;

            let metadata = AgentMetadata {
                id: agent.id.clone(),
                name: agent.name.clone(),
                agent_type: agent.agent_type.clone(),
                model: agent.model.clone(),
                system: agent.system.clone(),
                description: agent.description.clone(),
                tool_ids: agent.tool_ids.clone(),
                tags: agent.tags.clone(),
                metadata: agent.metadata.clone(),
                created_at: agent.created_at,
                updated_at: agent.updated_at,
            };
            storage.save_agent(&metadata).await?;

            // Also persist blocks
            storage.save_blocks(&agent.id, &agent.blocks).await?;
        }
        Ok(())
    }

    /// Persist a message to durable storage
    pub async fn persist_message(
        &self,
        agent_id: &str,
        message: &Message,
    ) -> Result<(), StorageError> {
        if let Some(storage) = &self.inner.storage {
            storage.append_message(agent_id, message).await?;
        }
        Ok(())
    }

    /// Persist a block update to durable storage
    pub async fn persist_block(&self, agent_id: &str, block: &Block) -> Result<(), StorageError> {
        if let Some(storage) = &self.inner.storage {
            storage
                .update_block(agent_id, &block.label, &block.value)
                .await?;
        }
        Ok(())
    }

    /// Load agent from storage and populate in-memory cache
    ///
    /// TigerStyle: Loads from durable storage on cache miss.
    pub async fn load_agent_from_storage(
        &self,
        agent_id: &str,
    ) -> Result<Option<AgentState>, StorageError> {
        let Some(storage) = &self.inner.storage else {
            return Ok(None);
        };

        // Load agent metadata
        let Some(metadata) = storage.load_agent(agent_id).await? else {
            return Ok(None);
        };

        // Load blocks
        let blocks = storage.load_blocks(agent_id).await?;

        // Reconstruct AgentState from metadata + blocks
        let agent = AgentState {
            id: metadata.id,
            name: metadata.name,
            agent_type: metadata.agent_type,
            model: metadata.model,
            system: metadata.system,
            description: metadata.description,
            blocks,
            tool_ids: metadata.tool_ids,
            tags: metadata.tags,
            metadata: metadata.metadata,
            created_at: metadata.created_at,
            updated_at: metadata.updated_at,
        };

        // Populate cache
        if let Ok(mut agents) = self.inner.agents.write() {
            agents.insert(agent.id.clone(), agent.clone());
        }

        Ok(Some(agent))
    }

    /// Load messages from storage for an agent
    pub async fn load_messages_from_storage(
        &self,
        agent_id: &str,
        limit: usize,
    ) -> Result<Vec<Message>, StorageError> {
        let Some(storage) = &self.inner.storage else {
            return Ok(vec![]);
        };

        storage.load_messages(agent_id, limit).await
    }

    // =========================================================================
    // Agent operations (HashMap-based - DEPRECATED)
    // =========================================================================
    //
    // Phase 6.11: These methods use in-memory HashMap and are DEPRECATED.
    // Production code should use *_async() methods with AgentService instead.
    //
    // These methods are kept for backward compatibility with existing tests only.
    // They will be removed in a future phase once all tests migrate to AgentService.

    /// Create a new agent (DEPRECATED - use create_agent_async)
    #[deprecated(since = "0.1.0", note = "Use create_agent_async with AgentService")]
    pub fn create_agent(&self, agent: AgentState) -> Result<AgentState, StateError> {
        let mut agents = self
            .inner
            .agents
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        if agents.len() >= AGENTS_COUNT_MAX {
            return Err(StateError::LimitExceeded {
                resource: "agents",
                limit: AGENTS_COUNT_MAX,
            });
        }

        if agents.contains_key(&agent.id) {
            return Err(StateError::AlreadyExists {
                resource: "agent",
                id: agent.id.clone(),
            });
        }

        let result = agent.clone();
        agents.insert(agent.id.clone(), agent);

        // Initialize empty message list for the agent
        let mut messages = self
            .inner
            .messages
            .write()
            .map_err(|_| StateError::LockPoisoned)?;
        messages.insert(result.id.clone(), Vec::new());

        // Initialize empty archival list for the agent
        let mut archival = self
            .inner
            .archival
            .write()
            .map_err(|_| StateError::LockPoisoned)?;
        archival.insert(result.id.clone(), Vec::new());

        Ok(result)
    }

    /// Get an agent by ID
    pub fn get_agent(&self, id: &str) -> Result<Option<AgentState>, StateError> {
        let agents = self
            .inner
            .agents
            .read()
            .map_err(|_| StateError::LockPoisoned)?;
        Ok(agents.get(id).cloned())
    }

    /// List all agents with pagination
    pub fn list_agents(
        &self,
        limit: usize,
        cursor: Option<&str>,
    ) -> Result<(Vec<AgentState>, Option<String>), StateError> {
        let agents = self
            .inner
            .agents
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        let mut all_agents: Vec<_> = agents.values().cloned().collect();
        all_agents.sort_by(|a, b| a.created_at.cmp(&b.created_at));

        // Apply cursor (skip until we find the cursor ID)
        let start_idx = if let Some(cursor_id) = cursor {
            all_agents
                .iter()
                .position(|a| a.id == cursor_id)
                .map(|i| i + 1)
                .unwrap_or(0)
        } else {
            0
        };

        let page: Vec<_> = all_agents
            .into_iter()
            .skip(start_idx)
            .take(limit + 1)
            .collect();

        // Determine next cursor
        let (items, next_cursor) = if page.len() > limit {
            let items: Vec<_> = page.into_iter().take(limit).collect();
            let next_cursor = items.last().map(|a| a.id.clone());
            (items, next_cursor)
        } else {
            (page, None)
        };

        Ok((items, next_cursor))
    }

    /// Update an agent
    pub fn update_agent(
        &self,
        id: &str,
        update: impl FnOnce(&mut AgentState),
    ) -> Result<AgentState, StateError> {
        // DST: Check for fault injection on agent write
        if self.should_inject_fault("agent_write").is_some() {
            return Err(StateError::FaultInjected {
                operation: "agent_write".to_string(),
            });
        }

        let mut agents = self
            .inner
            .agents
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        let agent = agents.get_mut(id).ok_or_else(|| StateError::NotFound {
            resource: "agent",
            id: id.to_string(),
        })?;

        update(agent);
        Ok(agent.clone())
    }

    /// Delete an agent
    pub fn delete_agent(&self, id: &str) -> Result<(), StateError> {
        let mut agents = self
            .inner
            .agents
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        if agents.remove(id).is_none() {
            return Err(StateError::NotFound {
                resource: "agent",
                id: id.to_string(),
            });
        }

        // Also delete messages
        let mut messages = self
            .inner
            .messages
            .write()
            .map_err(|_| StateError::LockPoisoned)?;
        messages.remove(id);

        // Also delete archival entries
        let mut archival = self
            .inner
            .archival
            .write()
            .map_err(|_| StateError::LockPoisoned)?;
        archival.remove(id);

        Ok(())
    }

    /// Get agent count
    pub fn agent_count(&self) -> Result<usize, StateError> {
        let agents = self
            .inner
            .agents
            .read()
            .map_err(|_| StateError::LockPoisoned)?;
        let count = agents.len();

        // Record metric (this is called frequently from /metrics endpoint)
        // No need to record here - we'll record in the endpoint directly

        Ok(count)
    }

    /// Calculate and record memory usage metrics
    pub fn record_memory_metrics(&self) -> Result<(), StateError> {
        let agents = self
            .inner
            .agents
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        let messages = self
            .inner
            .messages
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        let archival = self
            .inner
            .archival
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        // Calculate memory usage by tier
        let mut core_memory_bytes = 0u64;
        let mut working_memory_bytes = 0u64;
        let mut archival_memory_bytes = 0u64;
        let mut total_blocks = 0u64;

        // Core memory: agent blocks
        for agent in agents.values() {
            for block in &agent.blocks {
                let block_size = block.value.len() + block.label.len();
                core_memory_bytes += block_size as u64;
                total_blocks += 1;
            }
        }

        // Working memory: messages
        for msgs in messages.values() {
            for msg in msgs {
                let msg_size = msg.content.len();
                working_memory_bytes += msg_size as u64;
            }
        }

        // Archival memory: archival entries
        for entries in archival.values() {
            for entry in entries {
                let entry_size = entry.content.len();
                archival_memory_bytes += entry_size as u64;
            }
        }

        // Note: Memory metrics (core, working, archival) are not yet implemented
        // because they require observable gauges with callbacks, which need proper
        // lifecycle management. For now, we just calculate the values here for future use.
        let _ = (
            core_memory_bytes,
            working_memory_bytes,
            archival_memory_bytes,
            total_blocks,
        );

        Ok(())
    }

    // =========================================================================
    // Block operations
    // =========================================================================

    /// Get a memory block by agent ID and block ID
    pub fn get_block(&self, agent_id: &str, block_id: &str) -> Result<Option<Block>, StateError> {
        let agents = self
            .inner
            .agents
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        let agent = agents.get(agent_id).ok_or_else(|| StateError::NotFound {
            resource: "agent",
            id: agent_id.to_string(),
        })?;

        Ok(agent.blocks.iter().find(|b| b.id == block_id).cloned())
    }

    /// Update a memory block
    pub fn update_block(
        &self,
        agent_id: &str,
        block_id: &str,
        update: impl FnOnce(&mut Block),
    ) -> Result<Block, StateError> {
        let mut agents = self
            .inner
            .agents
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        let agent = agents
            .get_mut(agent_id)
            .ok_or_else(|| StateError::NotFound {
                resource: "agent",
                id: agent_id.to_string(),
            })?;

        let block = agent
            .blocks
            .iter_mut()
            .find(|b| b.id == block_id)
            .ok_or_else(|| StateError::NotFound {
                resource: "block",
                id: block_id.to_string(),
            })?;

        update(block);
        Ok(block.clone())
    }

    /// List blocks for an agent
    pub fn list_blocks(&self, agent_id: &str) -> Result<Vec<Block>, StateError> {
        let agents = self
            .inner
            .agents
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        let agent = agents.get(agent_id).ok_or_else(|| StateError::NotFound {
            resource: "agent",
            id: agent_id.to_string(),
        })?;

        Ok(agent.blocks.clone())
    }

    /// Get a memory block by agent ID and label (for letta-code compatibility)
    pub fn get_block_by_label(
        &self,
        agent_id: &str,
        label: &str,
    ) -> Result<Option<Block>, StateError> {
        // DST: Check for fault injection
        if self.should_inject_fault("block_read").is_some() {
            return Err(StateError::FaultInjected {
                operation: "block_read".to_string(),
            });
        }

        let agents = self
            .inner
            .agents
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        let agent = agents.get(agent_id).ok_or_else(|| StateError::NotFound {
            resource: "agent",
            id: agent_id.to_string(),
        })?;

        Ok(agent.blocks.iter().find(|b| b.label == label).cloned())
    }

    /// Update a memory block by label (for letta-code compatibility)
    pub fn update_block_by_label(
        &self,
        agent_id: &str,
        label: &str,
        update: impl FnOnce(&mut Block),
    ) -> Result<Block, StateError> {
        // DST: Check for fault injection
        if self.should_inject_fault("block_write").is_some() {
            return Err(StateError::FaultInjected {
                operation: "block_write".to_string(),
            });
        }

        let mut agents = self
            .inner
            .agents
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        let agent = agents
            .get_mut(agent_id)
            .ok_or_else(|| StateError::NotFound {
                resource: "agent",
                id: agent_id.to_string(),
            })?;

        let block = agent
            .blocks
            .iter_mut()
            .find(|b| b.label == label)
            .ok_or_else(|| StateError::NotFound {
                resource: "block",
                id: label.to_string(),
            })?;

        update(block);
        Ok(block.clone())
    }

    /// Atomically append to a block or create it if it doesn't exist.
    ///
    /// BUG-001 FIX: This method eliminates the TOCTOU race condition in core_memory_append
    /// by holding the write lock for the entire check-and-update/create operation.
    ///
    /// TigerStyle: Atomic operation prevents race between check and modification.
    pub fn append_or_create_block_by_label(
        &self,
        agent_id: &str,
        label: &str,
        content: &str,
    ) -> Result<Block, StateError> {
        // DST: Check for fault injection
        if self.should_inject_fault("block_write").is_some() {
            return Err(StateError::FaultInjected {
                operation: "block_write".to_string(),
            });
        }

        // TigerStyle: Single write lock for entire operation (atomicity)
        let mut agents = self
            .inner
            .agents
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        let agent = agents
            .get_mut(agent_id)
            .ok_or_else(|| StateError::NotFound {
                resource: "agent",
                id: agent_id.to_string(),
            })?;

        // Find existing block or create new one - all within single lock
        if let Some(block) = agent.blocks.iter_mut().find(|b| b.label == label) {
            // Append to existing block
            block.value.push('\n');
            block.value.push_str(content);
            Ok(block.clone())
        } else {
            // Create new block and add to agent
            let block = Block::new(label, content);
            let result = block.clone();
            agent.blocks.push(block);
            Ok(result)
        }
    }

    // =========================================================================
    // Standalone block operations (for letta-code compatibility)
    // =========================================================================

    /// Create a standalone block
    pub fn create_standalone_block(&self, block: Block) -> Result<Block, StateError> {
        let mut blocks = self
            .inner
            .blocks
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        if blocks.len() >= BLOCKS_COUNT_MAX {
            return Err(StateError::LimitExceeded {
                resource: "blocks",
                limit: BLOCKS_COUNT_MAX,
            });
        }

        if blocks.contains_key(&block.id) {
            return Err(StateError::AlreadyExists {
                resource: "block",
                id: block.id.clone(),
            });
        }

        let result = block.clone();
        blocks.insert(block.id.clone(), block);
        Ok(result)
    }

    /// Get a standalone block by ID
    pub fn get_standalone_block(&self, id: &str) -> Result<Option<Block>, StateError> {
        let blocks = self
            .inner
            .blocks
            .read()
            .map_err(|_| StateError::LockPoisoned)?;
        Ok(blocks.get(id).cloned())
    }

    /// List all standalone blocks with pagination
    pub fn list_standalone_blocks(
        &self,
        limit: usize,
        cursor: Option<&str>,
        label: Option<&str>,
    ) -> Result<(Vec<Block>, Option<String>), StateError> {
        let blocks = self
            .inner
            .blocks
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        let mut all_blocks: Vec<_> = blocks.values().cloned().collect();

        // Filter by label if provided
        if let Some(l) = label {
            all_blocks.retain(|b| b.label == l);
        }

        all_blocks.sort_by(|a, b| a.created_at.cmp(&b.created_at));

        // Apply cursor (skip until we find the cursor ID)
        let start_idx = if let Some(cursor_id) = cursor {
            all_blocks
                .iter()
                .position(|b| b.id == cursor_id)
                .map(|i| i + 1)
                .unwrap_or(0)
        } else {
            0
        };

        let page: Vec<_> = all_blocks
            .into_iter()
            .skip(start_idx)
            .take(limit + 1)
            .collect();

        // Determine next cursor
        let (items, next_cursor) = if page.len() > limit {
            let items: Vec<_> = page.into_iter().take(limit).collect();
            let next_cursor = items.last().map(|b| b.id.clone());
            (items, next_cursor)
        } else {
            (page, None)
        };

        Ok((items, next_cursor))
    }

    /// Update a standalone block
    pub fn update_standalone_block(
        &self,
        id: &str,
        update: impl FnOnce(&mut Block),
    ) -> Result<Block, StateError> {
        let mut blocks = self
            .inner
            .blocks
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        let block = blocks.get_mut(id).ok_or_else(|| StateError::NotFound {
            resource: "block",
            id: id.to_string(),
        })?;

        update(block);
        Ok(block.clone())
    }

    /// Delete a standalone block
    pub fn delete_standalone_block(&self, id: &str) -> Result<(), StateError> {
        let mut blocks = self
            .inner
            .blocks
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        if blocks.remove(id).is_none() {
            return Err(StateError::NotFound {
                resource: "block",
                id: id.to_string(),
            });
        }

        Ok(())
    }

    /// Get standalone block count
    pub fn standalone_block_count(&self) -> Result<usize, StateError> {
        let blocks = self
            .inner
            .blocks
            .read()
            .map_err(|_| StateError::LockPoisoned)?;
        Ok(blocks.len())
    }

    // =========================================================================
    // Message operations
    // =========================================================================

    /// Add a message to an agent's history
    pub fn add_message(&self, agent_id: &str, message: Message) -> Result<Message, StateError> {
        // DST: Check for fault injection on message write
        if self.should_inject_fault("message_write").is_some() {
            return Err(StateError::FaultInjected {
                operation: "message_write".to_string(),
            });
        }

        let mut messages = self
            .inner
            .messages
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        let agent_messages = messages
            .get_mut(agent_id)
            .ok_or_else(|| StateError::NotFound {
                resource: "agent",
                id: agent_id.to_string(),
            })?;

        if agent_messages.len() >= MESSAGES_PER_AGENT_MAX {
            return Err(StateError::LimitExceeded {
                resource: "messages",
                limit: MESSAGES_PER_AGENT_MAX,
            });
        }

        let result = message.clone();
        agent_messages.push(message);
        Ok(result)
    }

    /// List messages for an agent with pagination
    pub fn list_messages(
        &self,
        agent_id: &str,
        limit: usize,
        before: Option<&str>,
    ) -> Result<Vec<Message>, StateError> {
        // DST: Check for fault injection on message read
        if self.should_inject_fault("message_read").is_some() {
            return Err(StateError::FaultInjected {
                operation: "message_read".to_string(),
            });
        }

        let messages = self
            .inner
            .messages
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        let agent_messages = messages.get(agent_id).ok_or_else(|| StateError::NotFound {
            resource: "agent",
            id: agent_id.to_string(),
        })?;

        // If before is specified, find messages before that ID
        let end_idx = if let Some(before_id) = before {
            agent_messages
                .iter()
                .position(|m| m.id == before_id)
                .unwrap_or(agent_messages.len())
        } else {
            agent_messages.len()
        };

        let start_idx = end_idx.saturating_sub(limit);
        Ok(agent_messages[start_idx..end_idx].to_vec())
    }

    // =========================================================================
    // Tool operations
    // =========================================================================

    /// Register a tool
    pub fn register_tool(
        &self,
        name: String,
        description: String,
        input_schema: serde_json::Value,
        source: Option<String>,
    ) -> Result<(), StateError> {
        let mut tools = self
            .inner
            .tools
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        tools.insert(
            name.clone(),
            ToolInfo {
                name,
                description,
                input_schema,
                source,
            },
        );
        Ok(())
    }

    /// Get a tool by name
    pub fn get_tool(&self, name: &str) -> Option<ToolInfo> {
        let tools = self.inner.tools.read().ok()?;
        tools.get(name).cloned()
    }

    /// List all tools
    pub fn list_tools(&self) -> Vec<ToolInfo> {
        let tools = self.inner.tools.read().ok();
        match tools {
            Some(t) => t.values().cloned().collect(),
            None => vec![],
        }
    }

    /// Delete a tool
    pub fn delete_tool(&self, name: &str) -> Result<(), StateError> {
        let mut tools = self
            .inner
            .tools
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        if tools.remove(name).is_none() {
            return Err(StateError::NotFound {
                resource: "tool",
                id: name.to_string(),
            });
        }

        Ok(())
    }

    /// Execute a tool (placeholder - actual execution would integrate with kelpie-tools)
    pub async fn execute_tool(
        &self,
        name: &str,
        _arguments: serde_json::Value,
    ) -> Result<String, StateError> {
        // Verify tool exists
        let tools = self
            .inner
            .tools
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        if !tools.contains_key(name) {
            return Err(StateError::NotFound {
                resource: "tool",
                id: name.to_string(),
            });
        }

        // For now, return a placeholder response
        // In a full implementation, this would integrate with kelpie-tools
        Ok(format!("Tool '{}' executed successfully", name))
    }

    // =========================================================================
    // Archival memory operations
    // =========================================================================

    /// Add entry to archival memory
    pub fn add_archival(
        &self,
        agent_id: &str,
        content: String,
        metadata: Option<serde_json::Value>,
    ) -> Result<ArchivalEntry, StateError> {
        // DST: Check for fault injection on archival write
        if self.should_inject_fault("archival_write").is_some() {
            return Err(StateError::FaultInjected {
                operation: "archival_write".to_string(),
            });
        }

        let mut archival = self
            .inner
            .archival
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        let entries = archival
            .get_mut(agent_id)
            .ok_or_else(|| StateError::NotFound {
                resource: "agent",
                id: agent_id.to_string(),
            })?;

        if entries.len() >= ARCHIVAL_ENTRIES_PER_AGENT_MAX {
            return Err(StateError::LimitExceeded {
                resource: "archival_entries",
                limit: ARCHIVAL_ENTRIES_PER_AGENT_MAX,
            });
        }

        let entry = ArchivalEntry {
            id: Uuid::new_v4().to_string(),
            content,
            metadata,
            created_at: Utc::now().to_rfc3339(),
        };

        let result = entry.clone();
        entries.push(entry);
        Ok(result)
    }

    /// Search archival memory
    pub fn search_archival(
        &self,
        agent_id: &str,
        query: Option<&str>,
        limit: usize,
    ) -> Result<Vec<ArchivalEntry>, StateError> {
        // DST: Check for fault injection on archival read
        if self.should_inject_fault("archival_read").is_some() {
            return Err(StateError::FaultInjected {
                operation: "archival_read".to_string(),
            });
        }

        let archival = self
            .inner
            .archival
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        let entries = archival.get(agent_id).ok_or_else(|| StateError::NotFound {
            resource: "agent",
            id: agent_id.to_string(),
        })?;

        // Simple text search if query is provided
        let results: Vec<_> = if let Some(q) = query {
            let q_lower = q.to_lowercase();
            entries
                .iter()
                .filter(|e| e.content.to_lowercase().contains(&q_lower))
                .take(limit)
                .cloned()
                .collect()
        } else {
            entries.iter().take(limit).cloned().collect()
        };

        Ok(results)
    }

    /// Get a specific archival entry
    pub fn get_archival_entry(
        &self,
        agent_id: &str,
        entry_id: &str,
    ) -> Result<Option<ArchivalEntry>, StateError> {
        let archival = self
            .inner
            .archival
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        let entries = archival.get(agent_id).ok_or_else(|| StateError::NotFound {
            resource: "agent",
            id: agent_id.to_string(),
        })?;

        Ok(entries.iter().find(|e| e.id == entry_id).cloned())
    }

    /// Delete an archival entry
    pub fn delete_archival_entry(&self, agent_id: &str, entry_id: &str) -> Result<(), StateError> {
        let mut archival = self
            .inner
            .archival
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        let entries = archival
            .get_mut(agent_id)
            .ok_or_else(|| StateError::NotFound {
                resource: "agent",
                id: agent_id.to_string(),
            })?;

        let initial_len = entries.len();
        entries.retain(|e| e.id != entry_id);

        if entries.len() == initial_len {
            return Err(StateError::NotFound {
                resource: "archival_entry",
                id: entry_id.to_string(),
            });
        }

        Ok(())
    }

    // =========================================================================
    // Job operations (Phase 5: Scheduling)
    // =========================================================================

    /// Add a scheduled job
    pub fn add_job(&self, job: Job) -> Result<(), StateError> {
        let mut jobs = self
            .inner
            .jobs
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        if jobs.contains_key(&job.id) {
            return Err(StateError::AlreadyExists {
                resource: "job",
                id: job.id.clone(),
            });
        }

        jobs.insert(job.id.clone(), job);
        Ok(())
    }

    /// Get a job by ID
    pub fn get_job(&self, job_id: &str) -> Result<Option<Job>, StateError> {
        let jobs = self
            .inner
            .jobs
            .read()
            .map_err(|_| StateError::LockPoisoned)?;
        Ok(jobs.get(job_id).cloned())
    }

    /// List jobs for a specific agent
    pub fn list_jobs_for_agent(&self, agent_id: &str) -> Result<Vec<Job>, StateError> {
        let jobs = self
            .inner
            .jobs
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        let agent_jobs: Vec<_> = jobs
            .values()
            .filter(|j| j.agent_id == agent_id)
            .cloned()
            .collect();

        Ok(agent_jobs)
    }

    /// List all jobs with optional agent filter
    pub fn list_all_jobs(&self, agent_id: Option<&str>) -> Result<Vec<Job>, StateError> {
        let jobs = self
            .inner
            .jobs
            .read()
            .map_err(|_| StateError::LockPoisoned)?;

        let filtered_jobs: Vec<_> = if let Some(agent_id) = agent_id {
            jobs.values()
                .filter(|j| j.agent_id == agent_id)
                .cloned()
                .collect()
        } else {
            jobs.values().cloned().collect()
        };

        Ok(filtered_jobs)
    }

    /// Update a job
    pub fn update_job(&self, job: Job) -> Result<(), StateError> {
        let mut jobs = self
            .inner
            .jobs
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        if !jobs.contains_key(&job.id) {
            return Err(StateError::NotFound {
                resource: "job",
                id: job.id.clone(),
            });
        }

        jobs.insert(job.id.clone(), job);
        Ok(())
    }

    /// Delete a job
    pub fn delete_job(&self, job_id: &str) -> Result<(), StateError> {
        let mut jobs = self
            .inner
            .jobs
            .write()
            .map_err(|_| StateError::LockPoisoned)?;

        if jobs.remove(job_id).is_none() {
            return Err(StateError::NotFound {
                resource: "job",
                id: job_id.to_string(),
            });
        }

        Ok(())
    }
}

impl Default for AppState {
    fn default() -> Self {
        Self::new()
    }
}

/// State operation errors
#[derive(Debug, Clone)]
pub enum StateError {
    /// Resource not found
    NotFound { resource: &'static str, id: String },
    /// Resource already exists
    AlreadyExists { resource: &'static str, id: String },
    /// Limit exceeded
    LimitExceeded {
        resource: &'static str,
        limit: usize,
    },
    /// Lock poisoned (shouldn't happen in practice)
    LockPoisoned,
    /// Fault injected (DST testing only)
    FaultInjected { operation: String },
    /// Internal error (service errors, etc.)
    Internal { message: String },
}

impl std::fmt::Display for StateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StateError::NotFound { resource, id } => {
                write!(f, "{} with id '{}' not found", resource, id)
            }
            StateError::AlreadyExists { resource, id } => {
                write!(f, "{} with id '{}' already exists", resource, id)
            }
            StateError::LimitExceeded { resource, limit } => {
                write!(f, "{} limit ({}) exceeded", resource, limit)
            }
            StateError::LockPoisoned => write!(f, "internal lock error"),
            StateError::FaultInjected { operation } => {
                write!(f, "fault injected during operation: {}", operation)
            }
            StateError::Internal { message } => {
                write!(f, "internal error: {}", message)
            }
        }
    }
}

impl std::error::Error for StateError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{AgentType, CreateAgentRequest, CreateBlockRequest};

    fn create_test_agent(name: &str) -> AgentState {
        AgentState::from_request(CreateAgentRequest {
            name: name.to_string(),
            agent_type: AgentType::default(),
            model: None,
            system: None,
            description: None,
            memory_blocks: vec![CreateBlockRequest {
                label: "persona".to_string(),
                value: "I am a test agent".to_string(),
                description: None,
                limit: None,
            }],
            block_ids: vec![],
            tool_ids: vec![],
            tags: vec![],
            metadata: serde_json::json!({}),
        })
    }

    #[test]
    fn test_create_and_get_agent() {
        let state = AppState::new();
        let agent = create_test_agent("test-agent");
        let agent_id = agent.id.clone();

        let created = state.create_agent(agent).unwrap();
        assert_eq!(created.name, "test-agent");

        let retrieved = state.get_agent(&agent_id).unwrap().unwrap();
        assert_eq!(retrieved.id, agent_id);
        assert_eq!(retrieved.blocks.len(), 1);
    }

    #[test]
    fn test_list_agents_pagination() {
        let state = AppState::new();

        for i in 0..5 {
            let agent = create_test_agent(&format!("agent-{}", i));
            state.create_agent(agent).unwrap();
        }

        // First page
        let (page1, cursor1) = state.list_agents(2, None).unwrap();
        assert_eq!(page1.len(), 2);
        assert!(cursor1.is_some());

        // Second page
        let (page2, cursor2) = state.list_agents(2, cursor1.as_deref()).unwrap();
        assert_eq!(page2.len(), 2);
        assert!(cursor2.is_some());

        // Third page (last)
        let (page3, cursor3) = state.list_agents(2, cursor2.as_deref()).unwrap();
        assert_eq!(page3.len(), 1);
        assert!(cursor3.is_none());
    }

    #[test]
    fn test_delete_agent() {
        let state = AppState::new();
        let agent = create_test_agent("to-delete");
        let agent_id = agent.id.clone();

        state.create_agent(agent).unwrap();
        assert!(state.get_agent(&agent_id).unwrap().is_some());

        state.delete_agent(&agent_id).unwrap();
        assert!(state.get_agent(&agent_id).unwrap().is_none());
    }

    #[test]
    fn test_update_block() {
        let state = AppState::new();
        let agent = create_test_agent("block-test");
        let agent_id = agent.id.clone();
        let block_id = agent.blocks[0].id.clone();

        state.create_agent(agent).unwrap();

        let updated = state
            .update_block(&agent_id, &block_id, |block| {
                block.value = "Updated value".to_string();
            })
            .unwrap();

        assert_eq!(updated.value, "Updated value");
    }

    #[test]
    fn test_messages() {
        let state = AppState::new();
        let agent = create_test_agent("msg-test");
        let agent_id = agent.id.clone();

        state.create_agent(agent).unwrap();

        // Add messages
        for i in 0..5 {
            let msg = Message {
                id: format!("msg-{}", i),
                agent_id: agent_id.clone(),
                message_type: "user_message".to_string(),
                role: crate::models::MessageRole::User,
                content: format!("Message {}", i),
                tool_call_id: None,
                tool_calls: None,
                created_at: chrono::Utc::now(),
            };
            state.add_message(&agent_id, msg).unwrap();
        }

        // List last 3
        let messages = state.list_messages(&agent_id, 3, None).unwrap();
        assert_eq!(messages.len(), 3);
        assert_eq!(messages[0].content, "Message 2");
        assert_eq!(messages[2].content, "Message 4");
    }

    #[tokio::test]
    async fn test_dual_mode_get_agent_hashmap() {
        // Test dual-mode with HashMap (no service)
        let state = AppState::new();
        let agent = create_test_agent("dual-mode-test");
        let agent_id = agent.id.clone();

        // Create via HashMap
        state.create_agent(agent).unwrap();

        // Get via dual-mode method (should use HashMap)
        let retrieved = state.get_agent_async(&agent_id).await.unwrap();
        assert!(retrieved.is_some());
        assert_eq!(retrieved.unwrap().id, agent_id);

        // Delete via dual-mode
        state.delete_agent_async(&agent_id).await.unwrap();

        // Verify deleted
        let retrieved = state.get_agent_async(&agent_id).await.unwrap();
        assert!(retrieved.is_none());
    }
}
