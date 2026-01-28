//! Telegram Bot Interface
//!
//! TigerStyle: Telegram bot that allows users to chat with Kelpie agents.
//!
//! Features:
//! - Maps Telegram users to agents (configurable strategy)
//! - Supports pseudo-streaming via message edits
//! - Rate limiting per user
//! - Graceful shutdown
//!
//! Configuration via environment variables:
//! - KELPIE_TELEGRAM_TOKEN: Bot token from @BotFather (required)
//! - KELPIE_TELEGRAM_AGENT_STRATEGY: "user_agent" or "shared_agent" (default: user_agent)
//! - KELPIE_TELEGRAM_SHARED_AGENT_ID: Agent ID for shared mode (required if strategy is shared_agent)
//! - KELPIE_TELEGRAM_RATE_LIMIT: Messages per minute per user (default: 20)

use crate::models::{AgentType, CreateAgentRequest};
use crate::service::AgentService;
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use teloxide::prelude::*;
use teloxide::types::ChatId;
use tokio::sync::RwLock;

// =============================================================================
// TigerStyle Constants
// =============================================================================

/// Default rate limit in messages per minute per user
pub const RATE_LIMIT_MESSAGES_PER_MINUTE_DEFAULT: u32 = 20;

/// Rate limit window in seconds
pub const RATE_LIMIT_WINDOW_SECONDS: u64 = 60;

/// Minimum time between message edits (pseudo-streaming)
pub const MESSAGE_EDIT_INTERVAL_MS_MIN: u64 = 500;

/// Maximum message length for Telegram
pub const TELEGRAM_MESSAGE_LENGTH_MAX: usize = 4096;

/// Typing indicator refresh interval
pub const TYPING_INDICATOR_REFRESH_MS: u64 = 4000;

// =============================================================================
// Agent Strategy
// =============================================================================

/// Strategy for mapping Telegram users to agents
#[derive(Debug, Clone)]
pub enum AgentStrategy {
    /// Each Telegram user gets their own agent
    UserAgent {
        /// Prefix for auto-created agent names
        name_prefix: String,
    },
    /// All users share a single agent
    SharedAgent {
        /// The shared agent ID
        agent_id: String,
    },
}

impl AgentStrategy {
    /// Parse strategy from environment
    pub fn from_env() -> Self {
        let strategy = std::env::var("KELPIE_TELEGRAM_AGENT_STRATEGY")
            .unwrap_or_else(|_| "user_agent".to_string());

        match strategy.to_lowercase().as_str() {
            "shared_agent" | "shared" => {
                let agent_id = std::env::var("KELPIE_TELEGRAM_SHARED_AGENT_ID")
                    .expect("KELPIE_TELEGRAM_SHARED_AGENT_ID required for shared_agent strategy");
                Self::SharedAgent { agent_id }
            }
            _ => Self::UserAgent {
                name_prefix: std::env::var("KELPIE_TELEGRAM_AGENT_PREFIX")
                    .unwrap_or_else(|_| "telegram_user_".to_string()),
            },
        }
    }
}

// =============================================================================
// Rate Limiter
// =============================================================================

/// Per-user rate limiter
#[derive(Debug, Default)]
struct RateLimiter {
    /// User timestamps: user_id -> list of message timestamps
    timestamps: HashMap<i64, Vec<Instant>>,
}

impl RateLimiter {
    /// Check if user is rate limited
    fn is_limited(&mut self, user_id: i64, limit: u32) -> bool {
        let now = Instant::now();
        let window = Duration::from_secs(RATE_LIMIT_WINDOW_SECONDS);

        // Get or create timestamps for user
        let timestamps = self.timestamps.entry(user_id).or_default();

        // Remove old timestamps outside the window
        timestamps.retain(|t| now.duration_since(*t) < window);

        // Check if over limit
        if timestamps.len() >= limit as usize {
            return true;
        }

        // Record this request
        timestamps.push(now);
        false
    }
}

// =============================================================================
// User Agent Map
// =============================================================================

/// Maps Telegram users to agent IDs
#[derive(Debug, Default)]
struct UserAgentMap {
    /// user_id -> agent_id
    agents: HashMap<i64, String>,
}

// =============================================================================
// Telegram Bot
// =============================================================================

/// Telegram bot state
pub struct TelegramBot<R: kelpie_core::Runtime + Clone + Send + Sync + 'static> {
    /// Agent service for handling messages
    service: Arc<AgentService<R>>,
    /// Agent strategy
    strategy: AgentStrategy,
    /// Rate limiter
    rate_limiter: Arc<RwLock<RateLimiter>>,
    /// User to agent mapping (for user_agent strategy)
    user_agents: Arc<RwLock<UserAgentMap>>,
    /// Rate limit per user
    rate_limit: u32,
}

impl<R: kelpie_core::Runtime + Clone + Send + Sync + 'static> TelegramBot<R> {
    /// Create a new Telegram bot
    pub fn new(service: Arc<AgentService<R>>) -> Self {
        let rate_limit = std::env::var("KELPIE_TELEGRAM_RATE_LIMIT")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(RATE_LIMIT_MESSAGES_PER_MINUTE_DEFAULT);

        Self {
            service,
            strategy: AgentStrategy::from_env(),
            rate_limiter: Arc::new(RwLock::new(RateLimiter::default())),
            user_agents: Arc::new(RwLock::new(UserAgentMap::default())),
            rate_limit,
        }
    }

    /// Start the bot
    pub async fn start(self: Arc<Self>) -> anyhow::Result<()> {
        let token = std::env::var("KELPIE_TELEGRAM_TOKEN")
            .map_err(|_| anyhow::anyhow!("KELPIE_TELEGRAM_TOKEN not set"))?;

        let bot = Bot::new(token);

        tracing::info!(
            strategy = ?self.strategy,
            rate_limit = self.rate_limit,
            "Starting Telegram bot"
        );

        // Set up message handler
        let bot_state = self.clone();
        let handler = Update::filter_message()
            .filter_map(|msg: Message| {
                let text = msg.text()?.to_string();
                Some((msg, text))
            })
            .endpoint(move |bot: Bot, (msg, text): (Message, String)| {
                let state = bot_state.clone();
                async move {
                    state.handle_message(bot, msg, text).await;
                    Ok::<(), std::convert::Infallible>(())
                }
            });

        Dispatcher::builder(bot, handler)
            .enable_ctrlc_handler()
            .build()
            .dispatch()
            .await;

        Ok(())
    }

    /// Handle incoming message
    async fn handle_message(&self, bot: Bot, msg: Message, text: String) {
        let user_id = msg.from().map(|u| u.id.0 as i64).unwrap_or(0);
        let chat_id = msg.chat.id;
        let username = msg
            .from()
            .and_then(|u| u.username.clone())
            .unwrap_or_else(|| format!("user_{}", user_id));

        // Rate limiting
        {
            let mut limiter = self.rate_limiter.write().await;
            if limiter.is_limited(user_id, self.rate_limit) {
                let _ = bot
                    .send_message(
                        chat_id,
                        "Rate limit exceeded. Please wait a moment before sending more messages.",
                    )
                    .await;
                return;
            }
        }

        // Handle /start command
        if text.starts_with("/start") {
            let welcome = match &self.strategy {
                AgentStrategy::UserAgent { .. } => {
                    "Welcome! I'm your personal Kelpie assistant. Just send me a message to get started."
                }
                AgentStrategy::SharedAgent { .. } => {
                    "Welcome! Send me a message to chat with the assistant."
                }
            };
            let _ = bot.send_message(chat_id, welcome).await;
            return;
        }

        // Handle /help command
        if text.starts_with("/help") {
            let help = "Commands:\n\
                /start - Start the conversation\n\
                /help - Show this help\n\
                /reset - Reset your conversation (user_agent mode only)\n\
                \n\
                Just type your message to chat!";
            let _ = bot.send_message(chat_id, help).await;
            return;
        }

        // Handle /reset command (user_agent mode only)
        if text.starts_with("/reset") {
            if let AgentStrategy::UserAgent { .. } = &self.strategy {
                // Remove user's agent mapping
                self.user_agents.write().await.agents.remove(&user_id);
                let _ = bot
                    .send_message(
                        chat_id,
                        "Conversation reset. Your next message will start fresh.",
                    )
                    .await;
            } else {
                let _ = bot
                    .send_message(chat_id, "Reset is not available in shared agent mode.")
                    .await;
            }
            return;
        }

        // Send typing indicator
        let _ = bot
            .send_chat_action(chat_id, teloxide::types::ChatAction::Typing)
            .await;

        // Get or create agent for this user
        let agent_id = match self.get_or_create_agent(user_id, &username).await {
            Ok(id) => id,
            Err(e) => {
                tracing::error!(error = %e, "Failed to get/create agent");
                let _ = bot
                    .send_message(
                        chat_id,
                        "Sorry, I'm having trouble right now. Please try again later.",
                    )
                    .await;
                return;
            }
        };

        // Send message to agent using send_message_full
        match self
            .service
            .send_message_full(&agent_id, text.clone())
            .await
        {
            Ok(response) => {
                // Find assistant response from HandleMessageFullResponse
                let assistant_content = response
                    .messages
                    .iter()
                    .rev()
                    .find(|m| m.role == crate::models::MessageRole::Assistant)
                    .map(|m| m.content.clone())
                    .unwrap_or_else(|| "I didn't have a response.".to_string());

                // Split long messages
                self.send_long_message(&bot, chat_id, &assistant_content)
                    .await;
            }
            Err(e) => {
                tracing::error!(error = %e, agent_id = %agent_id, "Failed to send message to agent");
                let _ = bot
                    .send_message(
                        chat_id,
                        "Sorry, I couldn't process your message. Please try again.",
                    )
                    .await;
            }
        }
    }

    /// Get or create agent for user
    async fn get_or_create_agent(&self, user_id: i64, username: &str) -> anyhow::Result<String> {
        match &self.strategy {
            AgentStrategy::SharedAgent { agent_id } => Ok(agent_id.clone()),
            AgentStrategy::UserAgent { name_prefix } => {
                // Check if user already has an agent
                {
                    let agents = self.user_agents.read().await;
                    if let Some(agent_id) = agents.agents.get(&user_id) {
                        return Ok(agent_id.clone());
                    }
                }

                // Create new agent for user
                let agent_name = format!("{}{}", name_prefix, username);
                let request = CreateAgentRequest {
                    name: agent_name.clone(),
                    agent_type: AgentType::MemgptAgent,
                    system: Some("You are a helpful assistant chatting via Telegram.".to_string()),
                    ..Default::default()
                };
                let agent = self.service.create_agent(request).await?;

                // Store mapping
                let agent_id = agent.id.clone();
                self.user_agents
                    .write()
                    .await
                    .agents
                    .insert(user_id, agent_id.clone());

                tracing::info!(
                    user_id = user_id,
                    username = %username,
                    agent_id = %agent_id,
                    "Created new agent for Telegram user"
                );

                Ok(agent_id)
            }
        }
    }

    /// Send a potentially long message, splitting if necessary
    async fn send_long_message(&self, bot: &Bot, chat_id: ChatId, content: &str) {
        // Split into chunks if too long
        let chunks: Vec<&str> = content
            .as_bytes()
            .chunks(TELEGRAM_MESSAGE_LENGTH_MAX)
            .map(|chunk| std::str::from_utf8(chunk).unwrap_or(""))
            .collect();

        for chunk in chunks {
            if !chunk.is_empty() {
                if let Err(e) = bot.send_message(chat_id, chunk).await {
                    tracing::error!(error = %e, "Failed to send Telegram message");
                }
            }
        }
    }
}

/// Start the Telegram bot if configured
pub async fn start_if_configured<R: kelpie_core::Runtime + Clone + Send + Sync + 'static>(
    service: Arc<AgentService<R>>,
) {
    if std::env::var("KELPIE_TELEGRAM_TOKEN").is_ok() {
        let bot = Arc::new(TelegramBot::new(service));

        // Spawn bot in background
        let runtime = kelpie_core::current_runtime();
        drop(kelpie_core::Runtime::spawn(&runtime, async move {
            if let Err(e) = bot.start().await {
                tracing::error!(error = %e, "Telegram bot failed");
            }
        }));

        tracing::info!("Telegram bot started");
    } else {
        tracing::debug!("KELPIE_TELEGRAM_TOKEN not set, Telegram bot disabled");
    }
}
