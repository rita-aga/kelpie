/**
 * Kelpie TypeScript Client
 *
 * A Letta-compatible client for the Kelpie agent runtime.
 */

export interface Agent {
  id: string;
  name: string;
  agent_type: string;
  model: string | null;
  system: string | null;
  description: string | null;
  blocks: Block[];
  tool_ids: string[];
  tags: string[];
  metadata: Record<string, unknown> | null;
  created_at: string;
  updated_at: string;
}

export interface Block {
  id: string;
  label: string;
  value: string;
  description: string | null;
  limit: number | null;
  created_at: string;
  updated_at: string;
}

export interface Message {
  id: string;
  agent_id: string;
  role: "user" | "assistant" | "system" | "tool";
  content: string;
  tool_call_id: string | null;
  tool_calls: ToolCall[] | null;
  created_at: string;
}

export interface ToolCall {
  id: string;
  name: string;
  arguments: Record<string, unknown>;
}

export interface MessageResponse {
  messages: Message[];
  usage: UsageStats | null;
}

export interface UsageStats {
  prompt_tokens: number;
  completion_tokens: number;
  total_tokens: number;
}

export interface CreateAgentRequest {
  name: string;
  agent_type?: string;
  model?: string;
  system?: string;
  description?: string;
  memory_blocks?: { label: string; value: string; description?: string; limit?: number }[];
  tool_ids?: string[];
  tags?: string[];
  metadata?: Record<string, unknown>;
}

export interface CreateMessageRequest {
  role: "user" | "system" | "tool";
  content: string;
  tool_call_id?: string;
}

export interface UpdateBlockRequest {
  value?: string;
  description?: string;
  limit?: number;
}

export class KelpieError extends Error {
  code?: string;
  status?: number;

  constructor(message: string, code?: string, status?: number) {
    super(message);
    this.name = "KelpieError";
    this.code = code;
    this.status = status;
  }
}

export class KelpieClient {
  private baseUrl: string;
  private timeout: number;

  constructor(baseUrl: string = "http://localhost:8283", timeout: number = 30000) {
    this.baseUrl = baseUrl.replace(/\/$/, "");
    this.timeout = timeout;
  }

  private async request<T>(
    method: string,
    path: string,
    body?: unknown
  ): Promise<T> {
    const controller = new AbortController();
    const timeoutId = setTimeout(() => controller.abort(), this.timeout);

    try {
      const response = await fetch(`${this.baseUrl}${path}`, {
        method,
        headers: {
          "Content-Type": "application/json",
        },
        body: body ? JSON.stringify(body) : undefined,
        signal: controller.signal,
      });

      if (!response.ok) {
        const errorBody = await response.text();
        let errorData: { message?: string; code?: string } = {};
        try {
          errorData = JSON.parse(errorBody);
        } catch {
          errorData = { message: errorBody };
        }
        throw new KelpieError(
          errorData.message || `HTTP ${response.status}`,
          errorData.code,
          response.status
        );
      }

      if (response.status === 204) {
        return undefined as T;
      }

      return response.json();
    } finally {
      clearTimeout(timeoutId);
    }
  }

  // Agent operations

  async createAgent(request: CreateAgentRequest): Promise<Agent> {
    return this.request("POST", "/v1/agents", request);
  }

  async getAgent(agentId: string): Promise<Agent> {
    return this.request("GET", `/v1/agents/${agentId}`);
  }

  async listAgents(limit: number = 50, cursor?: string): Promise<{ items: Agent[]; cursor?: string }> {
    const params = new URLSearchParams({ limit: String(limit) });
    if (cursor) params.set("cursor", cursor);
    return this.request("GET", `/v1/agents?${params}`);
  }

  async updateAgent(
    agentId: string,
    update: { name?: string; system?: string; description?: string; tags?: string[]; metadata?: Record<string, unknown> }
  ): Promise<Agent> {
    return this.request("PATCH", `/v1/agents/${agentId}`, update);
  }

  async deleteAgent(agentId: string): Promise<void> {
    return this.request("DELETE", `/v1/agents/${agentId}`);
  }

  // Block operations

  async listBlocks(agentId: string): Promise<Block[]> {
    return this.request("GET", `/v1/agents/${agentId}/blocks`);
  }

  async getBlock(agentId: string, blockId: string): Promise<Block> {
    return this.request("GET", `/v1/agents/${agentId}/blocks/${blockId}`);
  }

  async updateBlock(agentId: string, blockId: string, update: UpdateBlockRequest): Promise<Block> {
    return this.request("PATCH", `/v1/agents/${agentId}/blocks/${blockId}`, update);
  }

  // Message operations

  async sendMessage(agentId: string, content: string, role: "user" | "system" | "tool" = "user"): Promise<MessageResponse> {
    return this.request("POST", `/v1/agents/${agentId}/messages`, { role, content });
  }

  async listMessages(agentId: string, limit: number = 100, before?: string): Promise<Message[]> {
    const params = new URLSearchParams({ limit: String(limit) });
    if (before) params.set("before", before);
    return this.request("GET", `/v1/agents/${agentId}/messages?${params}`);
  }

  // Health check

  async health(): Promise<{ status: string; version: string; uptime_seconds: number }> {
    return this.request("GET", "/health");
  }
}

export default KelpieClient;
