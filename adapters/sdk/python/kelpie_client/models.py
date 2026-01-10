"""Data models for Kelpie client.

These models match the Letta API schema for compatibility.
"""

from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum
from typing import Any, Optional


class AgentType(str, Enum):
    """Agent type enumeration."""
    MEMGPT_AGENT = "memgpt_agent"
    LETTA_V1_AGENT = "letta_v1_agent"
    REACT_AGENT = "react_agent"


class MessageRole(str, Enum):
    """Message role enumeration."""
    USER = "user"
    ASSISTANT = "assistant"
    SYSTEM = "system"
    TOOL = "tool"


@dataclass
class Block:
    """Memory block."""
    id: str
    label: str
    value: str
    description: Optional[str] = None
    limit: Optional[int] = None
    created_at: Optional[datetime] = None
    updated_at: Optional[datetime] = None

    @classmethod
    def from_dict(cls, data: dict) -> "Block":
        """Create a Block from a dictionary."""
        return cls(
            id=data["id"],
            label=data["label"],
            value=data["value"],
            description=data.get("description"),
            limit=data.get("limit"),
            created_at=datetime.fromisoformat(data["created_at"].replace("Z", "+00:00"))
            if data.get("created_at")
            else None,
            updated_at=datetime.fromisoformat(data["updated_at"].replace("Z", "+00:00"))
            if data.get("updated_at")
            else None,
        )


@dataclass
class Agent:
    """Agent state."""
    id: str
    name: str
    agent_type: AgentType
    model: Optional[str] = None
    system: Optional[str] = None
    description: Optional[str] = None
    blocks: list[Block] = field(default_factory=list)
    tool_ids: list[str] = field(default_factory=list)
    tags: list[str] = field(default_factory=list)
    metadata: dict[str, Any] = field(default_factory=dict)
    created_at: Optional[datetime] = None
    updated_at: Optional[datetime] = None

    @classmethod
    def from_dict(cls, data: dict) -> "Agent":
        """Create an Agent from a dictionary."""
        blocks = [Block.from_dict(b) for b in data.get("blocks", [])]
        return cls(
            id=data["id"],
            name=data["name"],
            agent_type=AgentType(data.get("agent_type", "memgpt_agent")),
            model=data.get("model"),
            system=data.get("system"),
            description=data.get("description"),
            blocks=blocks,
            tool_ids=data.get("tool_ids", []),
            tags=data.get("tags", []),
            metadata=data.get("metadata", {}),
            created_at=datetime.fromisoformat(data["created_at"].replace("Z", "+00:00"))
            if data.get("created_at")
            else None,
            updated_at=datetime.fromisoformat(data["updated_at"].replace("Z", "+00:00"))
            if data.get("updated_at")
            else None,
        )


@dataclass
class ToolCall:
    """Tool call in a message."""
    id: str
    name: str
    arguments: dict[str, Any]

    @classmethod
    def from_dict(cls, data: dict) -> "ToolCall":
        """Create a ToolCall from a dictionary."""
        return cls(
            id=data["id"],
            name=data["name"],
            arguments=data.get("arguments", {}),
        )


@dataclass
class Message:
    """Message in a conversation."""
    id: str
    agent_id: str
    role: MessageRole
    content: str
    tool_call_id: Optional[str] = None
    tool_calls: Optional[list[ToolCall]] = None
    created_at: Optional[datetime] = None

    @classmethod
    def from_dict(cls, data: dict) -> "Message":
        """Create a Message from a dictionary."""
        tool_calls = None
        if data.get("tool_calls"):
            tool_calls = [ToolCall.from_dict(tc) for tc in data["tool_calls"]]
        return cls(
            id=data["id"],
            agent_id=data["agent_id"],
            role=MessageRole(data["role"]),
            content=data["content"],
            tool_call_id=data.get("tool_call_id"),
            tool_calls=tool_calls,
            created_at=datetime.fromisoformat(data["created_at"].replace("Z", "+00:00"))
            if data.get("created_at")
            else None,
        )


@dataclass
class UsageStats:
    """Token usage statistics."""
    prompt_tokens: int
    completion_tokens: int
    total_tokens: int

    @classmethod
    def from_dict(cls, data: dict) -> "UsageStats":
        """Create UsageStats from a dictionary."""
        return cls(
            prompt_tokens=data["prompt_tokens"],
            completion_tokens=data["completion_tokens"],
            total_tokens=data["total_tokens"],
        )


@dataclass
class MessageResponse:
    """Response from sending a message."""
    messages: list[Message]
    usage: Optional[UsageStats] = None

    @classmethod
    def from_dict(cls, data: dict) -> "MessageResponse":
        """Create a MessageResponse from a dictionary."""
        messages = [Message.from_dict(m) for m in data.get("messages", [])]
        usage = UsageStats.from_dict(data["usage"]) if data.get("usage") else None
        return cls(messages=messages, usage=usage)


@dataclass
class ListResponse:
    """Paginated list response."""
    items: list[Any]
    total: int
    cursor: Optional[str] = None
