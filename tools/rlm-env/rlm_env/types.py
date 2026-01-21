"""Types for RLM environment."""

from dataclasses import dataclass
from typing import List, Dict, Any, Optional


@dataclass
class GrepMatch:
    """A single grep match result."""

    file: str
    line: int
    content: str

    def __repr__(self) -> str:
        return f"GrepMatch({self.file}:{self.line}: {self.content[:50]}...)"


@dataclass
class ModuleContext:
    """Context for a single module, used for partitioning."""

    module_name: str
    files: List[str]
    root_path: str

    def __repr__(self) -> str:
        return f"ModuleContext({self.module_name}, {len(self.files)} files)"


@dataclass
class ExecutionResult:
    """Result of RLM code execution."""

    success: bool
    result: Optional[Any] = None
    error: Optional[str] = None
    execution_log: Optional[List[str]] = None

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON serialization."""
        return {
            "success": self.success,
            "result": str(self.result) if self.result is not None else None,
            "error": self.error,
            "execution_log": self.execution_log or [],
        }
