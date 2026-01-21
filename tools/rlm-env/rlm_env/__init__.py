"""RLM Environment - Recursive Language Model execution environment for Kelpie.

This package provides a sandboxed Python REPL environment where agents can write
code to interact with the codebase without loading it into LLM context.

Key components:
- CodebaseContext: Programmatic codebase access (grep, peek, read_section)
- RLMEnvironment: Sandboxed execution with RestrictedPython
- CLI: Interface for MCP server to invoke via subprocess
"""

__version__ = "0.1.0"

from .types import GrepMatch, ModuleContext
from .codebase import CodebaseContext
from .environment import RLMEnvironment

__all__ = [
    "CodebaseContext",
    "RLMEnvironment",
    "GrepMatch",
    "ModuleContext",
]
