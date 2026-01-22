"""
Sub-LLM integration for RLM environment.

VDE insight: Sub-models can analyze loaded variables server-side without
using the primary model's context window. This enables cost-efficient
analysis using Haiku for routine queries while preserving Opus for reasoning.

Tools exposed:
- repl_sub_llm: Have sub-model analyze a variable IN THE SERVER
"""

import os
from typing import Any

from anthropic import Anthropic

from .types import LoadedVariable, SubLLMResult

# TigerStyle: Explicit constants
DEFAULT_MODEL = "claude-3-haiku-20240307"  # Cost-efficient for analysis
DEFAULT_MAX_TOKENS = 4096
MAX_CONTEXT_CHARS = 100_000  # ~25K tokens for context


class SubLLM:
    """Sub-LLM caller for analyzing loaded variables.

    VDE insight: The sub-model analyzes variables server-side, not in the
    primary model's context. This enables:
    1. Cost efficiency (Haiku vs Opus)
    2. Parallel analysis of multiple partitions
    3. Specialized prompts for different analysis tasks
    """

    def __init__(self, api_key: str | None = None, default_model: str = DEFAULT_MODEL):
        """Initialize SubLLM client.

        Args:
            api_key: Anthropic API key (defaults to ANTHROPIC_API_KEY env var)
            default_model: Default model for sub-LLM calls
        """
        self.api_key = api_key or os.environ.get("ANTHROPIC_API_KEY")
        self.default_model = default_model
        self._client: Anthropic | None = None

    def _get_client(self) -> Anthropic:
        """Get or create Anthropic client."""
        if self._client is None:
            if not self.api_key:
                raise ValueError("ANTHROPIC_API_KEY not set and no API key provided")
            self._client = Anthropic(api_key=self.api_key)
        return self._client

    async def analyze_variable(
        self,
        variable: LoadedVariable,
        query: str,
        model: str | None = None,
        max_tokens: int = DEFAULT_MAX_TOKENS,
    ) -> SubLLMResult:
        """Have a sub-LLM analyze a loaded variable.

        Args:
            variable: LoadedVariable to analyze
            query: Question to ask about the variable
            model: Model to use (defaults to Haiku)
            max_tokens: Maximum response tokens

        Returns:
            SubLLMResult with response

        VDE pattern: The variable content becomes the context for the sub-LLM,
        which can be much larger than what fits in the primary model's context.
        """
        model = model or self.default_model

        # Build context from variable files
        context_parts = []
        total_chars = 0

        for path, content in variable.files.items():
            # Check if adding this file would exceed limit
            file_content = f"=== {path} ===\n{content}\n"
            if total_chars + len(file_content) > MAX_CONTEXT_CHARS:
                context_parts.append(f"\n[Truncated: {len(variable.files) - len(context_parts)} more files]")
                break
            context_parts.append(file_content)
            total_chars += len(file_content)

        context = "\n".join(context_parts)

        # Build prompt
        system_prompt = f"""You are analyzing code files loaded into a variable named '{variable.name}'.
The variable contains {variable.file_count} files ({variable.total_bytes / 1024:.1f}KB) matching pattern: {variable.glob_pattern}

Your task is to answer questions about this code. Be specific and reference file names and line numbers when relevant.
Keep your response focused and concise."""

        user_message = f"""Here are the files:

{context}

Question: {query}"""

        try:
            client = self._get_client()

            # Synchronous call (wrapped in async for consistency)
            response = client.messages.create(
                model=model,
                max_tokens=max_tokens,
                system=system_prompt,
                messages=[{"role": "user", "content": user_message}],
            )

            # Extract response text
            response_text = ""
            for block in response.content:
                if hasattr(block, "text"):
                    response_text += block.text

            return SubLLMResult(
                success=True,
                response=response_text,
                model=model,
                input_tokens=response.usage.input_tokens,
                output_tokens=response.usage.output_tokens,
            )

        except Exception as e:
            return SubLLMResult(
                success=False,
                error=f"Sub-LLM call failed: {type(e).__name__}: {e}",
                model=model,
            )

    async def analyze_content(
        self,
        content: str,
        query: str,
        context_name: str = "content",
        model: str | None = None,
        max_tokens: int = DEFAULT_MAX_TOKENS,
    ) -> SubLLMResult:
        """Have a sub-LLM analyze arbitrary content.

        Args:
            content: Content to analyze
            query: Question to ask
            context_name: Name for the content (for prompt)
            model: Model to use (defaults to Haiku)
            max_tokens: Maximum response tokens

        Returns:
            SubLLMResult with response
        """
        model = model or self.default_model

        # Truncate if needed
        if len(content) > MAX_CONTEXT_CHARS:
            content = content[:MAX_CONTEXT_CHARS] + f"\n\n[Truncated: {len(content) - MAX_CONTEXT_CHARS} more chars]"

        system_prompt = f"""You are analyzing {context_name}. Be specific and concise in your response."""

        user_message = f"""Here is the content:

{content}

Question: {query}"""

        try:
            client = self._get_client()

            response = client.messages.create(
                model=model,
                max_tokens=max_tokens,
                system=system_prompt,
                messages=[{"role": "user", "content": user_message}],
            )

            response_text = ""
            for block in response.content:
                if hasattr(block, "text"):
                    response_text += block.text

            return SubLLMResult(
                success=True,
                response=response_text,
                model=model,
                input_tokens=response.usage.input_tokens,
                output_tokens=response.usage.output_tokens,
            )

        except Exception as e:
            return SubLLMResult(
                success=False,
                error=f"Sub-LLM call failed: {type(e).__name__}: {e}",
                model=model,
            )

    def analyze_variable_sync(
        self,
        variable: LoadedVariable,
        query: str,
        model: str | None = None,
        max_tokens: int = DEFAULT_MAX_TOKENS,
    ) -> SubLLMResult:
        """Synchronous version of analyze_variable.

        For use in contexts where async is not available.
        """
        import asyncio

        return asyncio.get_event_loop().run_until_complete(
            self.analyze_variable(variable, query, model, max_tokens)
        )
