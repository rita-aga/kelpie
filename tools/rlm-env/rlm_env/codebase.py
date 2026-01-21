"""Codebase access layer for RLM environment.

Provides programmatic access to the codebase without loading it into LLM context.
All operations are read-only and work with the structural indexes.
"""

import json
import re
from pathlib import Path
from typing import List, Dict, Any, Optional

from .types import GrepMatch, ModuleContext


class CodebaseContext:
    """Codebase access layer - never loads full content into LLM context.

    TigerStyle: All methods are read-only. No mutation of codebase allowed.
    """

    def __init__(self, root_path: str, indexes_path: str):
        """Initialize codebase context.

        Args:
            root_path: Path to codebase root
            indexes_path: Path to .kelpie-index/ directory
        """
        self.root = Path(root_path)
        self.indexes_path = Path(indexes_path)

        # TigerStyle: Validate paths exist
        assert self.root.exists(), f"Codebase root not found: {root_path}"
        assert self.indexes_path.exists(), f"Indexes not found: {indexes_path}"

        # Load structural indexes
        self.indexes = self._load_indexes()

    def _load_indexes(self) -> Dict[str, Any]:
        """Load all structural indexes into memory."""
        indexes = {}

        structural_dir = self.indexes_path / "structural"
        if structural_dir.exists():
            for index_file in structural_dir.glob("*.json"):
                index_name = index_file.stem
                with open(index_file) as f:
                    indexes[index_name] = json.load(f)

        return indexes

    def list_files(self, glob_pattern: str = "**/*.rs") -> List[str]:
        """List files matching glob pattern.

        Args:
            glob_pattern: Glob pattern (default: all Rust files)

        Returns:
            List of file paths relative to root
        """
        return [
            str(p.relative_to(self.root))
            for p in self.root.glob(glob_pattern)
            if p.is_file()
        ]

    def list_crates(self) -> List[str]:
        """List all crates in the workspace.

        Returns:
            List of crate names from modules index
        """
        if "modules" not in self.indexes:
            return []

        return [crate["name"] for crate in self.indexes["modules"].get("crates", [])]

    def list_modules(self, crate_name: Optional[str] = None) -> List[str]:
        """List all modules, optionally filtered by crate.

        Args:
            crate_name: If provided, only list modules from this crate

        Returns:
            List of module paths (e.g., "kelpie_core::actor")
        """
        if "modules" not in self.indexes:
            return []

        modules = []
        for crate in self.indexes["modules"].get("crates", []):
            if crate_name and crate["name"] != crate_name:
                continue

            for module in crate.get("modules", []):
                modules.append(module["path"])

        return modules

    def peek(self, file: str, lines: int = 50) -> str:
        """Sample first N lines of a file (for structure understanding).

        Args:
            file: File path relative to root
            lines: Number of lines to read (default: 50)

        Returns:
            First N lines of file

        TigerStyle: Explicit line limit to prevent accidental full file loads
        """
        assert lines > 0, "lines must be positive"
        assert lines <= 500, "lines exceeds maximum (500)"

        path = self.root / file
        if not path.exists():
            return f"File not found: {file}"

        try:
            with open(path) as f:
                return "".join(f.readline() for _ in range(lines))
        except Exception as e:
            return f"Error reading file: {e}"

    def grep(
        self, pattern: str, glob: str = "**/*.rs", max_matches: int = 100
    ) -> List[GrepMatch]:
        """Search for pattern without loading files into context.

        Args:
            pattern: Regular expression pattern
            glob: Glob pattern for files to search (default: all Rust files)
            max_matches: Maximum matches to return (default: 100)

        Returns:
            List of GrepMatch objects

        TigerStyle: Explicit max_matches to prevent unbounded memory use
        """
        assert max_matches > 0, "max_matches must be positive"
        assert max_matches <= 1000, "max_matches exceeds maximum (1000)"

        matches = []
        try:
            regex = re.compile(pattern)
        except re.error as e:
            return [GrepMatch("error", 0, f"Invalid regex: {e}")]

        for file in self.list_files(glob):
            if len(matches) >= max_matches:
                break

            path = self.root / file
            try:
                with open(path) as f:
                    for i, line in enumerate(f, 1):
                        if regex.search(line):
                            matches.append(GrepMatch(file, i, line.rstrip()))
                            if len(matches) >= max_matches:
                                break
            except Exception:
                # Skip files that can't be read
                continue

        return matches

    def read_section(self, file: str, start: int, end: int) -> str:
        """Read specific line range from file.

        Args:
            file: File path relative to root
            start: Start line (1-indexed, inclusive)
            end: End line (1-indexed, inclusive)

        Returns:
            Lines from start to end

        TigerStyle: Explicit bounds to prevent accidental full file loads
        """
        assert start > 0, "start must be positive"
        assert end >= start, "end must be >= start"
        assert (end - start) <= 500, "section size exceeds maximum (500 lines)"

        path = self.root / file
        if not path.exists():
            return f"File not found: {file}"

        try:
            with open(path) as f:
                lines = f.readlines()
                # TigerStyle: Validate bounds
                if start > len(lines):
                    return f"Start line {start} exceeds file length {len(lines)}"
                return "".join(lines[start - 1 : end])
        except Exception as e:
            return f"Error reading file: {e}"

    def read_context(self, file: str, line: int, padding: int = 10) -> str:
        """Read context around a specific line.

        Args:
            file: File path relative to root
            line: Target line number (1-indexed)
            padding: Lines before and after to include (default: 10)

        Returns:
            Context around the line
        """
        assert padding >= 0, "padding must be non-negative"
        assert padding <= 50, "padding exceeds maximum (50)"

        start = max(1, line - padding)
        end = line + padding
        return self.read_section(file, start, end)

    def get_module(self, module_path: str) -> Optional[ModuleContext]:
        """Get focused context for a single module.

        Args:
            module_path: Module path (e.g., "kelpie_core::actor")

        Returns:
            ModuleContext or None if not found
        """
        if "modules" not in self.indexes:
            return None

        for crate in self.indexes["modules"].get("crates", []):
            for module in crate.get("modules", []):
                if module["path"] == module_path:
                    return ModuleContext(
                        module_name=module_path,
                        files=[module["file"]],
                        root_path=str(self.root),
                    )

        return None

    def partition_by_crate(self) -> List[ModuleContext]:
        """Partition codebase by crate for map-reduce operations.

        Returns:
            List of ModuleContext objects, one per crate
        """
        if "modules" not in self.indexes:
            return []

        contexts = []
        for crate in self.indexes["modules"].get("crates", []):
            files = []
            for module in crate.get("modules", []):
                files.append(module["file"])

            if files:
                contexts.append(
                    ModuleContext(
                        module_name=crate["name"],
                        files=files,
                        root_path=str(self.root),
                    )
                )

        return contexts

    def get_index(self, index_name: str) -> Optional[Dict[str, Any]]:
        """Get a specific index by name.

        Args:
            index_name: Index name (e.g., "symbols", "dependencies", "tests", "modules")

        Returns:
            Index data or None if not found
        """
        return self.indexes.get(index_name)

    def list_tests(self, topic: Optional[str] = None, test_type: Optional[str] = None) -> List[Dict[str, Any]]:
        """List tests, optionally filtered by topic or type.

        Args:
            topic: Filter by topic (e.g., "storage", "actor")
            test_type: Filter by type (e.g., "unit", "dst", "integration")

        Returns:
            List of test info dictionaries
        """
        if "tests" not in self.indexes:
            return []

        tests = self.indexes["tests"].get("tests", [])

        if topic:
            # Filter tests that have this topic
            tests = [t for t in tests if topic in t.get("topics", [])]

        if test_type:
            # Filter tests by type
            tests = [t for t in tests if t.get("type") == test_type]

        return tests
