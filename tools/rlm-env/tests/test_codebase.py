"""Tests for CodebaseContext."""

import pytest
from pathlib import Path
from rlm_env.codebase import CodebaseContext


# Fixtures
@pytest.fixture
def codebase_path():
    """Path to kelpie codebase root."""
    # Assuming tests run from tools/rlm-env/
    return Path(__file__).parent.parent.parent.parent.absolute()


@pytest.fixture
def indexes_path(codebase_path):
    """Path to .kelpie-index/."""
    return codebase_path / ".kelpie-index"


@pytest.fixture
def codebase(codebase_path, indexes_path):
    """Initialize CodebaseContext."""
    return CodebaseContext(str(codebase_path), str(indexes_path))


# Tests
def test_codebase_init(codebase):
    """Test CodebaseContext initialization."""
    assert codebase.root.exists()
    assert codebase.indexes_path.exists()
    assert isinstance(codebase.indexes, dict)


def test_list_files(codebase):
    """Test listing files."""
    rust_files = codebase.list_files("**/*.rs")
    assert len(rust_files) > 0
    assert all(f.endswith(".rs") for f in rust_files)

    # Check specific known files exist
    assert any("Cargo.toml" in f for f in codebase.list_files("**/Cargo.toml"))


def test_list_crates(codebase):
    """Test listing crates."""
    crates = codebase.list_crates()
    assert len(crates) > 0
    # Should have kelpie crates
    assert any("kelpie" in c for c in crates)


def test_list_modules(codebase):
    """Test listing modules."""
    modules = codebase.list_modules()
    assert len(modules) > 0
    # Module paths should have :: separator
    assert any("::" in m for m in modules)


def test_peek(codebase, codebase_path):
    """Test peeking at file."""
    # Peek at Cargo.toml
    content = codebase.peek("Cargo.toml", lines=10)
    assert "[workspace]" in content or "[package]" in content


def test_peek_bounds(codebase):
    """Test peek respects line limits."""
    # Test max limit enforcement
    with pytest.raises(AssertionError, match="exceeds maximum"):
        codebase.peek("Cargo.toml", lines=1000)

    # Test positive limit
    with pytest.raises(AssertionError, match="must be positive"):
        codebase.peek("Cargo.toml", lines=0)


def test_grep(codebase):
    """Test grep functionality."""
    # Search for "kelpie" in Cargo files
    matches = codebase.grep("kelpie", "**/*.toml")
    assert len(matches) > 0

    # Check match structure
    match = matches[0]
    assert hasattr(match, "file")
    assert hasattr(match, "line")
    assert hasattr(match, "content")
    assert match.line > 0


def test_grep_bounds(codebase):
    """Test grep respects limits."""
    # Test max matches
    with pytest.raises(AssertionError, match="exceeds maximum"):
        codebase.grep("fn", max_matches=2000)

    # Test positive limit
    with pytest.raises(AssertionError, match="must be positive"):
        codebase.grep("fn", max_matches=0)


def test_grep_invalid_regex(codebase):
    """Test grep with invalid regex."""
    matches = codebase.grep("[invalid(", "**/*.rs")
    assert len(matches) == 1
    assert "Invalid regex" in matches[0].content


def test_read_section(codebase):
    """Test reading file sections."""
    content = codebase.read_section("Cargo.toml", start=1, end=5)
    assert len(content) > 0
    # Should have at most 5 lines
    assert content.count("\n") <= 5


def test_read_section_bounds(codebase):
    """Test read_section validates bounds."""
    # Start must be positive
    with pytest.raises(AssertionError, match="must be positive"):
        codebase.read_section("Cargo.toml", start=0, end=10)

    # End must be >= start
    with pytest.raises(AssertionError, match="must be >= start"):
        codebase.read_section("Cargo.toml", start=10, end=5)

    # Section size limit
    with pytest.raises(AssertionError, match="exceeds maximum"):
        codebase.read_section("Cargo.toml", start=1, end=1000)


def test_read_context(codebase):
    """Test reading context around a line."""
    content = codebase.read_context("Cargo.toml", line=5, padding=3)
    assert len(content) > 0


def test_read_context_bounds(codebase):
    """Test read_context validates bounds."""
    # Padding must be non-negative
    with pytest.raises(AssertionError, match="must be non-negative"):
        codebase.read_context("Cargo.toml", line=5, padding=-1)

    # Padding limit
    with pytest.raises(AssertionError, match="exceeds maximum"):
        codebase.read_context("Cargo.toml", line=5, padding=100)


def test_get_module(codebase):
    """Test getting module context."""
    modules = codebase.list_modules()
    if modules:
        module_ctx = codebase.get_module(modules[0])
        assert module_ctx is not None
        assert module_ctx.module_name == modules[0]
        assert len(module_ctx.files) > 0


def test_partition_by_crate(codebase):
    """Test partitioning by crate."""
    partitions = codebase.partition_by_crate()
    assert len(partitions) > 0

    # Each partition should have files
    for partition in partitions:
        assert partition.module_name
        assert len(partition.files) > 0


def test_get_index(codebase):
    """Test getting specific indexes."""
    # Test existing indexes
    symbols = codebase.get_index("symbols")
    if symbols:
        assert "files" in symbols or "version" in symbols

    tests = codebase.get_index("tests")
    if tests:
        assert "tests" in tests or "version" in tests

    # Test non-existent index
    fake = codebase.get_index("nonexistent")
    assert fake is None


def test_list_tests(codebase):
    """Test listing tests."""
    all_tests = codebase.list_tests()
    # May be empty if tests.json not generated yet
    if all_tests:
        # Check test structure
        test = all_tests[0]
        assert "name" in test
        assert "file" in test
        assert "type" in test

    # Test filtering by topic
    storage_tests = codebase.list_tests(topic="storage")
    # If there are storage tests, they should all have "storage" in topics
    if storage_tests:
        assert all("storage" in t.get("topics", []) for t in storage_tests)

    # Test filtering by type
    dst_tests = codebase.list_tests(test_type="dst")
    if dst_tests:
        assert all(t.get("type") == "dst" for t in dst_tests)
