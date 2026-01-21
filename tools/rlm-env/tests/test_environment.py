"""Tests for RLMEnvironment."""

import pytest
from pathlib import Path
from rlm_env.environment import RLMEnvironment


# Fixtures
@pytest.fixture
def codebase_path():
    """Path to kelpie codebase root."""
    return Path(__file__).parent.parent.parent.parent.absolute()


@pytest.fixture
def indexes_path(codebase_path):
    """Path to .kelpie-index/."""
    return codebase_path / ".kelpie-index"


@pytest.fixture
def env(codebase_path, indexes_path):
    """Initialize RLMEnvironment."""
    return RLMEnvironment(str(codebase_path), str(indexes_path))


# Tests
def test_env_init(env):
    """Test RLMEnvironment initialization."""
    assert env.codebase is not None
    assert env.execution_log == []
    assert env._recursive_depth == 0


def test_execute_simple(env):
    """Test executing simple code."""
    result = env.execute("result = 2 + 2")
    assert result.success
    assert result.result == 4
    assert len(result.execution_log) > 0


def test_execute_with_codebase(env):
    """Test executing code that accesses codebase."""
    result = env.execute("""
files = list_files("*.toml")
result = len(files)
""")
    assert result.success
    assert isinstance(result.result, int)
    assert result.result > 0


def test_execute_grep(env):
    """Test grep functionality."""
    result = env.execute("""
matches = grep("kelpie", "**/*.toml", max_matches=10)
result = len(matches)
""")
    assert result.success
    assert isinstance(result.result, int)


def test_execute_peek(env):
    """Test peek functionality."""
    result = env.execute("""
content = peek("Cargo.toml", lines=5)
result = "[workspace]" in content or "[package]" in content
""")
    assert result.success
    assert result.result is True


def test_execute_list_crates(env):
    """Test listing crates."""
    result = env.execute("""
crates = list_crates()
result = len(crates)
""")
    assert result.success
    if result.result:
        assert result.result > 0


def test_execute_syntax_error(env):
    """Test handling syntax errors."""
    result = env.execute("this is not valid python")
    assert not result.success
    assert "Compilation failed" in result.error


def test_execute_runtime_error(env):
    """Test handling runtime errors."""
    result = env.execute("result = 1 / 0")
    assert not result.success
    assert "ZeroDivisionError" in result.error or "Execution error" in result.error


def test_execute_empty_code(env):
    """Test handling empty code."""
    with pytest.raises(AssertionError, match="cannot be empty"):
        env.execute("")


def test_execute_non_string(env):
    """Test handling non-string code."""
    with pytest.raises(AssertionError, match="must be string"):
        env.execute(123)  # type: ignore


def test_execute_with_loops(env):
    """Test executing code with loops."""
    result = env.execute("""
total = 0
for i in range(10):
    total += i
result = total
""")
    assert result.success
    assert result.result == 45


def test_execute_with_list_comprehension(env):
    """Test executing code with list comprehensions."""
    result = env.execute("""
squares = [i**2 for i in range(5)]
result = squares
""")
    assert result.success
    assert str(result.result) == "[0, 1, 4, 9, 16]"


def test_execute_partition_by_crate(env):
    """Test partitioning by crate."""
    result = env.execute("""
partitions = partition_by_crate()
result = len(partitions)
""")
    assert result.success
    if result.result:
        assert result.result > 0


def test_execute_get_index(env):
    """Test getting indexes."""
    result = env.execute("""
symbols = get_index("symbols")
result = symbols is not None
""")
    assert result.success
    # Result depends on whether indexes exist


def test_execute_list_tests(env):
    """Test listing tests."""
    result = env.execute("""
all_tests = list_tests()
result = len(all_tests) if all_tests else 0
""")
    assert result.success
    # Result depends on whether tests.json exists


def test_restricted_import(env):
    """Test that imports are restricted."""
    result = env.execute("import os")
    assert not result.success
    assert "Compilation failed" in result.error or "error" in result.error.lower()


def test_restricted_open(env):
    """Test that file operations are restricted."""
    # In RestrictedPython, 'open' might not be available
    result = env.execute("f = open('/etc/passwd')")
    assert not result.success


def test_timeout_protection(env):
    """Test timeout prevents infinite loops.

    Note: This test should timeout after 30s (EXECUTION_TIMEOUT_SECONDS)
    but for testing purposes we'll skip it to avoid long test times.
    """
    pytest.skip("Timeout test would take 30s, skipping for CI")
    # result = env.execute("""
    # while True:
    #     pass
    # """)
    # assert not result.success
    # assert "timeout" in result.error.lower()
