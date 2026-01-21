#!/bin/bash
# Install Kelpie Git Hooks
#
# This script installs the pre-commit hook that enforces hard controls.
# Run this after cloning the repository.

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HOOK_SOURCE="$REPO_ROOT/tools/hooks/pre-commit"
HOOK_DEST="$REPO_ROOT/.git/hooks/pre-commit"

echo "🔧 Installing Kelpie Git Hooks..."
echo ""

# Check if git directory exists
if [ ! -d "$REPO_ROOT/.git" ]; then
    echo "❌ Error: .git directory not found"
    echo "Are you in a git repository?"
    exit 1
fi

# Check if hook source exists
if [ ! -f "$HOOK_SOURCE" ]; then
    echo "❌ Error: Hook source not found at $HOOK_SOURCE"
    exit 1
fi

# Backup existing hook if present
if [ -f "$HOOK_DEST" ]; then
    echo "⚠️  Existing pre-commit hook found, backing up..."
    cp "$HOOK_DEST" "$HOOK_DEST.backup.$(date +%s)"
fi

# Copy hook
cp "$HOOK_SOURCE" "$HOOK_DEST"
chmod +x "$HOOK_DEST"

echo "✅ Pre-commit hook installed at $HOOK_DEST"
echo ""
echo "The hook will run:"
echo "  1. Constraint checks (from .kelpie-index/constraints/)"
echo "  2. cargo fmt --check"
echo "  3. cargo clippy (with warnings as errors)"
echo "  4. cargo test (full suite)"
echo ""
echo "Every commit will be verified to ensure working code."
echo ""
echo "To test the hook:"
echo "  git commit --allow-empty -m 'test hook'"
echo ""
