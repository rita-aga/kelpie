#!/bin/bash
set -e

# DST Verification Script
# Runs the DST suite twice with the same seed and ensures identical output.

SEED=${1:-12345}
LOG_DIR="target/dst_check"
mkdir -p $LOG_DIR

echo "Running DST Check with SEED=$SEED..."

# Run 1
echo "Pass 1..."
DST_SEED=$SEED cargo test -p kelpie-dst --test "*" -- --nocapture > $LOG_DIR/run1.log 2>&1

# Run 2
echo "Pass 2..."
DST_SEED=$SEED cargo test -p kelpie-dst --test "*" -- --nocapture > $LOG_DIR/run2.log 2>&1

# Compare - filter out timestamps or non-deterministic build artifacts if necessary
# For now, we expect exact matches for "DST" code.
DIFF=$(diff $LOG_DIR/run1.log $LOG_DIR/run2.log)

if [ -z "$DIFF" ]; then
    echo "✅ DST Verification Passed: Runs are identical."
    rm -rf $LOG_DIR
    exit 0
else
    echo "❌ DST Verification Failed: Runs differ."
    echo "Diff written to $LOG_DIR/diff.log"
    echo "$DIFF" > $LOG_DIR/diff.log
    exit 1
fi
