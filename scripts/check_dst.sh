#!/bin/bash
set -e

# DST Verification Script
# Runs the DST suite twice with the same seed and ensures identical output.

SEED=${1:-12345}
LOG_DIR="target/dst_check"
mkdir -p $LOG_DIR

echo "Running DST Check with SEED=$SEED..."

# Function to run tests and compare
run_check() {
    local package=$1
    local features=$2
    local name=$3

    echo "Checking $name ($package)..."
    
    # Run 1
    echo "  Pass 1..."
    DST_SEED=$SEED cargo test -p $package --features "$features" --test "*" -- --nocapture > $LOG_DIR/${name}_run1.log 2>&1

    # Run 2
    echo "  Pass 2..."
    DST_SEED=$SEED cargo test -p $package --features "$features" --test "*" -- --nocapture > $LOG_DIR/${name}_run2.log 2>&1

    # Compare - filter out timestamps or non-deterministic build artifacts if necessary
    # Note: madsim output is deterministic, so we expect exact matches.
    DIFF=$(diff $LOG_DIR/${name}_run1.log $LOG_DIR/${name}_run2.log)

    if [ -z "$DIFF" ]; then
        echo "  ✅ $name Verification Passed: Runs are identical."
    else
        echo "  ❌ $name Verification Failed: Runs differ."
        echo "Diff written to $LOG_DIR/${name}_diff.log"
        echo "$DIFF" > $LOG_DIR/${name}_diff.log
        return 1
    fi
}

# Check kelpie-dst (Core DST framework)
# kelpie-dst uses madsim by default in its internal tests
run_check "kelpie-dst" "" "kelpie-dst"

# Check kelpie-server (Application DST tests)
# Requires 'dst' and 'madsim' features to be deterministic
run_check "kelpie-server" "dst,madsim" "kelpie-server"

echo "🎉 All DST checks passed!"
rm -rf $LOG_DIR
exit 0
