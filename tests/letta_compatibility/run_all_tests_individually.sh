#!/bin/bash
# Run each Letta SDK test individually with timeout
# Save results to individual files

set -e

VENV="/Users/seshendranalla/Development/kelpie/tests/letta_compatibility/.venv"
LETTA_DIR="/Users/seshendranalla/Development/letta"
export LETTA_SERVER_URL="http://localhost:8283"
TIMEOUT_SECONDS=10
RESULTS_DIR="./test_results_individual"

# Create results directory
mkdir -p "$RESULTS_DIR"
rm -f "$RESULTS_DIR"/*.txt 2>/dev/null || true

# Color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo "================================================"
echo "Running All Letta SDK Tests Individually"
echo "================================================"
echo "Server: $LETTA_SERVER_URL"
echo "Timeout: ${TIMEOUT_SECONDS}s per test"
echo "Results: $RESULTS_DIR/"
echo ""

# Get all test functions
cd "$LETTA_DIR"
TEST_FUNCTIONS=$($VENV/bin/pytest tests/sdk/ --collect-only -q 2>/dev/null | grep "::" | grep -v "^=" || true)

TOTAL=0
PASSED=0
FAILED=0
TIMEOUT=0
ERROR=0
SKIPPED=0

# Function to run a single test with timeout
run_test() {
    local test_path="$1"
    local test_name=$(echo "$test_path" | sed 's/.*:://' | sed 's/\[.*\]//')
    local safe_name=$(echo "$test_path" | tr '/:[]' '_' | tr -d ' ')
    local result_file="$RESULTS_DIR/${safe_name}.txt"

    TOTAL=$((TOTAL + 1))

    printf "[$TOTAL] Testing: %-60s " "$test_name"

    # Run test with timeout
    if timeout $TIMEOUT_SECONDS $VENV/bin/pytest "$test_path" -v --tb=short > "$result_file" 2>&1; then
        if grep -q "PASSED" "$result_file"; then
            echo -e "${GREEN}✅ PASS${NC}"
            PASSED=$((PASSED + 1))
            echo "PASSED" > "${result_file}.status"
        elif grep -q "SKIPPED" "$result_file"; then
            echo -e "${YELLOW}⏭️  SKIP${NC}"
            SKIPPED=$((SKIPPED + 1))
            echo "SKIPPED" > "${result_file}.status"
        else
            echo -e "${YELLOW}? UNKNOWN${NC}"
            echo "UNKNOWN" > "${result_file}.status"
        fi
    elif [ $? -eq 124 ]; then
        echo -e "${YELLOW}⏱️  TIMEOUT${NC}"
        TIMEOUT=$((TIMEOUT + 1))
        echo "TIMEOUT (>${TIMEOUT_SECONDS}s)" > "$result_file"
        echo "TIMEOUT" > "${result_file}.status"
    else
        if grep -q "FAILED" "$result_file" 2>/dev/null; then
            echo -e "${RED}❌ FAIL${NC}"
            FAILED=$((FAILED + 1))
            echo "FAILED" > "${result_file}.status"
        elif grep -q "ERROR" "$result_file" 2>/dev/null; then
            echo -e "${RED}💥 ERROR${NC}"
            ERROR=$((ERROR + 1))
            echo "ERROR" > "${result_file}.status"
        else
            echo -e "${RED}❌ FAIL${NC}"
            FAILED=$((FAILED + 1))
            echo "FAILED" > "${result_file}.status"
        fi
    fi
}

# Process each test
while IFS= read -r test; do
    [ -z "$test" ] && continue
    run_test "$test"
done <<< "$TEST_FUNCTIONS"

# Generate summary
echo ""
echo "================================================"
echo "SUMMARY"
echo "================================================"
echo -e "Total:   $TOTAL tests"
echo -e "${GREEN}Passed:  $PASSED${NC}"
echo -e "${RED}Failed:  $FAILED${NC}"
echo -e "${RED}Errors:  $ERROR${NC}"
echo -e "${YELLOW}Timeout: $TIMEOUT${NC}"
echo -e "${YELLOW}Skipped: $SKIPPED${NC}"
echo ""
echo "Pass rate: $(awk "BEGIN {printf \"%.1f\", ($PASSED/$TOTAL)*100}")%"
echo ""
echo "Results saved to: $RESULTS_DIR/"
echo ""

# Generate detailed report
REPORT_FILE="$RESULTS_DIR/SUMMARY.txt"
cat > "$REPORT_FILE" <<EOF
Letta SDK Test Results (Individual Test Run)
=============================================

Date: $(date)
Server: $LETTA_SERVER_URL
Timeout: ${TIMEOUT_SECONDS}s per test

SUMMARY
-------
Total:   $TOTAL
Passed:  $PASSED ($(awk "BEGIN {printf \"%.1f\", ($PASSED/$TOTAL)*100}")%)
Failed:  $FAILED ($(awk "BEGIN {printf \"%.1f\", ($FAILED/$TOTAL)*100}")%)
Errors:  $ERROR ($(awk "BEGIN {printf \"%.1f\", ($ERROR/$TOTAL)*100}")%)
Timeout: $TIMEOUT ($(awk "BEGIN {printf \"%.1f\", ($TIMEOUT/$TOTAL)*100}")%)
Skipped: $SKIPPED ($(awk "BEGIN {printf \"%.1f\", ($SKIPPED/$TOTAL)*100}")%)

DETAILED RESULTS
----------------

EOF

# Add details for each status
for status in PASSED FAILED ERROR TIMEOUT SKIPPED; do
    echo "$status TESTS:" >> "$REPORT_FILE"
    echo "-------------" >> "$REPORT_FILE"
    find "$RESULTS_DIR" -name "*.status" -exec grep -l "^$status$" {} \; | while read f; do
        test_name=$(basename "$f" .status)
        echo "  - $test_name" >> "$REPORT_FILE"
    done
    echo "" >> "$REPORT_FILE"
done

echo "Summary report: $REPORT_FILE"
