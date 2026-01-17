#!/bin/bash
# run_all_tests.sh
# Comprehensive Letta compatibility test runner
#
# Usage:
#   ./run_all_tests.sh                    # Run all tests
#   ./run_all_tests.sh --quick            # Run only SDK tests
#   ./run_all_tests.sh --with-openapi     # Include OpenAPI diff (requires Letta server)

set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Options
QUICK_MODE=false
WITH_OPENAPI=false
KELPIE_URL="http://localhost:8283"

# Parse arguments
for arg in "$@"; do
    case $arg in
        --quick)
            QUICK_MODE=true
            shift
            ;;
        --with-openapi)
            WITH_OPENAPI=true
            shift
            ;;
        --kelpie-url=*)
            KELPIE_URL="${arg#*=}"
            shift
            ;;
        --help)
            echo "Usage: $0 [options]"
            echo ""
            echo "Options:"
            echo "  --quick              Run only SDK tests (fastest)"
            echo "  --with-openapi       Include OpenAPI diff (requires Letta server)"
            echo "  --kelpie-url=URL     Kelpie server URL (default: http://localhost:8283)"
            echo "  --help               Show this help message"
            exit 0
            ;;
    esac
done

echo -e "${BLUE}══════════════════════════════════════════════════════════════${NC}"
echo -e "${BLUE}  LETTA COMPATIBILITY TEST SUITE${NC}"
echo -e "${BLUE}══════════════════════════════════════════════════════════════${NC}"
echo ""

# Check if Kelpie server is running
echo -e "${YELLOW}🔍 Checking Kelpie server...${NC}"
if ! curl -s "$KELPIE_URL/health" > /dev/null 2>&1; then
    echo -e "${RED}❌ Kelpie server not running at $KELPIE_URL${NC}"
    echo ""
    echo "Start the server with:"
    echo "  ANTHROPIC_API_KEY=sk-... cargo run -p kelpie-server"
    exit 1
fi
echo -e "${GREEN}✅ Kelpie server is running${NC}"
echo ""

# Check if dependencies are installed
echo -e "${YELLOW}📦 Checking Python dependencies...${NC}"
if ! python3 -c "import letta_client" > /dev/null 2>&1; then
    echo -e "${YELLOW}⚠️  Installing dependencies...${NC}"
    pip install -q -r requirements.txt
fi
echo -e "${GREEN}✅ Dependencies installed${NC}"
echo ""

# Test 1: SDK Integration Tests
echo -e "${BLUE}──────────────────────────────────────────────────────────────${NC}"
echo -e "${BLUE}  Test 1: Letta SDK Integration Tests (Full Coverage)${NC}"
echo -e "${BLUE}──────────────────────────────────────────────────────────────${NC}"
echo ""

SDK_FAILED=false
if pytest sdk_tests_full.py -v --tb=short; then
    echo ""
    echo -e "${GREEN}✅ SDK tests PASSED${NC}"
else
    echo ""
    echo -e "${RED}❌ SDK tests FAILED${NC}"
    SDK_FAILED=true
fi
echo ""

# Quick mode - skip remaining tests
if [ "$QUICK_MODE" = true ]; then
    echo -e "${YELLOW}⏭️  Quick mode enabled - skipping remaining tests${NC}"
    echo ""
    if [ "$SDK_FAILED" = true ]; then
        exit 1
    else
        exit 0
    fi
fi

# Test 2: Coverage Report
echo -e "${BLUE}──────────────────────────────────────────────────────────────${NC}"
echo -e "${BLUE}  Test 2: API Coverage Report${NC}"
echo -e "${BLUE}──────────────────────────────────────────────────────────────${NC}"
echo ""

COVERAGE_FAILED=false
if python3 coverage_report.py --kelpie-url "$KELPIE_URL"; then
    echo ""
    echo -e "${GREEN}✅ Coverage report generated${NC}"
else
    echo ""
    echo -e "${RED}❌ Coverage report failed${NC}"
    COVERAGE_FAILED=true
fi
echo ""

# Test 3: OpenAPI Diff (optional)
if [ "$WITH_OPENAPI" = true ]; then
    echo -e "${BLUE}──────────────────────────────────────────────────────────────${NC}"
    echo -e "${BLUE}  Test 3: OpenAPI Specification Comparison${NC}"
    echo -e "${BLUE}──────────────────────────────────────────────────────────────${NC}"
    echo ""

    echo -e "${YELLOW}🔍 Checking Letta server...${NC}"
    if ! curl -s http://localhost:8080/health > /dev/null 2>&1; then
        echo -e "${RED}❌ Letta server not running at http://localhost:8080${NC}"
        echo ""
        echo "Start the Letta server with:"
        echo "  letta server"
        echo ""
        OPENAPI_FAILED=true
    else
        echo -e "${GREEN}✅ Letta server is running${NC}"
        echo ""

        OPENAPI_FAILED=false
        if python3 openapi_diff.py --letta-url http://localhost:8080 --kelpie-url "$KELPIE_URL"; then
            echo ""
            echo -e "${GREEN}✅ OpenAPI comparison complete${NC}"
        else
            echo ""
            echo -e "${RED}❌ OpenAPI comparison failed${NC}"
            OPENAPI_FAILED=true
        fi
    fi
    echo ""
fi

# Summary
echo -e "${BLUE}══════════════════════════════════════════════════════════════${NC}"
echo -e "${BLUE}  TEST SUMMARY${NC}"
echo -e "${BLUE}══════════════════════════════════════════════════════════════${NC}"
echo ""

TOTAL_TESTS=2
PASSED_TESTS=0
FAILED_TESTS=0

echo "Results:"
if [ "$SDK_FAILED" = false ]; then
    echo -e "  ${GREEN}✅ SDK Integration Tests${NC}"
    PASSED_TESTS=$((PASSED_TESTS + 1))
else
    echo -e "  ${RED}❌ SDK Integration Tests${NC}"
    FAILED_TESTS=$((FAILED_TESTS + 1))
fi

if [ "$COVERAGE_FAILED" = false ]; then
    echo -e "  ${GREEN}✅ Coverage Report${NC}"
    PASSED_TESTS=$((PASSED_TESTS + 1))
else
    echo -e "  ${RED}❌ Coverage Report${NC}"
    FAILED_TESTS=$((FAILED_TESTS + 1))
fi

if [ "$WITH_OPENAPI" = true ]; then
    TOTAL_TESTS=3
    if [ "$OPENAPI_FAILED" = false ]; then
        echo -e "  ${GREEN}✅ OpenAPI Comparison${NC}"
        PASSED_TESTS=$((PASSED_TESTS + 1))
    else
        echo -e "  ${RED}❌ OpenAPI Comparison${NC}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
    fi
fi

echo ""
echo -e "Total: ${PASSED_TESTS}/${TOTAL_TESTS} tests passed"
echo ""

if [ "$FAILED_TESTS" -gt 0 ]; then
    echo -e "${RED}❌ Some tests failed${NC}"
    echo ""
    echo "For more details:"
    echo "  - SDK tests: Review output above"
    echo "  - Coverage: Check which endpoints are missing/broken"
    if [ "$WITH_OPENAPI" = true ]; then
        echo "  - OpenAPI: Review schema differences"
    fi
    echo ""
    exit 1
else
    echo -e "${GREEN}✅ All tests passed!${NC}"
    echo ""
    echo "Kelpie is compatible with Letta SDK ✨"
    echo ""
    exit 0
fi
