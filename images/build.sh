#!/usr/bin/env bash
#
# Build multi-arch VM base images for Kelpie
#
# TigerStyle: Explicit error handling, clear output, reproducible builds

set -euo pipefail

# Constants
readonly ALPINE_VERSION="3.19"
readonly SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly BUILD_DATE="$(date -u +%Y%m%d)"
readonly GIT_SHA="$(git rev-parse --short HEAD 2>/dev/null || echo "unknown")"

# Colors for output
readonly RED='\033[0;31m'
readonly GREEN='\033[0;32m'
readonly YELLOW='\033[1;33m'
readonly NC='\033[0m' # No Color

# Default values
ARCH="${ARCH:-all}"
VERSION="${VERSION:-1.0.0}"
PUSH="${PUSH:-false}"
REGISTRY="${REGISTRY:-}"

# Print usage
usage() {
    cat <<EOF
Usage: $0 [OPTIONS]

Build multi-arch Kelpie base images.

OPTIONS:
    --arch <arch>       Architecture to build (arm64, amd64, all) [default: all]
    --version <ver>     Image version (SemVer format) [default: 1.0.0]
    --push              Push to registry after build [default: false]
    --registry <reg>    Registry to push to [default: none]
    --help              Show this help message

EXAMPLES:
    # Build for current architecture
    ./build.sh --arch \$(uname -m | sed 's/aarch64/arm64/;s/x86_64/amd64/')

    # Build for all architectures
    ./build.sh --arch all

    # Build and push to registry
    ./build.sh --version 1.0.0 --push --registry ghcr.io/kelpie/base

ENVIRONMENT:
    ARCH                Architecture override
    VERSION             Version override
    PUSH                Push flag override
    REGISTRY            Registry override

EOF
    exit 0
}

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --arch)
            ARCH="$2"
            shift 2
            ;;
        --version)
            VERSION="$2"
            shift 2
            ;;
        --push)
            PUSH="true"
            shift
            ;;
        --registry)
            REGISTRY="$2"
            shift 2
            ;;
        --help)
            usage
            ;;
        *)
            echo -e "${RED}Error: Unknown option: $1${NC}" >&2
            usage
            ;;
    esac
done

# Validate version format (SemVer with optional pre-release/metadata)
# Accepts: 1.0.0, 1.0.0-dev, 1.0.0-alpha.1, etc.
if ! [[ "$VERSION" =~ ^[0-9]+\.[0-9]+\.[0-9]+(-[a-zA-Z0-9.-]+)?$ ]]; then
    echo -e "${RED}Error: Invalid version format: $VERSION${NC}" >&2
    echo "Expected SemVer format: MAJOR.MINOR.PATCH[-prerelease]" >&2
    echo "Examples: 1.0.0, 1.0.0-dev, 1.0.0-alpha.1" >&2
    exit 1
fi

# Build full version string with date and git SHA
readonly FULL_VERSION="${VERSION}-${BUILD_DATE}-${GIT_SHA}"

# Print build info
echo -e "${GREEN}Building Kelpie Base Image${NC}"
echo "Version:       $FULL_VERSION"
echo "Alpine:        $ALPINE_VERSION"
echo "Architecture:  $ARCH"
echo "Registry:      ${REGISTRY:-<local only>}"
echo "Push:          $PUSH"
echo ""

# Check if Docker is available
if ! command -v docker &> /dev/null; then
    echo -e "${RED}Error: docker is not installed${NC}" >&2
    exit 1
fi

# Check if buildx is available
if ! docker buildx version &> /dev/null; then
    echo -e "${RED}Error: docker buildx is not available${NC}" >&2
    echo "Install with: docker buildx install" >&2
    exit 1
fi

# Create buildx builder if it doesn't exist
BUILDER_NAME="kelpie-builder"
if ! docker buildx inspect "$BUILDER_NAME" &> /dev/null; then
    echo -e "${YELLOW}Creating buildx builder: $BUILDER_NAME${NC}"
    docker buildx create --name "$BUILDER_NAME" --driver docker-container --bootstrap
fi

# Use the builder
docker buildx use "$BUILDER_NAME"

# Determine platforms to build
case "$ARCH" in
    arm64)
        PLATFORMS="linux/arm64"
        ;;
    amd64)
        PLATFORMS="linux/amd64"
        ;;
    all)
        PLATFORMS="linux/arm64,linux/amd64"
        ;;
    *)
        echo -e "${RED}Error: Unknown architecture: $ARCH${NC}" >&2
        echo "Supported: arm64, amd64, all" >&2
        exit 1
        ;;
esac

# Build image name
if [ -n "$REGISTRY" ]; then
    IMAGE_NAME="${REGISTRY}:${FULL_VERSION}"
    IMAGE_NAME_LATEST="${REGISTRY}:latest"
else
    IMAGE_NAME="kelpie-base:${FULL_VERSION}"
    IMAGE_NAME_LATEST="kelpie-base:latest"
fi

# Build command
BUILD_CMD=(
    docker buildx build
    --platform "$PLATFORMS"
    --build-arg "ALPINE_VERSION=$ALPINE_VERSION"
    --build-arg "VERSION=$FULL_VERSION"
    --build-arg "GIT_SHA=$GIT_SHA"
    --build-arg "BUILD_DATE=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    --tag "$IMAGE_NAME"
    --tag "$IMAGE_NAME_LATEST"
)

# Add push or load flag
if [ "$PUSH" = "true" ]; then
    if [ -z "$REGISTRY" ]; then
        echo -e "${RED}Error: --push requires --registry${NC}" >&2
        exit 1
    fi
    BUILD_CMD+=(--push)
    echo -e "${YELLOW}Building and pushing to registry...${NC}"
else
    # Load into local Docker (only works for single arch)
    if [ "$ARCH" = "all" ]; then
        echo -e "${YELLOW}Warning: Building for multiple architectures without --push${NC}"
        echo "Images will be built but not loaded into local Docker"
    else
        BUILD_CMD+=(--load)
    fi
    echo -e "${YELLOW}Building locally...${NC}"
fi

# Add Dockerfile path
BUILD_CMD+=("$SCRIPT_DIR")

# Run build
echo -e "${GREEN}Running: ${BUILD_CMD[*]}${NC}"
if "${BUILD_CMD[@]}"; then
    echo ""
    echo -e "${GREEN}✓ Build successful!${NC}"
    echo ""
    echo "Image: $IMAGE_NAME"
    echo "Version: $FULL_VERSION"

    if [ "$PUSH" = "false" ] && [ "$ARCH" != "all" ]; then
        echo ""
        echo "To run the image:"
        echo "  docker run --rm -it $IMAGE_NAME"
    fi

    if [ "$PUSH" = "true" ]; then
        echo ""
        echo "Image pushed to: $IMAGE_NAME"
    fi
else
    echo ""
    echo -e "${RED}✗ Build failed${NC}" >&2
    exit 1
fi

# Save metadata
METADATA_FILE="$SCRIPT_DIR/build-metadata.json"
cat > "$METADATA_FILE" <<EOF
{
  "version": "$FULL_VERSION",
  "semver": "$VERSION",
  "build_date": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "git_sha": "$GIT_SHA",
  "alpine_version": "$ALPINE_VERSION",
  "architectures": "${PLATFORMS}",
  "registry": "${REGISTRY:-local}",
  "pushed": $PUSH
}
EOF

echo ""
echo "Metadata saved to: $METADATA_FILE"
