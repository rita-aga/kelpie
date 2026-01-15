# Kelpie Base Images

This directory contains the build system for Kelpie's multi-architecture VM base images.

## Overview

Kelpie uses lightweight Alpine Linux-based VM images for sandboxed code execution. These images:

- Boot in <1 second
- Are ~50MB in size (compressed)
- Support ARM64 and x86_64 architectures
- Include a guest agent for host-VM communication
- Enable teleportation between machines

## Quick Start

### Build Locally

```bash
# Build for current architecture
cd images
./build.sh --arch $(uname -m | sed 's/aarch64/arm64/;s/x86_64/amd64/')

# Build for all architectures (requires Docker buildx)
./build.sh --arch all
```

### Use Pre-built Images

Kelpie automatically downloads and caches images on first use:

```bash
# Images are cached in ~/.kelpie/images/
kelpie images list
kelpie images download 1.0.0-20260115-abc1234
```

## Image Structure

```
kelpie-base:1.0.0-20260115-abc1234
├── /etc/kelpie-version          # Version string
├── /etc/kelpie-git-sha          # Build commit SHA
├── /etc/kelpie-build-date       # Build timestamp
├── /usr/local/bin/kelpie-guest  # Guest agent (Phase 5.2)
├── /sbin/init                   # Init system (Phase 5.3)
└── /workspace/                  # Mounted from host via virtio-fs
```

## Versioning

Images use the format: `MAJOR.MINOR.PATCH-DATE-GITSHA`

Example: `1.0.0-20260115-a3f4d21`

- **MAJOR.MINOR**: Breaking changes (Alpine version, kernel ABI, guest agent protocol)
- **PATCH**: Non-breaking updates (security patches, bug fixes)
- **DATE**: Build date (YYYYMMDD)
- **GITSHA**: Git commit hash (short, 7 chars)

### Compatibility Rules

- Same MAJOR.MINOR versions can restore from each other's teleport packages
- Different MAJOR.MINOR versions will reject restore (prevents corruption)
- PATCH differences generate warnings but allow restore

## Build System

### Prerequisites

- Docker with buildx support
- Git (for version tagging)
- ~500MB disk space for build cache

### Build Options

```bash
./build.sh [OPTIONS]

OPTIONS:
    --arch <arch>       Architecture (arm64, amd64, all) [default: all]
    --version <ver>     Image version (SemVer) [default: 1.0.0]
    --push              Push to registry [default: false]
    --registry <reg>    Registry URL [default: none]
    --help              Show help
```

### Examples

```bash
# Local development build
./build.sh --arch arm64 --version 1.0.0-dev

# Release build for CI
./build.sh --arch all --version 1.2.3 --push --registry ghcr.io/kelpie/base

# Quick test build
ARCH=arm64 VERSION=test ./build.sh
```

## Image Components

### Phase 5.1: Base System ✓ (Current)
- Alpine Linux 3.19
- Essential packages (busybox, ca-certificates, coreutils)
- Multi-arch support (ARM64 + x86_64)
- Version metadata

### Phase 5.2: Guest Agent (Pending)
- Rust-based agent (`kelpie-guest`)
- virtio-vsock communication
- Command execution
- File transfer
- Health monitoring

### Phase 5.3: Init System (Pending)
- Minimal init script
- Mount essential filesystems
- Start guest agent
- Graceful shutdown

### Phase 5.4: Kernel (Pending)
- Alpine linux-virt kernel (~10MB)
- Optimized for VMs (virtio drivers only)
- Multi-arch (ARM64 + x86_64)

## Development Workflow

### 1. Make Changes

Edit `Dockerfile`, `build.sh`, or related files.

### 2. Build Locally

```bash
./build.sh --arch $(uname -m | sed 's/aarch64/arm64/;s/x86_64/amd64/')
```

### 3. Test Image

```bash
# With Docker
docker run --rm -it kelpie-base:latest

# With libkrun (Phase 5.7)
# kelpie sandbox create --image 1.0.0-20260115-abc1234
```

### 4. Run Existing Tests

```bash
# Existing DST tests should work with new images (Phase 5.7)
cargo test -p kelpie-dst --features libkrun
```

## Distribution

### GitHub Releases (Recommended)

Images are automatically built and published to GitHub Releases via CI:

```bash
# Download from GitHub
curl -L -o kelpie-base-1.0.0-arm64.tar.gz \
  https://github.com/YOUR_ORG/kelpie/releases/download/v1.0.0/kelpie-base-1.0.0-arm64.tar.gz
```

### Docker Registry (Optional)

For faster access, push to a container registry:

```bash
./build.sh --arch all --version 1.0.0 \
  --push --registry ghcr.io/your-org/kelpie-base
```

### Local Development

Images are cached in `~/.kelpie/images/`:

```
~/.kelpie/images/
├── 1.0.0-20260115-abc1234/
│   ├── rootfs.ext4          # Root filesystem
│   ├── vmlinuz              # Kernel
│   ├── initrd               # Initial ramdisk
│   └── metadata.json        # Image metadata
└── cache.json               # Cache index
```

## Troubleshooting

### Build Fails with "buildx not found"

Install Docker buildx:

```bash
docker buildx install
```

### Multi-arch Build is Slow

QEMU emulation is slow (~10-30x). For faster builds:

1. Use native architecture: `--arch arm64` on ARM64, `--arch amd64` on x86_64
2. Use CI with native runners (GitHub Actions supports both)
3. Enable BuildKit cache: `DOCKER_BUILDKIT=1`

### Image Won't Boot

Check kernel compatibility:

```bash
# Verify kernel exists
docker run --rm kelpie-base:latest ls -lh /boot/

# Check kernel version
docker run --rm kelpie-base:latest cat /etc/alpine-release
```

### Guest Agent Not Starting

Check logs (Phase 5.3):

```bash
# Inside VM
cat /var/log/kelpie-guest.log

# Or via serial console
# (libkrun provides console access)
```

## Architecture

### Image Layers

```
┌─────────────────────────────────────┐
│  Application Layer (user code)     │  Ephemeral
├─────────────────────────────────────┤
│  Guest Agent (kelpie-guest)        │  Base Image
├─────────────────────────────────────┤
│  Alpine Userland (busybox, etc.)   │  Base Image
├─────────────────────────────────────┤
│  Linux Kernel (linux-virt)         │  Separate
└─────────────────────────────────────┘
```

### Boot Sequence

1. libkrun loads kernel and initrd
2. Kernel mounts rootfs (ext4)
3. Init system starts (`/sbin/init`)
4. Guest agent starts (`/usr/local/bin/kelpie-guest`)
5. Agent listens on virtio-vsock
6. Host connects and sends commands

### Communication Flow

```
Host (Rust)                           Guest (Rust)
┌──────────────┐                      ┌──────────────┐
│ LibkrunSandbox│                      │ kelpie-guest │
│              │                      │              │
│ exec("ls")   │────virtio-vsock─────>│ execute      │
│              │                      │              │
│              │<────response─────────│ return output│
└──────────────┘                      └──────────────┘
```

## References

- [Alpine Linux](https://alpinelinux.org/)
- [Docker buildx](https://docs.docker.com/buildx/working-with-buildx/)
- [libkrun](https://github.com/containers/libkrun)
- [virtio-vsock](https://www.kernel.org/doc/html/latest/virt/kvm/devices/vm-socket-device.html)

## License

Same as Kelpie project.
