# Task: Base Image Build System for Teleportable Sandboxes

**Created:** 2026-01-15 10:00:00
**State:** PLANNING

---

## Vision Alignment

**Vision files read:** CONSTRAINTS.md

**Relevant constraints/guidance:**
- Simulation-first development (CONSTRAINTS.md §1) - While image building itself doesn't need DST, validation that images work correctly should be tested through DST
- TigerStyle safety principles (CONSTRAINTS.md §3) - Explicit versioning, validation, no silent failures
- No placeholders in production (CONSTRAINTS.md §4) - Images must be functional, not stub implementations
- Quality over speed (CONSTRAINTS.md §6) - Better to have one solid multi-arch image than multiple broken ones

---

## Task Description

Implement a reproducible build system for multi-architecture VM base images that:

1. **Provides consistent environments** across macOS (ARM64) and Linux (ARM64/x86_64)
2. **Enables teleportation** - Same base image versions can restore from teleport packages
3. **Includes guest agent** - In-VM agent for command execution, file transfer, and monitoring
4. **Supports versioning** - Explicit version tracking to prevent image mismatches
5. **Is reproducible** - Same build inputs = same output image

**Why this matters:**
- Without proper base images, libkrun sandboxes can't actually run
- Image mismatches will cause teleport failures (can't restore ARM64 snapshot on different base)
- Guest agent is required for `sandbox.exec()` functionality
- Versioning prevents subtle bugs from environment drift

---

## Options & Decisions [REQUIRED]

### Decision 1: Base Linux Distribution

**Context:** Need a minimal, fast-booting Linux distribution for VM images.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Alpine Linux | Minimal musl-based distro (~5MB base) | Very small, fast boot (<1s), multi-arch support, security-focused | musl libc can have compatibility issues with some binaries |
| B: Ubuntu Core | Minimal Ubuntu variant (~50MB) | glibc compatibility, familiar, well-documented | Larger size, slower boot |
| C: Buildroot | Custom-built minimal system | Maximum control, smallest possible | Complex build process, maintenance burden |
| D: Fedora CoreOS | Container-focused minimal OS | Modern, well-maintained | Larger size (~200MB), container-focused not VM-focused |

**Decision:** **Option A (Alpine Linux)** - The 5MB base size and <1s boot time are critical for fast sandbox startup. The musl libc compatibility issues are acceptable since we control what runs inside (guest agent + user code). Alpine's multi-arch support is mature.

**Trade-offs accepted:**
- musl libc incompatibility - mitigate by testing common tools, documenting known issues
- Less familiar than Ubuntu - acceptable given team Rust/systems experience
- Smaller package ecosystem - acceptable since we're running minimal workloads

---

### Decision 2: Multi-Arch Build Strategy

**Context:** Need to build images for both ARM64 (Mac M1/M2, AWS Graviton) and x86_64 (traditional cloud).

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: QEMU emulation | Use QEMU to build non-native arch on any machine | Can build anywhere, no special hardware | Slow builds (10-30x slower), high CPU usage |
| B: Native builds | Build ARM64 on ARM64, x86_64 on x86_64 | Fast, accurate | Requires access to both architectures |
| C: Docker buildx | Use Docker's multi-arch build system | Easy, well-documented | Requires Docker, another dependency |
| D: GitHub Actions matrix | Use CI to build on native runners | Free for OSS, parallel builds, reproducible | Slower iteration during development |

**Decision:** **Hybrid: Option C (Docker buildx) + Option D (GitHub Actions)**
- Local development: Docker buildx for convenience
- CI/releases: GitHub Actions for reproducibility and artifact storage
- Docker buildx uses QEMU internally but abstracts the complexity

**Trade-offs accepted:**
- Docker dependency - acceptable since most developers already have it
- QEMU slowness for local builds - mitigate by caching aggressively
- CI cost - GitHub Actions is free for public repos

---

### Decision 3: Guest Agent Implementation

**Context:** Need an agent running inside the VM to handle exec(), file transfer, and monitoring.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Rust binary | Static Rust binary, virtio-vsock protocol | Type-safe, small binary (~2MB), no runtime needed | More upfront development |
| B: Go binary | Go with virtio-vsock | Easy development, good stdlib | Larger binary (~10MB), GC overhead |
| C: Shell script | Bash script with netcat | Minimal, no compilation | Limited functionality, error-prone |
| D: Python script | Python with minimal deps | Fast development | Requires Python runtime (~50MB), slow startup |

**Decision:** **Option A (Rust binary)** - Aligns with rest of codebase, provides type safety, produces small static binary. The upfront development cost is worth it for long-term maintainability and performance.

**Trade-offs accepted:**
- More development time than shell script - worth it for reliability
- Need to cross-compile for multiple archs - already set up for project
- Debugging inside VM harder than interpreted language - mitigate with logging

---

### Decision 4: Communication Protocol (Host ↔ Guest)

**Context:** Host needs to communicate with guest agent for exec(), file operations, etc.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: virtio-vsock | VM socket, kernel-supported | Fast (in-memory), secure, standard | Requires kernel support |
| B: Serial console | /dev/ttyS0 text protocol | Simple, universal | Slow, text-only, no multiplexing |
| C: Network (virtio-net) | TCP/IP over virtual network | Standard protocols (SSH, HTTP) | Overhead, needs IP config, security concerns |
| D: virtio-fs + polling | Shared filesystem with control files | No special protocol | Slow, polling overhead, file-based IPC is clunky |

**Decision:** **Option A (virtio-vsock)** - Purpose-built for VM communication, fast, secure. Already supported by libkrun. We'll design a simple binary protocol on top (length-prefixed protobuf or similar).

**Trade-offs accepted:**
- Custom protocol to implement - keep it simple (request/response pattern)
- Debugging harder than HTTP - mitigate with structured logging
- Not human-readable like HTTP - acceptable for internal use

---

### Decision 5: Image Versioning Scheme

**Context:** Need to track image versions to prevent teleport mismatches.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: SemVer (1.0.0) | Semantic versioning | Standard, familiar, conveys compatibility | Can be misleading for images |
| B: Date-based (2026.01.15) | Date of build | Clear when built, sortable | Doesn't convey compatibility |
| C: Git SHA | Commit hash of build scripts | Exact reproducibility | Not human-friendly |
| D: Hybrid (1.0.0-2026.01.15-abc1234) | SemVer + date + git SHA | All benefits combined | Verbose |

**Decision:** **Option D (Hybrid)** - Use format `MAJOR.MINOR.PATCH-DATE-GITSHORT`
- Example: `1.0.0-20260115-a3f4d21`
- MAJOR.MINOR for breaking changes (Alpine version, kernel ABI)
- DATE for tracking when built
- GITSHORT for exact reproducibility

**Trade-offs accepted:**
- More complex than simple SemVer - worth it for traceability
- Longer version strings - acceptable for internal use
- Need to maintain versioning discipline - document in build scripts

---

### Decision 6: Image Distribution

**Context:** Where to store and retrieve base images.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Docker Hub | Public container registry | Free for public images, familiar | Not designed for VM images, size limits |
| B: GitHub Releases | Attach to GitHub releases | Free, integrated with repo, no size limits for releases | Manual upload process |
| C: S3 / R2 | Object storage | Scalable, CDN-backed | Costs money, requires credentials |
| D: Embedded in binary | Include image in kelpie binary | No external dependency | Huge binary size (~500MB+) |
| E: HTTPS download | Host on simple web server | Simple, cacheable | Need to maintain server |

**Decision:** **Option B (GitHub Releases)** for distribution + **Option C (S3/R2)** for optional CDN caching
- GitHub Releases for official versioned releases (free, reliable)
- Local filesystem for development (`~/.kelpie/images/`)
- S3/R2 as optional fast path for production (configurable)

**Trade-offs accepted:**
- Users must download images on first use - acceptable, show progress
- GitHub has rate limits - mitigate with local caching
- Need fallback logic - acceptable, makes system more robust

---

### Decision 7: Kernel Management

**Context:** VMs need a kernel to boot.

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| A: Custom minimal kernel | Build kernel from source with minimal config | Smallest size (~2MB), optimized | Complex build, maintenance burden |
| B: Alpine kernel package | Use Alpine's kernel | Maintained, tested | Larger (~10MB), includes unused drivers |
| C: Cloud-optimized kernel | Use cloud vendor kernels (e.g., AWS kernel) | Optimized for cloud VMs | Platform-specific, multiple variants needed |
| D: Unified kernel image | Single kernel with drivers as modules | One kernel for all platforms | Larger base image |

**Decision:** **Option B (Alpine kernel package)** initially, migrate to **Option A (custom minimal)** later if size becomes issue
- Alpine's `linux-virt` package is already optimized for VMs (~10MB)
- Maintained by Alpine team, security updates
- Can optimize later without changing architecture

**Trade-offs accepted:**
- ~10MB kernel vs ~2MB custom - acceptable given total image size
- Some unused drivers included - acceptable for now
- Dependent on Alpine's release schedule - acceptable, they're responsive

---

## Quick Decision Log [REQUIRED]

| Time | Decision | Rationale | Trade-off |
|------|----------|-----------|-----------|
| Planning | Alpine Linux base | 5MB size, <1s boot, multi-arch | musl libc compatibility |
| Planning | Docker buildx + GitHub Actions | Local convenience + CI reproducibility | Docker dependency |
| Planning | Rust guest agent | Type-safe, small binary, aligns with codebase | More upfront dev |
| Planning | virtio-vsock protocol | Fast, secure, purpose-built for VMs | Custom protocol to implement |
| Planning | Hybrid versioning (1.0.0-DATE-SHA) | SemVer + traceability | More complex |
| Planning | GitHub Releases + S3 | Free + fast, with fallbacks | Download on first use |
| Planning | Alpine kernel initially | Maintained, VM-optimized | ~10MB size |
| Phase 5.1 | Allow dev versions in build.sh | Flexible versioning for development builds | Regex more complex |
| Phase 5.1 | Image size 28.8MB achieved | Under 50MB target, includes bash + utils | Slightly larger than minimal |

---

## Implementation Plan

### Phase 5.1: Build System Foundation
- [ ] Create `images/` directory structure
- [ ] Write Dockerfile for Alpine base
  - [ ] Multi-stage build (builder + runtime)
  - [ ] Install essential packages (busybox, ca-certificates)
  - [ ] Set up minimal init system
- [ ] Configure Docker buildx for multi-arch
- [ ] Write `build.sh` script with versioning
- [ ] Test build produces valid images for ARM64 and x86_64
- [ ] Document build process in `images/README.md`

**Files:**
```
images/
├── README.md
├── Dockerfile
├── build.sh
└── .dockerignore
```

**Validation:** Can build and boot image in QEMU

---

### Phase 5.2: Guest Agent (Rust)
- [ ] Create `images/guest-agent/` subdirectory
- [ ] Implement Rust guest agent crate
  - [ ] virtio-vsock listener
  - [ ] Command execution (exec with stdin/stdout/stderr capture)
  - [ ] File operations (read, write, list)
  - [ ] Health check / ping
- [ ] Define wire protocol (protobuf or simple length-prefixed JSON)
- [ ] Build static binary (musl target)
- [ ] Add to Docker image build
- [ ] Write unit tests for protocol handling

**Files:**
```
images/guest-agent/
├── Cargo.toml
├── src/
│   ├── main.rs          # Entry point, vsock server
│   ├── protocol.rs      # Wire protocol definition
│   ├── executor.rs      # Command execution
│   └── files.rs         # File operations
└── tests/
```

**Validation:** Agent can receive and execute commands via vsock

---

### Phase 5.3: Init System & Boot Integration
- [ ] Create minimal init script
  - [ ] Mount essential filesystems (/proc, /sys, /dev)
  - [ ] Set up networking (if needed)
  - [ ] Start guest agent
  - [ ] Handle graceful shutdown
- [ ] Configure kernel command line
- [ ] Set up virtio-fs mount points
- [ ] Test full boot sequence

**Files:**
```
images/base/
├── init           # Minimal init script
├── rc.local       # Startup script for guest agent
└── config/        # System config files
```

**Validation:** Image boots, agent starts, accepts commands

---

### Phase 5.4: Kernel Configuration
- [ ] Document Alpine kernel package usage
- [ ] Create script to extract kernel and initrd from Alpine
- [ ] Test kernel boots with libkrun
- [ ] Document kernel parameters for libkrun

**Files:**
```
images/kernel/
├── extract-kernel.sh
└── README.md
```

**Validation:** Kernel boots in libkrun with Alpine rootfs

---

### Phase 5.5: Image Registry & Distribution
- [ ] Write script to package images (rootfs.ext4 + kernel + metadata.json)
- [ ] Create GitHub Actions workflow for multi-arch builds
  - [ ] Build on ARM64 and x86_64 runners
  - [ ] Upload to GitHub Releases
  - [ ] Generate checksums (SHA256)
- [ ] Implement image downloader in `kelpie-sandbox`
  - [ ] Check `~/.kelpie/images/` cache
  - [ ] Download from GitHub Releases if missing
  - [ ] Verify checksum
  - [ ] Extract to cache
- [ ] Document image management in CLAUDE.md

**Files:**
```
.github/workflows/
└── build-images.yml

crates/kelpie-sandbox/src/
└── image_manager.rs

images/
└── package.sh
```

**Validation:** `kelpie` automatically downloads and caches images

---

### Phase 5.6: Versioning & Compatibility
- [ ] Implement version checking in TeleportService
  - [ ] Compare package `base_image_version` with current
  - [ ] Reject restore if major.minor differ
  - [ ] Warn if patch differs
- [ ] Add `--image-version` flag to CLI
- [ ] Document versioning scheme in ADR
- [ ] Test cross-version restore (should fail gracefully)

**Files:**
```
crates/kelpie-server/src/service/teleport_service.rs (updated)
docs/adr/009-base-image-versioning.md
```

**Validation:** Mismatched versions rejected with clear error

---

### Phase 5.7: Integration with libkrun
- [ ] Update `LibkrunSandbox` to use real images
- [ ] Configure rootfs path, kernel path, initrd path
- [ ] Mount workspace via virtio-fs
- [ ] Connect to guest agent via vsock
- [ ] Test full lifecycle: boot → exec → snapshot → restore
- [ ] Remove `MockVm` feature gate (make optional)

**Files:**
```
crates/kelpie-sandbox/src/libkrun.rs (updated)
```

**Validation:** Can exec commands in real VM, not mock

---

### Phase 5.8: Documentation & Examples
- [ ] Update CLAUDE.md with image management
- [ ] Write `images/README.md` with:
  - [ ] How to build images locally
  - [ ] Image structure and layout
  - [ ] Guest agent protocol
  - [ ] Troubleshooting common issues
- [ ] Add examples to CLI help
- [ ] Document system requirements (KVM/HVF)

---

## Checkpoints

- [x] Codebase understood
- [x] Plan approved
- [x] **Options & Decisions filled in** (7 decisions documented)
- [x] **Quick Decision Log maintained**
- [x] Phase 5.1 complete (Build system) ✅
- [ ] Phase 5.2 complete (Guest agent)
- [ ] Phase 5.3 complete (Init system)
- [ ] Phase 5.4 complete (Kernel)
- [ ] Phase 5.5 complete (Distribution)
- [ ] Phase 5.6 complete (Versioning)
- [ ] Phase 5.7 complete (libkrun integration)
- [ ] Phase 5.8 complete (Documentation)
- [ ] Tests passing (`cargo test`)
- [ ] Clippy clean (`cargo clippy`)
- [ ] Code formatted (`cargo fmt`)
- [ ] /no-cap passed
- [ ] Vision aligned
- [x] **What to Try section updated** (Phase 5.1)
- [ ] Committed

---

## Test Requirements

**Unit tests:**
- Guest agent protocol parsing (request/response roundtrip)
- Guest agent executor (command execution with output capture)
- Image manager (download, cache, checksum verification)
- Version compatibility checking

**Integration tests:**
- Full VM boot with real image
- Exec command via vsock to guest agent
- File transfer host → guest → host
- Snapshot and restore with real VM
- Multi-arch: Boot ARM64 image on ARM64, x86_64 on x86_64

**DST tests:**
Note: Base image building itself is not a DST critical path, but we should validate images work correctly through existing DST tests:
- [ ] Existing `test_sandbox_exec_under_faults` should work with real images
- [ ] Existing `test_sandbox_snapshot_restore_under_faults` should work with real images
- [ ] No new DST tests required (image building is deterministic, no fault injection needed)

**Manual tests:**
- Build images on macOS ARM64
- Build images on Linux x86_64
- Download image from GitHub Releases
- Boot image in libkrun on Mac
- Boot image in libkrun on Linux
- Teleport between Mac and AWS Graviton (same arch)
- Checkpoint from Mac to AWS x86 (cross-arch)

**Commands:**
```bash
# Build images locally
cd images && ./build.sh

# Build specific arch
cd images && ./build.sh --arch arm64

# Test image boots
qemu-system-aarch64 -kernel vmlinuz -initrd initrd -drive file=rootfs.ext4

# Run existing DST tests with real images
cargo test -p kelpie-dst --features libkrun

# Run sandbox tests with real images
cargo test -p kelpie-sandbox --features libkrun

# Test image download
kelpie images list
kelpie images download 1.0.0-20260115-abc1234

# Run clippy
cargo clippy --all-targets --all-features

# Format code
cargo fmt
```

---

## Dependencies

**New external dependencies:**
- Docker (for local builds)
- QEMU (optional, for testing images)
- KVM or Hypervisor.framework (runtime requirement)

**New crate dependencies:**
- `reqwest` - Download images from GitHub/S3
- `sha2` - Checksum verification
- `tar` or `zip` - Image extraction
- `serde_json` - Image metadata
- `tokio-vsock` - virtio-vsock communication (in guest agent)

**System packages (inside image):**
- Alpine Linux base
- busybox
- ca-certificates
- linux-virt (kernel package)

---

## Context Refreshes

| Time | Files Re-read | Notes |
|------|---------------|-------|
| | | |

---

## Blockers

| Blocker | Status | Resolution |
|---------|--------|------------|
| | | |

---

## Instance Log (Multi-Instance Coordination)

| Instance | Claimed Phases | Status | Last Update |
|----------|----------------|--------|-------------|
| | | | |

---

## Findings

[Key discoveries will be logged here as implementation progresses]

---

## What to Try [REQUIRED - UPDATE AFTER EACH PHASE]

### Works Now ✅
| What | How to Try | Expected Result |
|------|------------|-----------------|
| **Build base image (Phase 5.1)** | `cd images && ./build.sh --arch arm64 --version 1.0.0-dev` | Image builds successfully, 28.8MB |
| **Run base image** | `docker run --rm -it kelpie-base:latest` | Alpine shell starts |
| **Check image version** | `docker run --rm kelpie-base:latest cat /etc/kelpie-version` | Shows version string |
| **Build metadata** | `cat images/build-metadata.json` | JSON with version, arch, etc. |
| Existing teleport DST tests | `cargo test -p kelpie-dst --test teleport_service_dst` | 5 tests pass with SimTeleportStorage |
| MockVm sandbox | `cargo test -p kelpie-sandbox` | 60+ tests pass |
| TeleportService | `cargo test -p kelpie-server teleport` | 7 tests pass |

### Doesn't Work Yet ❌
| What | Why | When Expected |
|------|-----|---------------|
| Real VM images | Not built yet | Phase 5.1-5.4 |
| Guest agent | Not implemented | Phase 5.2 |
| Image download | Not implemented | Phase 5.5 |
| Real libkrun VMs | Requires images + guest agent | Phase 5.7 |
| Cross-machine teleport | Requires real VMs | Phase 5.7 + Phase 6 |

### Known Limitations ⚠️
- Docker required for building images (until we add native build scripts)
- First boot will download ~50MB image (cached after that)
- macOS requires Hypervisor.framework (Mac only, no iOS)
- Linux requires KVM (`/dev/kvm` access)
- musl libc in Alpine may have compatibility issues with some binaries

---

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Image build complexity | Dev friction | Good docs, Docker abstraction, CI automation |
| Image size bloat | Slow downloads, disk space | Alpine minimal base, exclude dev tools |
| Cross-arch compatibility | Teleport failures | Strict versioning, compatibility tests |
| Guest agent bugs | Sandbox unusable | Thorough testing, simple protocol, recovery mechanisms |
| virtio-vsock reliability | Communication failures | Retry logic, timeouts, fallback to serial console |
| Kernel incompatibility | Boot failures | Use well-tested Alpine kernel, document requirements |

---

## Success Criteria

Phase 5 is complete when:
- [ ] Multi-arch images (ARM64 + x86_64) build successfully
- [ ] Images boot in libkrun on macOS and Linux
- [ ] Guest agent accepts and executes commands via vsock
- [ ] `sandbox.exec()` works with real VM (not MockVm)
- [ ] Images are versioned and distributed via GitHub Releases
- [ ] Automatic download and caching works
- [ ] Existing DST tests pass with real images
- [ ] Documentation is complete and tested

---

## Completion Notes

[To be filled in when phase is complete]
