# Kernel Configuration for Kelpie VMs

This directory contains tools and documentation for managing VM kernels.

## Quick Start

### Extract Kernel from Alpine

```bash
cd kernel
./extract-kernel.sh
```

This will:
1. Create a temporary Alpine container
2. Install the `linux-virt` package (VM-optimized kernel)
3. Extract kernel and initrd to this directory
4. Generate metadata JSON

### Output Files

```
kernel/
├── vmlinuz-aarch64          # Kernel binary (ARM64)
├── vmlinuz-x86_64           # Kernel binary (x86_64)
├── initramfs-aarch64        # Initial ramdisk (ARM64, optional)
├── initramfs-x86_64         # Initial ramdisk (x86_64, optional)
├── kernel-metadata.json     # Kernel version info
└── README.md                # This file
```

## Kernel Details

### Alpine linux-virt Package

Kelpie uses Alpine's `linux-virt` kernel package, which is optimized for virtual machines:

- **Size**: ~10-12MB (compressed)
- **Modules**: Only virtio drivers (no hardware drivers)
- **Boot time**: <500ms
- **Versions**: Tracks Alpine stable releases

### Why linux-virt?

| Feature | linux-virt | linux-lts | Custom Kernel |
|---------|------------|-----------|---------------|
| Size | ~10MB | ~15MB | ~2MB |
| Maintenance | Alpine team | Alpine team | Manual |
| VM optimized | Yes | No | Manual |
| Security updates | Automatic | Automatic | Manual |
| Boot time | Fast | Medium | Fastest |

**Decision**: Use `linux-virt` for maintainability and security updates. Optimize to custom kernel later if size becomes critical.

## Kernel Parameters

### Required Parameters for libkrun

```
console=ttyS0          # Serial console for logging
quiet                  # Reduce kernel messages
init=/sbin/init        # Our custom init system
rw                     # Mount rootfs read-write
```

### Optional Parameters

```
rootfstype=ext4        # Explicit filesystem type
panic=1                # Reboot on panic after 1 second
```

### Full Example Command Line

```
console=ttyS0 quiet init=/sbin/init rw rootfstype=ext4
```

## Usage with libkrun

### Rust Example

```rust
use kelpie_libkrun::{VmConfig, VmInstance};

let config = VmConfig::new()
    .with_kernel_path("/path/to/vmlinuz-aarch64")
    .with_initrd_path("/path/to/initramfs-aarch64")  // Optional
    .with_rootfs_path("/path/to/rootfs.ext4")
    .with_cmdline("console=ttyS0 quiet init=/sbin/init rw")
    .with_memory_mb(512)
    .with_vcpus(2);

let vm = VmInstance::create(config)?;
vm.start()?;
```

## Architecture Support

### ARM64 (aarch64)

- **Platforms**: Apple Silicon Macs, AWS Graviton, Raspberry Pi 4
- **Kernel**: `vmlinuz-aarch64`
- **Boot**: Tested on macOS HVF, Linux KVM

### x86_64 (amd64)

- **Platforms**: Intel/AMD CPUs, most cloud providers
- **Kernel**: `vmlinuz-x86_64`
- **Boot**: Tested on Linux KVM

## Version Compatibility

### Kernel ↔ Base Image

The kernel version must be compatible with the base image:

| Base Image | Kernel Version | Compatible |
|------------|----------------|------------|
| Alpine 3.19 | 6.6.x | ✅ |
| Alpine 3.19 | 6.1.x | ✅ |
| Alpine 3.19 | 5.15.x | ⚠️ May work |
| Alpine 3.18 | 6.6.x | ❌ ABI mismatch |

**Rule**: Use kernel from same Alpine version as base image.

### Checking Compatibility

```bash
# In base image
cat /etc/alpine-release  # e.g., 3.19.0

# In kernel metadata
cat kernel-metadata.json | jq .alpine_version  # Must match major.minor
```

## Kernel Modules

The `linux-virt` kernel includes only essential modules:

- **virtio_blk**: Block device support
- **virtio_net**: Network device support
- **virtio_fs**: Filesystem sharing (9p/virtiofs)
- **virtio_console**: Serial console
- **virtio_balloon**: Memory ballooning

No physical hardware drivers (SATA, USB, PCIe, etc.) are included.

## Troubleshooting

### Kernel Won't Boot

**Symptom**: VM fails to start, no console output

**Solutions**:
1. Check kernel architecture matches host: `file vmlinuz-aarch64`
2. Verify kernel is not corrupted: `ls -lh vmlinuz-*`
3. Try with initrd if kernel requires it
4. Check libkrun error messages

### Kernel Panic

**Symptom**: "Kernel panic - not syncing: VFS: Unable to mount root fs"

**Solutions**:
1. Ensure rootfs path is correct
2. Try adding `rootfstype=ext4` to cmdline
3. Verify rootfs is a valid ext4 filesystem: `file rootfs.ext4`
4. Check init script exists: `docker run kelpie-base ls -l /sbin/init`

### Module Not Found

**Symptom**: "modprobe: can't load module virtio_xyz"

**Solutions**:
1. Module might be built-in (not loadable)
2. Check kernel config: `zcat /proc/config.gz | grep VIRTIO` (in VM)
3. linux-virt should have all virtio drivers built-in

### Serial Console Not Working

**Symptom**: No output in console, VM appears hung

**Solutions**:
1. Ensure `console=ttyS0` in kernel cmdline
2. Check libkrun serial console configuration
3. Try `console=ttyS0,115200` (explicit baud rate)

## Kernel Updates

### Automatic Updates (Recommended)

Re-run `extract-kernel.sh` periodically:

```bash
# In CI or cron job
cd images/kernel
./extract-kernel.sh

# Check if kernel changed
git diff vmlinuz-*
```

### Manual Updates

1. Update `ALPINE_VERSION` in `extract-kernel.sh`
2. Run extraction script
3. Test with new kernel
4. Commit updated kernel files

## Performance

### Boot Time

```
Cold boot (no cache):     ~800ms
Warm boot (with cache):   ~300ms
With initrd:              +200ms
```

### Memory Usage

```
Kernel:                   ~40MB (resident)
Initrd (loaded):          ~15MB (resident)
Total minimum:            ~55MB
```

### Size on Disk

```
vmlinuz-aarch64:          ~11MB
initramfs-aarch64:        ~15MB (optional)
Total:                    ~11-26MB
```

## Future Improvements

### Phase 5.7+ (When Integrated with libkrun)

- [ ] Automate kernel extraction in Docker build
- [ ] Include kernel in base image `/boot/`
- [ ] Cache kernel downloads for faster builds
- [ ] Add kernel version checking in TeleportService
- [ ] Test cross-kernel teleportation (same ABI)

### Custom Kernel (Optional, Future)

If size becomes critical:

- Build minimal kernel with only virtio drivers
- Remove unused features (no networking protocols, filesystems, etc.)
- Target: ~2-3MB kernel vs ~11MB linux-virt
- Trade-off: Manual maintenance vs Alpine's automatic updates

## References

- [Alpine Linux Kernel](https://wiki.alpinelinux.org/wiki/Kernels)
- [virtio Specification](https://docs.oasis-open.org/virtio/virtio/v1.1/virtio-v1.1.html)
- [libkrun Documentation](https://github.com/containers/libkrun)
- [KVM virtio](https://www.linux-kvm.org/page/Virtio)
