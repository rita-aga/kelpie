#import <Foundation/Foundation.h>
#import <Virtualization/Virtualization.h>

#include "vz_bridge.h"
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>

@interface KelpieVzVmWrapper : NSObject
@property (nonatomic, strong) VZVirtualMachine *vm;
@property (nonatomic) dispatch_queue_t queue;
@property (nonatomic, strong) VZVirtioSocketDevice *socketDevice;
@property (nonatomic, strong) NSMutableDictionary<NSNumber *, VZVirtioSocketConnection *> *connections;
@end

@implementation KelpieVzVmWrapper
@end

static void kelpie_vz_set_error(char **error_out, NSString *message) {
    if (error_out == NULL) {
        return;
    }
    const char *utf8 = message == nil ? "unknown error" : [message UTF8String];
    if (utf8 == NULL) {
        *error_out = strdup("unknown error");
        return;
    }
    *error_out = strdup(utf8);
}

bool kelpie_vz_is_supported(void) {
    return [VZVirtualMachine isSupported];
}

KelpieVzVmHandle *kelpie_vz_vm_create(const char *id,
                                      const char *kernel_path,
                                      const char *initrd_path,
                                      const char *rootfs_path,
                                      const char *boot_args,
                                      bool rootfs_readonly,
                                      uint32_t vcpu_count,
                                      uint64_t memory_mib,
                                      char **error_out) {
    @autoreleasepool {
        if (!kelpie_vz_is_supported()) {
            kelpie_vz_set_error(error_out, @"Virtualization.framework is not supported on this host");
            return NULL;
        }

        if (kernel_path == NULL || rootfs_path == NULL) {
            kelpie_vz_set_error(error_out, @"kernel_path and rootfs_path are required");
            return NULL;
        }

        NSString *kernel = [NSString stringWithUTF8String:kernel_path];
        NSString *rootfs = [NSString stringWithUTF8String:rootfs_path];
        NSString *initrd = initrd_path ? [NSString stringWithUTF8String:initrd_path] : nil;
        NSString *boot = boot_args ? [NSString stringWithUTF8String:boot_args] : @"";

        VZVirtualMachineConfiguration *config = [[VZVirtualMachineConfiguration alloc] init];
        config.CPUCount = (NSUInteger)vcpu_count;
        config.memorySize = memory_mib * 1024ULL * 1024ULL;

        VZLinuxBootLoader *bootLoader =
            [[VZLinuxBootLoader alloc] initWithKernelURL:[NSURL fileURLWithPath:kernel]];
        if (initrd != nil && initrd.length > 0) {
            bootLoader.initialRamdiskURL = [NSURL fileURLWithPath:initrd];
        }
        bootLoader.commandLine = boot;
        config.bootLoader = bootLoader;

        NSError *attachmentError = nil;
        VZDiskImageStorageDeviceAttachment *attachment =
            [[VZDiskImageStorageDeviceAttachment alloc] initWithURL:[NSURL fileURLWithPath:rootfs]
                                                            readOnly:rootfs_readonly
                                                               error:&attachmentError];
        if (attachmentError != nil) {
            kelpie_vz_set_error(error_out, [NSString stringWithFormat:@"disk attachment failed: %@", attachmentError]);
            return NULL;
        }

        VZVirtioBlockDeviceConfiguration *blockConfig =
            [[VZVirtioBlockDeviceConfiguration alloc] initWithAttachment:attachment];
        config.storageDevices = @[blockConfig];

        VZVirtioEntropyDeviceConfiguration *entropy = [[VZVirtioEntropyDeviceConfiguration alloc] init];
        config.entropyDevices = @[entropy];

        VZVirtioTraditionalMemoryBalloonDeviceConfiguration *balloon =
            [[VZVirtioTraditionalMemoryBalloonDeviceConfiguration alloc] init];
        config.memoryBalloonDevices = @[balloon];

        VZVirtioSocketDeviceConfiguration *socketConfig = [[VZVirtioSocketDeviceConfiguration alloc] init];
        config.socketDevices = @[socketConfig];

        // Add serial port for console output (console=hvc0)
        // VZVirtioConsoleDeviceSerialPortConfiguration provides hvc0 device to guest
        @try {
            // Open /dev/null for input (host -> guest, guest reads nothing)
            int nullFd = open("/dev/null", O_RDWR);
            if (nullFd >= 0) {
                // Duplicate for separate read/write handles
                int readFd = dup(nullFd);
                int writeFd = dup(nullFd);
                close(nullFd);

                if (readFd >= 0 && writeFd >= 0) {
                    NSFileHandle *readHandle = [[NSFileHandle alloc] initWithFileDescriptor:readFd closeOnDealloc:YES];
                    NSFileHandle *writeHandle = [[NSFileHandle alloc] initWithFileDescriptor:writeFd closeOnDealloc:YES];
                    VZFileHandleSerialPortAttachment *consoleAttachment =
                        [[VZFileHandleSerialPortAttachment alloc] initWithFileHandleForReading:readHandle
                                                                        fileHandleForWriting:writeHandle];
                    VZVirtioConsoleDeviceSerialPortConfiguration *consoleConfig =
                        [[VZVirtioConsoleDeviceSerialPortConfiguration alloc] init];
                    consoleConfig.attachment = consoleAttachment;
                    config.serialPorts = @[consoleConfig];
                } else {
                    if (readFd >= 0) close(readFd);
                    if (writeFd >= 0) close(writeFd);
                    NSLog(@"VZ console: failed to dup fds");
                }
            } else {
                NSLog(@"VZ console: failed to open /dev/null");
            }
        } @catch (NSException *exception) {
            NSLog(@"VZ console setup failed: %@", exception);
            // Continue without console - VM might still work for vsock communication
        }

        NSError *validationError = nil;
        if (![config validateWithError:&validationError]) {
            NSString *message = validationError ? validationError.localizedDescription : @"validation failed";
            kelpie_vz_set_error(error_out, message);
            return NULL;
        }

        const char *queue_label = id != NULL ? id : "kelpie.vz.vm";
        dispatch_queue_t queue = dispatch_queue_create(queue_label, DISPATCH_QUEUE_SERIAL);
        VZVirtualMachine *vm = [[VZVirtualMachine alloc] initWithConfiguration:config queue:queue];
        if (vm == nil) {
            kelpie_vz_set_error(error_out, @"failed to create VZVirtualMachine");
            return NULL;
        }

        KelpieVzVmWrapper *wrapper = [[KelpieVzVmWrapper alloc] init];
        wrapper.vm = vm;
        wrapper.queue = queue;
        wrapper.connections = [NSMutableDictionary dictionary];

        VZVirtioSocketDevice *socketDevice = nil;
        for (VZSocketDevice *device in vm.socketDevices) {
            if ([device isKindOfClass:[VZVirtioSocketDevice class]]) {
                socketDevice = (VZVirtioSocketDevice *)device;
                break;
            }
        }
        if (socketDevice == nil) {
            kelpie_vz_set_error(error_out, @"failed to find VZVirtioSocketDevice");
            return NULL;
        }
        wrapper.socketDevice = socketDevice;

        return (__bridge_retained KelpieVzVmHandle *)wrapper;
    }
}

void kelpie_vz_vm_free(KelpieVzVmHandle *vm) {
    if (vm == NULL) {
        return;
    }
    KelpieVzVmWrapper *obj = (__bridge_transfer KelpieVzVmWrapper *)vm;
    [obj.connections removeAllObjects];
}

static int kelpie_vz_run_vm_op(KelpieVzVmWrapper *vm,
                               void (^operation)(void (^)(NSError *)))
{
    if (vm == NULL) {
        return -1;
    }

    dispatch_semaphore_t sema = dispatch_semaphore_create(0);
    __block NSError *opError = nil;

    dispatch_async(vm.queue, ^{
        operation(^(NSError *error) {
            opError = error;
            dispatch_semaphore_signal(sema);
        });
    });

    dispatch_semaphore_wait(sema, DISPATCH_TIME_FOREVER);
    if (opError != nil) {
        return -1;
    }
    return 0;
}

int kelpie_vz_vm_start(KelpieVzVmHandle *vm, char **error_out) {
    if (vm == NULL) {
        kelpie_vz_set_error(error_out, @"vm handle is null");
        return -1;
    }

    KelpieVzVmWrapper *wrapper = (__bridge KelpieVzVmWrapper *)vm;
    dispatch_semaphore_t sema = dispatch_semaphore_create(0);
    __block NSError *startError = nil;

    dispatch_async(wrapper.queue, ^{
        [wrapper.vm startWithCompletionHandler:^(NSError * _Nullable errorOrNil) {
            startError = errorOrNil;
            dispatch_semaphore_signal(sema);
        }];
    });

    dispatch_semaphore_wait(sema, DISPATCH_TIME_FOREVER);

    if (startError != nil) {
        NSString *message = [NSString stringWithFormat:@"VZ start failed: %@ (code: %ld, domain: %@)",
                             startError.localizedDescription,
                             (long)startError.code,
                             startError.domain];
        kelpie_vz_set_error(error_out, message);
        return -1;
    }
    return 0;
}

int kelpie_vz_vm_stop(KelpieVzVmHandle *vm, char **error_out) {
    KelpieVzVmWrapper *wrapper = (__bridge KelpieVzVmWrapper *)vm;
    if (@available(macos 12.0, *)) {
        int result = kelpie_vz_run_vm_op(wrapper, ^(void (^completion)(NSError *)) {
            [wrapper.vm stopWithCompletionHandler:^(NSError * _Nullable errorOrNil) {
                completion(errorOrNil);
            }];
        });
        if (result != 0) {
            kelpie_vz_set_error(error_out, @"failed to stop VZ virtual machine");
        }
        return result;
    }
    kelpie_vz_set_error(error_out, @"stop requires macOS 12 or newer");
    return -1;
}

int kelpie_vz_vm_pause(KelpieVzVmHandle *vm, char **error_out) {
    KelpieVzVmWrapper *wrapper = (__bridge KelpieVzVmWrapper *)vm;
    int result = kelpie_vz_run_vm_op(wrapper, ^(void (^completion)(NSError *)) {
        [wrapper.vm pauseWithCompletionHandler:^(NSError * _Nullable errorOrNil) {
            completion(errorOrNil);
        }];
    });
    if (result != 0) {
        kelpie_vz_set_error(error_out, @"failed to pause VZ virtual machine");
    }
    return result;
}

int kelpie_vz_vm_resume(KelpieVzVmHandle *vm, char **error_out) {
    KelpieVzVmWrapper *wrapper = (__bridge KelpieVzVmWrapper *)vm;
    int result = kelpie_vz_run_vm_op(wrapper, ^(void (^completion)(NSError *)) {
        [wrapper.vm resumeWithCompletionHandler:^(NSError * _Nullable errorOrNil) {
            completion(errorOrNil);
        }];
    });
    if (result != 0) {
        kelpie_vz_set_error(error_out, @"failed to resume VZ virtual machine");
    }
    return result;
}

int kelpie_vz_vm_save_state(KelpieVzVmHandle *vm, const char *path, char **error_out) {
    KelpieVzVmWrapper *wrapper = (__bridge KelpieVzVmWrapper *)vm;
    if (path == NULL) {
        kelpie_vz_set_error(error_out, @"snapshot path is required");
        return -1;
    }
#if defined(__arm64__)
    if (@available(macos 14.0, *)) {
        NSString *pathString = [NSString stringWithUTF8String:path];
        NSURL *url = [NSURL fileURLWithPath:pathString];
        int result = kelpie_vz_run_vm_op(wrapper, ^(void (^completion)(NSError *)) {
            [wrapper.vm saveMachineStateToURL:url completionHandler:^(NSError * _Nullable errorOrNil) {
                completion(errorOrNil);
            }];
        });
        if (result != 0) {
            kelpie_vz_set_error(error_out, @"failed to save VZ virtual machine state");
        }
        return result;
    }
#endif
    kelpie_vz_set_error(error_out, @"saveMachineState requires macOS 14 on Apple Silicon");
    return -1;
}

int kelpie_vz_vm_restore_state(KelpieVzVmHandle *vm, const char *path, char **error_out) {
    KelpieVzVmWrapper *wrapper = (__bridge KelpieVzVmWrapper *)vm;
    if (path == NULL) {
        kelpie_vz_set_error(error_out, @"snapshot path is required");
        return -1;
    }
#if defined(__arm64__)
    if (@available(macos 14.0, *)) {
        NSString *pathString = [NSString stringWithUTF8String:path];
        NSURL *url = [NSURL fileURLWithPath:pathString];
        int result = kelpie_vz_run_vm_op(wrapper, ^(void (^completion)(NSError *)) {
            [wrapper.vm restoreMachineStateFromURL:url completionHandler:^(NSError * _Nullable errorOrNil) {
                completion(errorOrNil);
            }];
        });
        if (result != 0) {
            kelpie_vz_set_error(error_out, @"failed to restore VZ virtual machine state");
        }
        return result;
    }
#endif
    kelpie_vz_set_error(error_out, @"restoreMachineState requires macOS 14 on Apple Silicon");
    return -1;
}

int kelpie_vz_vm_connect_vsock(KelpieVzVmHandle *vm, uint32_t port, char **error_out) {
    if (vm == NULL) {
        kelpie_vz_set_error(error_out, @"vm handle is null");
        return -1;
    }

    KelpieVzVmWrapper *wrapper = (__bridge KelpieVzVmWrapper *)vm;
    dispatch_semaphore_t sema = dispatch_semaphore_create(0);
    __block VZVirtioSocketConnection *connection = nil;
    __block NSError *connectError = nil;

    dispatch_async(wrapper.queue, ^{
        [wrapper.socketDevice connectToPort:port completionHandler:^(VZVirtioSocketConnection * _Nullable conn, NSError * _Nullable error) {
            connection = conn;
            connectError = error;
            dispatch_semaphore_signal(sema);
        }];
    });

    dispatch_semaphore_wait(sema, DISPATCH_TIME_FOREVER);

    if (connectError != nil || connection == nil) {
        NSString *message = connectError ? connectError.localizedDescription : @"failed to connect vsock";
        kelpie_vz_set_error(error_out, message);
        return -1;
    }

    int fd = connection.fileDescriptor;
    if (fd < 0) {
        kelpie_vz_set_error(error_out, @"invalid vsock file descriptor");
        return -1;
    }

    NSNumber *key = [NSNumber numberWithInt:fd];
    wrapper.connections[key] = connection;

    return fd;
}

int kelpie_vz_vm_close_vsock(KelpieVzVmHandle *vm, int fd, char **error_out) {
    if (vm == NULL) {
        kelpie_vz_set_error(error_out, @"vm handle is null");
        return -1;
    }

    KelpieVzVmWrapper *wrapper = (__bridge KelpieVzVmWrapper *)vm;
    NSNumber *key = [NSNumber numberWithInt:fd];
    VZVirtioSocketConnection *connection = wrapper.connections[key];
    if (connection == nil) {
        kelpie_vz_set_error(error_out, @"vsock connection not found");
        return -1;
    }

    [connection close];
    [wrapper.connections removeObjectForKey:key];
    return 0;
}

void kelpie_vz_string_free(char *string) {
    if (string != NULL) {
        free(string);
    }
}
