#pragma once

#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct KelpieVzVmHandle KelpieVzVmHandle;

bool kelpie_vz_is_supported(void);

KelpieVzVmHandle *kelpie_vz_vm_create(const char *id,
                                      const char *kernel_path,
                                      const char *initrd_path,
                                      const char *rootfs_path,
                                      const char *boot_args,
                                      bool rootfs_readonly,
                                      uint32_t vcpu_count,
                                      uint64_t memory_mib,
                                      char **error_out);

void kelpie_vz_vm_free(KelpieVzVmHandle *vm);

int kelpie_vz_vm_start(KelpieVzVmHandle *vm, char **error_out);
int kelpie_vz_vm_stop(KelpieVzVmHandle *vm, char **error_out);
int kelpie_vz_vm_pause(KelpieVzVmHandle *vm, char **error_out);
int kelpie_vz_vm_resume(KelpieVzVmHandle *vm, char **error_out);
int kelpie_vz_vm_save_state(KelpieVzVmHandle *vm, const char *path, char **error_out);
int kelpie_vz_vm_restore_state(KelpieVzVmHandle *vm, const char *path, char **error_out);

int kelpie_vz_vm_connect_vsock(KelpieVzVmHandle *vm, uint32_t port, char **error_out);
int kelpie_vz_vm_close_vsock(KelpieVzVmHandle *vm, int fd, char **error_out);

void kelpie_vz_string_free(char *string);

#ifdef __cplusplus
}
#endif
