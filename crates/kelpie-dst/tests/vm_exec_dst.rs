//! DST tests for VmInstance exec behavior
//!
//! TigerStyle: Simulation-first with fault injection and determinism checks.

use kelpie_core::{Error, Result};
use kelpie_dst::{FaultConfig, FaultType, SimConfig, Simulation};
use kelpie_vm::{VmConfig, VmError, VmInstance};

fn vm_config() -> VmConfig {
    VmConfig::builder()
        .vcpu_count(2)
        .memory_mib(512)
        .root_disk("/tmp/kelpie-rootfs")
        .build()
        .expect("valid vm config")
}

#[test]
fn test_vm_exec_roundtrip_no_faults() -> Result<()> {
    let sim = Simulation::new(SimConfig::new(101));
    sim.run(|env| async move {
        let mut vm = env
            .vm_factory
            .create_vm(vm_config())
            .await
            .map_err(|e| Error::Internal {
                message: format!("Failed to create VM: {}", e),
            })?;
        vm.start().await.map_err(|e| Error::Internal {
            message: format!("Failed to start VM: {}", e),
        })?;
        let output = vm
            .exec("echo", &["hello", "world"])
            .await
            .map_err(|e| Error::Internal {
                message: format!("Failed to exec: {}", e),
            })?;
        assert!(output.success());
        assert_eq!(output.stdout_str(), "sim:0:echo:hello world");
        Ok(())
    })
    .map_err(|e| Error::Internal {
        message: format!("simulation failed: {}", e),
    })
}

#[test]
fn test_vm_exec_with_faults() -> Result<()> {
    let sim = Simulation::new(SimConfig::new(202))
        .with_fault(FaultConfig::new(FaultType::SandboxExecFail, 1.0).with_filter("vm_exec"));

    sim.run(|env| async move {
        let mut vm = env
            .vm_factory
            .create_vm(vm_config())
            .await
            .map_err(|e| Error::Internal {
                message: format!("Failed to create VM: {}", e),
            })?;
        vm.start().await.map_err(|e| Error::Internal {
            message: format!("Failed to start VM: {}", e),
        })?;
        let result = vm.exec("echo", &["fail"]).await;
        match result {
            Err(VmError::ExecFailed { .. }) => Ok(()),
            other => Err(Error::Internal {
                message: format!("expected exec failure, got {:?}", other),
            }),
        }
    })
    .map_err(|e| Error::Internal {
        message: format!("simulation failed: {}", e),
    })
}

#[test]
fn test_vm_exec_determinism() -> Result<()> {
    let sim = Simulation::new(SimConfig::new(303));
    sim.run(|env| async move {
        let mut vm = env
            .vm_factory
            .create_vm(vm_config())
            .await
            .map_err(|e| Error::Internal {
                message: format!("Failed to create VM: {}", e),
            })?;
        vm.start().await.map_err(|e| Error::Internal {
            message: format!("Failed to start VM: {}", e),
        })?;
        let first = vm
            .exec("date", &["+%s"])
            .await
            .map_err(|e| Error::Internal {
                message: format!("Failed to exec: {}", e),
            })?;
        let second = vm
            .exec("date", &["+%s"])
            .await
            .map_err(|e| Error::Internal {
                message: format!("Failed to exec: {}", e),
            })?;
        assert_eq!(first.stdout_str(), "sim:0:date:+%s");
        assert_eq!(second.stdout_str(), "sim:1:date:+%s");
        Ok(())
    })
    .map_err(|e| Error::Internal {
        message: format!("simulation failed: {}", e),
    })
}
