//! DST tests for VmInstance-based teleportation
//!
//! TigerStyle: Simulation-first testing with fault injection and determinism checks.

use bytes::Bytes;
use kelpie_core::{Error, Result};
use kelpie_dst::{
    Architecture, FaultConfig, FaultType, SimConfig, Simulation, TeleportPackage, VmSnapshotBlob,
};
use kelpie_vm::{VmConfig, VmInstance, VmSnapshot, VmSnapshotMetadata};

fn vm_config() -> VmConfig {
    VmConfig::builder()
        .vcpu_count(2)
        .memory_mib(512)
        .root_disk("/tmp/kelpie-rootfs")
        .build()
        .expect("valid vm config")
}

fn encode_vm_snapshot(snapshot: &VmSnapshot) -> Result<Bytes> {
    let metadata_bytes = serde_json::to_vec(&snapshot.metadata).map_err(|e| Error::Internal {
        message: format!("Failed to serialize snapshot metadata: {}", e),
    })?;
    Ok(VmSnapshotBlob::encode(
        Bytes::from(metadata_bytes),
        snapshot.data.clone(),
        Bytes::new(),
    ))
}

fn decode_vm_snapshot(blob: &Bytes) -> Result<VmSnapshot> {
    let decoded = VmSnapshotBlob::decode(blob).map_err(|e| Error::Internal {
        message: format!("Failed to decode snapshot blob: {}", e),
    })?;
    let metadata: VmSnapshotMetadata =
        serde_json::from_slice(&decoded.metadata_bytes).map_err(|e| Error::Internal {
            message: format!("Failed to deserialize snapshot metadata: {}", e),
        })?;
    VmSnapshot::new(metadata, decoded.snapshot_bytes).map_err(|e| Error::Internal {
        message: format!("Failed to rebuild snapshot: {}", e),
    })
}

async fn roundtrip(env: &kelpie_dst::SimEnvironment, i: u64) -> Result<bool> {
    let vm_config = vm_config();
    let mut vm = env
        .vm_factory
        .create_vm(vm_config.clone())
        .await
        .map_err(|e| Error::Internal {
            message: format!("Failed to create vm: {}", e),
        })?;
    vm.start().await.map_err(|e| Error::Internal {
        message: format!("Failed to start vm: {}", e),
    })?;

    let _ = vm
        .exec("echo", &["hello"])
        .await
        .map_err(|e| Error::Internal {
            message: format!("Failed to exec: {}", e),
        })?;

    let snapshot = vm.snapshot().await.map_err(|e| Error::Internal {
        message: format!("Failed to snapshot: {}", e),
    })?;
    let snapshot_blob = encode_vm_snapshot(&snapshot)?;

    let package = TeleportPackage::new(
        format!("vm-teleport-{}", i),
        format!("agent-{}", i),
        Architecture::Arm64,
        kelpie_dst::SnapshotKind::Teleport,
    )
    .with_vm_snapshot(snapshot_blob)
    .with_agent_state(Bytes::from(format!("agent-state-{}", i)))
    .with_base_image_version("1.0.0")
    .with_created_at(env.now_ms());

    let package_id = env
        .teleport_storage
        .upload(package)
        .await
        .map_err(|e| Error::Internal {
            message: format!("Failed to upload package: {}", e),
        })?;

    let downloaded = env
        .teleport_storage
        .download_for_restore(&package_id, Architecture::Arm64)
        .await
        .map_err(|e| Error::Internal {
            message: format!("Failed to download package: {}", e),
        })?;

    let snapshot_blob = downloaded
        .vm_snapshot
        .as_ref()
        .ok_or_else(|| Error::Internal {
            message: "Missing vm snapshot in package".to_string(),
        })?;
    let restored_snapshot = decode_vm_snapshot(snapshot_blob)?;

    let mut restored_vm =
        env.vm_factory
            .create_vm(vm_config)
            .await
            .map_err(|e| Error::Internal {
                message: format!("Failed to create restore vm: {}", e),
            })?;
    restored_vm
        .restore(&restored_snapshot)
        .await
        .map_err(|e| Error::Internal {
            message: format!("Failed to restore vm: {}", e),
        })?;

    Ok(true)
}

#[test]
fn test_vm_teleport_roundtrip_no_faults() {
    let config = SimConfig::new(7001);
    let result = Simulation::new(config).run(|env| async move { roundtrip(&env, 1).await });

    assert!(result.is_ok());
}

#[test]
fn test_vm_teleport_with_faults() {
    let config = SimConfig::new(7002);
    let result = Simulation::new(config)
        .with_fault(FaultConfig::new(FaultType::SnapshotCreateFail, 0.2))
        .with_fault(FaultConfig::new(FaultType::SnapshotCorruption, 0.1))
        .with_fault(FaultConfig::new(FaultType::SnapshotRestoreFail, 0.1))
        .with_fault(FaultConfig::new(FaultType::TeleportUploadFail, 0.2))
        .with_fault(FaultConfig::new(FaultType::TeleportDownloadFail, 0.2))
        .run(|env| async move {
            let mut successes = 0;
            let mut failures = 0;

            for i in 0..20 {
                match roundtrip(&env, i).await {
                    Ok(_) => successes += 1,
                    Err(_) => failures += 1,
                }
            }

            // At least one success or one failure is acceptable, but no panics.
            assert!(successes + failures == 20);
            Ok(())
        });

    assert!(result.is_ok());
}

#[test]
fn test_vm_teleport_determinism() {
    fn run(seed: u64) -> Vec<bool> {
        let config = SimConfig::new(seed);
        Simulation::new(config)
            .with_fault(FaultConfig::new(FaultType::SnapshotCreateFail, 0.2))
            .with_fault(FaultConfig::new(FaultType::TeleportUploadFail, 0.2))
            .run(|env| async move {
                let mut outcomes = Vec::new();
                for i in 0..10 {
                    outcomes.push(roundtrip(&env, i).await.is_ok());
                }
                Ok(outcomes)
            })
            .expect("simulation should run")
    }

    let result1 = run(7010);
    let result2 = run(7010);

    assert_eq!(result1, result2);
}
