//! DST tests for Firecracker snapshot metadata and blob versioning
//!
//! TigerStyle: Deterministic metadata encoding and strict version checks.

use bytes::Bytes;
use chrono::{TimeZone, Utc};
use kelpie_core::teleport::{
    TeleportSnapshotError, VmSnapshotBlob, TELEPORT_SNAPSHOT_FORMAT_VERSION,
};
use kelpie_dst::{SimConfig, Simulation};
use kelpie_sandbox::{Architecture, SnapshotKind, SnapshotMetadata, SNAPSHOT_FORMAT_VERSION};

fn build_firecracker_metadata() -> SnapshotMetadata {
    SnapshotMetadata {
        id: "snap-firecracker-1".to_string(),
        sandbox_id: "fc-sandbox-1".to_string(),
        version: SNAPSHOT_FORMAT_VERSION,
        created_at: Utc
            .timestamp_millis_opt(1_700_000_000_000)
            .single()
            .expect("valid timestamp"),
        kind: SnapshotKind::Teleport,
        architecture: Architecture::X86_64,
        base_image_version: "firecracker-1.8.0".to_string(),
        memory_bytes: 128 * 1024 * 1024,
        disk_bytes: 2 * 1024 * 1024 * 1024,
        includes_memory: true,
        includes_disk: true,
        description: Some("firecracker teleport snapshot".to_string()),
    }
}

#[test]
fn test_firecracker_snapshot_metadata_roundtrip() {
    let config = SimConfig::new(8101);
    let result = Simulation::new(config).run(|_env| async move {
        let metadata = build_firecracker_metadata();
        let metadata_bytes = serde_json::to_vec(&metadata).expect("serialize snapshot metadata");

        let blob = VmSnapshotBlob::encode(
            Bytes::from(metadata_bytes.clone()),
            Bytes::from_static(b"snapshot-state"),
            Bytes::from_static(b"snapshot-memory"),
        );
        let decoded = VmSnapshotBlob::decode(&blob).expect("decode snapshot blob");
        let decoded_meta: SnapshotMetadata =
            serde_json::from_slice(&decoded.metadata_bytes).expect("deserialize snapshot metadata");

        assert_eq!(decoded.metadata_bytes, Bytes::from(metadata_bytes));
        assert_eq!(decoded_meta.version, SNAPSHOT_FORMAT_VERSION);
        assert_eq!(decoded_meta.base_image_version, "firecracker-1.8.0");
        assert_eq!(decoded_meta.kind, SnapshotKind::Teleport);
        assert_eq!(decoded_meta.architecture, Architecture::X86_64);

        Ok(())
    });

    assert!(result.is_ok());
}

#[test]
fn test_firecracker_snapshot_blob_version_guard() {
    let config = SimConfig::new(8102);
    let result = Simulation::new(config).run(|_env| async move {
        let metadata = build_firecracker_metadata();
        let metadata_bytes = serde_json::to_vec(&metadata).expect("serialize snapshot metadata");
        let blob = VmSnapshotBlob::encode(
            Bytes::from(metadata_bytes),
            Bytes::from_static(b"snapshot-state"),
            Bytes::from_static(b"snapshot-memory"),
        );

        let version = TELEPORT_SNAPSHOT_FORMAT_VERSION + 1;
        let mut tampered = blob.to_vec();
        tampered[4..8].copy_from_slice(&version.to_le_bytes());
        let tampered = Bytes::from(tampered);

        let err = VmSnapshotBlob::decode(&tampered).expect_err("expected version mismatch");
        match err {
            TeleportSnapshotError::UnsupportedVersion { expected, actual } => {
                assert_eq!(expected, TELEPORT_SNAPSHOT_FORMAT_VERSION);
                assert_eq!(actual, TELEPORT_SNAPSHOT_FORMAT_VERSION + 1);
            }
            other => panic!("unexpected error: {}", other),
        }

        Ok(())
    });

    assert!(result.is_ok());
}
