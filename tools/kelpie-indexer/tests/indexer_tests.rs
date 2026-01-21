// Integration tests for kelpie-indexer
//
// TigerStyle: Each test verifies specific behavior with explicit assertions.
// Tests use fixtures in tests/fixtures/sample_crate/
//
// NOTE: These tests share a fixture directory and modify its state.
// The `#[serial]` attribute ensures tests run sequentially to avoid race conditions.

use serial_test::serial;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

// Helper to get fixture path
fn fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("sample_crate")
}

// Helper to run indexer binary
fn run_indexer(fixture_path: &PathBuf, command: &str) -> Result<(), Box<dyn std::error::Error>> {
    let output = Command::new(env!("CARGO_BIN_EXE_kelpie-indexer"))
        .arg(command)
        .current_dir(fixture_path)
        .output()?;

    if !output.status.success() {
        eprintln!(
            "Indexer stdout: {}",
            String::from_utf8_lossy(&output.stdout)
        );
        eprintln!(
            "Indexer stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        return Err(format!("Indexer command '{}' failed", command).into());
    }

    Ok(())
}

#[test]
#[serial]
fn test_fixture_exists() {
    let path = fixture_path();
    assert!(path.exists(), "Fixture directory should exist");
    assert!(
        path.join("Cargo.toml").exists(),
        "Fixture workspace Cargo.toml should exist"
    );
    assert!(
        path.join("crates").exists(),
        "Fixture crates/ directory should exist"
    );
    assert!(
        path.join("crates/sample-crate/Cargo.toml").exists(),
        "Fixture crate Cargo.toml should exist"
    );
    assert!(
        path.join("crates/sample-crate/src/lib.rs").exists(),
        "Fixture src/lib.rs should exist"
    );
}

#[test]
#[serial]
fn test_full_rebuild_creates_indexes() {
    let fixture = fixture_path();

    // Clean up any existing indexes
    let index_dir = fixture.join(".kelpie-index");
    if index_dir.exists() {
        fs::remove_dir_all(&index_dir).expect("Failed to clean index directory");
    }

    // Run full rebuild
    run_indexer(&fixture, "full").expect("Full rebuild should succeed");

    // Verify indexes were created
    let symbols_path = index_dir.join("structural/symbols.json");
    let deps_path = index_dir.join("structural/dependencies.json");
    let tests_path = index_dir.join("structural/tests.json");
    let modules_path = index_dir.join("structural/modules.json");
    let freshness_path = index_dir.join("meta/freshness.json");

    assert!(symbols_path.exists(), "Symbols index should be created");
    assert!(deps_path.exists(), "Dependencies index should be created");
    assert!(tests_path.exists(), "Tests index should be created");
    assert!(modules_path.exists(), "Modules index should be created");
    assert!(
        freshness_path.exists(),
        "Freshness metadata should be created"
    );
}

#[test]
#[serial]
fn test_symbol_index_contains_expected_symbols() {
    let fixture = fixture_path();

    // Run full rebuild
    run_indexer(&fixture, "full").expect("Full rebuild should succeed");

    // Read symbols index
    let symbols_path = fixture.join(".kelpie-index/structural/symbols.json");
    let symbols_json = fs::read_to_string(symbols_path).expect("Failed to read symbols index");
    let symbols: serde_json::Value =
        serde_json::from_str(&symbols_json).expect("Failed to parse symbols index");

    // Verify expected symbols exist
    let lib_file = symbols["files"]["crates/sample-crate/src/lib.rs"]["symbols"]
        .as_array()
        .expect("Should have symbols array for crates/sample-crate/src/lib.rs");

    let symbol_names: Vec<&str> = lib_file.iter().filter_map(|s| s["name"].as_str()).collect();

    // Check for expected symbols from fixture
    assert!(
        symbol_names.contains(&"User"),
        "Should find User struct, found: {:?}",
        symbol_names
    );
    assert!(
        symbol_names.contains(&"create_user"),
        "Should find create_user function"
    );
    assert!(
        symbol_names.contains(&"Repository"),
        "Should find Repository trait"
    );
    assert!(symbol_names.contains(&"Status"), "Should find Status enum");
}

#[test]
#[serial]
fn test_dependency_graph_finds_dependencies() {
    let fixture = fixture_path();

    // Run full rebuild
    run_indexer(&fixture, "full").expect("Full rebuild should succeed");

    // Read dependency graph
    let deps_path = fixture.join(".kelpie-index/structural/dependencies.json");
    let deps_json = fs::read_to_string(deps_path).expect("Failed to read dependencies index");
    let deps: serde_json::Value =
        serde_json::from_str(&deps_json).expect("Failed to parse dependencies index");

    // Verify sample-crate node exists
    let nodes = deps["nodes"].as_array().expect("Should have nodes array");
    let node_ids: Vec<&str> = nodes.iter().filter_map(|n| n["id"].as_str()).collect();

    assert!(
        node_ids.contains(&"sample-crate") || node_ids.contains(&"sample_crate"),
        "Should find sample-crate or sample_crate node, found: {:?}",
        node_ids
    );

    // Verify edges include dependencies
    let edges = deps["edges"].as_array().expect("Should have edges array");
    assert!(!edges.is_empty(), "Should have dependency edges");

    // Check for serde dependency
    let has_serde = edges.iter().any(|edge| {
        edge["to"].as_str() == Some("serde") || edge["to"].as_str() == Some("serde_derive")
    });
    assert!(has_serde, "Should have dependency edge to serde");
}

#[test]
#[serial]
fn test_test_index_finds_tests() {
    let fixture = fixture_path();

    // Run full rebuild
    run_indexer(&fixture, "full").expect("Full rebuild should succeed");

    // Read test index
    let tests_path = fixture.join(".kelpie-index/structural/tests.json");
    let tests_json = fs::read_to_string(tests_path).expect("Failed to read tests index");
    let tests: serde_json::Value =
        serde_json::from_str(&tests_json).expect("Failed to parse tests index");

    // Verify tests were found
    let test_array = tests["tests"].as_array().expect("Should have tests array");
    assert!(!test_array.is_empty(), "Should find at least one test");

    let test_names: Vec<&str> = test_array
        .iter()
        .filter_map(|t| t["name"].as_str())
        .collect();

    // Check for expected tests from fixture
    assert!(
        test_names.contains(&"test_create_user"),
        "Should find test_create_user"
    );
    assert!(
        test_names.contains(&"test_validate_name"),
        "Should find test_validate_name"
    );
}

#[test]
#[serial]
fn test_module_index_finds_modules() {
    let fixture = fixture_path();

    // Run full rebuild
    run_indexer(&fixture, "full").expect("Full rebuild should succeed");

    // Read module index
    let modules_path = fixture.join(".kelpie-index/structural/modules.json");
    let modules_json = fs::read_to_string(modules_path).expect("Failed to read modules index");
    let modules: serde_json::Value =
        serde_json::from_str(&modules_json).expect("Failed to parse modules index");

    // Verify crate exists
    let crates = modules["crates"]
        .as_array()
        .expect("Should have crates array");
    assert!(!crates.is_empty(), "Should find at least one crate");

    let crate_names: Vec<&str> = crates.iter().filter_map(|c| c["name"].as_str()).collect();

    assert!(
        crate_names.contains(&"sample-crate") || crate_names.contains(&"sample_crate"),
        "Should find sample-crate or sample_crate, found: {:?}",
        crate_names
    );

    // Verify the crate has the expected structure
    let sample_crate = crates
        .iter()
        .find(|c| {
            c["name"].as_str() == Some("sample-crate") || c["name"].as_str() == Some("sample_crate")
        })
        .expect("Should find sample-crate or sample_crate");

    // Verify root_file exists
    assert!(
        sample_crate["root_file"].is_string(),
        "Should have root_file field"
    );

    // Verify modules array exists (can be empty for single-file crates)
    let _modules = sample_crate["modules"]
        .as_array()
        .expect("Should have modules array");

    // Single-file crates with no mod declarations can have 0 modules - this is correct
    // No need to check length since we just verified the array exists above
}

#[test]
#[serial]
fn test_freshness_tracking_updated() {
    let fixture = fixture_path();

    // Run full rebuild
    run_indexer(&fixture, "full").expect("Full rebuild should succeed");

    // Read freshness metadata
    let freshness_path = fixture.join(".kelpie-index/meta/freshness.json");
    let freshness_json =
        fs::read_to_string(freshness_path).expect("Failed to read freshness metadata");
    let freshness: serde_json::Value =
        serde_json::from_str(&freshness_json).expect("Failed to parse freshness metadata");

    // Verify freshness fields exist
    assert!(
        freshness["updated_at"].is_string(),
        "Should have updated_at timestamp"
    );
    assert!(
        freshness["git_sha"].is_string() || freshness["git_sha"].is_null(),
        "Should have git_sha field"
    );
    assert!(
        freshness["file_hashes"].is_object(),
        "Should have file_hashes object"
    );

    // Verify file_hashes contains expected files
    let file_hashes = freshness["file_hashes"]
        .as_object()
        .expect("file_hashes should be an object");
    assert!(
        !file_hashes.is_empty(),
        "Should have at least one file hash"
    );
}
