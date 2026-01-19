//! Sandbox Isolation Probe Tests
//!
//! These tests probe the actual isolation capabilities of ProcessSandbox
//! to understand exactly what is and isn't sandboxed.

use kelpie_sandbox::{ExecOptions, ProcessSandbox, Sandbox, SandboxConfig, SandboxError};
use std::env;
use std::fs;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

fn test_config() -> SandboxConfig {
    // Use unique directory per test to avoid conflicts when running in parallel
    let unique_id = TEST_COUNTER.fetch_add(1, Ordering::SeqCst);
    let tmp_dir = env::temp_dir().join(format!(
        "kelpie-sandbox-test-{}-{}",
        std::process::id(),
        unique_id
    ));
    fs::create_dir_all(&tmp_dir).expect("Failed to create temp dir");
    SandboxConfig::default().with_workdir(tmp_dir.to_string_lossy())
}

fn cleanup_test_dir(config: &SandboxConfig) {
    let _ = fs::remove_dir_all(&config.workdir);
}

fn is_op_not_permitted(err: &SandboxError) -> bool {
    matches!(
        err,
        SandboxError::ExecFailed { reason, .. } if reason.contains("Operation not permitted")
    )
}

// =============================================================================
// ENVIRONMENT ISOLATION TESTS
// =============================================================================

#[tokio::test]
async fn test_isolation_env_cleared() {
    let config = test_config();
    let mut sandbox = ProcessSandbox::new(config.clone());
    sandbox.start().await.unwrap();

    // Use 'env' command which should be more universally available
    // Check if HOME is present in environment
    let output = sandbox
        .exec_simple("/bin/sh", &["-c", "env | grep HOME || echo 'HOME_NOT_SET'"])
        .await
        .unwrap();

    println!(
        "[ENV ISOLATION] env output: {:?}",
        output.stdout_string().trim()
    );

    // The sandbox clears environment - HOME should not be passed through
    let home_cleared = output.stdout_string().contains("HOME_NOT_SET")
        || !output.stdout_string().contains("HOME=");
    println!("[ENV ISOLATION] HOME var cleared: {}", home_cleared);
    assert!(home_cleared, "HOME environment variable should be cleared");

    // Check if PATH is the controlled one
    let output = sandbox
        .exec_simple("/bin/sh", &["-c", "echo $PATH"])
        .await
        .unwrap();
    let path = output.stdout_string();
    let path = path.trim();
    println!("[ENV ISOLATION] PATH value: {:?}", path);

    // The sandbox should only have PATH=/usr/local/bin:/usr/bin:/bin
    assert!(output.is_success());
    assert_eq!(path, "/usr/local/bin:/usr/bin:/bin");

    cleanup_test_dir(&config);
}

#[tokio::test]
async fn test_isolation_env_injection() {
    let config = test_config()
        .with_env("SANDBOX_SECRET", "test123")
        .with_env("CUSTOM_VAR", "custom_value");
    let mut sandbox = ProcessSandbox::new(config.clone());
    sandbox.start().await.unwrap();

    // Custom env vars should be available
    let output = sandbox
        .exec_simple("/bin/sh", &["-c", "echo $SANDBOX_SECRET"])
        .await
        .unwrap();
    println!(
        "[ENV INJECTION] SANDBOX_SECRET: {:?}",
        output.stdout_string().trim()
    );
    assert!(output.is_success());
    assert_eq!(output.stdout_string().trim(), "test123");

    let output = sandbox
        .exec_simple("/bin/sh", &["-c", "echo $CUSTOM_VAR"])
        .await
        .unwrap();
    assert_eq!(output.stdout_string().trim(), "custom_value");

    cleanup_test_dir(&config);
}

// =============================================================================
// FILESYSTEM ISOLATION TESTS
// =============================================================================

#[tokio::test]
async fn test_isolation_workdir_restriction() {
    let config = test_config();
    let mut sandbox = ProcessSandbox::new(config.clone());
    sandbox.start().await.unwrap();

    // Check current directory
    let output = sandbox.exec_simple("/bin/pwd", &[]).await.unwrap();
    let cwd = output.stdout_string().trim().to_string();
    println!("[WORKDIR] Current dir: {}", cwd);

    // On macOS /var is symlinked to /private/var, so normalize
    let normalized_cwd = cwd.replace("/private", "");
    let normalized_workdir = config.workdir.replace("/private", "");
    assert_eq!(normalized_cwd, normalized_workdir);

    cleanup_test_dir(&config);
}

#[tokio::test]
async fn test_isolation_can_escape_workdir() {
    let config = test_config();
    let mut sandbox = ProcessSandbox::new(config.clone());
    sandbox.start().await.unwrap();

    // Test 1: Can we cd to parent directory?
    let output = sandbox
        .exec_simple("/bin/sh", &["-c", "cd .. && /bin/pwd"])
        .await
        .unwrap();
    let parent_dir = output.stdout_string().trim().to_string();
    println!("[ESCAPE TEST] cd .. && pwd: {:?}", parent_dir);
    // ProcessSandbox does NOT prevent this - it's just a working directory, not a chroot
    assert!(output.is_success(), "Can navigate to parent directory");

    // Test 2: Can we access root filesystem?
    let output = sandbox
        .exec_simple("/bin/sh", &["-c", "/bin/ls / | head -5"])
        .await
        .unwrap();
    println!(
        "[ESCAPE TEST] ls /: success={}, has output={}",
        output.is_success(),
        !output.stdout_string().is_empty()
    );
    assert!(output.is_success(), "Can list root filesystem");

    // Test 3: Can we read /etc/passwd?
    let output = sandbox
        .exec_simple("/bin/sh", &["-c", "/bin/cat /etc/passwd | /usr/bin/wc -l"])
        .await
        .unwrap();
    println!(
        "[ESCAPE TEST] cat /etc/passwd: success={}, lines={}",
        output.is_success(),
        output.stdout_string().trim()
    );
    assert!(output.is_success(), "Can read /etc/passwd");

    // Test 4: Can we read home directory?
    let home = env::var("HOME").unwrap_or_default();
    if !home.is_empty() {
        let output = sandbox
            .exec_simple("/bin/sh", &["-c", &format!("/bin/ls {} | head -3", home)])
            .await
            .unwrap();
        println!("[ESCAPE TEST] ls $HOME: success={}", output.is_success());
    }

    cleanup_test_dir(&config);
}

#[tokio::test]
async fn test_isolation_file_creation_outside_workdir() {
    let config = test_config();
    let mut sandbox = ProcessSandbox::new(config.clone());
    sandbox.start().await.unwrap();

    // Try to create a file in /tmp (outside workdir)
    let unique_id = TEST_COUNTER.fetch_add(1, Ordering::SeqCst);
    let test_file = format!(
        "/tmp/kelpie-escape-test-{}-{}",
        std::process::id(),
        unique_id
    );
    let output = sandbox
        .exec_simple(
            "/bin/sh",
            &["-c", &format!("echo 'escaped' > {}", test_file)],
        )
        .await
        .unwrap();
    println!(
        "[FILE ESCAPE] Write to /tmp: success={}",
        output.is_success()
    );

    // Check if file was actually created
    let exists = std::path::Path::new(&test_file).exists();
    println!("[FILE ESCAPE] File exists outside workdir: {}", exists);

    // IMPORTANT: This demonstrates ProcessSandbox does NOT restrict filesystem access
    assert!(
        exists,
        "ProcessSandbox allows file creation outside workdir (no filesystem isolation)"
    );

    // Clean up
    let _ = fs::remove_file(&test_file);

    cleanup_test_dir(&config);
}

// =============================================================================
// NETWORK ISOLATION TESTS
// =============================================================================

#[tokio::test]
async fn test_isolation_network_access() {
    let config = test_config();
    let mut sandbox = ProcessSandbox::new(config.clone());
    sandbox.start().await.unwrap();

    // Test 1: Can we access network configuration files?
    let output = sandbox
        .exec(
            "/bin/sh",
            &["-c", "/bin/cat /etc/resolv.conf 2>&1 | head -3"],
            ExecOptions::new().with_timeout(Duration::from_millis(3000)),
        )
        .await
        .unwrap();
    println!(
        "[NETWORK] DNS config accessible: success={}",
        output.is_success()
    );

    // Test 2: Check if we can see network interfaces
    #[cfg(target_os = "macos")]
    {
        let output = sandbox
            .exec(
                "/sbin/ifconfig",
                &["-a"],
                ExecOptions::new().with_timeout(Duration::from_millis(2000)),
            )
            .await
            .unwrap();
        let has_interfaces = output.is_success() && output.stdout_string().contains("en0");
        println!("[NETWORK] Can see network interfaces: {}", has_interfaces);
    }

    #[cfg(target_os = "linux")]
    {
        let output = sandbox
            .exec(
                "/bin/sh",
                &["-c", "/sbin/ip addr 2>/dev/null || /sbin/ifconfig -a"],
                ExecOptions::new().with_timeout(Duration::from_millis(2000)),
            )
            .await
            .unwrap();
        println!(
            "[NETWORK] Can see network interfaces: {}",
            output.is_success()
        );
    }

    cleanup_test_dir(&config);
}

// =============================================================================
// PROCESS/RESOURCE ISOLATION TESTS
// =============================================================================

#[tokio::test]
async fn test_isolation_can_see_host_processes() {
    let config = test_config();
    let mut sandbox = ProcessSandbox::new(config.clone());
    sandbox.start().await.unwrap();

    // Can we see host processes?
    let output = match sandbox.exec_simple("/bin/ps", &["aux"]).await {
        Ok(output) => output,
        Err(err) => {
            if is_op_not_permitted(&err) {
                println!("[PROCESS] /bin/ps blocked by sandbox/host policy; skipping");
                cleanup_test_dir(&config);
                return;
            }
            panic!("unexpected /bin/ps failure: {}", err);
        }
    };
    let process_count = output.stdout_string().lines().count();
    println!("[PROCESS] Can see {} processes on host", process_count);

    // Should be able to see many processes (not isolated)
    assert!(
        process_count > 5,
        "Can see multiple host processes (no process namespace isolation)"
    );

    cleanup_test_dir(&config);
}

#[tokio::test]
async fn test_isolation_can_fork_processes() {
    let config = test_config();
    let mut sandbox = ProcessSandbox::new(config.clone());
    sandbox.start().await.unwrap();

    // Can we fork many processes?
    let output = sandbox
        .exec_simple(
            "/bin/sh",
            &["-c", "for i in 1 2 3 4 5; do echo $i & done; wait"],
        )
        .await
        .unwrap();
    println!("[FORK] Can fork processes: success={}", output.is_success());
    println!("[FORK] Output: {:?}", output.stdout_string());
    assert!(output.is_success());

    cleanup_test_dir(&config);
}

// =============================================================================
// TIMEOUT ENFORCEMENT TESTS
// =============================================================================

#[tokio::test]
async fn test_isolation_timeout_enforcement() {
    let config = test_config();
    let mut sandbox = ProcessSandbox::new(config.clone());
    sandbox.start().await.unwrap();

    // Command that takes longer than timeout
    let start = std::time::Instant::now();
    let output = sandbox
        .exec(
            "/bin/sleep",
            &["10"],
            ExecOptions::new().with_timeout(Duration::from_millis(500)),
        )
        .await
        .unwrap();
    let elapsed = start.elapsed();

    println!(
        "[TIMEOUT] Command killed: signal={:?}",
        output.status.signal
    );
    println!(
        "[TIMEOUT] Elapsed: {:?}ms (should be ~500ms, not 10s)",
        elapsed.as_millis()
    );

    assert!(
        elapsed.as_millis() < 2000,
        "Timeout should have killed process quickly"
    );
    assert_eq!(
        output.status.signal,
        Some(9),
        "Process should be killed with SIGKILL"
    );

    cleanup_test_dir(&config);
}

#[tokio::test]
async fn test_isolation_output_size_limit() {
    let config = test_config();
    let mut sandbox = ProcessSandbox::new(config.clone());
    sandbox.start().await.unwrap();

    // Generate a lot of output
    let output = sandbox
        .exec(
            "/bin/sh",
            &["-c", "/usr/bin/yes | head -n 100000"],
            ExecOptions::new().with_max_output(1024),
        )
        .await
        .unwrap();

    println!("[OUTPUT LIMIT] stdout bytes: {}", output.stdout.len());
    println!("[OUTPUT LIMIT] truncated: {}", output.stdout_truncated);

    assert!(
        output.stdout.len() <= 1024,
        "Output should be limited to 1024 bytes"
    );
    assert!(
        output.stdout_truncated,
        "Output should be marked as truncated"
    );

    cleanup_test_dir(&config);
}

// =============================================================================
// DANGEROUS OPERATIONS TESTS
// =============================================================================

#[tokio::test]
async fn test_isolation_cannot_kill_host_processes() {
    let config = test_config();
    let mut sandbox = ProcessSandbox::new(config.clone());
    sandbox.start().await.unwrap();

    // Try to kill init (pid 1) - should fail due to permissions
    let output = sandbox
        .exec_simple(
            "/bin/sh",
            &["-c", "kill -0 1 2>&1 || echo 'permission_denied'"],
        )
        .await
        .unwrap();
    println!("[DANGEROUS] kill -0 1: {:?}", output.stdout_string().trim());

    // On normal user, this should fail with permission denied
    let stdout = output.stdout_string();
    assert!(
        stdout.contains("permission")
            || stdout.contains("denied")
            || stdout.contains("Not permitted")
            || stdout.contains("Operation not permitted")
            || !output.is_success(),
        "Should not be able to signal init process"
    );

    cleanup_test_dir(&config);
}

#[tokio::test]
async fn test_isolation_cannot_access_kernel_modules() {
    let config = test_config();
    let mut sandbox = ProcessSandbox::new(config.clone());
    sandbox.start().await.unwrap();

    // Try to read kernel info (Linux) or system info (macOS)
    #[cfg(target_os = "linux")]
    {
        let output = sandbox
            .exec_simple("/bin/sh", &["-c", "/bin/cat /proc/kallsyms 2>&1 | head -1"])
            .await
            .unwrap();
        println!(
            "[DANGEROUS] /proc/kallsyms: {:?}",
            output.stdout_string().trim()
        );
    }

    #[cfg(target_os = "macos")]
    {
        // macOS doesn't have /proc, check system integrity
        let output = sandbox
            .exec_simple(
                "/bin/sh",
                &["-c", "/usr/bin/csrutil status 2>&1 || echo 'not_available'"],
            )
            .await
            .unwrap();
        println!(
            "[DANGEROUS] SIP status: {:?}",
            output.stdout_string().trim()
        );
    }

    cleanup_test_dir(&config);
}

// =============================================================================
// SUMMARY TEST - Run all probes and report
// =============================================================================

#[tokio::test]
async fn test_isolation_summary() {
    println!("\n");
    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║           SANDBOX ISOLATION CAPABILITY REPORT                 ║");
    println!("╚══════════════════════════════════════════════════════════════╝");

    let config = test_config();
    let mut sandbox = ProcessSandbox::new(config.clone());
    sandbox.start().await.unwrap();

    println!("\n┌─ WHAT IS SANDBOXED ─────────────────────────────────────────┐");

    // 1. Environment variables
    let output = sandbox
        .exec_simple("/bin/sh", &["-c", "env | grep HOME || echo 'HOME_NOT_SET'"])
        .await
        .unwrap();
    let env_cleared = output.stdout_string().contains("HOME_NOT_SET")
        || !output.stdout_string().contains("HOME=");
    println!("│ ✓ Environment variables cleared: {}", env_cleared);

    // 2. PATH controlled
    let output = sandbox
        .exec_simple("/bin/sh", &["-c", "echo $PATH"])
        .await
        .unwrap();
    let path_controlled = output.stdout_string().trim() == "/usr/local/bin:/usr/bin:/bin";
    println!("│ ✓ PATH is controlled: {}", path_controlled);

    // 3. Timeout enforcement
    let start = std::time::Instant::now();
    let output = sandbox
        .exec(
            "/bin/sleep",
            &["5"],
            ExecOptions::new().with_timeout(Duration::from_millis(100)),
        )
        .await
        .unwrap();
    let timeout_works = start.elapsed().as_millis() < 1000 && output.status.signal == Some(9);
    println!("│ ✓ Timeout enforcement works: {}", timeout_works);

    // 4. Output limits
    let output = sandbox
        .exec(
            "/usr/bin/yes",
            &[],
            ExecOptions::new()
                .with_timeout(Duration::from_millis(100))
                .with_max_output(100),
        )
        .await
        .unwrap();
    let output_limited = output.stdout.len() <= 100;
    println!("│ ✓ Output size limits work: {}", output_limited);

    // 5. Stdin disabled
    println!("│ ✓ Stdin piped to null: true (by design)");

    println!("└────────────────────────────────────────────────────────────────┘");

    println!("\n┌─ WHAT IS NOT SANDBOXED (LIMITATIONS) ─────────────────────────┐");

    // 1. Can escape workdir
    let output = sandbox
        .exec_simple("/bin/sh", &["-c", "/bin/ls / | head -3"])
        .await
        .unwrap();
    let can_access_root = output.is_success() && !output.stdout_string().is_empty();
    println!(
        "│ ✗ Filesystem access: {} (can ls /)",
        if can_access_root {
            "UNRESTRICTED"
        } else {
            "restricted"
        }
    );

    // 2. Can read sensitive files
    let output = sandbox
        .exec_simple("/bin/sh", &["-c", "/bin/cat /etc/passwd | head -1"])
        .await
        .unwrap();
    let can_read_passwd = output.is_success();
    println!("│ ✗ Can read /etc/passwd: {}", can_read_passwd);

    // 3. Can see processes
    match sandbox.exec_simple("/bin/ps", &["aux"]).await {
        Ok(output) => {
            let proc_count = output.stdout_string().lines().count();
            println!(
                "│ ✗ Process visibility: can see {} host processes",
                proc_count
            );
        }
        Err(err) => {
            if is_op_not_permitted(&err) {
                println!("│ ✗ Process visibility: blocked by sandbox/host policy");
            } else {
                panic!("unexpected /bin/ps failure: {}", err);
            }
        }
    }

    // 4. Network access (check if we can reach DNS config)
    let output = sandbox
        .exec_simple(
            "/bin/sh",
            &["-c", "/bin/cat /etc/resolv.conf 2>&1 | head -1"],
        )
        .await
        .unwrap();
    let has_network_config = output.is_success();
    println!("│ ✗ Network config accessible: {}", has_network_config);

    // 5. Can write outside workdir
    let unique_id = TEST_COUNTER.fetch_add(1, Ordering::SeqCst);
    let test_file = format!("/tmp/kelpie-test-{}-{}", std::process::id(), unique_id);
    let _output = sandbox
        .exec_simple("/bin/sh", &["-c", &format!("echo test > {}", test_file)])
        .await
        .unwrap();
    let can_write = std::path::Path::new(&test_file).exists();
    let _ = fs::remove_file(&test_file);
    println!("│ ✗ Can write to /tmp: {}", can_write);

    println!("└────────────────────────────────────────────────────────────────┘");

    println!("\n┌─ SANDBOX TYPE COMPARISON ───────────────────────────────────────┐");
    println!("│                                                                  │");
    println!("│  ProcessSandbox (current):                                       │");
    println!("│    ✓ Environment isolation                                       │");
    println!("│    ✓ Timeout enforcement                                         │");
    println!("│    ✓ Output size limits                                          │");
    println!("│    ✓ Working directory control                                   │");
    println!("│    ✗ No filesystem isolation (not a chroot)                      │");
    println!("│    ✗ No network isolation                                        │");
    println!("│    ✗ No process namespace isolation                              │");
    println!("│                                                                  │");
    println!("│  FirecrackerSandbox (Linux + KVM required):                      │");
    println!("│    ✓ Full VM isolation (hardware level)                          │");
    println!("│    ✓ Filesystem isolation                                        │");
    println!("│    ✓ Network isolation                                           │");
    println!("│    ✓ Process isolation                                           │");
    println!("│    ✓ Snapshot/restore capabilities                               │");
    println!("│                                                                  │");
    println!("└──────────────────────────────────────────────────────────────────┘");

    // Final assertions
    assert!(env_cleared, "Environment should be cleared");
    assert!(path_controlled, "PATH should be controlled");
    assert!(timeout_works, "Timeout should work");
    assert!(output_limited, "Output limits should work");

    cleanup_test_dir(&config);
}
