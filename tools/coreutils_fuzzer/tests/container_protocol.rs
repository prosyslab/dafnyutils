//! Exercise the private container-runner boundary through the compiled CLI.

use serde_json::json;
use std::io::Write;
use std::process::{Command, Stdio};

// A host cannot accidentally send an unversioned or future request to the privileged runner.
#[test]
fn container_runner_rejects_unknown_protocol_before_fixture_changes() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_coreutils_fuzzer"))
        .arg("__container-run-case")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let request = json!({
        "protocol_version": 999,
        "util": "cat",
        "reference": {"kind": "native", "path": "/bin/cat"},
        "dut": {"kind": "native", "path": "/bin/cat"},
        "case": {"argv": ["-"], "fixture": {"directories": [], "files": [], "symlinks": [], "hardlinks": []}, "stdin": [], "cwd": "."},
        "seed": 1,
        "child_iteration": 0,
        "work_iteration": 0,
        "workdir_mode": "per-iteration",
        "process_timeout_seconds": 1,
        "read_only_time_anchor_seconds": null,
        "process_umask": 18,
        "target_uid": 1000,
        "target_gid": 1000
    });
    child
        .stdin
        .take()
        .unwrap()
        .write_all(&serde_json::to_vec(&request).unwrap())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains("unsupported container protocol version 999"),
        "{stderr}"
    );
}
