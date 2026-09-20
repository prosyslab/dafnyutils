//! Compiled CLI infrastructure markers preserve setup failures and ordinary error fallback.

use std::io::Write;
use std::process::{Command, Stdio};

// Ordinary malformed external requests retain the existing unclassified build/tool failure.
#[test]
fn malformed_request_preserves_build_failure_fallback() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_coreutils_fuzzer"))
        .arg("__container-run-case")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(b"not-json").unwrap();
    let output = child.wait_with_output().unwrap();
    assert_eq!(output.status.code(), Some(2));
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains("FUZZER_OUTCOME=fuzzer_build_failure"),
        "{stderr}"
    );
    assert!(
        stderr.contains("failed to decode container case request"),
        "{stderr}"
    );
    assert!(
        !stderr.contains("FUZZER_OUTCOME=fuzzer_infrastructure_failure"),
        "{stderr}"
    );
}
