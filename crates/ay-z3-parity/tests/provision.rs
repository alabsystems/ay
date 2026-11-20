// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(any(
    target_os = "macos",
    all(target_os = "linux", not(target_env = "uclibc"))
))]

use ay_sys::metadata_capture::{capture, CaptureLimits};
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;

#[test]
#[ignore = "requires a retained authenticated offline input cache and fresh native admission"]
fn offline_provision_stdout_matches_retained_manifest() {
    let cache = fs::canonicalize(PathBuf::from(
        std::env::var_os("AY_NATIVE_TEST_PROVISION_ROOT")
            .expect("provide the retained authenticated offline input cache"),
    ))
    .unwrap();
    let manifest = cache.join("provision.json");
    let retained = fs::read(&manifest).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_ay-z3-parity"));
    command
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .args(["smtlib-conformance", "provision", "--directory"])
        .arg(&cache)
        .arg("--offline");
    let output = capture(
        command,
        CaptureLimits {
            timeout: Duration::from_secs(360),
            output_bytes: 1024 * 1024,
            resident_bytes: Some(4 * 1024 * 1024 * 1024),
        },
        "offline provisioning JSON",
    )
    .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let parsed: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(parsed["schema"], "ay-conformance-provision/v2");
    assert_eq!(output.stdout, retained);
    assert_eq!(fs::read(manifest).unwrap(), retained);
}
