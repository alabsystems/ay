// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The optional `CLEAN_PATH` replay of a external-codegen consumer certificate.

use std::process::Command;

use crate::spawn::OutputTimeout;
use crate::strict_certificate_publication::QUERY_TIMEOUT;

/// `CLEAN_PATH`'s verdict on the certificate, when one is configured:
/// the `verify-external` contract external-codegen promotes on.
pub(super) fn clean_verdict(problem: &str, proof: &str) -> Option<Result<(), String>> {
    let checker = std::env::var_os("CLEAN_PATH")?;
    let dir = tempfile::tempdir().expect("tempdir");
    let certificate = dir.path().join("cert.json");
    let json = serde_json::json!({
        "type": "alethe_certificate",
        "version": "1.0",
        "problem": problem,
        "proof": proof,
    });
    std::fs::write(&certificate, serde_json::to_vec(&json).expect("json")).expect("write cert");
    let output = Command::new(checker)
        .args(["cert", "verify-external"])
        .arg(&certificate)
        .arg("--verbose")
        .output_timeout(QUERY_TIMEOUT)
        .expect("run clean");
    let stdout = String::from_utf8_lossy(&output.stdout).to_lowercase();
    let lines: Vec<&str> = stdout.lines().map(str::trim).collect();
    let verified = output.status.success()
        && lines.contains(&"external certificate verification: passed")
        && lines.contains(&"type: alethe smt proof")
        && lines.contains(&"proof status: fully verified")
        && !lines.iter().any(|line| {
            line.contains("failed") || line.contains("holey") || line.contains("incomplete")
        });
    Some(if verified {
        Ok(())
    } else {
        Err(format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ))
    })
}
