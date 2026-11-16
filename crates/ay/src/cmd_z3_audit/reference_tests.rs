// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn reference_snapshot_uses_only_current_pinned_bytes() {
    let Some(candidate) = ay_test_support::z3::optional_z3("z3-audit pinned snapshot") else {
        return;
    };
    let root = resolve_repo_root(None).unwrap();
    let pin = Pin::load(&root).unwrap();
    let candidate_path = candidate.path().to_str().unwrap();
    if pin.executable_identity(candidate.path()).is_err() {
        assert!(Snapshot::capture(&root, candidate_path).is_err());
        return;
    }
    let snapshot = Snapshot::capture(&root, candidate_path).unwrap();
    assert_ne!(snapshot.path(), candidate.path());
    assert_eq!(
        sha256_file(snapshot.path()).unwrap(),
        snapshot.identity.executable_sha256
    );
    let output = run_command_capture_with_stdin(
        &root,
        snapshot.path(),
        &["-in"],
        b"(assert false)\n(check-sat)\n",
    )
    .unwrap();
    assert!(output.status.success());
    assert_eq!(output.stdout, b"unsat\n");
    assert_eq!(output.stderr.as_slice(), &[] as &[u8]);
}

#[test]
fn a_current_version_banner_is_not_pinned_executable_identity() {
    let pin = Pin::parse(include_str!("../../../../ci/z3.pin")).unwrap();
    let directory = tempfile::tempdir().unwrap();
    let candidate = directory.path().join("z3");
    fs::write(&candidate, "Z3 version 5.3.3 - 64 bit\n").unwrap();
    assert!(pin
        .executable_identity(&candidate)
        .unwrap_err()
        .to_string()
        .contains("executable bytes"));
}

#[cfg(unix)]
#[test]
fn unpinned_candidate_is_never_executed_even_for_its_banner() {
    use std::os::unix::fs::PermissionsExt;
    let directory = tempfile::tempdir().unwrap();
    let candidate = directory.path().join("z3");
    let marker = directory.path().join("executed");
    fs::write(
        &candidate,
        format!(
            "#!/bin/sh\ntouch '{}'\necho 'Z3 version 5.3.3 - 64 bit'\n",
            marker.display()
        ),
    )
    .unwrap();
    fs::set_permissions(&candidate, fs::Permissions::from_mode(0o700)).unwrap();
    let root = resolve_repo_root(None).unwrap();
    assert!(Snapshot::capture(&root, candidate.to_str().unwrap()).is_err());
    assert!(!marker.exists());
}

#[test]
fn current_pin_is_required_for_cached_evidence() {
    let pin = Pin::parse(include_str!("../../../../ci/z3.pin")).unwrap();
    let identity = pin.identity("darwin_arm64").unwrap();
    let banner = format!("Z3 version {} - 64 bit", identity.version);
    let value = serde_json::to_value(&identity).unwrap();
    pin.validate_cache(&value, &banner).unwrap();
    for key in ["version", "row", "pin_sha256", "executable_sha256"] {
        let mut wrong = value.clone();
        wrong[key] = json!("unbound");
        assert!(pin.validate_cache(&wrong, &banner).is_err(), "{key}");
    }
    assert!(pin
        .validate_cache(&value, "Z3 version 5.1.0 - 64 bit")
        .is_err());
    assert!(pin.validate_cache(&Value::Null, &banner).is_err());
}

#[test]
fn pin_refuses_unknown_duplicates_or_incomplete_rows() {
    let text = include_str!("../../../../ci/z3.pin");
    for wrong in [
        format!("{text}\nZ3_VERSION=5.3.3\n"),
        format!("{text}\nUNKNOWN=1\n"),
        text.replacen(".zip", ".ZIP", 1),
        text.replace("Z3_BIN_SHA256_darwin_arm64=", "ORPHAN="),
        text.replace(
            "Z3_ROWS=darwin_arm64,",
            "Z3_ROWS=darwin_arm64,darwin_arm64,",
        ),
    ] {
        assert!(Pin::parse(&wrong).is_err());
    }
}
