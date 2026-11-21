// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay::chc::ChcReplayObligationKind;

fn proof_config(path: &Path) -> ProofConfig {
    ProofConfig {
        path: path.display().to_string(),
        format: super::super::ProofFormat::Alethe,
        binary: false,
        artifact_path: None,
        is_temp: false,
        synthesized_default: false,
        format_was_explicit: false,
        label: None,
    }
}

fn available_artifacts(publication: ChcCertificatePublication) -> ChcCliReplayArtifacts {
    match publication {
        ChcCertificatePublication::Available(artifacts) => artifacts,
        ChcCertificatePublication::OptionalUnavailable => {
            panic!("certificate unexpectedly became optional-unavailable")
        }
        ChcCertificatePublication::RequiredUnavailable(diagnostic) => {
            panic!("certificate unexpectedly became required-unavailable: {diagnostic}")
        }
    }
}

fn obligation_directories(parent: &Path) -> Vec<PathBuf> {
    fs::read_dir(parent)
        .expect("read publication directory")
        .map(|entry| entry.expect("directory entry").path())
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.contains(".chc-obligations-"))
        })
        .collect()
}

#[test]
fn chc_publication_lock_excludes_a_concurrent_publisher() {
    let temp = tempfile::tempdir().expect("temporary directory");
    let proof = temp.path().join("proof.chccert");
    let first = ChcPublicationLock::acquire(&proof).expect("first publication lock");
    assert!(
        ChcPublicationLock::acquire(&proof).is_err(),
        "a second publisher acquired the same certificate lock"
    );
    drop(first);
    ChcPublicationLock::acquire(&proof).expect("lock after first publisher exits");
}

#[test]
fn chc_publication_lock_refuses_a_symlink_without_touching_its_target() {
    let temp = tempfile::tempdir().expect("temporary directory");
    let proof = temp.path().join("proof.chccert");
    let target = temp.path().join("unrelated");
    fs::write(&target, b"unrelated").expect("plant lock target");
    std::os::unix::fs::symlink(&target, temp.path().join(".proof.chccert.ay-chc.lock"))
        .expect("plant lock symlink");

    assert!(ChcPublicationLock::acquire(&proof).is_err());
    assert_eq!(fs::read(target).expect("read target"), b"unrelated");
}

#[test]
fn chc_publication_final_gate_rejects_lock_unlink_and_recreate() {
    let temp = tempfile::tempdir().expect("temporary directory");
    let proof = temp.path().join("proof.chccert");
    let mut artifacts =
        publish_chc_certificate_artifacts(&proof_config(&proof), "certificate\n", Vec::new())
            .expect("publish CHC certificate");
    let lock_path = temp.path().join(".proof.chccert.ay-chc.lock");

    fs::remove_file(&lock_path).expect("unlink active publication lock");
    let replacement = ChcPublicationLock::acquire(&proof)
        .expect("replacement inode demonstrates why identity validation is required");

    let error = artifacts
        .validate()
        .expect_err("final gate accepted an unlinked/recreated lock authority");
    assert!(
        error.to_string().contains("lock authority changed"),
        "unexpected final-gate error: {error}"
    );
    drop(replacement);
}

#[test]
fn certificate_only_scope_skips_safe_and_unsafe_obligation_trees() {
    let temp = tempfile::tempdir().expect("temporary directory");
    let proof = temp.path().join("proof.chccert");
    let config = proof_config(&proof);

    let safe_artifacts = available_artifacts(write_chc_safe_certificate_artifacts(
        Some(&config),
        ChcProofGates::for_script("", false),
        "safe certificate\n",
        ChcArtifactScope::CertificateOnly,
        || -> ChcResult<Vec<ChcReplayObligation>> {
            panic!("stats-off SAFE generated replay obligations")
        },
    ));
    assert_eq!(
        safe_artifacts.replay_obligations.as_slice(),
        &[] as &[ChcReplayObligationArtifact]
    );
    assert_eq!(
        obligation_directories(temp.path()).as_slice(),
        &[] as &[PathBuf]
    );
    drop(safe_artifacts);

    let unsafe_artifacts = available_artifacts(write_chc_unsafe_certificate_artifacts(
        Some(&config),
        ChcProofGates::for_script("", false),
        "unsafe certificate\n",
        ChcArtifactScope::CertificateOnly,
        || -> ChcResult<Vec<ChcReplayPayload>> {
            panic!("stats-off UNSAFE generated replay obligations")
        },
    ));
    assert_eq!(
        unsafe_artifacts.replay_obligations.as_slice(),
        &[] as &[ChcReplayObligationArtifact]
    );
    assert_eq!(
        obligation_directories(temp.path()).as_slice(),
        &[] as &[PathBuf]
    );
}

#[test]
fn chc_publication_seals_certificate_and_unique_obligations() {
    let temp = tempfile::tempdir().expect("temporary directory");
    let proof = temp.path().join("proof.chccert");
    // Publication resolves the certificate's directory once
    // (`resolve_artifact_target`) and publishes every artifact under the
    // resolved path, so the expectations are canonical while the request keeps
    // the caller's spelling. macOS's `$TMPDIR` sits under `/var`, a symlink to
    // `/private/var`, where comparing against `temp.path()` failed.
    let root = fs::canonicalize(temp.path()).expect("canonical temporary directory");
    let resolved_proof = root.join("proof.chccert");
    let obligation = ChcReplayObligation {
        name: "trace".to_string(),
        kind: ChcReplayObligationKind::TraceValidity,
        clause_index: 7,
        smtlib: "(set-logic QF_LIA)\n(check-sat)\n".to_string(),
    };
    let mut artifacts =
        publish_chc_certificate_artifacts(&proof_config(&proof), "certificate\n", vec![obligation])
            .expect("publish CHC transaction");

    assert_eq!(
        fs::read_to_string(&proof).expect("certificate"),
        "certificate\n"
    );
    assert_eq!(artifacts.replay_obligations.len(), 1);
    assert!(
        ChcPublicationLock::acquire(&proof).is_err(),
        "the publication lease was released before the artifacts"
    );
    let obligation_path = Path::new(
        artifacts.replay_obligations[0]
            .query
            .path
            .as_deref()
            .expect("obligation path"),
    );
    assert!(obligation_path.starts_with(&root));
    assert_ne!(obligation_path.parent(), resolved_proof.parent());
    for artifact in &mut artifacts.retained_files {
        artifact
            .validate()
            .expect("same-run artifact remains sealed");
    }

    fs::write(&proof, b"tampered\n").expect("tamper certificate");
    assert!(
        artifacts
            .retained_files
            .iter_mut()
            .any(|artifact| artifact.path == resolved_proof && artifact.validate().is_err()),
        "certificate replacement was not detected before verdict publication"
    );
    drop(artifacts);
    ChcPublicationLock::acquire(&proof)
        .expect("publication lease should be released with the artifacts");
}
