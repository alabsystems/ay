// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The competition fast publication (2026-09-13): one SHA-256 taken while the
//! proof is written, the seal and the verdict gates reading nothing back, and
//! custody unchanged. See `dimacs_fast_publication`.

use super::*;

fn custody_of(path: &str) -> Arc<DimacsProofCustody> {
    owned_dimacs_proof_custody(path).expect("registered custody")
}

/// Reserve a proof target the way the solver does outside the fast path, on a
/// named stage on every platform.
fn reserve_named(path: &str) -> File {
    #[cfg(target_os = "linux")]
    inject_anonymous_dimacs_staging_error_once(nix::libc::EOPNOTSUPP);
    create_owned_dimacs_proof_file(path).expect("reserve proof")
}

/// Reserve a fast-publication generation and write `steps` DRAT units through
/// the production sink, dropping it so the writer records its digest.
fn write_fast_publication(path: &str, named: bool, steps: usize) -> Arc<DimacsProofCustody> {
    #[cfg(target_os = "linux")]
    if named {
        inject_anonymous_dimacs_staging_error_once(nix::libc::EOPNOTSUPP);
    }
    #[cfg(not(target_os = "linux"))]
    let _ = named;
    let proof = ProofConfig {
        path: path.to_string(),
        format: ProofFormat::Drat,
        binary: false,
        artifact_path: None,
        is_temp: false,
        synthesized_default: false,
        format_was_explicit: true,
    };
    let mut reservation = None;
    let file = create_owned_dimacs_proof_file_with_status(
        path,
        &mut reservation,
        DimacsPublicationInvalidation::Proof { binary: false },
        true,
    )
    .expect("reserve a fast-publication proof");
    let custody = custody_of(path);
    let mut output =
        ProofOutput::drat_text(solver_proof_output_writer(file, &proof).expect("proof sink"));
    let unit = [Literal::positive(Variable::new(0))];
    for _ in 0..steps {
        output.add(&unit, &[]).expect("proof step");
    }
    output.flush().expect("final flush");
    drop(output);
    custody
}

/// The seal-latency lever (2026-09-13): a fast-publication proof is sealed,
/// captured and re-checked by all three verdict gates without one whole-file
/// pass, under the digest its writer took, which is the digest of the bytes on
/// disk.
#[test]
fn a_fast_publication_reaches_the_verdict_without_reading_the_proof_back() {
    for named in [false, true] {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("proof.out");
        let path_text = path.to_str().expect("UTF-8 path");
        let passes = whole_file_hash_passes();
        // 400,000 units of `1 0\n`: 1.6 MB, past the 1 MiB buffer, so the
        // writer hashes several writes and the final flush's tail.
        let custody = write_fast_publication(path_text, named, 400_000);
        let digest = custody
            .streamed_digest()
            .expect("the writer recorded its digest");
        assert_eq!(digest.len, 1_600_000);
        let published = seal_owned_dimacs_proof(path_text).expect("seal");
        let retained = retain_published_dimacs_proof(path_text, published, false).expect("capture");
        assert_eq!(retained.recheck, DimacsPublicationRecheck::Identity);
        let mut transaction = DimacsUnsatPublicationTransaction::new(
            retained,
            None,
            DimacsProofRequirement::Required,
        );
        for gate in ["authorization", "statistics", "verdict"] {
            transaction
                .validate()
                .unwrap_or_else(|error| panic!("{gate}: {error}"));
        }
        assert_eq!(
            whole_file_hash_passes(),
            passes,
            "named={named}: no whole-file pass between the writer and the verdict"
        );
        assert_eq!(published.len, digest.len);
        assert_eq!(published.sha256, digest.sha256);
        let bytes = std::fs::read(&path).expect("read the published proof");
        assert_eq!(
            sha256_digest(&bytes),
            digest.sha256,
            "the digest is the disk's"
        );
        transaction.commit();
        remove_owned_dimacs_proof(path_text).expect("settle the registry entry");
    }
}

/// Custody is untouched by the digest: an abandoned fast-publication proof is
/// never published, whether the abandon lands before the seal's early check or
/// only before its compare-and-swap.
#[test]
fn an_abandoned_fast_publication_is_never_published() {
    for named in [false, true] {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("proof.out");
        let path_text = path.to_str().expect("UTF-8 path");
        let custody = write_fast_publication(path_text, named, 1000);
        assert!(custody.streamed_digest().is_some());
        assert!(custody.abandon());
        let error = seal_owned_dimacs_proof(path_text).expect_err("the seal must refuse");
        assert!(error.to_string().contains("abandoned"), "{error}");
        let resolved = resolved_dimacs_proof_path(path_text).expect("resolve");
        {
            let mut owned = owned_dimacs_proofs().lock().expect("registry lock");
            let state = owned.get_mut(&resolved).expect("registered proof");
            let error = publish_owned_dimacs_proof_state(state, &resolved)
                .expect_err("the compare-and-swap must refuse");
            assert!(error.to_string().contains("abandoned"), "{error}");
        }
        assert!(
            !path.exists(),
            "named={named}: nothing may reach the target"
        );
        let _ = remove_owned_dimacs_proof(path_text);
    }
}

/// A fast-publication proof that anything else grew or shrank after its
/// writer finished is not published under the writer's digest.
#[test]
fn a_fast_publication_resized_after_its_writer_is_not_published() {
    for grow in [true, false] {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("proof.out");
        let path_text = path.to_str().expect("UTF-8 path");
        let custody = write_fast_publication(path_text, true, 1000);
        let len = custody.streamed_digest().expect("digest").len;
        custody
            .descriptor
            .set_len(if grow { len + 7 } else { len - 7 })
            .expect("resize behind the writer's back");
        let error = seal_owned_dimacs_proof(path_text).expect_err("the seal must refuse");
        assert!(error.to_string().contains("not published"), "{error}");
        assert!(!path.exists(), "grow={grow}: nothing may reach the target");
        remove_owned_dimacs_proof(path_text).expect("settle the registry entry");
    }
}

/// The identity-only rechecks still catch a replaced or resized proof before
/// the verdict. What they give up is a same-length rewrite in place, which the
/// external checker still sees.
#[test]
fn identity_rechecks_catch_replacement_and_resizing() {
    for tamper in ["replace", "truncate", "rewrite-in-place"] {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("proof.out");
        let path_text = path.to_str().expect("UTF-8 path");
        write_fast_publication(path_text, true, 1000);
        let published = seal_owned_dimacs_proof(path_text).expect("seal");
        let mut transaction = DimacsUnsatPublicationTransaction::new(
            retain_published_dimacs_proof(path_text, published, false).expect("capture"),
            None,
            DimacsProofRequirement::Required,
        );
        match tamper {
            "replace" => {
                std::fs::rename(&path, dir.path().join("displaced")).expect("displace");
                std::fs::write(&path, vec![b'0'; published.len as usize]).expect("replace");
            }
            "truncate" => {
                let visible = OpenOptions::new().write(true).open(&path).expect("open");
                visible.set_len(published.len - 1).expect("truncate");
            }
            _ => {
                let mut visible = OpenOptions::new().write(true).open(&path).expect("open");
                visible.write_all(b"9").expect("rewrite one byte in place");
            }
        }
        let caught = transaction.validate().is_err();
        assert_eq!(caught, tamper != "rewrite-in-place", "{tamper}");
        transaction.commit();
        let _ = remove_owned_dimacs_proof(path_text);
    }
}

/// The posture predicate: every term must hold, and each negated one names an
/// in-process reader of the proof's bytes.
#[test]
fn the_fast_publication_predicate_requires_every_term() {
    let explicit = ProofConfig {
        path: "proof.out".to_string(),
        format: ProofFormat::Veripb,
        binary: false,
        artifact_path: None,
        is_temp: false,
        synthesized_default: false,
        format_was_explicit: true,
    };
    assert!(dimacs_fast_publication_for(
        true, false, false, false, &explicit
    ));
    assert!(!dimacs_fast_publication_for(
        false, false, false, false, &explicit
    ));
    assert!(!dimacs_fast_publication_for(
        true, true, false, false, &explicit
    ));
    assert!(!dimacs_fast_publication_for(
        true, false, true, false, &explicit
    ));
    assert!(!dimacs_fast_publication_for(
        true, false, false, true, &explicit
    ));
    let with = |edit: fn(&mut ProofConfig)| {
        let mut proof = explicit.clone();
        edit(&mut proof);
        dimacs_fast_publication_for(true, false, false, false, &proof)
    };
    assert!(!with(|proof| proof.synthesized_default = true));
    assert!(!with(|proof| proof.is_temp = true));
    assert!(!with(
        |proof| proof.artifact_path = Some("artifact.json".to_string())
    ));
}

/// A fast-publication generation whose writer recorded no digest (a raw writer,
/// as on the parallel and dense-clique routes) falls back to one read-back
/// hash at the seal; the rechecks stay identity-only.
#[test]
fn a_fast_publication_without_a_digest_falls_back_to_one_read_back() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.out");
    let path_text = path.to_str().expect("UTF-8 path");
    let mut reservation = None;
    let mut file = create_owned_dimacs_proof_file_with_status(
        path_text,
        &mut reservation,
        DimacsPublicationInvalidation::Proof { binary: false },
        true,
    )
    .expect("reserve a fast-publication proof");
    file.write_all(b"1 0\n0\n").expect("raw write");
    drop(file);
    assert!(custody_of(path_text).streamed_digest().is_none());

    let passes = whole_file_hash_passes();
    let published = seal_owned_dimacs_proof(path_text).expect("seal");
    assert_eq!(
        whole_file_hash_passes(),
        passes + 1,
        "one read-back at the seal"
    );
    assert_eq!(published.sha256, sha256_digest(b"1 0\n0\n"));
    let retained = retain_published_dimacs_proof(path_text, published, false).expect("capture");
    assert_eq!(retained.recheck, DimacsPublicationRecheck::Identity);
    assert_eq!(whole_file_hash_passes(), passes + 1);
    let mut transaction =
        DimacsUnsatPublicationTransaction::new(retained, None, DimacsProofRequirement::Required);
    transaction.commit();
    remove_owned_dimacs_proof(path_text).expect("settle the registry entry");
}

/// The control for the fast path: outside it, the seal and every recheck still
/// read the proof back, and a same-length rewrite in place is caught.
#[test]
fn outside_the_fast_path_every_recheck_reads_the_proof_back() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.out");
    let path_text = path.to_str().expect("UTF-8 path");
    let mut file = reserve_named(path_text);
    file.write_all(b"1 0\n0\n").expect("write proof");
    drop(file);
    assert!(!custody_of(path_text).fast_publication);

    let passes = whole_file_hash_passes();
    let published = seal_owned_dimacs_proof(path_text).expect("seal");
    let retained = retain_published_dimacs_proof(path_text, published, false).expect("capture");
    assert_eq!(retained.recheck, DimacsPublicationRecheck::Bytes);
    let mut transaction =
        DimacsUnsatPublicationTransaction::new(retained, None, DimacsProofRequirement::Required);
    transaction
        .validate()
        .expect("an untouched proof validates");
    assert_eq!(
        whole_file_hash_passes(),
        passes + 5,
        "seal 1, capture 2, validate 2"
    );
    let mut visible = OpenOptions::new().write(true).open(&path).expect("open");
    visible.write_all(b"9").expect("rewrite one byte in place");
    assert!(
        transaction.validate().is_err(),
        "a byte recheck catches a same-length rewrite"
    );
    transaction.commit();
    let _ = remove_owned_dimacs_proof(path_text);
}
