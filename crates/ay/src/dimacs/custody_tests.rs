// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The custody state machine and its lock-free discard (2026-09-13).

use super::*;

/// Reserve a proof target the way the solver does (an anonymous inode on
/// Linux, a named stage elsewhere) or, with `named`, force the named stage
/// on every platform, as the exit sweep tests do.
fn reserve(path: &str, named: bool) -> File {
    #[cfg(target_os = "linux")]
    if named {
        inject_anonymous_dimacs_staging_error_once(nix::libc::EOPNOTSUPP);
    }
    #[cfg(not(target_os = "linux"))]
    let _ = named;
    create_owned_dimacs_proof_file(path).expect("reserve proof")
}

fn reserve_written(path: &str, named: bool) {
    let mut proof = reserve(path, named);
    proof
        .write_all(b"pseudo-Boolean proof version 3.0\n")
        .expect("write proof");
}

/// Everything left in `dir` apart from `keep`.
fn leftovers(dir: &Path, keep: &[&str]) -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(dir)
        .expect("read proof parent")
        .map(|entry| {
            entry
                .expect("entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .filter(|name| !keep.contains(&name.as_str()))
        .collect();
    names.sort();
    names
}

fn custody_of(path: &str) -> Arc<DimacsProofCustody> {
    owned_dimacs_proof_custody(path).expect("registered custody")
}

/// An abandoned generation is never published: the seal refuses it, and
/// nothing appears at the target or beside it.
#[test]
fn an_abandoned_generation_is_never_published() {
    for named in [false, true] {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("proof.out");
        let path_text = path.to_str().expect("UTF-8 path");
        reserve_written(path_text, named);

        let custody = custody_of(path_text);
        assert!(custody.abandon());
        custody.discard().expect("discard the abandoned generation");
        let error = seal_owned_dimacs_proof(path_text).expect_err("the seal must refuse");
        assert!(error.to_string().contains("abandoned"), "{error}");
        assert!(!path.exists(), "nothing may be published after an abandon");
        assert_eq!(
            leftovers(dir.path(), &[]),
            Vec::<String>::new(),
            "named={named}"
        );
        remove_owned_dimacs_proof(path_text).expect("settle the registry entry");
        assert_eq!(
            leftovers(dir.path(), &[]),
            Vec::<String>::new(),
            "named={named}"
        );
    }
}

/// The compare-and-swap immediately before the rename or link is what
/// stops a publication that an unanswered exit overtook after the seal's
/// early check: driven directly, it refuses and nothing is published.
#[test]
fn the_publication_compare_and_swap_refuses_an_abandoned_generation() {
    for named in [false, true] {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("proof.out");
        let path_text = path.to_str().expect("UTF-8 path");
        reserve_written(path_text, named);
        let resolved = resolved_dimacs_proof_path(path_text).expect("resolve");
        {
            let mut owned = owned_dimacs_proofs().lock().expect("registry lock");
            let state = owned.get_mut(&resolved).expect("registered proof");
            assert!(state.custody.abandon());
            let error = publish_owned_dimacs_proof_state(state, &resolved)
                .expect_err("an abandoned generation must not be published");
            assert!(error.to_string().contains("abandoned"), "{error}");
        }
        assert!(
            !path.exists(),
            "named={named}: nothing may reach the target"
        );
        remove_owned_dimacs_proof(path_text).expect("settle the registry entry");
    }
}

/// The measured defect: a proof published at its target whose verdict
/// never came. The discard takes it down and leaves nothing behind, not
/// even the private directory it moved the proof through.
#[test]
fn a_published_generation_of_an_unanswered_run_leaves_nothing() {
    for named in [false, true] {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("proof.out");
        let path_text = path.to_str().expect("UTF-8 path");
        reserve_written(path_text, named);
        seal_owned_dimacs_proof(path_text).expect("seal proof");
        assert!(path.exists());

        let custody = custody_of(path_text);
        assert!(custody.abandon());
        custody.discard().expect("discard the published generation");
        assert_eq!(
            leftovers(dir.path(), &[]),
            Vec::<String>::new(),
            "named={named}"
        );
        assert_eq!(custody.descriptor.metadata().expect("stat").len(), 0);
        remove_owned_dimacs_proof(path_text).expect("settle the registry entry");
        assert_eq!(
            leftovers(dir.path(), &[]),
            Vec::<String>::new(),
            "named={named}"
        );
    }
}

/// The target is public: an object another process put there is never
/// removed, even where this run's proof was published first.
#[test]
fn a_replaced_target_is_preserved() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.out");
    let path_text = path.to_str().expect("UTF-8 path");
    reserve_written(path_text, true);
    seal_owned_dimacs_proof(path_text).expect("seal proof");
    let displaced = dir.path().join("displaced");
    std::fs::rename(&path, &displaced).expect("displace the published proof");
    std::fs::write(&path, b"another process's file\n").expect("plant replacement");

    let custody = custody_of(path_text);
    assert!(custody.abandon());
    custody.discard().expect("discard");
    assert_eq!(
        std::fs::read(&path).expect("the replacement survives"),
        b"another process's file\n"
    );
    assert_eq!(
        leftovers(dir.path(), &["proof.out", "displaced"]),
        Vec::<String>::new()
    );
    let _ = remove_owned_dimacs_proof(path_text);
}

/// The exit never waits on the registry lock, which the main thread can
/// hold for tens of seconds while it seals and re-hashes a large proof.
#[test]
fn the_discard_does_not_wait_for_the_registry_lock() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.out");
    let path_text = path.to_str().expect("UTF-8 path");
    reserve_written(path_text, true);
    let custody = custody_of(path_text);

    let registry = owned_dimacs_proofs().lock().expect("registry lock");
    let (done, finished) = std::sync::mpsc::channel();
    let exiting = Arc::clone(&custody);
    std::thread::spawn(move || {
        let abandoned = exiting.abandon();
        let discarded = exiting.discard().is_ok();
        let _ = done.send((abandoned, discarded));
    });
    let outcome = finished.recv_timeout(std::time::Duration::from_secs(10));
    drop(registry);
    assert_eq!(
        outcome,
        Ok((true, true)),
        "the discard must not block on the registry"
    );
    assert_eq!(leftovers(dir.path(), &[]), Vec::<String>::new());
    remove_owned_dimacs_proof(path_text).expect("settle the registry entry");
}

/// An abandon that meets a publication in flight waits for it instead of
/// racing the rename, then claims the generation. The wait here is a minute,
/// not the exit's two seconds, so a slow harness cannot time it out.
#[test]
fn an_abandon_waits_out_a_publication_in_flight() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.out");
    let path_text = path.to_str().expect("UTF-8 path");
    reserve_written(path_text, true);
    let custody = custody_of(path_text);

    custody.begin_publication().expect("claim publication");
    let exiting = Arc::clone(&custody);
    let abandoning =
        std::thread::spawn(move || exiting.abandon_within(std::time::Duration::from_secs(60)));
    std::thread::sleep(std::time::Duration::from_millis(50));
    assert!(
        !abandoning.is_finished(),
        "the abandon must wait for the publication to settle"
    );
    custody.end_publication(true);
    assert!(abandoning.join().expect("abandon thread"));
    assert!(custody.is_abandoned());
    let _ = remove_owned_dimacs_proof(path_text);
}
