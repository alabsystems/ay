// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An authenticated removal leaves no name behind (2026-10-08).
//!
//! `remove_authenticated_visible_file` moves the visible file into a fresh
//! private `.ay-dimacs-proof-<pid>-<nonce>/discard` before deciding whether it
//! is this run's. It used to keep that quarantine, its invalidated inode
//! included, after every successful removal: one hidden directory per cleanup
//! beside the user's proof target. Re-running `ay x.cnf` on an input whose
//! default-proof status marker already existed left four of them. A quarantine
//! move that failed outright left its empty private directory too.

use super::*;

const TOMBSTONE: &[u8] = b"invalidated-by-ay\n";
const INVALIDATION: DimacsPublicationInvalidation =
    DimacsPublicationInvalidation::Proof { binary: false };

/// Every name in `dir`, hidden ones included, sorted.
fn names(dir: &Path) -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(dir)
        .expect("read proof parent")
        .map(|entry| {
            entry
                .expect("entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    names.sort();
    names
}

/// The private quarantine directories left in `dir`.
#[cfg(target_os = "linux")]
fn quarantines(dir: &Path) -> Vec<PathBuf> {
    names(dir)
        .into_iter()
        .filter(|name| name.starts_with(DIMACS_PROOF_STAGING_PREFIX))
        .map(|name| dir.join(name))
        .collect()
}

/// A fresh single-link file at `path` holding `bytes`, with its identity.
fn owned_file(path: &Path, bytes: &[u8]) -> (File, ProofFileIdentity) {
    let mut file = OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .open(path)
        .expect("create owned file");
    file.write_all(bytes).expect("write owned file");
    file.sync_all().expect("sync owned file");
    let identity = regular_file_identity(&file, path).expect("owned identity");
    (file, identity)
}

/// What an inode held open across its removal now holds.
fn held_bytes(mut held: File) -> Vec<u8> {
    let mut bytes = Vec::new();
    held.read_to_end(&mut bytes).expect("read the held inode");
    bytes
}

fn remove(path: &Path, descriptor: &File, identity: ProofFileIdentity) -> io::Result<bool> {
    remove_authenticated_visible_file(path, descriptor, identity, "test file", INVALIDATION)
}

/// The removed inode is invalidated, then discarded with its quarantine:
/// nothing is left in the directory.
#[test]
fn authenticated_removal_leaves_no_name_behind() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let (descriptor, identity) = owned_file(&path, b"0\n");
    let held = File::open(&path).expect("hold the owned inode");

    assert!(remove(&path, &descriptor, identity).expect("remove the owned file"));
    assert_eq!(names(dir.path()), Vec::<String>::new());
    assert_eq!(
        held_bytes(held),
        TOMBSTONE,
        "the inode is invalidated first"
    );
}

/// The negative twin: a replacement found at the visible name is restored,
/// never removed, and its round trip leaves no quarantine either.
#[test]
fn authenticated_removal_restores_a_replacement_without_a_quarantine() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let displaced = dir.path().join("displaced.drat");
    let (descriptor, identity) = owned_file(&path, b"0\n");
    std::fs::rename(&path, &displaced).expect("displace the owned file");
    std::fs::write(&path, b"replacement\n").expect("plant a replacement");

    assert!(!remove(&path, &descriptor, identity).expect("restore the replacement"));
    assert_eq!(
        std::fs::read(&path).expect("read replacement"),
        b"replacement\n"
    );
    assert_eq!(
        std::fs::read(&displaced).expect("read displaced"),
        TOMBSTONE
    );
    assert_eq!(names(dir.path()), ["displaced.drat", "proof.drat"]);
}

/// An object the quarantine cannot authenticate (a symlink, refused by
/// `O_NOFOLLOW`) is restored, and the emptied quarantine goes with the error.
#[cfg(unix)]
#[test]
fn unauthenticatable_object_is_restored_without_a_quarantine() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let displaced = dir.path().join("displaced.drat");
    let (descriptor, identity) = owned_file(&path, b"0\n");
    std::fs::rename(&path, &displaced).expect("displace the owned file");
    std::os::unix::fs::symlink(&displaced, &path).expect("plant a symlink");

    let error = remove(&path, &descriptor, identity).expect_err("a symlink is not authenticated");
    assert!(error.to_string().contains("it was restored"), "{error}");
    assert!(std::fs::symlink_metadata(&path)
        .expect("restored symlink")
        .file_type()
        .is_symlink());
    assert_eq!(names(dir.path()), ["displaced.drat", "proof.drat"]);
}

/// The negative twin of the new unlink: a stranger found at the quarantine
/// name when it is discarded is preserved, with the directory holding it, and
/// the failure is reported.
#[cfg(target_os = "linux")]
#[test]
fn stranger_at_the_quarantine_name_is_preserved() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let (descriptor, identity) = owned_file(&path, b"0\n");
    inject_dimacs_quarantine_swap_once();

    let error = remove(&path, &descriptor, identity).expect_err("the stranger must be refused");
    assert!(
        error.to_string().contains("could not be discarded"),
        "{error}"
    );
    assert!(!path.exists(), "the owned file did leave the visible name");
    let quarantine = quarantines(dir.path());
    assert_eq!(quarantine.len(), 1, "{:?}", names(dir.path()));
    assert_eq!(
        std::fs::read(quarantine[0].join("discard")).expect("read stranger"),
        b"raced quarantine replacement\n"
    );
    assert_eq!(
        std::fs::read(quarantine[0].join("displaced")).expect("read displaced owned inode"),
        TOMBSTONE
    );
}

/// The negative twin of the new `remove_dir`: an entry another process put
/// beside the quarantine name is preserved with the directory holding it, and
/// the failure is reported. The entry is a copy of what `discard` held when
/// its discard began, so it also shows the inode was invalidated by then.
#[cfg(target_os = "linux")]
#[test]
fn foreign_entry_in_the_quarantine_directory_is_preserved() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let (descriptor, identity) = owned_file(&path, b"0\n");
    let held = File::open(&path).expect("hold the owned inode");
    inject_dimacs_quarantine_sibling_once();

    let error = remove(&path, &descriptor, identity).expect_err("a non-empty quarantine is kept");
    assert!(
        error.to_string().contains("could not be discarded"),
        "{error}"
    );
    assert!(!path.exists(), "the owned file did leave the visible name");
    let quarantine = quarantines(dir.path());
    assert_eq!(quarantine.len(), 1, "{:?}", names(dir.path()));
    assert_eq!(names(&quarantine[0]), ["sibling"]);
    assert_eq!(
        std::fs::read(quarantine[0].join("sibling")).expect("read foreign entry"),
        TOMBSTONE,
        "the owned inode is invalidated before its discard begins"
    );
    assert_eq!(held_bytes(held), TOMBSTONE);
}

/// A quarantine move that fails (EINVAL: NFS has no `RENAME_NOREPLACE`) moved
/// nothing, so it leaves nothing either: the visible file stays, invalidated,
/// and the private directory created for the move goes.
#[cfg(target_os = "linux")]
#[test]
fn failed_quarantine_move_leaves_no_private_directory() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let (descriptor, identity) = owned_file(&path, b"0\n");
    inject_dimacs_rename_noreplace_error_once(nix::libc::EINVAL);

    let error = remove(&path, &descriptor, identity).expect_err("EINVAL surfaces");
    assert_eq!(error.raw_os_error(), Some(nix::libc::EINVAL));
    assert_eq!(names(dir.path()), ["proof.drat"]);
    assert_eq!(std::fs::read(&path).expect("read visible file"), TOMBSTONE);
}

/// A failure between the move and the authentication still preserves the
/// quarantined object: only an authenticated inode is ever discarded.
#[cfg(target_os = "linux")]
#[test]
fn failed_authentication_preserves_the_quarantine() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("proof.drat");
    let (descriptor, identity) = owned_file(&path, b"0\n");
    inject_dimacs_proof_cleanup_failure_once();

    remove(&path, &descriptor, identity).expect_err("the injected failure must surface");
    assert!(!path.exists());
    let quarantine = quarantines(dir.path());
    assert_eq!(quarantine.len(), 1, "{:?}", names(dir.path()));
    assert_eq!(
        std::fs::read(quarantine[0].join("discard")).expect("read preserved quarantine"),
        TOMBSTONE
    );
}

/// The real caller: a synthesized default whose status marker already exists
/// is refused, and its released transaction lock leaves nothing but that
/// marker. Each such run used to leave one hidden directory per proof route.
#[test]
fn preexisting_status_marker_is_all_a_refused_transaction_leaves() {
    let dir = tempfile::tempdir().expect("tempdir");
    let proof_path = dir.path().join("input.cnf.drat");
    let proof = ProofConfig {
        path: proof_path.to_string_lossy().into_owned(),
        format: ProofFormat::Drat,
        binary: false,
        artifact_path: None,
        is_temp: false,
        synthesized_default: true,
        format_was_explicit: false,
    };
    let status_path = dimacs_proof_status_path(&proof.path);
    std::fs::write(&status_path, b"unrelated status bytes\n").expect("seed status marker");

    let error = create_configured_dimacs_proof_file(&proof)
        .expect_err("a pre-existing status marker refuses the transaction");
    assert_eq!(error.kind(), io::ErrorKind::AlreadyExists);
    assert_eq!(
        std::fs::read(&status_path).expect("read preserved status"),
        b"unrelated status bytes\n"
    );
    assert_eq!(names(dir.path()), ["input.cnf.drat.ay-status"]);
}
