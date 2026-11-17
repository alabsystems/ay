// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(all(test, unix))]

use super::*;
use std::os::unix::fs::{symlink, FileTypeExt as _};

fn original_file() -> (tempfile::TempDir, std::path::PathBuf, Vec<u8>) {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("archive.tar.gz");
    let bytes = include_str!("../fixtures/original-archive.hex")
        .split_whitespace()
        .flat_map(|line| {
            let (pairs, remainder) = line.as_bytes().as_chunks::<2>();
            assert_eq!(remainder, &[] as &[u8]);
            pairs
        })
        .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
        .collect::<Vec<_>>();
    std::fs::write(&path, &bytes).unwrap();
    (dir, path, bytes)
}

#[test]
fn stale_regular_path_check_cannot_authorize_a_replacement_symlink() {
    let (dir, path, _) = original_file();
    assert!(std::fs::symlink_metadata(&path).unwrap().is_file());
    let displaced = dir.path().join("displaced.tar.gz");
    std::fs::rename(&path, &displaced).unwrap();
    symlink(&displaced, &path).unwrap();
    // A plain File::open here would follow the link to an otherwise authentic
    // archive; the production descriptor funnel must reject the replacement.
    assert!(open_archive(&path).is_err());
}

#[test]
fn replacement_fifo_opens_without_a_writer_and_is_rejected_by_handle_type() {
    let (_dir, path, _) = original_file();
    assert!(std::fs::symlink_metadata(&path).unwrap().is_file());
    std::fs::remove_file(&path).unwrap();
    nix::unistd::mkfifo(&path, nix::sys::stat::Mode::S_IRUSR).unwrap();
    // No writer is created. O_NONBLOCK is essential for this open to return;
    // O_NOFOLLOW alone would still hang on the substituted FIFO.
    let opened = open_archive(&path).unwrap();
    assert!(opened.metadata().unwrap().file_type().is_fifo());
    assert!(read_opened(opened, &capture::load().unwrap().archive).is_err());
}

#[test]
fn replaced_path_after_open_cannot_redirect_the_authenticated_descriptor() {
    let (dir, path, expected) = original_file();
    let opened = open_archive(&path).unwrap();
    let replacement = dir.path().join("replacement.tar.gz");
    std::fs::write(&replacement, vec![0; expected.len()]).unwrap();
    std::fs::remove_file(&path).unwrap();
    symlink(&replacement, &path).unwrap();
    let bytes = read_opened(opened, &capture::load().unwrap().archive).unwrap();
    assert_eq!(bytes, expected);
    assert_ne!(std::fs::read(&path).unwrap(), expected);
}

#[test]
fn same_inode_same_length_mutation_after_open_is_rejected_by_exact_hash() {
    let (_dir, path, mut bytes) = original_file();
    let opened = open_archive(&path).unwrap();
    let last = bytes.len() - 1;
    bytes[last] ^= 1;
    std::fs::write(&path, bytes).unwrap();
    let error = read_opened(opened, &capture::load().unwrap().archive).unwrap_err();
    assert!(error.to_string().contains("archive identity mismatch"));
}

#[test]
fn truncation_after_open_is_rejected_using_opened_file_metadata() {
    let (_dir, path, bytes) = original_file();
    let opened = open_archive(&path).unwrap();
    std::fs::OpenOptions::new()
        .write(true)
        .open(&path)
        .unwrap()
        .set_len(bytes.len() as u64 - 1)
        .unwrap();
    let error = read_opened(opened, &capture::load().unwrap().archive).unwrap_err();
    assert!(error.to_string().contains("exact regular file"));
}

#[test]
fn opened_directory_is_not_an_archive_even_when_path_checks_are_absent() {
    let dir = tempfile::tempdir().unwrap();
    let opened = open_archive(dir.path()).unwrap();
    assert!(read_opened(opened, &capture::load().unwrap().archive).is_err());
}

#[test]
fn oversized_opened_file_cannot_make_the_archive_reader_allocate_its_length() {
    let (_dir, path, _) = original_file();
    std::fs::OpenOptions::new()
        .write(true)
        .open(&path)
        .unwrap()
        .set_len(MAX_ARCHIVE + 1)
        .unwrap();
    let opened = open_archive(&path).unwrap();
    let mut identity = capture::load().unwrap().archive;
    identity.bytes = MAX_ARCHIVE + 1;
    assert!(read_opened(opened, &identity).is_err());
}
