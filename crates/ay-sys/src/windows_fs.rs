// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Windows file identity and link-count queries.
//!
//! Unix exposes `(dev, ino)` and `nlink` through the stable `MetadataExt`
//! traits. Windows has no stable equivalent: `volume_serial_number`,
//! `file_index`, and `number_of_links` all sit behind the `windows_by_handle`
//! feature, unstable since 2019 (rust-lang/rust#63010). The underlying values
//! are only reachable through `GetFileInformationByHandle`, which needs a
//! handle rather than a `Metadata`.
//!
//! Callers use these queries to detect a file being swapped or hard-linked out
//! from under a run, so the values must be exact — a silently skipped check is
//! a hole, not a degradation.

use std::fs::{File, OpenOptions};
use std::io;
use std::mem::MaybeUninit;
use std::os::windows::ffi::OsStrExt as _;
use std::os::windows::fs::OpenOptionsExt as _;
use std::os::windows::io::AsRawHandle as _;
use std::path::Path;
use windows_sys::Win32::Storage::FileSystem::{
    GetFileInformationByHandle, MoveFileExW, BY_HANDLE_FILE_INFORMATION,
    FILE_FLAG_BACKUP_SEMANTICS, FILE_FLAG_OPEN_REPARSE_POINT, FILE_READ_ATTRIBUTES,
    FILE_SHARE_DELETE, FILE_SHARE_READ, FILE_SHARE_WRITE,
};

/// Share mask permitting concurrent read, write, and **delete/rename**.
///
/// Unix lets a file be renamed or unlinked while descriptors remain open.
/// Windows does not: `MoveFileExW` and `DeleteFile` fail with
/// `ERROR_ACCESS_DENIED` unless EVERY open handle to the file was opened
/// permitting deletion. Rust's `OpenOptions` defaults to
/// `FILE_SHARE_READ | FILE_SHARE_WRITE` only.
///
/// Any staging file that is published or quarantined by rename WHILE its
/// authenticating descriptor is still held must be opened with this mask —
/// closing the descriptor first is not an option, because holding it open
/// across the rename is precisely what makes the publication descriptor-
/// authenticated rather than path-authenticated.
pub const SHARE_READ_WRITE_DELETE: u32 = FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE;

/// Identity and link count of an open file, as reported by the volume.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WindowsFileInfo {
    /// Serial number of the volume holding the file. Pairs with `file_index`
    /// to form the Windows analogue of a unix `(dev, ino)` pair.
    pub volume_serial_number: u32,
    /// Volume-unique file index, combined from its high and low halves.
    pub file_index: u64,
    /// Number of hard links naming this file.
    pub number_of_links: u32,
}

/// Query identity and link count through an already-open handle.
pub fn file_info(file: &File) -> io::Result<WindowsFileInfo> {
    let mut info = MaybeUninit::<BY_HANDLE_FILE_INFORMATION>::uninit();
    // SAFETY: `file` keeps its handle open for the whole of this borrow, and
    // `info` is a correctly sized and aligned writable allocation for the
    // out-parameter. The structure is read only on the non-zero (success)
    // return, which is exactly when the OS has initialized every field.
    let ok = unsafe { GetFileInformationByHandle(file.as_raw_handle() as _, info.as_mut_ptr()) };
    if ok == 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: the call returned success, so every field is initialized.
    let info = unsafe { info.assume_init() };
    Ok(WindowsFileInfo {
        volume_serial_number: info.dwVolumeSerialNumber,
        file_index: (u64::from(info.nFileIndexHigh) << 32) | u64::from(info.nFileIndexLow),
        number_of_links: info.nNumberOfLinks,
    })
}

/// Open `path` solely to query attributes, without following a reparse point.
///
/// `FILE_FLAG_OPEN_REPARSE_POINT` preserves `symlink_metadata` semantics: a
/// symlink or junction occupying the pathname is reported as itself, never as
/// its target. `FILE_FLAG_BACKUP_SEMANTICS` is what allows a directory handle
/// to be opened at all; without it the call fails on directories.
pub fn open_for_attributes_no_follow(path: &Path) -> io::Result<File> {
    OpenOptions::new()
        .access_mode(FILE_READ_ATTRIBUTES)
        .custom_flags(FILE_FLAG_BACKUP_SEMANTICS | FILE_FLAG_OPEN_REPARSE_POINT)
        .open(path)
}

/// Query identity and link count for a pathname without following a reparse
/// point.
///
/// Matches the resolution behaviour of `std::fs::symlink_metadata`.
pub fn file_info_no_follow(path: &Path) -> io::Result<WindowsFileInfo> {
    file_info(&open_for_attributes_no_follow(path)?)
}

/// Query identity and link count for a pathname, following reparse points.
///
/// Matches the resolution behaviour of `std::fs::metadata`.
pub fn file_info_follow(path: &Path) -> io::Result<WindowsFileInfo> {
    let file = OpenOptions::new()
        .access_mode(FILE_READ_ATTRIBUTES)
        .custom_flags(FILE_FLAG_BACKUP_SEMANTICS)
        .open(path)?;
    file_info(&file)
}

/// Renames `source` to `target` without replacing an existing target.
///
/// `MoveFileExW` without `MOVEFILE_REPLACE_EXISTING` is the Windows counterpart
/// of Linux `renameat2(RENAME_NOREPLACE)` and macOS `renamex_np(RENAME_EXCL)`:
/// it either moves `source` or leaves both names intact and fails, reporting
/// `ERROR_ALREADY_EXISTS` (surfaced as [`io::ErrorKind::AlreadyExists`]) when
/// `target` is already taken.
pub fn rename_noreplace(source: &Path, target: &Path) -> io::Result<()> {
    let source = wide_null(source);
    let target = wide_null(target);
    // SAFETY: both pointers address NUL-terminated UTF-16 buffers that outlive
    // the call, which is the contract for the two PCWSTR parameters.
    let ok = unsafe { MoveFileExW(source.as_ptr(), target.as_ptr(), 0) };
    if ok == 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

fn wide_null(path: &Path) -> Vec<u16> {
    path.as_os_str().encode_wide().chain(Some(0)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reports_a_single_link_for_a_fresh_file() {
        let dir = std::env::temp_dir().join("ay-sys-windows-fs-single-link");
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("create temp dir");
        let path = dir.join("trace.bin");
        std::fs::write(&path, b"payload").expect("write file");

        let info = file_info_no_follow(&path).expect("query file info");
        assert_eq!(info.number_of_links, 1);
        assert_ne!(info.file_index, 0);

        let handle = File::open(&path).expect("open file");
        let via_handle = file_info(&handle).expect("query via handle");
        assert_eq!(
            via_handle, info,
            "path and handle queries must agree on identity"
        );

        drop(handle);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn distinct_files_have_distinct_identities() {
        let dir = std::env::temp_dir().join("ay-sys-windows-fs-distinct");
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("create temp dir");
        let first = dir.join("a.bin");
        let second = dir.join("b.bin");
        std::fs::write(&first, b"a").expect("write a");
        std::fs::write(&second, b"b").expect("write b");

        let a = file_info_no_follow(&first).expect("query a");
        let b = file_info_no_follow(&second).expect("query b");
        assert_ne!(
            (a.volume_serial_number, a.file_index),
            (b.volume_serial_number, b.file_index)
        );

        let _ = std::fs::remove_dir_all(&dir);
    }
}
