// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Audited filesystem syscall wrappers missing from the pinned safe OS facade.

use std::ffi::CString;
use std::io;
use std::os::unix::ffi::OsStrExt as _;
use std::path::Path;

/// Atomically renames `source` to `target` without replacing an existing target.
///
/// On Linux this is `renameat2(RENAME_NOREPLACE)` (issued directly so it also
/// covers libc targets where the pinned `nix` release does not expose its safe
/// wrapper). On macOS it is the exact-equivalent `renamex_np(RENAME_EXCL)`.
/// Both either atomically move `source` without replacing `target` or leave
/// both names intact and fail (`EEXIST` when `target` already exists).
pub fn rename_noreplace(source: &Path, target: &Path) -> io::Result<()> {
    let source = CString::new(source.as_os_str().as_bytes()).map_err(|_| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "rename source path contains a NUL byte",
        )
    })?;
    let target = CString::new(target.as_os_str().as_bytes()).map_err(|_| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "rename target path contains a NUL byte",
        )
    })?;

    #[cfg(target_os = "linux")]
    // SAFETY: both path pointers refer to live, NUL-terminated C strings for
    // the duration of the call. `AT_FDCWD` makes them ordinary pathname
    // arguments. `SYS_renameat2` with `RENAME_NOREPLACE` atomically either
    // moves `source` without replacing `target` or leaves both names intact.
    let result = unsafe {
        libc::syscall(
            libc::SYS_renameat2,
            libc::AT_FDCWD,
            source.as_ptr(),
            libc::AT_FDCWD,
            target.as_ptr(),
            libc::RENAME_NOREPLACE,
        )
    };
    #[cfg(target_os = "macos")]
    // SAFETY: both path pointers refer to live, NUL-terminated C strings for
    // the duration of the call. `renamex_np` with `RENAME_EXCL` atomically
    // either moves `source` without replacing `target` or leaves both names
    // intact; filesystems without RENAME_EXCL support fail closed (ENOTSUP).
    let result = unsafe { libc::renamex_np(source.as_ptr(), target.as_ptr(), libc::RENAME_EXCL) };
    if result == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

#[cfg(test)]
mod tests {
    use super::rename_noreplace;
    use std::fs;
    use std::io;
    use std::sync::atomic::{AtomicU64, Ordering};

    fn create_unique_test_directory() -> std::path::PathBuf {
        static NONCE: AtomicU64 = AtomicU64::new(0);
        for _ in 0..128 {
            let nonce = NONCE.fetch_add(1, Ordering::Relaxed);
            let candidate = std::env::temp_dir().join(format!(
                "ay-sys-rename-noreplace-{}-{nonce}",
                std::process::id()
            ));
            match fs::create_dir(&candidate) {
                Ok(()) => return candidate,
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
                Err(error) => panic!("create isolated rename test directory: {error}"),
            }
        }
        panic!("could not reserve an isolated rename test directory")
    }

    #[test]
    fn rename_noreplace_moves_source_and_refuses_existing_target() {
        let directory = create_unique_test_directory();
        let source = directory.join("source");
        let target = directory.join("target");

        fs::write(&source, b"first").expect("write first source");
        rename_noreplace(&source, &target).expect("publish first source");
        assert!(!source.exists());
        assert_eq!(fs::read(&target).expect("read published target"), b"first");

        fs::write(&source, b"replacement").expect("write replacement source");
        let error = rename_noreplace(&source, &target).expect_err("refuse existing target");
        assert_eq!(error.kind(), io::ErrorKind::AlreadyExists);
        assert_eq!(
            fs::read(&source).expect("read preserved source"),
            b"replacement"
        );
        assert_eq!(fs::read(&target).expect("read preserved target"), b"first");

        fs::remove_file(&source).expect("remove source");
        fs::remove_file(&target).expect("remove target");
        fs::remove_dir(&directory).expect("remove test directory");
    }
}
