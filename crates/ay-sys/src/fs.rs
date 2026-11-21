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

/// Sets the extended attribute `name` on the file behind `file` to `value`,
/// replacing any earlier value.
///
/// The attribute is written through the descriptor, so it lands on the inode
/// the caller holds even if its pathname has been renamed or replaced since.
/// On Linux `name` must carry its namespace (`user.`); macOS names have none.
/// A filesystem that cannot hold extended attributes fails with
/// [`io::ErrorKind::Unsupported`].
pub fn set_xattr(file: &std::fs::File, name: &str, value: &[u8]) -> io::Result<()> {
    use std::os::fd::AsRawFd as _;
    let name = xattr_name(name)?;
    let fd = file.as_raw_fd();
    #[cfg(target_os = "linux")]
    // SAFETY: `fd` is a live descriptor borrowed from `file` for the duration
    // of the call, `name` is a NUL-terminated C string that outlives it, and
    // `value` points to `value.len()` initialized bytes that the kernel only
    // reads. Flags 0 means create-or-replace.
    let result =
        unsafe { libc::fsetxattr(fd, name.as_ptr(), value.as_ptr().cast(), value.len(), 0) };
    #[cfg(target_os = "macos")]
    // SAFETY: as above; `position` 0 is required for every attribute but the
    // resource fork, and options 0 means create-or-replace, following links
    // is moot for a descriptor.
    let result =
        unsafe { libc::fsetxattr(fd, name.as_ptr(), value.as_ptr().cast(), value.len(), 0, 0) };
    if result == 0 {
        Ok(())
    } else {
        Err(xattr_error(io::Error::last_os_error()))
    }
}

/// Reads the extended attribute `name` of the file behind `file`: `None` when
/// the file has no such attribute.
pub fn get_xattr(file: &std::fs::File, name: &str) -> io::Result<Option<Vec<u8>>> {
    use std::os::fd::AsRawFd as _;
    let name = xattr_name(name)?;
    let fd = file.as_raw_fd();
    // The value can change between the size query and the read; a value that
    // grew in between fails with ERANGE, and the size is asked again.
    loop {
        let size = fgetxattr_into(fd, &name, &mut [])?;
        let Some(size) = size else {
            return Ok(None);
        };
        let mut value = vec![0u8; size];
        match fgetxattr_into(fd, &name, &mut value) {
            Ok(Some(read)) => {
                value.truncate(read);
                return Ok(Some(value));
            }
            Ok(None) => return Ok(None),
            Err(error) if error.raw_os_error() == Some(libc::ERANGE) => continue,
            Err(error) => return Err(error),
        }
    }
}

/// One `fgetxattr`: the attribute's size when `buffer` is empty, else the
/// bytes read into it. `None` when the attribute does not exist.
fn fgetxattr_into(
    fd: std::os::fd::RawFd,
    name: &CString,
    buffer: &mut [u8],
) -> io::Result<Option<usize>> {
    let (pointer, len) = if buffer.is_empty() {
        (std::ptr::null_mut(), 0)
    } else {
        (buffer.as_mut_ptr().cast(), buffer.len())
    };
    #[cfg(target_os = "linux")]
    // SAFETY: `fd` is a live descriptor owned by the caller, `name` is a
    // NUL-terminated C string, and `pointer` is either null with length 0 (a
    // size query, which writes nothing) or `buffer`'s own storage of `len`
    // writable bytes, which the kernel writes at most `len` of.
    let result = unsafe { libc::fgetxattr(fd, name.as_ptr(), pointer, len) };
    #[cfg(target_os = "macos")]
    // SAFETY: as above; `position` and `options` 0 read the whole value.
    let result = unsafe { libc::fgetxattr(fd, name.as_ptr(), pointer, len, 0, 0) };
    if let Ok(read) = usize::try_from(result) {
        return Ok(Some(read));
    }
    let error = io::Error::last_os_error();
    #[cfg(target_os = "linux")]
    let missing = libc::ENODATA;
    #[cfg(target_os = "macos")]
    let missing = libc::ENOATTR;
    if error.raw_os_error() == Some(missing) {
        Ok(None)
    } else {
        Err(xattr_error(error))
    }
}

fn xattr_name(name: &str) -> io::Result<CString> {
    CString::new(name).map_err(|_| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "extended attribute name contains a NUL byte",
        )
    })
}

/// `ENOTSUP`/`EOPNOTSUPP` (a filesystem without extended attributes) as
/// [`io::ErrorKind::Unsupported`], whatever std maps the errno to.
fn xattr_error(error: io::Error) -> io::Error {
    match error.raw_os_error() {
        Some(code) if code == libc::ENOTSUP || code == libc::EOPNOTSUPP => {
            io::Error::new(io::ErrorKind::Unsupported, error)
        }
        _ => error,
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
    fn xattr_round_trips_through_the_descriptor_and_a_missing_one_is_none() {
        let directory = create_unique_test_directory();
        let path = directory.join("labelled");
        let file = fs::File::create(&path).expect("create file");
        #[cfg(target_os = "linux")]
        let name = "user.com.alab.test";
        #[cfg(target_os = "macos")]
        let name = "com.alab.test";
        match super::get_xattr(&file, name) {
            Ok(None) => {}
            Err(error) if error.kind() == io::ErrorKind::Unsupported => {
                // A test directory on a filesystem without extended attributes.
                fs::remove_file(&path).expect("remove file");
                fs::remove_dir(&directory).expect("remove test directory");
                return;
            }
            other => panic!("a fresh file has no attribute: {other:?}"),
        }
        super::set_xattr(&file, name, b"first").expect("set");
        super::set_xattr(&file, name, b"second, longer").expect("replace");
        let reopened = fs::File::open(&path).expect("reopen");
        assert_eq!(
            super::get_xattr(&reopened, name).expect("get"),
            Some(b"second, longer".to_vec())
        );
        fs::remove_file(&path).expect("remove file");
        fs::remove_dir(&directory).expect("remove test directory");
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
