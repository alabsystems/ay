// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

/// The standard descriptors, by number.
///
/// `libc::STDOUT_FILENO`/`STDERR_FILENO` are Unix-only in the `libc` crate. The
/// numbers themselves are not Unix-only: the Windows CRT that backs
/// `libc::write` (`_write`) opens 0/1/2 as stdin/stdout/stderr exactly as POSIX
/// does, so the literals are correct on both and keep this path — which runs
/// inside the global allocator — free of any lookup.
#[cfg(unix)]
pub(super) const STDOUT_FD: libc::c_int = libc::STDOUT_FILENO;
#[cfg(unix)]
pub(super) const STDERR_FD: libc::c_int = libc::STDERR_FILENO;
#[cfg(not(unix))]
pub(super) const STDOUT_FD: libc::c_int = 1;
#[cfg(not(unix))]
pub(super) const STDERR_FD: libc::c_int = 2;

/// The `count` argument of `libc::write`, which is `size_t` on Unix and
/// `c_uint` on Windows.
///
/// Clamping rather than converting is correct here: `write` is already allowed
/// to write fewer bytes than asked, and the caller loops on the returned count,
/// so a slice longer than `u32::MAX` simply takes another pass. The clamp is a
/// plain compare, so the path stays allocation-free.
#[cfg(unix)]
#[inline]
fn write_count(len: usize) -> usize {
    len
}

#[cfg(not(unix))]
#[inline]
fn write_count(len: usize) -> libc::c_uint {
    // `c_uint::MAX as usize` cannot truncate: c_uint is 32-bit and usize is at
    // least 32-bit on every target this builds for.
    len.min(libc::c_uint::MAX as usize) as libc::c_uint
}

/// Allocation-free, retry-on-partial write to a raw descriptor.
pub(super) fn write_fd(fd: libc::c_int, mut bytes: &[u8]) {
    while !bytes.is_empty() {
        // SAFETY: `bytes` is a valid readable slice of `bytes.len()` bytes and
        // `write` neither allocates nor retains the pointer.
        let written = unsafe { libc::write(fd, bytes.as_ptr().cast(), write_count(bytes.len())) };
        let Ok(written) = usize::try_from(written) else {
            // Negative: EINTR is worth retrying, anything else is unrecoverable
            // and must not spin.
            if std::io::Error::last_os_error().raw_os_error() == Some(libc::EINTR) {
                continue;
            }
            return;
        };
        if written == 0 {
            return;
        }
        bytes = &bytes[written..];
    }
}
