// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded Linux memory-poll input, without a heap buffer for /proc contents.
//! Linux documents seven statm fields:
//! https://www.kernel.org/doc/html/latest/filesystems/proc.html#process-specific-subdirectories
//! Each host-width decimal value needs at most usize::BITS characters; one
//! separator per field also fits. Real statm is substantially smaller.
//!
//! Failure retains the caller's existing zero/peak-RSS advisory fallback.
//! Parsing still uses the original second-field UTF-8/usize semantics.

use std::io::{ErrorKind, Read};
use std::os::fd::FromRawFd;

const CAPACITY: usize = 7 * (usize::BITS as usize + 1);
const MAX_READS: usize = CAPACITY + 8;

pub(super) fn resident_pages() -> Option<usize> {
    // One open attempt: std's Unix File::open retries EINTR indefinitely.
    // This advisory sample must remain bounded even under repeated signals.
    // SAFETY: the static C path is terminated; read-only open needs no mode
    // argument. A nonnegative return is a fresh descriptor owned by this call.
    let fd = unsafe {
        libc::open(
            c"/proc/self/statm".as_ptr(),
            libc::O_RDONLY | libc::O_CLOEXEC,
        )
    };
    if fd < 0 {
        return None;
    }
    // SAFETY: fd is the successful fresh descriptor above, transferred exactly
    // once into File, which closes it on every success/error/unwind path.
    let mut file = unsafe { std::fs::File::from_raw_fd(fd) };
    read_resident_pages(&mut file)
}

fn read_resident_pages(reader: &mut impl Read) -> Option<usize> {
    let mut bytes = [0u8; CAPACITY];
    let mut extra = [0u8; 1];
    let mut used = 0;
    // Bound repeated interruptions as well as adversarial one-byte reads.
    // A failed read never accepts a partially received resident field.
    for _ in 0..MAX_READS {
        let target = if used < bytes.len() {
            &mut bytes[used..]
        } else {
            &mut extra[..]
        };
        match reader.read(target) {
            Ok(0) => return resident_field(&bytes[..used]),
            Ok(_) if used == bytes.len() => return None,
            Ok(count) => used += count,
            Err(error) if error.kind() == ErrorKind::Interrupted => continue,
            Err(_) => return None,
        }
    }
    None
}

fn resident_field(bytes: &[u8]) -> Option<usize> {
    std::str::from_utf8(bytes)
        .ok()?
        .split_whitespace()
        .nth(1)?
        .parse()
        .ok()
}

#[cfg(test)]
mod tests;
