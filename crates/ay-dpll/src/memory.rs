// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cross-platform memory measurement for solver resource limits.
//!
//! Delegates to `ay_sys` for efficient syscall-based measurement
//! (no subprocess overhead).

/// Get current process memory usage in bytes.
///
/// Returns peak RSS via `getrusage` syscall. For a continuously-growing solver
/// process, peak RSS closely tracks current RSS because Rust's allocator does
/// not aggressively return memory to the OS.
///
/// Returns 0 if measurement fails or on unsupported platforms.
pub(crate) fn current_memory_bytes() -> usize {
    ay_sys::current_rss_bytes()
}

/// Check if memory limit is exceeded.
///
/// Returns `true` if current memory usage exceeds the specified limit.
/// If `limit` is `None`, returns `false` (no limit).
/// If memory measurement is unavailable, returns `false` (assume under limit).
#[inline]
pub(crate) fn memory_exceeded(limit: Option<usize>) -> bool {
    match limit {
        Some(limit) => {
            let current = current_memory_bytes();
            // If we can't measure memory (current == 0), assume under limit
            current > 0 && current > limit
        }
        None => false,
    }
}

#[cfg(test)]
#[path = "memory_tests.rs"]
mod tests;
