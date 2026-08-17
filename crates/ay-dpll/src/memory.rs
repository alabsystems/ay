// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cross-platform memory measurement for solver resource limits.
//!
//! Delegates to `ay_sys` for efficient syscall-based measurement
//! (no subprocess overhead).

/// Get current process memory usage in bytes.
///
/// Prefers the live physical footprint: current RSS on Linux and
/// `phys_footprint` on macOS. Unlike `getrusage().ru_maxrss`, that observation
/// can fall after a solver releases memory, so one large solve does not
/// permanently exhaust every later per-solver memory limit in the same
/// process. Peak RSS remains the conservative fallback when the live probe
/// fails or is unavailable.
///
/// Returns 0 if measurement fails or on unsupported platforms.
pub(crate) fn current_memory_bytes() -> usize {
    observed_memory_bytes(ay_sys::current_footprint_bytes(), ay_sys::current_rss_bytes)
}

fn observed_memory_bytes(current_footprint: usize, peak_rss: impl FnOnce() -> usize) -> usize {
    if current_footprint == 0 {
        peak_rss()
    } else {
        current_footprint
    }
}

/// Check if memory limit is exceeded.
///
/// Returns `true` if current memory usage exceeds the specified limit.
/// If `limit` is `None`, returns `false` (no limit).
/// If memory measurement is unavailable, returns `false` (assume under limit).
#[inline]
pub(crate) fn memory_exceeded(limit: Option<usize>) -> bool {
    memory_exceeded_at(limit, current_memory_bytes())
}

fn memory_exceeded_at(limit: Option<usize>, current: usize) -> bool {
    limit.is_some_and(|limit| current > 0 && current > limit)
}

#[cfg(test)]
#[path = "memory_tests.rs"]
mod tests;
