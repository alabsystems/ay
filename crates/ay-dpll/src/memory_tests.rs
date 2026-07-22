// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_current_memory_returns_nonzero() {
    let bytes = current_memory_bytes();
    // On supported platforms, we should get a non-zero value
    // A typical Rust test process uses at least 1MB
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    assert!(
        bytes > 0,
        "Memory should be non-zero on supported platforms"
    );
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    assert!(
        bytes > 1024 * 1024,
        "Memory should be at least 1MB for a test process"
    );
}

#[test]
fn test_memory_exceeded_no_limit() {
    // No limit means never exceeded
    assert!(!memory_exceeded(None));
}

#[test]
fn test_memory_exceeded_huge_limit() {
    // 100GB limit should never be exceeded by a test
    assert!(!memory_exceeded(Some(100 * 1024 * 1024 * 1024)));
}

#[test]
fn test_memory_exceeded_tiny_limit() {
    // 1KB limit should always be exceeded by a running process
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    assert!(memory_exceeded(Some(1024)));
}
