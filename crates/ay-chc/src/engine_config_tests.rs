// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use serial_test::serial;

/// RAII guard that forces `global_memory_exceeded()` to return true.
/// Resets both the term-byte counter and process memory limit on drop.
struct GlobalTermBytesGuard;

impl GlobalTermBytesGuard {
    fn force_exceeded() -> Self {
        // DEFAULT_TERM_MEMORY_LIMIT is usize::MAX (unlimited), so the
        // term-byte comparison alone cannot trigger the check. Instead,
        // force the process-level RSS limit to 1 byte so that
        // process_memory_exceeded() fires.
        TermStore::force_process_memory_exceeded_for_testing();
        Self
    }
}

impl Drop for GlobalTermBytesGuard {
    fn drop(&mut self) {
        TermStore::reset_global_term_bytes();
        TermStore::reset_process_memory_limit_for_testing();
    }
}

#[test]
fn default_config() {
    let config = ChcEngineConfig::default();
    assert!(!config.verbose);
    assert!(config.cancellation_token.is_none());
    assert!(!config.is_cancelled());
}

#[test]
fn with_verbose() {
    let config = ChcEngineConfig::with_verbose(true);
    assert!(config.verbose);
}

#[test]
fn is_cancelled_no_token() {
    let config = ChcEngineConfig::new();
    assert!(!config.is_cancelled());
}

#[test]
fn is_cancelled_with_token() {
    let token = CancellationToken::new();
    let config = ChcEngineConfig::new().with_cancellation_token(Some(token.clone()));

    assert!(!config.is_cancelled());
    token.cancel();
    assert!(config.is_cancelled());
}

#[test]
fn builder_chaining() {
    let token = CancellationToken::new();
    let config = ChcEngineConfig::new()
        .verbose(true)
        .with_cancellation_token(Some(token));

    assert!(config.verbose);
    assert!(config.cancellation_token.is_some());
}

#[test]
#[serial(global_term_memory)]
fn is_cancelled_includes_memory_check() {
    // With a fresh counter and no cancellation token, is_cancelled should return false
    TermStore::reset_global_term_bytes();
    let config = ChcEngineConfig::new();
    assert!(
        !config.is_cancelled(),
        "fresh state should not be cancelled"
    );

    // Force global_memory_exceeded() to return true and verify is_cancelled triggers.
    // Guard ensures reset even if assertions panic (#2769 self-audit).
    let guard = GlobalTermBytesGuard::force_exceeded();
    assert!(
        config.is_cancelled(),
        "should be cancelled when global memory exceeded"
    );

    // Explicit drop to verify reset behavior.
    drop(guard);
    assert!(
        !config.is_cancelled(),
        "should not be cancelled after reset"
    );
}

#[test]
#[serial(global_term_memory)]
fn is_cancelled_memory_independent_of_token() {
    // Memory check should trigger cancellation even without a cancellation token.
    // Guard ensures reset even if assertions panic (#2769 self-audit).
    TermStore::reset_global_term_bytes();
    let config = ChcEngineConfig::new();
    assert!(config.cancellation_token.is_none());

    let _guard = GlobalTermBytesGuard::force_exceeded();
    assert!(
        config.is_cancelled(),
        "memory exceeded should cancel even without token"
    );

    // With a token that is NOT cancelled, memory should still trigger.
    let token = CancellationToken::new();
    let config_with_token = ChcEngineConfig::new().with_cancellation_token(Some(token));
    assert!(
        config_with_token.is_cancelled(),
        "memory exceeded should cancel even with un-triggered token"
    );
    // _guard drops here, resetting global counter
}
