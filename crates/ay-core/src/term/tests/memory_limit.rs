// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;
use serial_test::serial;

struct GlobalMemoryStateGuard;

impl GlobalMemoryStateGuard {
    fn new() -> Self {
        TermStore::reset_process_memory_limit_for_testing();
        TermStore::reset_global_term_bytes();
        TermStore::reset_global_term_memory_limit_for_testing();
        TermStore::set_engine_count(1);
        Self
    }
}

impl Drop for GlobalMemoryStateGuard {
    fn drop(&mut self) {
        TermStore::reset_process_memory_limit_for_testing();
        TermStore::reset_global_term_bytes();
        TermStore::reset_global_term_memory_limit_for_testing();
        TermStore::set_engine_count(1);
    }
}

#[test]
#[serial(global_term_memory)]
fn default_global_term_memory_limit_is_unlimited() {
    let _guard = GlobalMemoryStateGuard::new();

    TermStore::force_global_term_bytes_for_testing(usize::MAX);

    assert!(
        !TermStore::global_memory_exceeded(),
        "default term-memory limit should not reintroduce a fixed cap"
    );
    assert_eq!(TermStore::per_engine_budget(), usize::MAX);
}

#[test]
#[serial(global_term_memory)]
fn global_memory_exceeded_uses_configured_limit() {
    let _guard = GlobalMemoryStateGuard::new();

    let limit = 1024 * 1024 * 1024;
    TermStore::set_global_term_memory_limit(limit);
    TermStore::force_global_term_bytes_for_testing(limit - 64 * 1024 * 1024);
    assert!(
        !TermStore::global_memory_exceeded(),
        "configured term-memory limit should not fire below the cap"
    );

    TermStore::force_global_term_bytes_for_testing(limit + 1);
    assert!(
        TermStore::global_memory_exceeded(),
        "configured term-memory limit should cap global term bytes"
    );
}

#[test]
#[serial(global_term_memory)]
fn reset_global_term_memory_limit_restores_default() {
    let _guard = GlobalMemoryStateGuard::new();

    TermStore::set_global_term_memory_limit(7);
    TermStore::force_global_term_bytes_for_testing(8);
    assert!(TermStore::global_memory_exceeded());

    TermStore::reset_global_term_memory_limit_for_testing();
    TermStore::force_global_term_bytes_for_testing(usize::MAX);
    assert!(
        !TermStore::global_memory_exceeded(),
        "reset helper should restore the default unlimited term-memory limit"
    );
}

#[test]
#[serial(global_term_memory)]
fn per_engine_budget_uses_configured_limit() {
    let _guard = GlobalMemoryStateGuard::new();

    TermStore::set_global_term_memory_limit(4096);

    TermStore::set_engine_count(4);
    assert_eq!(TermStore::per_engine_budget(), 1024);

    TermStore::set_engine_count(0);
    assert_eq!(
        TermStore::per_engine_budget(),
        4096,
        "engine count should still clamp to one"
    );

    TermStore::reset_global_term_memory_limit_for_testing();
    TermStore::set_engine_count(2);
    assert_eq!(TermStore::per_engine_budget(), usize::MAX / 2);
}
