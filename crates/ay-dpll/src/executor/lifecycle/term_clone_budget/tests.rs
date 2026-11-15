// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::unwrap_used)]

//! Solver-free controls. Each case runs alone in a child test process because
//! the legacy term limit/divisor is global, unlike an executor's installed cap.

use super::*;
use ay_core::{Sort, TermStore};
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::time::{Duration, Instant};

const WORKER: &str = "AY_INTERNAL_PORTFOLIO_MEMORY_TEST_WORKER";
const TEST_PREFIX: &str = "executor::lifecycle::term_clone_budget::tests::";
static CHILD_LOCK: Mutex<()> = Mutex::new(());

fn isolated(name: &str) -> bool {
    if std::env::var(WORKER).as_deref() == Ok(name) {
        assert_eq!(TermStore::global_term_bytes(), 0);
        TermStore::set_global_term_memory_limit(64 * 1024 * 1024);
        TermStore::set_engine_count(1);
        return true;
    }
    let _lock = CHILD_LOCK.lock().unwrap();
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            &format!("{TEST_PREFIX}{name}"),
            "--nocapture",
            "--test-threads=1",
        ])
        .env(WORKER, name)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(20);
    loop {
        if child.try_wait().unwrap().is_some() {
            break;
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let output = child.wait_with_output().unwrap();
            panic!("isolated clone-budget test timed out: {output:?}");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("1 passed"),
        "the exact child test must actually run: {output:?}"
    );
    false
}

#[test]
fn installed_share_legacy_share_and_odd_zero_limits_are_exact() {
    if !isolated("installed_share_legacy_share_and_odd_zero_limits_are_exact") {
        return;
    }
    let mut executor = Executor::new();
    const GLOBAL: usize = 1 << 20;
    TermStore::set_global_term_memory_limit(GLOBAL);
    executor.set_term_memory_limit(Some(GLOBAL / 4));
    assert_eq!(executor.predictive_term_clone_budget(), GLOBAL / 8);
    TermStore::set_engine_count(16);
    assert_eq!(executor.predictive_term_clone_budget(), GLOBAL / 32);
    executor.set_term_memory_limit(None);
    assert_eq!(executor.predictive_term_clone_budget(), GLOBAL / 32);
    executor.set_term_memory_limit(Some(0));
    assert_eq!(executor.predictive_term_clone_budget(), 0);

    TermStore::set_global_term_memory_limit(101);
    TermStore::set_engine_count(1);
    for (installed, expected) in [(None, 50), (Some(7), 3), (Some(100), 50)] {
        executor.set_term_memory_limit(installed);
        assert_eq!(executor.predictive_term_clone_budget(), expected);
    }
    TermStore::set_engine_count(3);
    executor.set_term_memory_limit(Some(34));
    assert_eq!(executor.predictive_term_clone_budget(), 16);
    executor.set_term_memory_limit(Some(9));
    assert_eq!(executor.predictive_term_clone_budget(), 4);
    TermStore::set_global_term_memory_limit(0);
    assert_eq!(executor.predictive_term_clone_budget(), 0);
}

#[test]
fn separate_executors_keep_their_installed_clone_allowances() {
    if !isolated("separate_executors_keep_their_installed_clone_allowances") {
        return;
    }
    let mut first = Executor::new();
    let mut second = Executor::new();
    TermStore::set_global_term_memory_limit(8193);
    first.set_term_memory_limit(Some(1025));
    second.set_term_memory_limit(Some(4097));
    assert_eq!(first.predictive_term_clone_budget(), 512);
    assert_eq!(second.predictive_term_clone_budget(), 2048);
    second.set_term_memory_limit(None);
    assert_eq!(second.predictive_term_clone_budget(), 4096);
    assert_eq!(first.predictive_term_clone_budget(), 512);
    second.set_term_memory_limit(Some(0));
    assert_eq!(second.predictive_term_clone_budget(), 0);
    assert_eq!(first.predictive_term_clone_budget(), 512);
    TermStore::set_engine_count(16);
    assert_eq!(first.predictive_term_clone_budget(), 256);
    assert_eq!(second.predictive_term_clone_budget(), 0);
    TermStore::set_engine_count(1);
    assert_eq!(first.predictive_term_clone_budget(), 512);
}

#[test]
fn real_term_clone_admission_has_exact_and_one_short_local_boundaries() {
    if !isolated("real_term_clone_admission_has_exact_and_one_short_local_boundaries") {
        return;
    }
    let mut executor = Executor::new();
    for index in 0..32 {
        let _ = executor
            .ctx
            .terms
            .mk_var(format!("clone_{index}"), Sort::bitvec(64));
    }
    let bytes = executor
        .ctx
        .terms
        .diagnostic_clone_memory_bytes(usize::MAX)
        .unwrap();
    assert!(bytes > 0);
    let doubled = bytes.checked_mul(2).unwrap();
    TermStore::set_global_term_memory_limit(bytes.checked_mul(16).unwrap());
    let retained = TermStore::global_term_bytes();
    executor.set_term_memory_limit(Some(doubled));
    assert_eq!(executor.predictive_term_clone_budget(), bytes);
    assert_eq!(
        executor
            .ctx
            .terms
            .diagnostic_clone_memory_bytes(executor.predictive_term_clone_budget()),
        Some(bytes)
    );
    let cloned = executor.ctx.terms.clone();
    assert_eq!(
        TermStore::global_term_bytes(),
        retained + cloned.instance_term_bytes()
    );
    drop(cloned);
    assert_eq!(TermStore::global_term_bytes(), retained);

    executor.set_term_memory_limit(Some(doubled - 1));
    assert_eq!(executor.predictive_term_clone_budget(), bytes - 1);
    assert!(executor
        .ctx
        .terms
        .diagnostic_clone_memory_bytes(executor.predictive_term_clone_budget())
        .is_none());
    // The former legacy-only admission would still permit this exact clone.
    assert!(executor
        .ctx
        .terms
        .diagnostic_clone_memory_bytes(TermStore::per_engine_budget() / 2)
        .is_some());
    assert_eq!(TermStore::global_term_bytes(), retained);

    executor.set_term_memory_limit(Some(doubled));
    TermStore::set_global_term_memory_limit(doubled - 1);
    assert_eq!(executor.predictive_term_clone_budget(), bytes - 1);
    assert!(executor
        .ctx
        .terms
        .diagnostic_clone_memory_bytes(executor.predictive_term_clone_budget())
        .is_none());
    TermStore::set_global_term_memory_limit(doubled);
    assert_eq!(executor.predictive_term_clone_budget(), bytes);
    assert!(executor
        .ctx
        .terms
        .diagnostic_clone_memory_bytes(executor.predictive_term_clone_budget())
        .is_some());
    executor.set_term_memory_limit(Some(0));
    assert!(executor
        .ctx
        .terms
        .diagnostic_clone_memory_bytes(executor.predictive_term_clone_budget())
        .is_none());
    assert_eq!(TermStore::global_term_bytes(), retained);
}
