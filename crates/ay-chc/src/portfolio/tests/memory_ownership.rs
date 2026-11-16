// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Only mock engines run here. Exact child processes isolate the process-global
//! memory ledger from unrelated tests; no SMT search or verdict is exercised.

use super::*;
use ay_core::{Sort, TermStore};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

const WORKER: &str = "AY_INTERNAL_PORTFOLIO_MEMORY_TEST_WORKER";
const TEST_PREFIX: &str = "portfolio::tests::memory_ownership::";
static CHILD_LOCK: Mutex<()> = Mutex::new(());

/// Return true only in the exact, isolated child running this test. Launches
/// are serialized, and the parent kills and reaps a child that exceeds 20 s.
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
    let deadline = std::time::Instant::now() + Duration::from_secs(20);
    loop {
        if child.try_wait().unwrap().is_some() {
            break;
        }
        if std::time::Instant::now() >= deadline {
            let _ = child.kill();
            let output = child.wait_with_output().unwrap();
            panic!("isolated memory test timed out: {output:?}");
        }
        thread::sleep(Duration::from_millis(10));
    }
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("1 passed"),
        "the exact child test must actually run: {output:?}"
    );
    false
}

fn config(count: usize) -> PortfolioConfig {
    PortfolioConfig {
        engines: (0..count)
            .map(|_| EngineConfig::Pdr(PdrConfig::default()))
            .collect(),
        parallel: true,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        enable_preprocessing: false,
        engine_budgets: Default::default(),
        memory_budget: None,
        strict_proofs: true,
        external_cancellation: None,
    }
}

fn store(label: &str) -> TermStore {
    let mut terms = TermStore::new();
    for index in 0..32 {
        let _ = terms.mk_var(format!("{label}_{index}"), Sort::bitvec(64));
    }
    assert!(terms.instance_term_bytes() > 0);
    terms
}

fn unknown() -> EngineResult {
    EngineResult::Unified(PortfolioResult::Unknown, "MEMORY_TEST")
}

fn observer(count: usize, expected: usize, calls: Arc<AtomicUsize>) -> PortfolioSolver {
    PortfolioSolver::new(ChcProblem::new(), config(count)).with_sequential_test_engine(
        move |_, _| {
            assert_eq!(TermStore::global_term_bytes(), expected);
            calls.fetch_add(1, Ordering::SeqCst);
            unknown()
        },
    )
}

#[test]
fn schedule_entry_preserves_embedding_stores_and_clone_drop_ownership() {
    if !isolated("schedule_entry_preserves_embedding_stores_and_clone_drop_ownership") {
        return;
    }
    let original = store("original");
    let bytes = original.instance_term_bytes();
    assert_eq!(TermStore::global_term_bytes(), bytes);
    let cloned = original.clone();
    assert_eq!(cloned.instance_term_bytes(), bytes);
    assert_eq!(TermStore::global_term_bytes(), 2 * bytes);
    let calls = Arc::new(AtomicUsize::new(0));
    let parallel = observer(2, 2 * bytes, calls.clone());
    assert!(matches!(
        parallel.solve_parallel(),
        PortfolioResult::Unknown
    ));
    assert_eq!(calls.load(Ordering::SeqCst), 2);
    assert_eq!(TermStore::global_term_bytes(), 2 * bytes);
    let sequential = observer(3, 2 * bytes, calls.clone());
    assert!(matches!(
        sequential.solve_sequential(),
        PortfolioResult::Unknown
    ));
    assert_eq!(calls.load(Ordering::SeqCst), 5);
    assert_eq!(TermStore::global_term_bytes(), 2 * bytes);
    drop(original);
    assert_eq!(TermStore::global_term_bytes(), bytes);
    let later = observer(1, bytes, calls.clone());
    assert!(matches!(later.solve_sequential(), PortfolioResult::Unknown));
    assert_eq!(calls.load(Ordering::SeqCst), 6);
    drop(cloned);
    assert_eq!(TermStore::global_term_bytes(), 0);
}

#[test]
fn overlapping_portfolios_do_not_erase_live_worker_allocations() {
    if !isolated("overlapping_portfolios_do_not_erase_live_worker_allocations") {
        return;
    }
    let retained = store("embedding");
    let retained_bytes = retained.instance_term_bytes();
    let (started_tx, started_rx) = mpsc::channel();
    let (release_tx, release_rx) = mpsc::channel();
    let release_rx = Mutex::new(release_rx);
    let completed = Arc::new(AtomicBool::new(false));
    let worker_completed = completed.clone();
    let first = PortfolioSolver::new(ChcProblem::new(), config(1)).with_sequential_test_engine(
        move |_, _| {
            let worker = store("worker");
            let bytes = worker.instance_term_bytes();
            let copy = worker.clone();
            started_tx.send(bytes).unwrap();
            release_rx
                .lock()
                .unwrap()
                .recv_timeout(Duration::from_secs(5))
                .unwrap();
            assert_eq!(TermStore::global_term_bytes(), retained_bytes + 2 * bytes);
            drop(copy);
            assert_eq!(TermStore::global_term_bytes(), retained_bytes + bytes);
            drop(worker);
            assert_eq!(TermStore::global_term_bytes(), retained_bytes);
            worker_completed.store(true, Ordering::SeqCst);
            unknown()
        },
    );
    let handle = thread::spawn(move || first.solve_parallel());
    let worker_bytes = started_rx.recv_timeout(Duration::from_secs(5)).unwrap();
    let expected = retained_bytes + 2 * worker_bytes;
    assert_eq!(TermStore::global_term_bytes(), expected);
    let calls = Arc::new(AtomicUsize::new(0));
    let second = observer(2, expected, calls.clone());
    assert!(matches!(second.solve_parallel(), PortfolioResult::Unknown));
    assert!(matches!(
        second.solve_sequential(),
        PortfolioResult::Unknown
    ));
    assert_eq!(calls.load(Ordering::SeqCst), 4);
    assert_eq!(TermStore::global_term_bytes(), expected);
    release_tx.send(()).unwrap();
    assert!(matches!(handle.join().unwrap(), PortfolioResult::Unknown));
    assert!(completed.load(Ordering::SeqCst));
    assert_eq!(TermStore::global_term_bytes(), retained_bytes);
    drop(retained);
    assert_eq!(TermStore::global_term_bytes(), 0);
}

#[test]
fn a_live_over_budget_store_refuses_both_schedules_without_launching() {
    if !isolated("a_live_over_budget_store_refuses_both_schedules_without_launching") {
        return;
    }
    let retained = store("over_budget");
    let bytes = retained.instance_term_bytes();
    let calls = Arc::new(AtomicUsize::new(0));
    let solver = observer(2, bytes, calls.clone());
    TermStore::set_global_term_memory_limit(bytes - 1);
    assert!(TermStore::global_memory_exceeded());
    assert!(matches!(solver.solve_parallel(), PortfolioResult::Unknown));
    assert_eq!(TermStore::global_term_bytes(), bytes);
    assert!(matches!(
        solver.solve_sequential(),
        PortfolioResult::Unknown
    ));
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    assert_eq!(TermStore::global_term_bytes(), bytes);
    assert!(TermStore::global_memory_exceeded());
    drop(retained);
    assert_eq!(TermStore::global_term_bytes(), 0);
    assert!(!TermStore::global_memory_exceeded());
}

#[test]
fn fallback_shares_are_local_and_explicit_limits_keep_precedence() {
    if !isolated("fallback_shares_are_local_and_explicit_limits_keep_precedence") {
        return;
    }
    const LIMIT: usize = 65_537;
    TermStore::set_global_term_memory_limit(LIMIT);
    TermStore::set_engine_count(7);
    let first = config(2);
    let second = config(5);
    assert_eq!(first.per_engine_term_budget(2), Some(LIMIT / 2));
    assert_eq!(second.per_engine_term_budget(5), Some(LIMIT / 5));
    assert_eq!(first.per_engine_term_budget(2), Some(LIMIT / 2));
    for count in [0, 1] {
        assert_eq!(first.per_engine_term_budget(count), Some(LIMIT));
    }
    let calls = Arc::new(AtomicUsize::new(0));
    let parallel = observer(2, 0, calls.clone());
    assert!(matches!(
        parallel.solve_parallel(),
        PortfolioResult::Unknown
    ));
    assert_eq!(TermStore::per_engine_budget(), LIMIT / 7);
    let sequential = observer(3, 0, calls.clone());
    assert!(matches!(
        sequential.solve_sequential(),
        PortfolioResult::Unknown
    ));
    assert_eq!(TermStore::per_engine_budget(), LIMIT / 7);
    assert_eq!(calls.load(Ordering::SeqCst), 5);
    TermStore::set_engine_count(11);
    assert_eq!(first.per_engine_term_budget(2), Some(LIMIT / 2));
    let mut explicit = first.clone();
    explicit.memory_budget = Some(4097);
    assert_eq!(explicit.per_engine_term_budget(2), Some(2048));
    assert_eq!(explicit.per_engine_term_budget(0), Some(4097));
    explicit.memory_budget = Some(0);
    assert_eq!(explicit.per_engine_term_budget(2), Some(0));
    assert_eq!(explicit.per_engine_term_budget(0), Some(0));
    TermStore::set_global_term_memory_limit(0);
    assert_eq!(second.per_engine_term_budget(5), Some(0));
    explicit.memory_budget = Some(4097);
    assert_eq!(explicit.per_engine_term_budget(2), Some(2048));
    assert_eq!(TermStore::global_term_bytes(), 0);
}
