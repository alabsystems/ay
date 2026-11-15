// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::resource::enter_check_stop;
use ay_frontend::parse;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

const FORMULA: &str = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(declare-const y (_ BitVec 128))
(assert (= (bvmul x y) x))
"#;

fn executor() -> Executor {
    let mut executor = Executor::new();
    executor.execute_all(&parse(FORMULA).unwrap()).unwrap();
    executor
}

#[test]
fn captured_encoding_stop_declines_native_result_and_credentials() {
    let mut executor = executor();
    let flag = Arc::new(AtomicBool::new(false));
    let stop = Arc::clone(&flag);
    let scope = enter_check_stop(Arc::new(move || stop.load(Ordering::Relaxed)));
    let owner = executor.bv_encoding_owner();
    flag.store(true, Ordering::Relaxed);
    assert!(!owner.open());
    drop(scope);
    flag.store(false, Ordering::Relaxed);
    assert!(!owner.open());
    assert_eq!(executor.abort_bv_encoding().unwrap(), SolveResult::Unknown);
    assert!(executor.last_result_is_unknown());
    assert!(executor.last_model.is_none());
}

#[test]
fn stopped_incremental_transaction_clears_encoding_but_preserves_push_depth() {
    let mut executor = executor();
    let commands = parse("(push 1) (check-sat)").unwrap();
    assert_eq!(executor.execute_all(&commands).unwrap(), vec!["sat"]);
    let old_depth = executor.incr_bv_state.as_ref().unwrap().scope_depth;
    assert!(old_depth > 0);
    assert!(!executor
        .incr_bv_state
        .as_ref()
        .unwrap()
        .term_to_bits
        .is_empty());
    assert_eq!(executor.abort_bv_encoding().unwrap(), SolveResult::Unknown);
    let state = executor.incr_bv_state.as_ref().unwrap();
    assert_eq!(state.scope_depth, old_depth);
    assert_eq!(state.pending_pushes, old_depth);
    assert!(state.persistent_sat.is_none());
    assert!(state.term_to_bits.is_empty());
    assert!(state.encoded_assertions.is_empty());
    assert!(executor.last_model.is_none());
    assert_eq!(
        executor
            .execute_all(&parse("(check-sat)").unwrap())
            .unwrap(),
        vec!["sat"]
    );
    assert_eq!(
        executor.incr_bv_state.as_ref().unwrap().scope_depth,
        old_depth
    );
}

#[test]
fn preclosed_callback_prohibits_native_bv_model_publication() {
    let mut executor = executor();
    let _scope = enter_check_stop(Arc::new(|| true));
    let output = executor
        .execute_all(&parse("(check-sat)").unwrap())
        .unwrap();
    assert_eq!(output, vec!["unknown"]);
    assert!(executor.last_result_is_unknown());
    assert!(executor.last_model.is_none());
}

#[test]
fn explicit_zero_term_cap_does_not_publish_a_bv_result() {
    let mut executor = executor();
    executor.set_term_memory_limit(Some(0));
    let output = executor
        .execute_all(&parse("(check-sat)").unwrap())
        .unwrap();
    assert_eq!(output, vec!["unknown"]);
    assert!(executor.last_model.is_none());
}

#[test]
fn independently_authorized_native_queries_do_not_retain_completed_cache_owners() {
    let mut executor = executor();
    let old_end = ay_core::time::Instant::now() + std::time::Duration::from_secs(20);
    let old_flag = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&old_flag);
    let first = enter_check_stop(Arc::new(move || {
        observed.load(Ordering::Relaxed) || ay_core::time::Instant::now() >= old_end
    }));
    executor.set_deadline(Some(old_end));
    assert_eq!(
        executor
            .execute_all(&parse("(push 1) (check-sat)").unwrap())
            .unwrap(),
        vec!["sat"]
    );
    let depth = executor.incr_bv_state.as_ref().unwrap().scope_depth;
    let old_guard = executor.bv_encoding_owner();
    drop(first);
    old_flag.store(true, Ordering::Relaxed);
    assert!(!old_guard.open());
    let new_end = ay_core::time::Instant::now() + std::time::Duration::from_secs(20);
    let second = enter_check_stop(Arc::new(move || ay_core::time::Instant::now() >= new_end));
    executor.set_deadline(Some(new_end));
    assert_eq!(
        executor
            .execute_all(&parse("(check-sat)").unwrap())
            .unwrap(),
        vec!["sat"]
    );
    assert_eq!(executor.incr_bv_state.as_ref().unwrap().scope_depth, depth);
    assert!(executor.last_model.is_some());
    assert!(!old_guard.open());
    drop(second);
}
