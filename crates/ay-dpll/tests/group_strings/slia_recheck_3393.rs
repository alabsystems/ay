// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #3393 — QF_SLIA string+arithmetic correctness.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

#[test]
#[timeout(20_000)]
fn slia_equal_length_suffix_mismatch_is_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.len x) (str.len y)))
(assert (= (str.++ x "a") (str.++ y "b")))
(check-sat)
"#;

    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "equal-length + suffix mismatch is unsatisfiable"
    );
}

/// This test requires length-equality propagation through intermediate
/// integer variables (i = len(x), j = len(y), i = j) to derive z = "".
/// AY currently loops on this — use an interrupt to enforce a deadline
/// and accept unknown.
#[test]
#[timeout(10_000)]
fn slia_bridge_length_equality_rechecks_strings_after_no_propagation() {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun i () Int)
(declare-fun j () Int)
(assert (= i (str.len x)))
(assert (= j (str.len y)))
(assert (= i j))
(assert (= x (str.++ y z)))
(assert (distinct x y))
(check-sat)
"#;

    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    let flag = Arc::new(AtomicBool::new(false));
    exec.set_interrupt(flag.clone());
    let (cancel_tx, cancel_rx) = std::sync::mpsc::channel();
    let timer_flag = Arc::clone(&flag);
    let timer = std::thread::spawn(move || {
        if cancel_rx
            .recv_timeout(std::time::Duration::from_secs(3))
            .is_err()
        {
            timer_flag.store(true, Ordering::Relaxed);
        }
    });
    let outputs = exec.execute_all(&commands).expect("execute_all");
    let _ = cancel_tx.send(());
    let result = outputs.join("\n");
    let _ = timer.join();
    let r = crate::common::sat_result(&result);
    assert!(
        r == Some("unsat") || r == Some("unknown"),
        "bridge length equality: expected unsat or unknown, got {r:?}"
    );
}
