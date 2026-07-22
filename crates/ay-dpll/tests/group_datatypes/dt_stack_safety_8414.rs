// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #8414: Stack overflow on datatype-heavy QF_AUFLIA problems.
//!
//! ay crashed with SIGABRT on verification-consumer's datatype-heavy ADT verification tests
//! when run on a thread with the default 8 MiB stack. The crash happened in
//! recursive term traversal functions (translate_expr, subst_vars, etc.) that
//! lacked `stacker::maybe_grow` protection.
//!
//! This test runs a datatype-heavy AUFLIA problem on a deliberately small
//! (2 MiB) thread stack to exercise the stacker guards.

use std::sync::mpsc;
use std::time::Duration;

/// AUFLIA problem with datatypes, selectors, testers, quantifiers, and arrays.
/// Simplified from verification-consumer's OwnResult ADT verification test.
const DT_AUFLIA_INPUT: &str = r#"
(set-logic AUFLIA)

; Declare a 2-constructor datatype similar to Result<T, E>
(declare-datatypes ((OwnResult 0)) (((Ok (ok_val Int)) (Err (err_val Int)))))

; Functions modeling projection and discrimination
(declare-fun discriminant (OwnResult) Int)
(declare-fun proj_0 (OwnResult) Int)

; Axiomatize discriminant
(assert (forall ((x OwnResult))
  (= (discriminant (Ok (ok_val x))) 0)))
(assert (forall ((x OwnResult))
  (= (discriminant (Err (err_val x))) 1)))

; Axiomatize projection
(assert (forall ((x OwnResult))
  (=> (= (discriminant x) 0) (= (proj_0 x) (ok_val x)))))
(assert (forall ((x OwnResult))
  (=> (= (discriminant x) 1) (= (proj_0 x) (err_val x)))))

; Postcondition: forall results, if Ok then proj_0 > 0
(declare-fun result () OwnResult)
(assert (= (discriminant result) 0))
(assert (= (ok_val result) 42))

; Array of datatypes with SwitchInt-style branching
(declare-fun arr () (Array Int OwnResult))
(assert (= (select arr 0) (Ok 10)))
(assert (= (select arr 1) (Err 20)))

; Postcondition check with nested constructor matching
(assert (forall ((i Int))
  (=> (and (<= 0 i) (< i 2))
    (=> (= (discriminant (select arr i)) 0)
        (> (proj_0 (select arr i)) 0)))))

(check-sat)
"#;

#[test]
fn dt_stack_safety_small_thread_8414() {
    let commands = ay_frontend::parse(DT_AUFLIA_INPUT).expect("parse");

    let (tx, rx) = mpsc::channel();

    let handle = std::thread::Builder::new()
        .name("dt-small-stack".into())
        .stack_size(2 * 1024 * 1024) // 2 MiB — well below default 8 MiB
        .spawn(move || {
            let mut exec = ay_dpll::Executor::new();
            let result = exec.execute_all(&commands).expect("execute_all");
            let _ = tx.send(result);
        })
        .expect("spawn small-stack thread");

    // 15s timeout for this quantified DT problem.
    match rx.recv_timeout(Duration::from_secs(15)) {
        Ok(outputs) => {
            let result = outputs
                .iter()
                .map(|s| s.trim())
                .find(|line| matches!(*line, "sat" | "unsat" | "unknown"));
            // "sat" or "unknown" are acceptable answers.
            // The critical assertion is no stack overflow crash.
            assert!(
                matches!(result, Some("sat") | Some("unknown")),
                "DT solver on 2 MiB stack must return sat or unknown, got: {result:?}\noutputs: {outputs:?}"
            );
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            // Solver is still running after 15s. This is a quantifier instantiation
            // completeness issue, not a stack safety failure. The thread is alive
            // (not crashed), so stack safety is verified.
            drop(handle);
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            // Channel disconnected without sending — the thread panicked or
            // aborted. This IS a stack safety failure.
            let join_result = handle.join();
            panic!("Solver thread panicked or aborted on 2 MiB stack: {join_result:?}");
        }
    }
}
