// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! INTERFACE-DIET (`AY_INTERFACE_DIET`) M1 blocking pins.
//!
//! The diet withholds POSITIVE pure-UF=UF Int equalities from the LIA
//! Nelson-Oppen interface and value-certifies the arrangement against RAW LIA
//! values before accepting Sat (see `combined_solvers/combiner_check` /
//! `interface-diet-campaign` memory). These pins guard the SOUNDNESS of that
//! transformation — the campaign is refuted for the *flip* (the certifier
//! re-floods on the deep recursive-ADT catamorphism), but the mechanism must
//! never produce a WRONG verdict.
//!
//! This is a STANDALONE test binary: it arms the diet for its whole process
//! (the mode is read once per process at combiner construction), so no other
//! test binary is affected. Runs serially (`--test-threads=1` in CI).

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;

/// Solve `smt` under `AY_INTERFACE_DIET=on` in a worker thread with a hard cap,
/// returning the final verdict line. The env var is set before every solve so
/// the diet is armed regardless of test execution order.
fn solve_diet(smt: &str, timeout: Duration) -> String {
    std::env::set_var("AY_INTERFACE_DIET", "on");
    let src = smt.to_string();
    let interrupt = Arc::new(AtomicBool::new(false));
    let interrupt_worker = Arc::clone(&interrupt);
    let (tx, rx) = std::sync::mpsc::channel();
    let _worker = std::thread::spawn(move || {
        let commands = parse(&src).expect("parse interface-diet pin fixture");
        let mut exec = Executor::new();
        exec.set_interrupt(interrupt_worker);
        exec.set_timeout(Some(timeout));
        let verdict = match exec.execute_all(&commands) {
            Ok(outputs) => outputs.last().cloned().unwrap_or_default(),
            Err(_) => "unknown".to_string(),
        };
        let _ = tx.send(verdict);
    });
    match rx.recv_timeout(timeout + Duration::from_secs(5)) {
        Ok(verdict) => verdict.trim().to_string(),
        Err(_) => {
            interrupt.store(true, Ordering::Relaxed);
            "unknown".to_string()
        }
    }
}

/// Pin (i): `f(x) <= 4 /\ g(x) = 5 /\ f(x) = g(x)` — the pure-UF=UF link
/// `f(x)=g(x)` is WITHHELD, but bridge const-propagation must still refute:
/// EUF merges `{f(x), g(x), 5}`, drains the eager `f(x)=5` (UF=const stays
/// eager), and LIA closes `5 <= 4`. If R1 regressed (const-prop starved) this
/// would wrongly go `sat`.
#[test]
fn pin_i_bridge_const_prop_unsat() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-const x Int)
        (assert (<= (f x) 4))
        (assert (= (g x) 5))
        (assert (= (f x) (g x)))
        (check-sat)
    "#;
    assert_eq!(solve_diet(smt, Duration::from_secs(20)), "unsat");
}

/// Pin (ii): unvaluable side. `f(x) = h(x)` withheld, `f(x) >= 10`, `h(x)`
/// otherwise unconstrained. The certifier must NOT falsely refute (no spurious
/// UNSAT from the missing-column handling) — a model exists (`h(x) = f(x)`).
#[test]
fn pin_ii_unvaluable_side_sat() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun h (Int) Int)
        (declare-const x Int)
        (assert (= (f x) (h x)))
        (assert (>= (f x) 10))
        (check-sat)
    "#;
    assert_eq!(solve_diet(smt, Duration::from_secs(20)), "sat");
}

/// Pin (iii): finite-domain shape. `f(x) = g(x)` withheld, `f(x) in {1,2}`,
/// `g(x) in {3,4}` (disjoint). The empty-`shared_equalities` finite-domain
/// Sat-unlock is gated off under a hidden interface (R2), so no false SAT
/// witness stands; the arrangement is refuted (`unsat`).
#[test]
fn pin_iii_finite_domain_gate_unsat() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-const x Int)
        (assert (= (f x) (g x)))
        (assert (or (= (f x) 1) (= (f x) 2)))
        (assert (or (= (g x) 3) (= (g x) 4)))
        (check-sat)
    "#;
    assert_eq!(solve_diet(smt, Duration::from_secs(20)), "unsat");
}

/// Pin (iv): become-shared via congruence. `c = g(a)`, `d = g(b)`, `c >= 5`,
/// `d <= 3`, `a = b`. EUF congruence yields `g(a) = g(b)` (pure-UF=UF, drained
/// and WITHHELD by C2), yet the eager class members `c`, `d` still force
/// `c = d` into LIA, closing `5 <= 3`. Guards that congruence-derived shared
/// equalities cannot hide a conflict.
#[test]
fn pin_iv_become_shared_unsat() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun g (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (declare-const d Int)
        (assert (= c (g a)))
        (assert (= d (g b)))
        (assert (>= c 5))
        (assert (<= d 3))
        (assert (= a b))
        (check-sat)
    "#;
    assert_eq!(solve_diet(smt, Duration::from_secs(20)), "unsat");
}

/// Certifier-direct pin: `f(x) = g(x)` withheld, `f(x) >= 5`, `g(x) <= 3`,
/// with NO eager (const/var) class member to drain the equality. The ONLY path
/// to `unsat` is the pre-Sat certifier detecting the EUF-equal resident pair's
/// RAW-LIA value mismatch and materializing `f(x)=g(x)` on demand (R1). A
/// certifier that consulted the EUF-fallback value (#6930) would see them
/// agree and wrongly accept `sat`.
#[test]
fn pin_certifier_value_mismatch_unsat() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-const x Int)
        (assert (= (f x) (g x)))
        (assert (>= (f x) 5))
        (assert (<= (g x) 3))
        (check-sat)
    "#;
    assert_eq!(solve_diet(smt, Duration::from_secs(20)), "unsat");
}

/// Positive control: a withheld pure-UF=UF equality with NO conflicting
/// constraint is genuine `sat`, and the certifier must CERTIFY it (reach the
/// terminal Sat) rather than diverge.
#[test]
fn pin_withheld_equality_sat() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-const x Int)
        (assert (= (f x) (g x)))
        (check-sat)
    "#;
    assert_eq!(solve_diet(smt, Duration::from_secs(20)), "sat");
}
