// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Cross-vocabulary UF congruence over datatype selector-bridge equalities
//! (#dt-uf-bridge-congruence).
//!
//! Permanent RED→GREEN pin for the recursive-ADT catamorphism wall that owned
//! the rusthorn / `inc_some_list` / `binary_search_list` verification-consumer cluster.
//!
//! verification-consumer encodes a datatype field-read in TWO vocabularies at once: the
//! declared datatype selector `enum_payload_get_1_1(x)` AND a shadow
//! uninterpreted selector `list_cons_1(x)`, linked by a guarded bridge equality
//! `is-Cons(x) ⟹ enum_payload_get_1_1(x) = list_cons_1(x)`. A recursively-defined
//! logic function (`logic_sum`) is applied to BOTH terms, so the refutation needs
//! the congruence
//!   `list_cons_1(x) = enum_payload_get_1_1(x)
//!      ⟹ logic_sum(list_cons_1(x)) = logic_sum(enum_payload_get_1_1(x))`
//! to reach the LIA side. EUF closes this congruence only in the branch where the
//! bridge equality is already asserted, and the combined UF+LIA loop can return a
//! UF-containing-expression split (#7884) from a candidate assignment BEFORE that
//! branch is explored — degrading a provable UNSAT to `unknown`. Before the fix,
//! ay returned Incomplete at DT depth 3 and diverged at depth 4; z3 refutes the
//! same obligation in well under a second.
//!
//! The fixture is the FAITHFUL `inc_some_list` decisive obligation
//! (`tests/fixtures/dt_uf_bridge_congruence_inc_some_list.smt2`), reconstructed
//! WITH `declare-datatypes` (the raw driver dump without them produces a
//! misleading e-matching artifact). The `dt_uf_bridge_congruence_axioms` pass now
//! emits the congruence tautology statically as a base assertion, so the solve
//! closes at depth 3.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;

/// Fixture: the real `inc_some_list` dual-vocabulary catamorphism obligation.
const INC_SOME_LIST: &str = include_str!("../fixtures/dt_uf_bridge_congruence_inc_some_list.smt2");

/// Solve `smt` in a worker thread with a hard internal timeout + interrupt, so a
/// regression (the pre-fix depth-4 divergence) reports `unknown` instead of
/// wedging the harness. Returns the final verdict line.
fn solve_capped(smt: &str, timeout: Duration) -> String {
    let src = smt.to_string();
    let interrupt = Arc::new(AtomicBool::new(false));
    let interrupt_worker = Arc::clone(&interrupt);
    let (tx, rx) = std::sync::mpsc::channel();
    let _worker = std::thread::spawn(move || {
        let commands = parse(&src).expect("parse dt-uf-bridge-congruence fixture");
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

/// RED→GREEN: the faithful `inc_some_list` obligation is UNSAT (z3 <1s) and now
/// discharges through ay's ground DT+EUF+LIA combiner via the statically-emitted
/// cross-vocabulary congruence. Before the fix this returned `unknown` at DT
/// depth 3 and diverged at depth 4.
#[test]
fn inc_some_list_dual_vocab_obligation_is_unsat() {
    let verdict = solve_capped(INC_SOME_LIST, Duration::from_secs(60));
    assert_eq!(
        verdict, "unsat",
        "the inc_some_list dual-vocabulary catamorphism obligation must refute \
         via cross-vocabulary UF-bridge congruence (got `{verdict}`)"
    );
}

/// NO-WRONG-UNSAT soundness guard for the congruence pass. The bridge equality is
/// GUARDED by `is-Cons`; when the list is `Nil` the two selector vocabularies are
/// unconstrained, so a model may give their `sum`s DIFFERENT values. The emitted
/// congruence `(= (scons1 x) (tl x)) ⟹ (= (sum (scons1 x)) (sum (tl x)))` is a
/// tautology that does NOT force the results equal when the arguments are not —
/// so this stays SAT. A pass that wrongly merged the results would report `unsat`.
#[test]
fn bridge_congruence_does_not_force_unequal_argument_results() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-fun scons1 (List) List)
        (declare-fun sum (List) Int)
        (declare-const self List)
        ; bridge is guarded by is-Cons
        (assert (or (not (is-Cons self)) (= (scons1 self) (tl self))))
        ; self is Nil, so the guard is FALSE and the two vocabularies are free
        (assert (is-Nil self))
        (assert (not (= (sum (scons1 self)) (sum (tl self)))))
        (check-sat)
    "#;
    let verdict = solve_capped(smt, Duration::from_secs(20));
    assert_eq!(
        verdict, "sat",
        "guarded bridge congruence must not merge f(a),f(b) when a,b are not \
         equal (got `{verdict}`)"
    );
}
