// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! A `:pattern` is an instantiation HINT and must not change the verdict.
//!
//! A trigger tells the solver WHERE to look for instantiations. It carries no
//! semantic content: `(forall ((x Int)) B)` and
//! `(forall ((x Int)) (! B :pattern (t)))` denote the same formula. Any verdict
//! difference between them is a defect, never an incompleteness trade.
//!
//! AY returned `sat` for the first and `unknown` for the second. Traced with
//! `--debug-cert`, the cause was NOT a quantifier-completeness gap — the
//! quantifier lane already returned `Sat`:
//!
//! ```text
//! CERT/after-classify: final=Ok("Sat") reason=None
//! CERT/restore-branch: final_sat=true bound_dep=true
//! CERT/finite-table:   certified SAT (1 foralls, 1 table syms)
//! CERT/gate[quantified] -> Unknown          <-- the downgrade
//! ```
//!
//! The finite-table SAT certificate had certified every snapshot universal
//! under an explicitly constructed interpretation, but on this route (CEGQI has
//! already classified the ground remainder `Sat`, so `final_result` is `Sat`
//! and the phase-2.5/3.5 grant arms — which fire only on `Unknown` — never run)
//! nothing recorded that authority. `apply_quantified_model_failclosed_gate`
//! then tried to evaluate a `forall` over an infinite domain against a
//! ground-core model, could not, and failed closed. The DT certificate already
//! had exactly this handoff (`dt_cert_grant_active`); the finite-table one did
//! not.
//!
//! The rejecting-direction tests are the point of this file. Recording
//! certificate authority must not become a way to skip checking: a formula the
//! axiom actually refutes must still come back `unsat`.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};
use ntest::timeout;

fn verdict(smt: &str) -> SolverOutcome {
    run_executor_smt_with_timeout(smt, 30).expect("execution should succeed")
}

const WITHOUT_PATTERN: &str = r#"
(set-logic AUFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (<= 0 (f x))))
(check-sat)
"#;

const WITH_PATTERN: &str = r#"
(set-logic AUFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (! (<= 0 (f x)) :pattern ((f x)))))
(check-sat)
"#;

/// The two formulas are logically identical, so the verdicts must agree.
///
/// Stated as an EQUALITY between the two runs rather than as "expect sat", so
/// the test keeps its meaning if AY's decision power on the triggerless form
/// ever changes: the invariant is that the annotation is inert, not that this
/// particular formula is decided.
#[test]
#[timeout(60_000)]
fn a_pattern_annotation_does_not_change_the_verdict() {
    let bare = verdict(WITHOUT_PATTERN);
    let patterned = verdict(WITH_PATTERN);
    assert_eq!(
        bare, patterned,
        "a :pattern is an instantiation hint with no semantic content, so it \
         cannot change the verdict — got {bare:?} without it and {patterned:?} \
         with it"
    );
}

/// Pins the direction too: this formula IS satisfiable (interpret `f` as the
/// constant 0), so the agreed verdict must be `sat`, not agreed-`unknown`.
#[test]
#[timeout(60_000)]
fn the_patterned_bound_axiom_is_decided_sat() {
    assert_eq!(
        verdict(WITH_PATTERN),
        SolverOutcome::Sat,
        "`forall x. 0 <= f(x)` is satisfied by f = 0"
    );
}

/// REJECTING DIRECTION. The certificate handoff must not become a skip: adding
/// a ground fact the axiom refutes must still produce `unsat`.
#[test]
#[timeout(60_000)]
fn a_ground_fact_refuting_the_patterned_axiom_is_still_unsat() {
    assert_eq!(
        verdict(
            r#"
(set-logic AUFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (! (<= 0 (f x)) :pattern ((f x)))))
(assert (= (f 3) (- 1)))
(check-sat)
"#
        ),
        SolverOutcome::Unsat,
        "f(3) = -1 contradicts the non-negativity axiom — deferring the \
         universal to the certificate must not lose this refutation"
    );
}

/// REJECTING DIRECTION, second shape: the contradiction reachable only through
/// the quantifier over a term the trigger does match.
#[test]
#[timeout(60_000)]
fn a_refutation_through_the_trigger_term_is_still_unsat() {
    assert_eq!(
        verdict(
            r#"
(set-logic AUFLIA)
(declare-fun f (Int) Int)
(declare-fun k () Int)
(assert (forall ((x Int)) (! (<= 0 (f x)) :pattern ((f x)))))
(assert (< (f k) 0))
(check-sat)
"#
        ),
        SolverOutcome::Unsat,
        "(< (f k) 0) contradicts the axiom at the symbolic index k"
    );
}
