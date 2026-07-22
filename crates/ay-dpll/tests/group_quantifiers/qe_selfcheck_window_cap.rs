// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Termination regression tests for the deep-QE pre-pass on machine-integer
//! type-range-guarded existential witnesses (#clusterD divergence).
//!
//! CONTEXT. deductive-checks encodes Rust integer-typed `exists`/`choose` goals by
//! wrapping the bound variable in type-range guards, then refutes the
//! negation: `(not (exists ((x Int)) (and (>= x -2³¹) (< x 2³¹) (= x 42))))`
//! must come back UNSAT. The deep-QE pre-pass routes this pure-LIA
//! existential through Cooper, whose fail-closed equivalence self-check used
//! to decide `∃x.φ[σ]` by EXHAUSTIVE enumeration of `x` in a window scaled by
//! `Σ|consts|` — the 2³¹/2³² guard constants pushed the window to ~10¹⁰
//! values × ~200 battery assignments, an effectively nonterminating
//! 100%-CPU loop inside `check_sat` that never polled the solve interrupt.
//!
//! THE FIX. `SEARCH_WINDOW_CAP` (qe/cooper/selfcheck.rs) refuses over-cap
//! windows fail-closed — the elimination is discarded, the ORIGINAL
//! quantified assertion flows into the downstream quantifier machinery, which
//! decides these witness shapes directly — and the pre-pass now polls the
//! executor's solve-interrupt flag between eliminator invocations so an
//! application watchdog can always land. Pre-fix, every test below hangs
//! (in-process watchdog never observed); post-fix they all decide UNSAT well
//! inside the deterministic budget.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};

fn assert_unsat_within_budget(smt: &str, label: &str) {
    let result = run_executor_smt_with_timeout(smt, 60).expect("execution should succeed");
    assert_eq!(
        result,
        SolverOutcome::Unsat,
        "#clusterD {label}: refuting a valid type-range-guarded existential \
         witness must be UNSAT within the budget (pre-fix: nonterminating \
         self-check enumeration). Got: {result:?}"
    );
}

/// deductive-checks `quantifier_exists_witness` shape: `exists(|x: i32| x == 42)`.
#[test]
fn test_i32_exists_witness_range_guard_unsat() {
    assert_unsat_within_budget(
        r"
(set-logic LIA)
(assert (not (exists ((x Int))
  (and (and (>= x (- 2147483648)) (< x 2147483648)) (= x 42)))))
(check-sat)
",
        "i32 witness",
    );
}

/// deductive-checks `test_exists_unsigned_in_range_verified` shape:
/// `exists(|x: u32| x == 5)`.
#[test]
fn test_u32_exists_witness_range_guard_unsat() {
    assert_unsat_within_budget(
        r"
(set-logic LIA)
(assert (not (exists ((x Int))
  (and (and (>= x 0) (< x 4294967296)) (= x 5)))))
(check-sat)
",
        "u32 witness",
    );
}

/// deductive-checks `test_choose_with_explicit_witness_preserves_conjunction_bounds`
/// shape: `choose(|w: i32| w >= 0 && w < 10)` under the i32 type-range guard.
#[test]
fn test_choose_conjunction_bounds_range_guard_unsat() {
    assert_unsat_within_budget(
        r"
(set-logic LIA)
(assert (not (exists ((w Int))
  (and (and (>= w (- 2147483648)) (< w 2147483648))
       (and (>= w 0) (< w 10))))))
(check-sat)
",
        "choose conjunction bounds",
    );
}

/// deductive-checks `quantifier_nested_exists_forall` shape:
/// `exists y. forall x. (x != y || x == y)` — a tautological inner forall
/// under the i32 range guard on `y`.
#[test]
fn test_nested_exists_forall_range_guard_unsat() {
    assert_unsat_within_budget(
        r"
(set-logic LIA)
(assert (not (exists ((y Int))
  (and (and (>= y (- 2147483648)) (< y 2147483648))
       (forall ((x Int)) (or (not (= x y)) (= x y)))))))
(check-sat)
",
        "nested exists-forall",
    );
}
