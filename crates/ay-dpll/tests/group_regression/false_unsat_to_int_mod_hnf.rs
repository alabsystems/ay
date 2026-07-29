// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression: `(mod (to_int r) k)` on a Real VARIABLE was refuted.
//!
//! ```smt2
//! (set-logic QF_LIRA)
//! (declare-const r Real)
//! (assert (= r (- 1.5)))
//! (assert (= (mod (to_int r) 3) 1))
//! (check-sat)
//! ```
//!
//! AY answered `unsat` (and emitted an Alethe refutation for it). The formula
//! is **satisfiable**: SMT-LIB 2.6 `Reals_Ints` defines `to_int` as floor — the
//! unique integer with `to_int(m) <= m < to_int(m) + 1` — so `to_int(-1.5) = -2`,
//! and SMT-LIB 2.6 `Ints` defines Euclidean `mod` by
//! `m = n * div(m,n) + mod(m,n)` with `0 <= mod(m,n) < |n|`, so
//! `-2 = 3 * (-1) + 1` gives `mod(-2, 3) = 1`.
//!
//! Root cause: `crates/ay-theories/lia/src/cuts.rs::parse_equality_for_hnf` ran
//! the linear collector with `fallback_as_var = false`, which silently DROPS a
//! subterm it cannot place in a column. `(to_int r)` is an opaque Int-sorted
//! application, so the mod-elimination equality `to_int(r) = 3q + rr` entered
//! the HNF constraint matrix as `-3q - rr = 0` — an equality nobody asserted.
//! That fabricated row plus `rr = 1` has no integer solution, so HNF emitted
//! the "cut" `q >= 0`, which was installed as an LRA bound carrying the two
//! REAL equality atoms as its reasons, and the false conflict propagated out as
//! a proof-carrying wrong `unsat`.
//!
//! The assertions below are ORACLE-FREE: they never demand `sat`, only that AY
//! must not claim `unsat`. `unknown` is an acceptable (honest) answer.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};
use anyhow::Result;
use ntest::timeout;

const BUDGET_SECS: u64 = 10;

fn mod_of_to_int(numerator: i64, denominator: i64, modulus: i64, rhs: i64) -> String {
    let rhs_term = if rhs < 0 {
        format!("(- {})", -rhs)
    } else {
        rhs.to_string()
    };
    format!(
        "(set-logic QF_LIRA)\n\
         (declare-const r Real)\n\
         (assert (= (* r {denominator}.0) (- {numerator}.0)))\n\
         (assert (= (mod (to_int r) {modulus}) {rhs_term}))\n\
         (check-sat)\n"
    )
}

/// The exact reproducer. `r = -1.5`, `to_int(r) = -2`, `mod(-2, 3) = 1`.
#[test]
#[timeout(30_000)]
fn to_int_mod_on_negative_real_is_not_refuted() -> Result<()> {
    let smt = "(set-logic QF_LIRA)\n\
               (declare-const r Real)\n\
               (assert (= r (- 1.5)))\n\
               (assert (= (mod (to_int r) 3) 1))\n\
               (check-sat)\n";
    let outcome = run_executor_smt_with_timeout(smt, BUDGET_SECS)?;
    assert_ne!(
        outcome,
        SolverOutcome::Unsat,
        "(mod (to_int -1.5) 3) = 1 holds: to_int is floor so to_int(-1.5) = -2, \
         and -2 = 3*(-1) + 1 so the Euclidean remainder is 1"
    );
    Ok(())
}

/// Oracle-free self-consistency sweep. `mod _ 3` is a TOTAL function with range
/// `{0, 1, 2}`, so for a fixed `r` at least one of `k = 0, 1, 2` must be
/// satisfiable — answering `unsat` to all three is jointly impossible whatever
/// the value of `to_int(r)` is. The pre-fix build answered `unsat` for every
/// `k` in `-2..=3`.
#[test]
#[timeout(90_000)]
fn to_int_mod_residue_sweep_is_not_uniformly_refuted() -> Result<()> {
    for (numerator, denominator) in [(3_i64, 2_i64), (5, 2), (7, 2), (1, 2)] {
        let mut all_unsat = true;
        for k in 0..3 {
            let smt = mod_of_to_int(numerator, denominator, 3, k);
            if run_executor_smt_with_timeout(&smt, BUDGET_SECS)? != SolverOutcome::Unsat {
                all_unsat = false;
                break;
            }
        }
        assert!(
            !all_unsat,
            "`mod _ 3` has range {{0,1,2}}, so refuting all three residues for \
             r = -{numerator}/{denominator} is jointly impossible"
        );
    }
    Ok(())
}

/// The same shape reached through a strict interval rather than an exact value:
/// `-1.6 < r < -1.4` forces `to_int(r) = -2` and hence `mod(to_int(r), 3) = 1`.
#[test]
#[timeout(30_000)]
fn to_int_mod_under_strict_bounds_is_not_refuted() -> Result<()> {
    let smt = "(set-logic QF_LIRA)\n\
               (declare-const r Real)\n\
               (assert (< r (- 1.4)))\n\
               (assert (> r (- 1.6)))\n\
               (assert (= (mod (to_int r) 3) 1))\n\
               (check-sat)\n";
    let outcome = run_executor_smt_with_timeout(smt, BUDGET_SECS)?;
    assert_ne!(
        outcome,
        SolverOutcome::Unsat,
        "every r in (-1.6, -1.4) has to_int(r) = -2 and mod(-2, 3) = 1"
    );
    Ok(())
}

/// The residues AY refutes must be the ones the standard refutes. `to_int(-1.5)`
/// is `-2` and `mod(-2, 3) = 1`, so `k = 0` and `k = 2` ARE unsatisfiable — the
/// fix must not have been a blanket "never answer unsat here".
#[test]
#[timeout(30_000)]
fn to_int_mod_still_refutes_the_wrong_residues() -> Result<()> {
    for k in [0_i64, 2] {
        let smt = mod_of_to_int(3, 2, 3, k);
        assert_eq!(
            run_executor_smt_with_timeout(&smt, BUDGET_SECS)?,
            SolverOutcome::Unsat,
            "mod(to_int(-1.5), 3) = 1, so residue {k} must stay refuted"
        );
    }
    Ok(())
}
