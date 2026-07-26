// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded regressions distilled from the verification-consumer `slices/range` obligations.
//!
//! The original 245/271-line captures are retained under
//! `tests/fixtures/slr_expression_split/` as benchmark-campaign inputs.  They
//! combined two independent defects and consequently made poor default tests:
//! an Array-sorted expression-split gap and a convergence loop after candidate
//! models acquired conflicting `select` table rows.
//!
//! These reductions keep the decisive #7956 shape:
//!
//! - two opaque `seq_offset` applications are asserted equal;
//! - each appears below the same affine `+` context as an array index;
//! - a final array is a store chain over the current array; and
//! - reads at the equal affine indices have deliberately different values
//!   because one observes the pre-store array and one the post-store array.
//!
//! The array bridge must lift the EUF equality through the affine contexts,
//! retain its SAT-visible reason, and converge on the valid store model.  It
//! must not repeatedly discard the model due to a conflicted `select` table.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};
use ntest::timeout;

fn expect_sat(input: &str, label: &str) {
    let result = run_executor_smt_with_timeout(input, 20).expect("execution should succeed");
    assert_eq!(result, SolverOutcome::Sat, "{label}: expected SAT");
}

const SLICES_RANGE_SINGLE_STORE: &str = r#"
(set-logic QF_AUFLIA)
(declare-sort SeqInt 0)
(declare-fun seq_array (SeqInt) (Array Int Int))
(declare-fun seq_offset (SeqInt) Int)
(declare-const current SeqInt)
(declare-const final SeqInt)
(assert (= (seq_offset final) (seq_offset current)))
(assert (= (seq_array final)
           (store (seq_array current) (+ (seq_offset current) 1) 1)))
(assert (= (select (seq_array current) (+ (seq_offset current) 1)) 0))
(assert (= (select (seq_array final) (+ (seq_offset final) 1)) 1))
(check-sat)
"#;

const SLICES_RANGE_SYMBOLIC_TWO_STORE: &str = r#"
(set-logic QF_AUFLIA)
(declare-sort SeqInt 0)
(declare-fun seq_array (SeqInt) (Array Int Int))
(declare-fun seq_offset (SeqInt) Int)
(declare-const current SeqInt)
(declare-const final SeqInt)
(declare-const k Int)
(assert (= (seq_offset final) (seq_offset current)))
(assert (= (seq_array final)
           (store
             (store (seq_array current) (+ (seq_offset current) k) 1)
             (+ (seq_offset current) k 1)
             1)))
(assert (= (select (seq_array current) (+ (seq_offset current) k 1)) 0))
(assert (= (select (seq_array final) (+ (seq_offset final) k 1)) 1))
(check-sat)
"#;

const AFFINE_EUF_DISJUNCTION_WITH_SAT_DISEQUALITY_BRANCH: &str = r#"
(set-logic QF_AUFLIA)
(declare-sort SeqInt 0)
(declare-fun seq_offset (SeqInt) Int)
(declare-const current SeqInt)
(declare-const final SeqInt)
(declare-const values (Array Int Int))
(declare-const take-disequality Bool)
(assert (or (= (seq_offset final) (seq_offset current))
            take-disequality))
(assert (or (not take-disequality)
            (distinct (seq_offset final) (seq_offset current))))
(assert (= (select values (+ (seq_offset current) 1)) 0))
(assert (= (select values (+ (seq_offset final) 1)) 1))
(check-sat)
"#;

#[test]
#[timeout(30_000)]
fn slices_range_single_store_affine_euf_index_converges_sat_7956() {
    expect_sat(
        SLICES_RANGE_SINGLE_STORE,
        "slices/range single-store affine EUF index",
    );
}

#[test]
#[timeout(30_000)]
fn slices_range_symbolic_two_store_affine_euf_index_converges_sat_7956() {
    expect_sat(
        SLICES_RANGE_SYMBOLIC_TWO_STORE,
        "slices/range symbolic two-store affine EUF index",
    );
}

/// The equality arm makes the two reads alias and is inconsistent with their
/// pinned values.  The disjunction remains satisfiable through its explicit
/// disequality arm; an unguarded array edge would leak across that backtrack
/// and incorrectly report UNSAT.
#[test]
#[timeout(30_000)]
fn affine_euf_disjunction_backtracks_to_satisfiable_disequality_7956() {
    expect_sat(
        AFFINE_EUF_DISJUNCTION_WITH_SAT_DISEQUALITY_BRANCH,
        "affine EUF disjunction with satisfiable disequality branch",
    );
}
