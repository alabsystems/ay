// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A guarded disequality split is lowered through its guard AS PRINTED.
//!
//! `(assert (not (= 1 x)))` is stored as `(= x 1)` and printed as the authored
//! `(= 1 x)`. At c57bd8481 the split lowering read the guard's operands off the
//! TermId, so this five-assertion problem published
//! `(step t7.split (cl (or (= 1 x) (not (<= x 1)) (not (<= 1 x)))) :rule la_disequality)`
//! and pinned carcara 1.1.0 refused the whole document: "checking failed on
//! step 't7.split' with rule 'la_disequality': expected terms to be equal: '1'
//! and 'x'" (`invalid`). The lowering now follows the printed operands
//! (`ay-proof`'s `alethe_printer/arith_disequality_split.rs`) and every
//! printed `la_disequality` is judged over its bytes
//! (`alethe_printer/printed_la_disequality.rs`).
//!
//! The document still carries holes from unrelated lowerings (two bound
//! mutexes and an equality-from-bounds lemma), so the most it can be today is
//! `holey`; it must never again be `invalid`.

use super::{
    carcara_verdict_without_allowances, require_carcara_or_skip, solve_unsat_and_get_proof,
    CarcaraVerdict,
};
use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

const SWAPPED_GUARD_SPLIT: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (not (= 1 x)))
(assert (<= 0 x))
(assert (<= x 2))
(assert (not (= x 0)))
(assert (not (= 2 x)))
(check-sat)
"#;

/// The same problem without `x != 2`: `x = 2` is a model (z3 4.8.12: `sat`).
const SWAPPED_GUARD_SPLIT_SAT: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (not (= 1 x)))
(assert (<= 0 x))
(assert (<= x 2))
(assert (not (= x 0)))
(check-sat)
"#;

#[test]
#[timeout(60_000)]
fn a_split_over_a_swapped_authored_guard_never_publishes_an_invalid_document() {
    let label = "printed_split_guard";
    let proof = solve_unsat_and_get_proof(SWAPPED_GUARD_SPLIT, label);
    assert!(
        !proof.contains(":rule trust"),
        "{label}: no trust step:\n{proof}"
    );
    assert!(
        proof.contains("(cl (or (= 1 x) (not (<= 1 x)) (not (<= x 1)))) :rule la_disequality)"),
        "{label}: the split over `(= 1 x)` must be lowered through its printed operands:\n{proof}"
    );
    assert!(
        !proof.contains("(or (= 1 x) (not (<= x 1)) (not (<= 1 x)))"),
        "{label}: the TermId-order operands must not reach the wire:\n{proof}"
    );
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let verdict = carcara_verdict_without_allowances(&carcara, label, SWAPPED_GUARD_SPLIT, &proof);
    assert!(
        matches!(verdict, CarcaraVerdict::Valid | CarcaraVerdict::Holey),
        "{label}: pinned carcara must not refuse any step ({verdict:?}):\n{proof}"
    );
}

/// NEGATIVE TWIN: the lowering is printer-only; the satisfiable twin stays
/// `sat`.
#[test]
#[timeout(60_000)]
fn the_satisfiable_twin_of_the_swapped_guard_split_stays_sat() {
    let script = format!("(set-option :produce-proofs true)\n{SWAPPED_GUARD_SPLIT_SAT}");
    let commands = parse(&script).expect("parse SMT-LIB script");
    let outputs = Executor::new()
        .execute_all(&commands)
        .expect("execute SMT-LIB script");
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
}
