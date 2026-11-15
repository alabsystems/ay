// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A `forall_inst` instance whose authored comparison is ground, such as
//! `(> 3 3)` from `(forall ((w Int)) (> w 3))`, must never be bridged onto its
//! operand-swapped canonical `(< 3 3)` through `comp_simplify`: pinned carcara
//! EVALUATES `(< c d)` over two numerals instead of rewriting it to
//! `(not (<= d c))` (`checker/rules/simplification.rs` at `9a352ee`).
//!
//! MEASURED with the printed-equivalence comparison schema
//! (`surface_equivalence/comparison.rs`) before `comparison_reversal_step`
//! declined that pair: `(forall ((w Int)) (> w 3))` went from a `valid`
//! document to one pinned carcara rejects at `(= (not (<= 3 3)) (< 3 3))`,
//! and `--strict-proofs` answered `unsat` with it; the guarded
//! `(=> (> w 0) (P w))` instance at `2` went from an honest hole to the same
//! invalid step. The pattern-guarded instances below (`(> 5 7)`, `(> 5.0 7.0)`,
//! `(> (g 5) (g 5))`, and the bounded-array VC shape `(> 10 2)`) each went
//! from `valid` to `invalid` the same way, with `--strict-proofs` printing
//! `unsat_admission=strict-proof` over the rejected document.

use super::{
    carcara_verdict_without_allowances, require_carcara_or_skip, solve_unsat_and_get_proof,
    CarcaraVerdict,
};
use ntest::timeout;

const ROOT: &str = "(set-logic UFLIA)\n(assert (forall ((w Int)) (> w 3)))\n(check-sat)\n";
const GUARDED: &str = "(set-logic UFLIA)\n(declare-fun P (Int) Bool)\n\
                       (assert (forall ((w Int)) (=> (> w 0) (P w))))\n\
                       (assert (not (P 2)))\n(check-sat)\n";

#[test]
#[timeout(120_000)]
fn a_ground_comparison_instance_keeps_a_valid_document() {
    let proof = solve_unsat_and_get_proof(ROOT, "ground_comparison_root");
    assert!(
        !proof.contains("(cl (= (not (<= 3 3)) (< 3 3)))"),
        "{proof}"
    );
    if let Some(carcara) = require_carcara_or_skip() {
        assert_eq!(
            carcara_verdict_without_allowances(&carcara, "ground_comparison_root", ROOT, &proof),
            CarcaraVerdict::Valid,
            "{proof}"
        );
    }
}

/// NEGATIVE TWIN: the guarded instance has no checked bridge either way; it
/// may keep its disclosed hole, but never a step pinned carcara rejects.
#[test]
#[timeout(120_000)]
fn a_guarded_ground_comparison_instance_is_never_claimed_invalidly() {
    let proof = solve_unsat_and_get_proof(GUARDED, "ground_comparison_guarded");
    assert!(!proof.contains("(< 0 2))) :rule comp_simplify"), "{proof}");
    if let Some(carcara) = require_carcara_or_skip() {
        assert_ne!(
            carcara_verdict_without_allowances(
                &carcara,
                "ground_comparison_guarded",
                GUARDED,
                &proof
            ),
            CarcaraVerdict::Invalid,
            "{proof}"
        );
    }
}

/// Pattern-guarded instances whose comparison turns ground, or the same term
/// twice, once the pattern fixes the bound variable.
const GUARDED_GROUND_INSTANCES: [(&str, &str); 4] = [
    (
        "ground_comparison_pattern_int",
        "(set-logic UFLIA)\n(declare-fun P (Int) Bool)\n\
         (assert (forall ((w Int)) (! (=> (P w) (> 5 w)) :pattern ((P w)))))\n\
         (assert (P 7))\n(check-sat)\n",
    ),
    (
        "ground_comparison_pattern_real",
        "(set-logic UFLRA)\n(declare-fun P (Real) Bool)\n\
         (assert (forall ((w Real)) (! (=> (P w) (> 5.0 w)) :pattern ((P w)))))\n\
         (assert (P 7.0))\n(check-sat)\n",
    ),
    (
        "ground_comparison_pattern_same_term",
        "(set-logic UFLIA)\n(declare-fun P (Int) Bool)\n(declare-fun g (Int) Int)\n\
         (assert (forall ((w Int)) (! (=> (P w) (> (g 5) (g w))) :pattern ((P w)))))\n\
         (assert (P 5))\n(check-sat)\n",
    ),
    (
        "ground_comparison_bounded_array_vc",
        "(set-logic UFLIA)\n(declare-fun a (Int) Int)\n\
         (assert (forall ((i Int)) (! (=> (> 10 i) (>= (a i) 0)) :pattern ((a i)))))\n\
         (assert (< (a 2) 0))\n(check-sat)\n",
    ),
];

#[test]
#[timeout(240_000)]
fn a_pattern_fixed_ground_comparison_instance_keeps_a_valid_document() {
    for (label, problem) in GUARDED_GROUND_INSTANCES {
        let proof = solve_unsat_and_get_proof(problem, label);
        assert_eq!(proof.matches(":rule hole").count(), 0, "{label}:\n{proof}");
        if let Some(carcara) = require_carcara_or_skip() {
            assert_eq!(
                carcara_verdict_without_allowances(&carcara, label, problem, &proof),
                CarcaraVerdict::Valid,
                "{label}:\n{proof}"
            );
        }
    }
}
