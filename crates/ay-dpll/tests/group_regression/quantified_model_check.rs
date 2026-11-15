// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! The quantified model check (roadmap QM, model-check half), pinned
//! corpus-free.
//!
//! Each SAT fixture is the minimal shape of one class of the ten z3
//! zero-instantiation QM gap files (2026-09-29 architecture roadmap, critic
//! C3): a universal over an uninterpreted sort whose function needs model
//! COMPLETION (a table plus an else value) — directly or after one
//! counterexample round — a `(not (exists …))` over a 64-bit binder decided
//! under the fixed candidate model, and a nested negated goal that must be
//! prenexed before the window is covered. z3 5.1.0 answers `sat` on every
//! one. Before the check, main 532fe0346e answered `unknown` on all of them.
//!
//! The never-wrong fixtures are the ways a model check could be unsound: an
//! else value that hides a violated point, a universal that bounds an
//! uninterpreted universe (no finite pin set proves it), and a satisfiable
//! universal no table can represent. z3 5.1.0 answers `unsat`, `unsat` and
//! times out; the check may answer `unknown`, never the wrong side.

use super::hunt_quantifier_wrong_verdicts::{assert_never, solve, verdicts, Posture};

/// UFDTLIRA P801-002 minimised: the type axiom mentions a function no ground
/// term applies, so only the completed else value decides it.
const RANGE_AXIOM: &str = r#"
(set-logic UFLIA)
(declare-sort t2 0)
(declare-fun t2qtint (t2) Int)
(declare-const w t2)
(assert (forall ((i t2)) (and (<= (- 2147483648) (t2qtint i)) (<= (t2qtint i) 2147483647))))
(assert (not (forall ((usf Int)) (=> (and (<= (- 2147483648) usf) (<= usf 2147483647)) (not (= usf 0))))))
(check-sat)
(get-value ((t2qtint w)))
"#;

/// The default else value 0 violates the axiom; one counterexample instance
/// at a fresh element pins a row, and the next pass completes from it.
const RANGE_AXIOM_NEEDS_REFINEMENT: &str = r#"
(set-logic UFLIA)
(declare-sort t4b 0)
(declare-fun t4bqtint (t4b) Int)
(declare-const w t4b)
(assert (forall ((i t4b)) (and (<= 1 (t4bqtint i)) (<= (t4bqtint i) 5))))
(assert (not (forall ((x Int)) (=> (and (<= 1 x) (<= x 5)) (< x 5)))))
(check-sat)
(get-value ((t4bqtint w)))
"#;

/// BVFPLRA double_req_bl minimised: `x` must not be the double whose bits
/// have high word `j`. Decided under the fixed `x`, `j` by one bit-blasted
/// auxiliary refutation.
const BIT_PATTERN: &str = r#"
(set-logic BVFP)
(declare-fun x () (_ FloatingPoint 11 53))
(declare-fun j () (_ BitVec 32))
(assert (not (exists ((v (_ BitVec 64)))
  (and (= x (fp ((_ extract 63 63) v) ((_ extract 62 52) v) ((_ extract 51 0) v)))
       (= j ((_ extract 63 32) v))))))
(check-sat)
"#;

/// UFDTLIRA P715-019 minimised: the negated goal nests three universals in
/// implication conclusions, one prenex block.
const NESTED_GOAL: &str = r#"
(set-logic UFLIA)
(declare-sort U 0)
(declare-fun g (U) Int)
(assert (forall ((i U)) (and (<= 1 (g i)) (<= (g i) 5))))
(assert (not (forall ((j Int)) (=> (= j 2)
  (forall ((k Int)) (=> (= k (+ j 1))
    (forall ((m Int)) (=> (= m k) (not (= m 3))))))))))
(check-sat)
"#;

/// BVFPLRA zonotope_tight in Float16: `y` must be an infinity no normal
/// `x < 1` squares to. `y = +oo` is violated (`x = -512` overflows), so the
/// first candidate is refined; `y = -oo` is then decided by a bit-blasted
/// floating-point refutation, which no strict checker certifies today.
const FP_AUXILIARY_REFUTATION: &str = r#"
(set-logic BVFP)
(declare-fun y () (_ FloatingPoint 5 11))
(assert (fp.isInfinite y))
(assert (not (exists ((x (_ FloatingPoint 5 11)))
  (and (fp.isNormal x) (fp.lt x ((_ to_fp 5 11) RNE 1.0)) (= (fp.mul RNE x x) y)))))
(check-sat)
"#;

/// `f(5) = 3` violates the universal at 5; the completed else value (3) must
/// not hide it.
const VIOLATED_ROW: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (=> (> x 0) (> (f x) x))))
(assert (= (f 5) 3))
(check-sat)
"#;

/// Two distinct elements under a universal that allows one.
const UNIVERSE_BOUND: &str = r#"
(set-logic UF)
(declare-sort U 0)
(declare-const u U)
(declare-const a U)
(declare-const b U)
(assert (distinct a b))
(assert (forall ((x U)) (= x u)))
(check-sat)
"#;

/// Satisfiable (`f(x) = x + 1`), but by no finite table plus else value.
const NO_TABLE_WITNESS: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (> (f x) x)))
(check-sat)
"#;

#[test]
fn completed_else_value_decides_a_type_axiom() {
    assert_never("range axiom", RANGE_AXIOM, "unsat");
    let got = solve(RANGE_AXIOM, Posture::Z3Mode, None);
    assert_eq!(verdicts(&got), ["sat"], "z3 5.1.0 answers sat; got {got:?}");
    let value = got.get(1).map(String::as_str).unwrap_or_default();
    assert!(
        value.contains("((t2qtint w) 0)"),
        "the printed function must be the completed table the check proved \
         (else value 0); got {value:?}"
    );
}

#[test]
fn counterexample_refinement_moves_the_else_value_into_range() {
    assert_never(
        "range axiom, refinement",
        RANGE_AXIOM_NEEDS_REFINEMENT,
        "unsat",
    );
    let got = solve(RANGE_AXIOM_NEEDS_REFINEMENT, Posture::Z3Mode, None);
    assert_eq!(verdicts(&got), ["sat"], "z3 5.1.0 answers sat; got {got:?}");
    let value = got.get(1).map(String::as_str).unwrap_or_default();
    let in_range = (1..=5).any(|v| value.contains(&format!("((t4bqtint w) {v})")));
    assert!(
        in_range,
        "the completed table must satisfy the axiom at w; got {value:?}"
    );
}

#[test]
fn bit_pattern_universal_is_decided_under_the_fixed_model() {
    assert_never("bit pattern", BIT_PATTERN, "unsat");
    let got = solve(BIT_PATTERN, Posture::Z3Mode, None);
    assert_eq!(verdicts(&got), ["sat"], "z3 5.1.0 answers sat; got {got:?}");
}

#[test]
fn nested_negated_goal_is_one_prenex_block() {
    assert_never("nested goal", NESTED_GOAL, "unsat");
    let got = solve(NESTED_GOAL, Posture::Z3Mode, None);
    assert_eq!(verdicts(&got), ["sat"], "z3 5.1.0 answers sat; got {got:?}");
}

#[test]
fn completion_never_hides_a_violated_point() {
    assert_never("violated row", VIOLATED_ROW, "sat");
}

#[test]
fn a_universe_bound_is_never_certified() {
    assert_never("universe bound", UNIVERSE_BOUND, "sat");
}

#[test]
fn a_witness_no_table_represents_is_never_refuted() {
    assert_never("no table witness", NO_TABLE_WITNESS, "unsat");
}

/// The auxiliary refutation carries the enclosing posture's trust and no more:
/// admitted raw where a top-level UNSAT would be (`--z3-mode`, proof work
/// shed), refused where every refutation must be checked (`--self-check`).
/// If floating-point refutations become strictly checkable, the second
/// assertion turns `sat` legitimately and should be updated then.
#[test]
fn the_auxiliary_refutation_carries_the_posture_trust() {
    assert_never("fp auxiliary refutation", FP_AUXILIARY_REFUTATION, "unsat");
    let shed = solve(FP_AUXILIARY_REFUTATION, Posture::Z3Mode, None);
    assert_eq!(
        verdicts(&shed),
        ["sat"],
        "z3 5.1.0 answers sat; got {shed:?}"
    );
    let checked = solve(FP_AUXILIARY_REFUTATION, Posture::SelfCheck, None);
    assert_eq!(
        verdicts(&checked),
        ["unknown"],
        "an uncheckable auxiliary refutation must not publish under --self-check; got {checked:?}"
    );
}
