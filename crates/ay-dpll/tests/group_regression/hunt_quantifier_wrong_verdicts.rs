// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Wrong verdicts from the 2026-09-23 quantifier hunts, pinned corpus-free.
//!
//! # D1 — wrong `sat` with `confirmed-sat` evidence (UFDT, `forall` over a
//! field sort)
//!
//! The MBQI finite-universe certificate enumerated a universal over an
//! uninterpreted sort `U` at the ground `U`-terms only. A datatype with a
//! `U` field holds `U` elements of its own — `a0 = w(@U!3)` — and a universal
//! false exactly there was certified, and the model gate took the
//! certificate's word (`deferred-certified-mbqi-sat`). z3 5.1.0 answers
//! `unsat` on every fixture here; main f399eca07a answered `sat` 3/3 in both
//! postures. `unsat` or `unknown` are acceptable, `sat` is wrong.
//!
//! # D11 — wrong `unsat` from the infeasible-universal rewrite
//!
//! `(forall v. (= (+ v (* v w)) 0))` was rewritten to `false` because the
//! binder's coefficient `1 + w` was read with `w` set to 0. At `w = -1` the
//! universal holds. The rewrite runs only when the proof cycle is shed
//! (`--z3-mode`, driven here by `set_competition_mode(true)`). z3 5.1.0 answers
//! `sat`; `sat` or `unknown` are acceptable, `unsat` is wrong.
//!
//! # D10(b) — a `check-sat-assuming` literal outlived its query
//!
//! Over a quantified problem the assumption route solved `assertions ∧
//! assumptions` as one assertion set; the propositional lane encoded the free
//! Boolean assumption into its persistent SAT solver at depth 0, and the next
//! query was refuted under it (`--z3-mode`). z3 5.1.0 answers `sat` to every
//! query.
//!
//! Every fixture runs in four postures: the plain and authored executors, the
//! fail-closed self-check, and the `--z3-mode` posture (proof cycle shed), the
//! only one in which D11 and D10(b) were wrong. Measured with the three fixes
//! reverted and these tests kept: the eight tests that pin a wrong verdict
//! fail; the controls (the satisfiable twins, the numeral coefficient) pass.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;

const D1_FOUR_VALUES: &str = r#"
(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((W 0)) (((w (g U)) (w2))))
(declare-const u0 U)
(declare-const u1 U)
(declare-const a0 W)
(declare-const a1 W)
(declare-const a2 W)
(declare-const a3 W)
(assert (distinct a0 a1 a2 a3))
(assert (forall ((x U)) (or (= x u0) (= x u1))))
(check-sat)
"#;

const D1_SINGLETON_TWO_CELLS: &str = r#"
(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((W 0)) (((w (g U)) (w2))))
(declare-const a W)
(declare-const b W)
(declare-const u U)
(assert (distinct a b))
(assert ((_ is w) a))
(assert ((_ is w) b))
(assert (forall ((x U)) (= x u)))
(check-sat)
"#;

const D1_LIST_CELLS: &str = r#"
(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((L 0)) (((nil) (cons (hd U) (tl L)))))
(declare-const a L)
(declare-const b L)
(declare-const u U)
(assert (distinct a b))
(assert ((_ is cons) a))
(assert ((_ is cons) b))
(assert (= (tl a) nil))
(assert (= (tl b) nil))
(assert (forall ((x U)) (= x u)))
(check-sat)
"#;

/// The declarations and the four distinct `W` values of [`D1_FOUR_VALUES`];
/// each shape below adds its universal.
const D1_FOUR_VALUES_PREFIX: &str = r#"
(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((W 0)) (((w (g U)) (w2))))
(declare-const u0 U)
(declare-const u1 U)
(declare-const a0 W)
(declare-const a1 W)
(declare-const a2 W)
(declare-const a3 W)
(assert (distinct a0 a1 a2 a3))
"#;

/// [`D1_FOUR_VALUES`] with the universal in three other shapes the hunt did
/// not generate — a guarded universal beside a second one over a predicate, a
/// conjunctive body with an uninterpreted predicate, an `ite` body. main
/// f399eca07a answered `sat` with `confirmed-sat` on all three, in both
/// postures (z3 5.1.0: `unsat`); the same missing carried elements.
const D1_FOUR_VALUES_OTHER_SHAPES: [(&str, &str); 3] = [
    (
        "guarded universal beside a predicate universal",
        "(declare-fun P (U) Bool) (assert (P u0)) (assert (P u1))
         (assert (forall ((x U)) (=> (P x) (or (= x u0) (= x u1)))))
         (assert (forall ((x U)) (P x))) (check-sat)",
    ),
    (
        "conjunctive body with a predicate",
        "(declare-fun Q (U) Bool)
         (assert (forall ((x U)) (and (Q x) (or (= x u0) (= x u1))))) (check-sat)",
    ),
    (
        "ite body",
        "(declare-const b Bool)
         (assert (forall ((x U)) (ite b (= x u0) (or (= x u0) (= x u1))))) (check-sat)",
    ),
];

/// Satisfiable twin of [`D1_FOUR_VALUES`]: three distinct `W` values fit in
/// `{w(u0), w(u1), w2}`. The certificate may still certify it once the model's
/// fields are elements it enumerated.
const D1_THREE_VALUES_SAT: &str = r#"
(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((W 0)) (((w (g U)) (w2))))
(declare-const u0 U)
(declare-const u1 U)
(declare-const a0 W)
(declare-const a1 W)
(declare-const a2 W)
(assert (distinct a0 a1 a2))
(assert (forall ((x U)) (or (= x u0) (= x u1))))
(check-sat)
"#;

/// Satisfiable twins the certificate can only reach by instantiating at the
/// carried elements: a predicate `Q` that the model must pin at `(g a_i)`
/// (D1x `conj_pred`), and a list whose third cell no solver term registers
/// until MBQI proposes `(hd (tl (tl a1)))` (hunt g11_00005, z3 `sat`). The
/// first D1 fix answered `unknown` on both; main answered `sat` only through
/// the defective certificate, with a printed model that falsifies the universal.
const D1_CARRIED_SAT_TWINS: [(&str, &str); 2] = [
    (
        "predicate pinned at the carried elements",
        r#"
(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((W 0)) (((w (g U)) (w2))))
(declare-const u0 U)
(declare-const u1 U)
(declare-const a0 W)
(declare-const a1 W)
(declare-const a2 W)
(declare-fun Q (U) Bool)
(assert (distinct a0 a1 a2))
(assert (forall ((x U)) (and (Q x) (or (= x u0) (= x u1)))))
(check-sat)
"#,
    ),
    (
        "list cells past the registered selector chains",
        r#"
(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((L 0)) (((nil) (cons (hd U) (tl L)))))
(declare-const u0 U)
(declare-const u1 U)
(declare-const u2 U)
(declare-const a0 L)
(declare-const a1 L)
(declare-const a2 L)
(declare-const a3 L)
(assert ((_ is cons) a0))
(assert ((_ is cons) a3))
(assert ((_ is cons) a1))
(assert (= (tl a0) nil))
(assert (= (tl a2) nil))
(assert (= (tl a3) (cons u0 nil)))
(assert (forall ((x U)) (or (= x u0) (= x u1) (= x u2))))
(assert (distinct a0 a1 a2 a3))
(check-sat)
"#,
    ),
];

const D11_EQUALITY: &str = r#"
(set-logic NIA)
(declare-fun w () Int)
(assert (forall ((v Int)) (= (+ v (* v w)) 0)))
(check-sat)
"#;

const D11_INEQUALITY: &str = r#"
(set-logic NIA)
(declare-fun w () Int)
(assert (forall ((v Int)) (and (>= w 0) (<= (* v (- w 2)) 7))))
(check-sat)
"#;

const D11_DISJUNCT: &str = r#"
(set-logic NIA)
(declare-fun w () Int)
(declare-fun p () Bool)
(assert (forall ((v Int)) (or (= (+ v (* v w)) 0) p)))
(assert (not p))
(check-sat)
"#;

const D11_UF_COEFFICIENT: &str = r#"
(set-logic UFNIA)
(declare-fun f (Int) Int)
(declare-fun a () Int)
(assert (forall ((v Int)) (<= (* v (+ (f a) 1)) 3)))
(check-sat)
"#;

/// A NUMERAL coefficient still refutes: the rewrite must keep firing where it
/// is sound.
const D11_CONSTANT_COEFFICIENT_UNSAT: &str = r#"
(set-logic LIA)
(declare-fun w () Int)
(assert (forall ((v Int)) (= (+ v (* 2 v) w) 0)))
(check-sat)
"#;

/// A symbolic coefficient whose universal is false for EVERY value of it:
/// at `v = 0` the conjunct reads `w < w`. main refuted it only through the
/// defective read (`unsat`, right by luck); the exact elimination
/// (`(f a) + w − 1 = 0 ∧ w < w`) refutes it for the right reason.
const D11_SYMBOLIC_COEFFICIENT_UNSAT: &str = r#"
(set-logic ALL)
(declare-fun w () Int)
(declare-fun a () Int)
(declare-fun f (Int) Int)
(assert (forall ((v Int)) (and (< (+ (* v (+ (f a) w)) (* (- 1) v) w) w) (<= a 7))))
(check-sat)
"#;

/// A symbolic coefficient that never vanishes over the integers: `2w − 1`
/// is odd, so the first conjunct is false at some `v` whatever `w` is, and
/// the universal refutes exactly as a numeral coefficient's does (fresh-seed
/// w1_92301_00153). main refuted it only through the defective read (`-1`,
/// right by luck); the exact elimination without the gcd test kept
/// `(= (- (* 2 w) 1) 0)` under the universal and answered `unknown`, the
/// second universal (inside `=`) keeping the refutation from publication.
const D11_NEVER_VANISHING_COEFFICIENT_UNSAT: &str = r#"
(set-logic ALL)
(declare-fun w () Int)
(declare-fun a () Int)
(declare-fun f (Int) Int)
(declare-fun q () Bool)
(assert (forall ((v Int)) (and (> (+ (* v (* 2 w)) (* (- 1) v) (f a)) a) (not (= (f v) v)))))
(assert (= q (forall ((v Int)) (= (+ (* (+ w 1) v) (* 2 v)) 0))))
(assert (not q))
(check-sat)
"#;

const D10B_ASSUMPTION_SCOPE: &str = r#"
(set-logic UF)
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-fun g1 () Bool)
(assert (forall ((x U)) (not (P x))))
(check-sat-assuming (g1))
(check-sat-assuming ((not g1)))
"#;

const D10B_ASSUMPTION_THEN_ASSERT: &str = r#"
(set-logic UF)
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-fun g1 () Bool)
(assert (forall ((x U)) (not (P x))))
(check-sat-assuming (g1))
(check-sat)
(assert (not g1))
(check-sat)
"#;

const D10B_UFLIA: &str = r#"
(set-logic UFLIA)
(declare-fun g1 () Bool)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (not (P x))))
(check-sat-assuming (g1))
(check-sat-assuming ((not g1)))
"#;

pub(crate) fn verdicts(results: &[String]) -> Vec<&str> {
    results
        .iter()
        .map(|line| line.trim())
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect()
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum Posture {
    /// `Executor::execute_all`, no flags.
    Plain,
    /// The caller-authored boundary the CLI uses.
    Authored,
    /// Fail-closed self-certification (`--self-check`).
    SelfCheck,
    /// The CLI's `--z3-mode` posture: the internal proof cycle is shed.
    Z3Mode,
}

pub(crate) const POSTURES: [Posture; 4] = [
    Posture::Plain,
    Posture::Authored,
    Posture::SelfCheck,
    Posture::Z3Mode,
];

/// Every wrong verdict pinned here was immediate on main; the budget only
/// bounds the honest `unknown` the symbolic-coefficient fixtures now run to.
const NEVER_WRONG_BUDGET: Duration = Duration::from_secs(2);

pub(crate) fn solve(smt: &str, posture: Posture, budget: Option<Duration>) -> Vec<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = Executor::new();
    exec.set_timeout(budget);
    match posture {
        Posture::SelfCheck => exec.set_self_check(true),
        Posture::Z3Mode => exec.set_competition_mode(true),
        Posture::Plain | Posture::Authored => {}
    }
    if matches!(posture, Posture::Authored) {
        let mut output = Vec::new();
        for command in &commands {
            if let Some(line) = exec
                .execute_authored(command)
                .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"))
            {
                output.push(line);
            }
        }
        output
    } else {
        exec.execute_all(&commands)
            .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"))
    }
}

pub(crate) fn assert_never(name: &str, smt: &str, wrong: &str) {
    for posture in POSTURES {
        let results = solve(smt, posture, Some(NEVER_WRONG_BUDGET));
        let got = verdicts(&results);
        assert!(
            !got.contains(&wrong),
            "WRONG VERDICT ({name}, {posture:?}): z3 5.1.0 disagrees with `{wrong}` on \
             every query here; got {got:?}"
        );
    }
}

#[test]
fn d1_four_values_over_two_elements_is_never_sat() {
    assert_never("D1 four W values, |U| <= 2", D1_FOUR_VALUES, "sat");
}

#[test]
fn d1_two_cells_over_one_element_is_never_sat() {
    assert_never("D1 two w-cells, |U| = 1", D1_SINGLETON_TWO_CELLS, "sat");
}

#[test]
fn d1_recursive_list_cells_are_never_sat() {
    assert_never("D1 two one-element lists, |U| = 1", D1_LIST_CELLS, "sat");
}

#[test]
fn d1_other_universal_shapes_are_never_sat() {
    for (name, universal) in D1_FOUR_VALUES_OTHER_SHAPES {
        assert_never(name, &format!("{D1_FOUR_VALUES_PREFIX}{universal}"), "sat");
    }
}

/// The fix must name the carried elements, not stop answering: the refutation
/// needs the instances at `(g a_i)`, and MBQI now proposes them. The smaller
/// one-cell-per-element witness is refuted by every entry point.
#[test]
fn d1_two_cells_over_one_element_is_refuted() {
    for posture in [Posture::Plain, Posture::Authored] {
        let results = solve(D1_SINGLETON_TWO_CELLS, posture, None);
        assert_eq!(
            verdicts(&results),
            ["unsat"],
            "two distinct w-cells over |U| = 1 is refuted by instantiating the \
             universal at the carried fields ({posture:?}); got {results:?}"
        );
    }
}

/// The satisfiable twin stays DECIDED: the certificate still certifies once
/// the model's fields are elements it enumerated, and the gate confirms them.
/// A repair that bought soundness by failing closed on every datatype-carried
/// sort would pass every never-`sat` assertion above; this is what stops it.
#[test]
fn d1_satisfiable_twin_stays_sat() {
    assert_never("D1 three W values, |U| <= 2", D1_THREE_VALUES_SAT, "unsat");
    let got = solve(D1_THREE_VALUES_SAT, Posture::Authored, None);
    assert_eq!(
        verdicts(&got),
        ["sat"],
        "three distinct W values fit in {{w(u0), w(u1), w2}}; got {got:?}"
    );
}

/// The certificate reaches the twins that need instances at the carried
/// elements, in both shipping postures.
#[test]
fn d1_carried_sat_twins_stay_sat() {
    for (name, smt) in D1_CARRIED_SAT_TWINS {
        assert_never(name, smt, "unsat");
        for posture in [Posture::Authored, Posture::Z3Mode] {
            let got = solve(smt, posture, None);
            assert_eq!(
                verdicts(&got),
                ["sat"],
                "{name} ({posture:?}): z3 5.1.0 answers sat; got {got:?}"
            );
        }
    }
}

#[test]
fn d11_symbolic_coefficients_are_never_unsat() {
    for (name, smt) in [
        ("equality, coefficient 1 + w", D11_EQUALITY),
        ("inequality, coefficient w - 2", D11_INEQUALITY),
        ("dropped disjunct, coefficient 1 + w", D11_DISJUNCT),
        ("UF coefficient (f a) + 1", D11_UF_COEFFICIENT),
    ] {
        assert_never(name, smt, "unsat");
    }
}

/// The elimination is exact, not merely silent: in the `--z3-mode` posture
/// the D11 witness is decided `sat` (at `w = -1`), and a universal false for
/// every value of its symbolic coefficient is still refuted.
#[test]
fn d11_symbolic_coefficients_are_decided_exactly() {
    let got = solve(D11_EQUALITY, Posture::Z3Mode, None);
    assert_eq!(
        verdicts(&got),
        ["sat"],
        "`(forall v. v + v*w = 0)` holds exactly at w = -1; got {got:?}"
    );
    let got = solve(D11_SYMBOLIC_COEFFICIENT_UNSAT, Posture::Z3Mode, None);
    assert_eq!(
        verdicts(&got),
        ["unsat"],
        "at v = 0 the conjunct reads w < w; got {got:?}"
    );
    let got = solve(D11_NEVER_VANISHING_COEFFICIENT_UNSAT, Posture::Z3Mode, None);
    assert_eq!(
        verdicts(&got),
        ["unsat"],
        "the coefficient 2w - 1 is odd, never 0; got {got:?}"
    );
}

#[test]
fn d11_numeral_coefficient_still_refutes() {
    let got = solve(D11_CONSTANT_COEFFICIENT_UNSAT, Posture::Z3Mode, None);
    assert_eq!(
        verdicts(&got),
        ["unsat"],
        "`(forall v. 3v + w = 0)` is false for every w; got {got:?}"
    );
}

#[test]
fn d10b_quantified_assumptions_do_not_outlive_their_query() {
    for (name, smt) in [
        ("negated assumption next", D10B_ASSUMPTION_SCOPE),
        ("plain check-sat then assert", D10B_ASSUMPTION_THEN_ASSERT),
        ("UFLIA", D10B_UFLIA),
    ] {
        assert_never(name, smt, "unsat");
    }
}
