// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! LNH symmetry breaking losing verdicts it should not (2026-10-09 audit and
//! verification of the domain + lane-leak repair; no wrong answers, every
//! finding a lost verdict).
//!
//! * A check whose `unsat` must carry a checked certificate (`--self-check`,
//!   `:produce-proofs`) cannot use the symmetry clauses `B`: they are
//!   satisfiability-preserving, not entailed, so no proof rule derives them.
//!   The pass now declines there (C5), as z3 does under proofs.
//! * A declined pass interned the swap images of its invariance check, so
//!   declining shifted every later term id (`lv5a`/`lv5b`, `lv5`, `lv6`).
//! * Datatype-sorted free constants were admitted as a domain (`lv3`); the
//!   domain is now a genuinely uninterpreted sort.
//! * After the least-index pin `x = c0` substituted `x` away, the evaluator
//!   could not read the uninterpreted-sort application `(f x)` (`lv9`).
//! * A quantified problem: the pass fired inside instantiation rounds and
//!   cost a `sat` (`lv7`); the pass is now for ground problems (C6).
//! * Later checks of a session after a check that carried `B` (`lv1`,
//!   `lv4`). `lv1` is a datatype defect the pass only exposed: the datatype
//!   tester bridge read stale atoms out of the append-only store (an earlier
//!   check's substituted `(= (e c0) E0)`), reproduced with the pass off by
//!   an authored pin and `reset-assertions`. `lv4`'s nested executors ran
//!   the pass on borrowed and cloned contexts; only the caller's own check
//!   (and the certification re-solve of a refutation that used `B`) may.
//!
//! The same harness and postures as `lnh_symmetry_domain_soundness`; z3
//! 5.1.0's answers are in each fixture's table row.

use super::lnh_symmetry_domain_soundness::{
    solve, verdicts, Posture, DECIDED_BUDGET, NEVER_WRONG_BUDGET, POSTURES,
};

/// PHP(6 pigeons, 5 holes) over a symmetric domain: the shape the pass
/// exists for.
const PHP5: &str = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-const c0 U) (declare-const c1 U) (declare-const c2 U) (declare-const c3 U) (declare-const c4 U)
(declare-const x0 U) (declare-const x1 U) (declare-const x2 U) (declare-const x3 U) (declare-const x4 U) (declare-const x5 U)
(assert (distinct c0 c1 c2 c3 c4))
(assert (or (= x0 c0) (= x0 c1) (= x0 c2) (= x0 c3) (= x0 c4)))
(assert (or (= x1 c0) (= x1 c1) (= x1 c2) (= x1 c3) (= x1 c4)))
(assert (or (= x2 c0) (= x2 c1) (= x2 c2) (= x2 c3) (= x2 c4)))
(assert (or (= x3 c0) (= x3 c1) (= x3 c2) (= x3 c3) (= x3 c4)))
(assert (or (= x4 c0) (= x4 c1) (= x4 c2) (= x4 c3) (= x4 c4)))
(assert (or (= x5 c0) (= x5 c1) (= x5 c2) (= x5 c3) (= x5 c4)))
(assert (distinct x0 x1 x2 x3 x4 x5))
(check-sat)
"#;

/// `lv3`: a domain of DATATYPE-sorted free constants (`U` is a list of an
/// enum). The pinned model over-populated the enum sort: `unknown` in both
/// postures, single check.
const LV3_DT_SORTED_DOMAIN: &str = r#"
(set-logic QF_UFDT)
(declare-datatypes ((E 0) (U 0)) (((K0) (K1) (K2) (K3)) ((cons (hd E) (tl U)) (nil))))
(declare-const c0 U)
(declare-fun c1 () U)
(declare-const c2 U)
(declare-const c3 U)
(declare-fun c4 () U)
(declare-fun c5 () U)
(declare-const e U)
(declare-const d U)
(declare-fun f (U) U)
(declare-fun p (U) Bool)
(declare-fun q (U) Bool)
(assert (or (= c0 (f (f e))) (= c1 (f (f e))) (= (f (f e)) c2) (= (f (f e)) c3) (= (f (f e)) c4) (= (f (f e)) c5)))
(assert (not (= c0 c5)))
(assert (not (= c3 c5)))
(assert (not (= c4 c5)))
(assert (or (p c4) (q c4)))
(assert (not (= c1 c2)))
(assert (not (= c0 c2)))
(assert (or (p c1) (q c1)))
(assert (or (p c3) (q c3)))
(assert (or (p c5) (q c5)))
(assert (not (= c0 c4)))
(assert (not (= c1 c3)))
(assert (or (p c2) (q c2)))
(assert (not (= c2 c5)))
(assert (not (= c2 c3)))
(assert (not (= c0 c1)))
(assert (not (= c1 c4)))
(assert (not (= c0 c3)))
(assert (not (= c1 c5)))
(assert (or (p c0) (q c0)))
(assert (not (= c3 c4)))
(assert (not (= c2 c4)))
(check-sat)
"#;

/// `lv9`: the pin `x = c0` lets variable substitution remove `x`; the
/// uninterpreted-sort application `(f x)` then had no value of its own.
const LV9_QF_UFBV: &str = r#"
(set-logic QF_UFBV)
(declare-sort U 0)
(declare-const c0 U) (declare-const c1 U) (declare-const c2 U) (declare-const c3 U) (declare-const c4 U)
(declare-const x U)
(declare-fun f (U) U)
(assert (or (= x c0) (= x c1) (= x c2) (= x c3) (= x c4)))
(assert (or (= (f x) c0) (= (f x) c1) (= (f x) c2) (= (f x) c3) (= (f x) c4)))
(check-sat)
"#;

/// `lv10`: the same evaluator gap with no symmetry pass at all.
const LV10_QF_UFBV_PINNED: &str = r#"
(set-logic QF_UFBV)
(declare-sort U 0)
(declare-const c0 U) (declare-const c1 U)
(declare-const x U)
(declare-fun f (U) U)
(assert (= x c0))
(assert (or (= (f x) c0) (= (f x) c1)))
(check-sat)
"#;

/// `lv7`: a quantified UFLIA problem; the pass fired three times and
/// `--z3-mode` answered `unknown` (quantifier-unhandled).
const LV7_QUANTIFIED_UFLIA: &str = r#"
(set-logic UFLIA)
(declare-sort U 0)
(declare-const c0 U) (declare-const c1 U) (declare-const c2 U) (declare-const c3 U) (declare-const c4 U) (declare-const c5 U)
(declare-const x U) (declare-const y U) (declare-const z U)
(declare-fun f (U) U)
(declare-fun g (U U) U)
(declare-fun p (U) Bool)
(declare-fun q (U) Bool)
(declare-fun h (U) Int)
(assert (or (= (g x y) c0) (= (g x y) c1) (= (g x y) c2) (= (g x y) c3) (= (g x y) c4) (= (g x y) c5)))
(assert (or (= y c0) (= y c1) (= y c2) (= y c3) (= y c4) (= y c5)))
(assert (or (or (> (h y) 1) (not (p (ite (= x z) c0 c0)))) (not (p (f y)))))
(assert (or (or (> (h y) 1) (not (p (ite (= x z) c1 c1)))) (not (p (f y)))))
(assert (or (or (> (h y) 1) (not (p (ite (= x z) c2 c2)))) (not (p (f y)))))
(assert (or (or (> (h y) 1) (not (p (ite (= x z) c3 c3)))) (not (p (f y)))))
(assert (or (or (> (h y) 1) (not (p (ite (= x z) c4 c4)))) (not (p (f y)))))
(assert (or (or (> (h y) 1) (not (p (ite (= x z) c5 c5)))) (not (p (f y)))))
(assert (or (not (q c0)) (not (> (h y) 1))))
(assert (or (not (q c1)) (not (> (h y) 1))))
(assert (or (not (q c2)) (not (> (h y) 1))))
(assert (or (not (q c3)) (not (> (h y) 1))))
(assert (or (not (q c4)) (not (> (h y) 1))))
(assert (or (not (q c5)) (not (> (h y) 1))))
(assert (or (q (f y)) (or (p (g z c0)) (p (f z)))))
(assert (or (q (f y)) (or (p (g z c1)) (p (f z)))))
(assert (or (q (f y)) (or (p (g z c2)) (p (f z)))))
(assert (or (q (f y)) (or (p (g z c3)) (p (f z)))))
(assert (or (q (f y)) (or (p (g z c4)) (p (f z)))))
(assert (or (q (f y)) (or (p (g z c5)) (p (f z)))))
(assert (q x))
(assert (and (=> (q (f c0)) (p (g z z))) (=> (q z) (p (f x)))))
(assert (and (=> (q (f c1)) (p (g z z))) (=> (q z) (p (f x)))))
(assert (and (=> (q (f c2)) (p (g z z))) (=> (q z) (p (f x)))))
(assert (and (=> (q (f c3)) (p (g z z))) (=> (q z) (p (f x)))))
(assert (and (=> (q (f c4)) (p (g z z))) (=> (q z) (p (f x)))))
(assert (and (=> (q (f c5)) (p (g z z))) (=> (q z) (p (f x)))))
(assert (or (and (=> (= y (f y)) (= (f z) x)) (q z)) (=> (or (= z (f z)) (= (f y) (f y))) (or (not (= (ite (p x) x z) (f z))) (p (f x))))))
(assert (forall ((w U)) (p (g x w))))
(assert (and (forall ((w U)) (not (p (ite (= y z) z x)))) (not (= z (g z z)))))
(check-sat)
"#;

/// `lv5a`: an asymmetric problem the pass declines; its swap check interned
/// terms anyway and the verdict depended on whether the pass ran.
const LV5A_DECLINED_PERTURBATION: &str = r#"
(set-logic QF_UFDTLIA)
(declare-sort U 0)
(declare-datatypes ((P 0)) (((mk (fst U) (snd U)))))
(declare-datatypes ((O 0)) (((none) (some (val U)))))
(declare-const c0 U) (declare-const c1 U) (declare-const c2 U) (declare-const c3 U) (declare-const c4 U) (declare-const c5 U)
(declare-const x0 U)
(declare-fun h (U) Int)
(declare-const pr1 P)
(declare-const o0 O)
(declare-const o1 O)
(assert (or (= x0 c0) (= x0 c1) (= c2 x0) (= x0 c3) (= x0 c4) (= x0 c5)))
(assert (distinct c0 c1 c2 c3 c4 c5))
(assert (= (h (ite (< (h x0) (h x0)) x0 x0)) (h (ite (= pr1 (mk c2 x0)) c2 x0))))
(assert (= (h (ite (< (h x0) (h x0)) x0 x0)) (h (ite (= pr1 (mk c5 x0)) c5 x0))))
(check-sat)
"#;

/// `lv1`: a check that carries `B` at depth 0, then `(push 1)(pop 1)` and a
/// second check.
const LV1_CHECK_THEN_PUSH_POP: &str = r#"
(set-logic QF_UFDT)
(declare-sort U 0)
(declare-datatypes ((E 0)) (((E0) (E1) (E2) (E3))))
(declare-fun c0 () U) (declare-fun c1 () U) (declare-fun c2 () U) (declare-fun c3 () U) (declare-fun c4 () U) (declare-fun c5 () U)
(declare-const x0 U)
(declare-fun f (U) U)
(declare-fun p (U) Bool)
(declare-fun e (U) E)
(assert (or (= x0 c0) (= x0 c1) (= c2 x0) (= x0 c3) (= x0 c4) (= x0 c5)))
(assert (=> (= (e x0) E0) (p (f c0))))
(assert (=> (= (e x0) E0) (p (f c1))))
(assert (=> (= (e x0) E0) (p (f c2))))
(assert (=> (= (e x0) E0) (p (f c3))))
(assert (=> (= (e x0) E0) (p (f c4))))
(assert (=> (= (e x0) E0) (p (f c5))))
(check-sat)
(push 1)
(pop 1)
(check-sat)
"#;

/// `lv4`: `check-sat-assuming` with symmetric literal orbits, then plain
/// checks of the satisfiable base.
const LV4_CSA_THEN_CHECKS: &str = r#"
(set-logic QF_UFDT)
(declare-sort U 0)
(declare-datatypes ((L 0)) (((cons (hd U) (tl L)) (nil))))
(declare-fun c0 () U)
(declare-fun c1 () U)
(declare-fun c2 () U)
(declare-fun c3 () U)
(declare-fun c4 () U)
(declare-const x0 U)
(declare-const x1 U)
(declare-fun f (U) U)
(declare-const l0 L)
(declare-const l1 L)
(assert (or (= x0 c0) (= x0 c1) (= x0 c2) (= x0 c3) (= x0 c4)))
(assert (or (= x1 c0) (= x1 c1) (= x1 c2) (= x1 c3) (= x1 c4)))
(assert (distinct x0 x1))
(assert ((_ is cons) l1))
(assert (= x0 (f c1)))
(assert (= x0 (f c4)))
(assert (= x0 (f c0)))
(assert (= x0 (f c2)))
(assert (= x0 (f c3)))
(assert (= c0 c0))
(assert (= c1 c1))
(assert (= c2 c2))
(assert (= c3 c3))
(assert (= c4 c4))
(assert (not (= (hd (tl l0)) (f x0))))
(check-sat-assuming ((= c0 x0) (= c1 x0) (= c2 x0) (= c3 x0) (= c4 x0)))
(assert (= c0 c0))
(check-sat-assuming ((= x0 (ite (= c0 c0) c0 c0)) (= x0 (ite (= c1 c1) c1 c1)) (= x0 (ite (= c2 c2) c2 c2)) (= x0 (ite (= c3 c3) c3 c3)) (= x0 (ite (= c4 c4) c4 c4))))
(check-sat-assuming ((= c0 c0) (= c1 c1) (= c2 c2) (= c3 c3) (= c4 c4)))
(check-sat)
(check-sat)
"#;

/// `lv2`: PHP(6, 5) beside a list of `U`, checked twice; the second check's
/// certification met a malformed tester application in the term store.
const LV2_PHP_LIST_TWICE: &str = r#"
(set-logic QF_UFDT)
(declare-sort U 0)
(declare-datatypes ((L 0)) (((cons (hd U) (tl L)) (nil))))
(declare-const c0 U) (declare-const c1 U) (declare-const c2 U) (declare-const c3 U) (declare-const c4 U)
(declare-const x0 U) (declare-const x1 U) (declare-const x2 U) (declare-const x3 U) (declare-const x4 U) (declare-const x5 U)
(declare-const l L)
(assert (or (= x0 c0) (= x0 c1) (= x0 c2) (= x0 c3) (= x0 c4)))
(assert (or (= x1 c0) (= x1 c1) (= x1 c2) (= x1 c3) (= x1 c4)))
(assert (or (= x2 c0) (= x2 c1) (= x2 c2) (= x2 c3) (= x2 c4)))
(assert (or (= x3 c0) (= x3 c1) (= x3 c2) (= x3 c3) (= x3 c4)))
(assert (or (= x4 c0) (= x4 c1) (= x4 c2) (= x4 c3) (= x4 c4)))
(assert (or (= x5 c0) (= x5 c1) (= x5 c2) (= x5 c3) (= x5 c4)))
(assert (distinct x0 x1 x2 x3 x4 x5))
(assert (= l (cons x0 nil)))
(check-sat)
(check-sat)
"#;

/// The `lv1` mechanism with the pass off: the first check's variable
/// substitution `x0 := c0` mints `(= (e c0) E0)`; after `reset-assertions`
/// nothing asserts it, but the datatype tester bridge still read it from the
/// store and pulled `(e c0)` into the next check without its exhaustiveness
/// axiom — a fifth value of a four-constructor enum, `unknown`.
const STALE_DT_ATOM_AFTER_RESET: &str = r#"
(set-logic QF_UFDT)
(declare-sort U 0)
(declare-datatypes ((E 0)) (((E0) (E1) (E2) (E3))))
(declare-const c0 U)
(declare-const x0 U)
(declare-fun p (U) Bool)
(declare-fun e (U) E)
(assert (=> (= (e x0) E0) (p c0)))
(assert (= x0 c0))
(check-sat)
(reset-assertions)
(assert (=> (= (e x0) E0) (p c0)))
(push 1)
(pop 1)
(check-sat)
"#;

/// Fixtures with z3 5.1.0's answers and the postures that must DECIDE every
/// check (every posture must never contradict z3).
const FIXTURES: [(&str, &str, &[&str], &[Posture]); 9] = [
    (
        "lv3 datatype-sorted domain",
        LV3_DT_SORTED_DOMAIN,
        &["sat"],
        &[Posture::Plain, Posture::Authored, Posture::Z3Mode],
    ),
    (
        "lv9 U-valued application over a substituted argument",
        LV9_QF_UFBV,
        &["sat"],
        &[Posture::Plain, Posture::Authored, Posture::Z3Mode],
    ),
    (
        "lv10 U-valued application, pinned argument",
        LV10_QF_UFBV_PINNED,
        &["sat"],
        &[Posture::Plain, Posture::Authored, Posture::Z3Mode],
    ),
    (
        "lv7 quantified UFLIA",
        LV7_QUANTIFIED_UFLIA,
        &["sat"],
        &[Posture::Z3Mode],
    ),
    (
        "lv5a declined-pass perturbation",
        LV5A_DECLINED_PERTURBATION,
        &["sat"],
        &[Posture::Plain, Posture::Authored, Posture::Z3Mode],
    ),
    (
        "lv1 check then push/pop",
        LV1_CHECK_THEN_PUSH_POP,
        &["sat", "sat"],
        &[Posture::Plain, Posture::Authored, Posture::Z3Mode],
    ),
    (
        "lv4 check-sat-assuming orbits then checks",
        LV4_CSA_THEN_CHECKS,
        &["unsat", "unsat", "sat", "sat", "sat"],
        &[Posture::Plain, Posture::Authored, Posture::Z3Mode],
    ),
    (
        "stale datatype atom after reset-assertions",
        STALE_DT_ATOM_AFTER_RESET,
        &["sat", "sat"],
        &[Posture::Plain, Posture::Authored, Posture::Z3Mode],
    ),
    (
        "lv2 PHP beside a list, checked twice",
        LV2_PHP_LIST_TWICE,
        &["unsat", "unsat"],
        &[Posture::Plain, Posture::Authored, Posture::Z3Mode],
    ),
];

/// A definite answer that contradicts z3 is wrong; `unknown` is not.
#[test]
fn lnh_r5_fixtures_are_never_wrong() {
    for (name, smt, expect, _) in FIXTURES {
        for posture in POSTURES {
            let results = solve(smt, posture, NEVER_WRONG_BUDGET);
            let got = verdicts(&results);
            assert_eq!(
                got.len(),
                expect.len(),
                "{name} ({posture:?}): one verdict per check expected; got {results:?}"
            );
            for (index, (&got, &want)) in got.iter().zip(expect).enumerate() {
                assert!(
                    got == want || got == "unknown",
                    "WRONG VERDICT ({name}, {posture:?}, check {index}): z3 5.1.0 says \
                     `{want}`, got `{got}`; all answers {all:?}",
                    all = verdicts(&results)
                );
            }
        }
    }
}

/// Each fixture is decided (z3 5.1.0 and AY with the pass off decide each in
/// milliseconds; the budget absorbs a loaded machine).
#[test]
fn lnh_r5_fixtures_are_decided() {
    for (name, smt, expect, decided_in) in FIXTURES {
        for &posture in decided_in {
            let results = solve(smt, posture, DECIDED_BUDGET);
            assert_eq!(
                verdicts(&results),
                expect.to_vec(),
                "{name} ({posture:?}): z3 5.1.0's answers expected; got {results:?}"
            );
        }
    }
}

/// (C5) Where the `unsat` must carry a checked certificate, the pass
/// declines and the refutation is certified without it: `--self-check`
/// answered `unknown` (self-check-rejected) on the very shape the pass exists
/// for, and so did `(set-option :produce-proofs true)` in both postures.
#[test]
fn lnh_declines_where_a_certificate_is_demanded() {
    let results = solve(PHP5, Posture::SelfCheck, DECIDED_BUDGET);
    assert_eq!(
        verdicts(&results),
        vec!["unsat"],
        "PHP(6,5) under --self-check: z3 5.1.0 says unsat; got {results:?}"
    );
    let with_proofs = format!("(set-option :produce-proofs true)\n{PHP5}");
    for posture in [Posture::Plain, Posture::Authored, Posture::Z3Mode] {
        let results = solve(&with_proofs, posture, DECIDED_BUDGET);
        assert_eq!(
            verdicts(&results),
            vec!["unsat"],
            "PHP(6,5) with :produce-proofs ({posture:?}): z3 5.1.0 says unsat; got {results:?}"
        );
    }
}
