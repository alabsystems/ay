// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A VALID disequality with a non-integral offset over `to_real` columns was
//! refuted, and the refutation was printed (`--z3-mode`) on ordinary solving.
//!
//! `(distinct (to_real t) (+ (to_real t) 0.5))` holds for every Int `t`, so a
//! universal with it as a disjunct is valid and the file is `sat` (z3 5.1.0
//! agrees). The quantifier route hands its counterexample-guided lemmas to the
//! AUFLIRA combined lane WITHOUT preprocessing, so `to_real t - to_real t`
//! never cancels and the LIA lane parsed the atom itself. Two defects:
//!
//! 1. `ay-lia`'s linear parse admitted only integral constants and silently
//!    DROPPED the `0.5`, reading the atom as `0 = 0`; its (valid) negation was
//!    refuted as `t != t`, a 1-literal conflict.
//! 2. Dispatch accepted every mixed int/real conflict with no check at all
//!    ("mixed int/real (LIRA-bridged) conflict skipped semantic
//!    re-verification", #6853), so the conflict was learned.
//!
//! Measured before the fix (pre-QSAT main 532fe03, main 4d58f9782d, and the
//! QSAT tip with `--no-qsat`): `--z3-mode` printed `unsat` on the four UF
//! fixtures, deterministically; the default posture refused to publish it and
//! answered `unknown`. An integral offset (`1.0`) was always right. After the
//! fix both postures answer `sat`. The QSAT kernel probe reached the same conflict on
//! `forall y. (or (distinct (to_real c) (+ (to_real c) 0.5)) (> y 0))`
//! (fuzzer fz5/s505_12), which is pinned here as well.

use crate::hunt_quantifier_wrong_verdicts::{assert_never, solve, verdicts, Posture, POSTURES};
use ntest::timeout;
use std::time::Duration;

/// The ordinary-solving reproducer: printed `unsat` in `--z3-mode` on main.
const UF_OFFSET_HALF: &str = r#"
(set-logic ALL)
(declare-fun c () Int)
(declare-fun f (Int) Int)
(assert (forall ((y Int)) (or (distinct (to_real (f c)) (+ (to_real (f c)) 0.5)) (> (f y) y))))
(check-sat)
"#;

/// The QSAT kernel's shape (fz5/s505_12), no UF.
const KERNEL_SHAPE: &str = r#"
(set-logic ALL)
(declare-fun c () Int)
(assert (forall ((y Int)) (or (distinct (to_real c) (+ (to_real c) 0.5)) (> y 0))))
(check-sat)
"#;

/// The same under the standard UFLIRA logic.
const UF_OFFSET_HALF_UFLIRA: &str = r#"
(set-logic UFLIRA)
(declare-fun c () Int)
(declare-fun f (Int) Int)
(assert (forall ((y Int)) (or (distinct (to_real (f c)) (+ (to_real (f c)) 0.5)) (> (f y) y))))
(check-sat)
"#;

/// A quarter offset.
const UF_OFFSET_QUARTER: &str = r#"
(set-logic ALL)
(declare-fun c () Int)
(declare-fun f (Int) Int)
(assert (forall ((y Int)) (or (distinct (to_real (f c)) (+ (to_real (f c)) 0.25)) (> (f y) (+ y 1)))))
(check-sat)
"#;

/// The negated-equality spelling.
const UF_OFFSET_HALF_NOT_EQ: &str = r#"
(set-logic ALL)
(declare-fun c () Int)
(declare-fun f (Int) Int)
(assert (forall ((y Int)) (or (not (= (to_real (f c)) (+ (to_real (f c)) 0.5))) (> (f y) y))))
(check-sat)
"#;

#[test]
#[timeout(120_000)]
fn valid_nonintegral_offset_disequality_is_never_refuted() {
    for (name, smt) in [
        ("uf offset 1/2", UF_OFFSET_HALF),
        ("uf offset 1/2, UFLIRA", UF_OFFSET_HALF_UFLIRA),
        ("uf offset 1/4", UF_OFFSET_QUARTER),
        ("uf offset 1/2, not =", UF_OFFSET_HALF_NOT_EQ),
        ("kernel shape", KERNEL_SHAPE),
    ] {
        assert_never(name, smt, "unsat");
    }
}

/// The verdict the fix restores on the reproducer that used to print `unsat`.
#[test]
#[timeout(120_000)]
fn valid_nonintegral_offset_disequality_is_decided_sat() {
    for posture in POSTURES {
        let results = solve(UF_OFFSET_HALF, posture, Some(Duration::from_secs(10)));
        let got = verdicts(&results);
        assert!(
            matches!(posture, Posture::SelfCheck) || got == ["sat"],
            "uf offset 1/2 ({posture:?}): z3 5.1.0 answers sat; got {got:?}"
        );
        assert!(
            !got.contains(&"unsat"),
            "WRONG VERDICT ({posture:?}): got {got:?}"
        );
    }
}
