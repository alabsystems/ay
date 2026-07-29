// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Congruence over FP-sorted arguments in the eager FP path.
//!
//! SMT-LIB 2.6 §5.2: `=` denotes identity and every function symbol denotes a
//! total function, so `x = y` entails `f(x) = f(y)` at every sort — including
//! `FloatingPoint`, and including the two values whose FP-specific comparison
//! behaviour differs from identity:
//!
//! | | `=` (identity) | `fp.eq` (IEEE) |
//! |---|---|---|
//! | `+zero` vs `-zero` | false | true |
//! | `NaN` vs `NaN` | true | false |
//!
//! Congruence follows `=`, never `fp.eq`: `f(+zero)` and `f(-zero)` are
//! unrelated, while `f(NaN)` and `f(fp.neg NaN)` must agree.
//!
//! ArraysEx gives `select` the rank `(par (X Y) (select (Array X Y) X) Y)`, so
//! a read at an FP index carries the same obligation.

use ntest::timeout;

/// `(= x y)` + `(f x)` + `(not (f y))` over Float32 is UNSAT.
#[test]
#[timeout(30_000)]
fn uf_over_float32_is_congruent() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun f ((_ FloatingPoint 8 24)) Bool)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x y))
        (assert (f x))
        (assert (not (f y)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "(= x y) must force (= (f x) (f y)) at FloatingPoint sort"
    );
}

/// The same obligation for an array read at an FP index.
#[test]
#[timeout(30_000)]
fn array_select_at_float32_index_is_congruent() {
    let smt = r#"
        (set-logic ALL)
        (declare-const t (Array (_ FloatingPoint 8 24) Bool))
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x y))
        (assert (select t x))
        (assert (not (select t y)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "(= x y) must force (= (select t x) (select t y))"
    );
}

/// Congruence keys on `=`, so the one NaN element makes `f(NaN)` and
/// `f(fp.neg NaN)` the same application — even though `fp.eq` says NaN
/// equals nothing.
#[test]
#[timeout(30_000)]
fn uf_at_nan_is_congruent_across_neg() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun f ((_ FloatingPoint 8 24)) Bool)
        (assert (f (_ NaN 8 24)))
        (assert (not (f (fp.neg (_ NaN 8 24)))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "NaN and (fp.neg NaN) are one element, so f must agree on them"
    );
}

/// The mirror image: `+zero` and `-zero` are DISTINCT elements (only `fp.eq`
/// conflates them), so `f` is free to disagree. Congruence must not overreach
/// into IEEE comparison semantics.
#[test]
#[timeout(30_000)]
fn uf_at_signed_zeros_is_not_congruent() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun f ((_ FloatingPoint 8 24)) Bool)
        (assert (f (_ +zero 8 24)))
        (assert (not (f (_ -zero 8 24))))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["sat"],
        "+zero and -zero are distinct elements: f may disagree on them"
    );
}

/// Congruence also has to fire when the equal arguments are reached through
/// FP operations rather than stated directly.
#[test]
#[timeout(30_000)]
fn uf_over_computed_float32_arguments_is_congruent() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun f ((_ FloatingPoint 8 24)) Bool)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (not (fp.isNaN x)))
        (assert (f (fp.neg (fp.neg x))))
        (assert (not (f x)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "(fp.neg (fp.neg x)) = x, so f must agree on the two arguments"
    );
}

/// The `fp.to_real` two-phase path shares the same encoder and therefore the
/// same obligation: presence of an `fp.to_real` must not reopen the hole.
#[test]
#[timeout(30_000)]
fn uf_over_float32_is_congruent_under_fp_to_real() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun f ((_ FloatingPoint 8 24)) Bool)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (declare-const r Real)
        (assert (= r (fp.to_real x)))
        (assert (= x y))
        (assert (f x))
        (assert (not (f y)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve_vec(smt),
        vec!["unsat"],
        "congruence must hold on the fp.to_real path too"
    );
}

/// Structure the FP path cannot encode must not be reported as `sat`: an
/// Int-valued function over FP has no representation here, so the honest
/// answer is `unknown` (never the wrong `sat` the bare relaxation gave).
#[test]
#[timeout(30_000)]
fn unencodable_result_sort_fails_closed() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun g ((_ FloatingPoint 8 24)) Int)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x y))
        (assert (distinct (g x) (g y)))
        (check-sat)
    "#;
    assert_ne!(
        crate::common::solve_vec(smt),
        vec!["sat"],
        "an unrepresentable UF result sort must fail closed, never report sat"
    );
}

/// A user function is identified by an EXACT name match against the builtin
/// tables, NEVER by prefix.
///
/// `is_interpreted_name` once began
/// `if name.starts_with("fp.") || name.starts_with("bv") { return true }`.
/// SMT-LIB simple symbols admit `~ ! @ $ % ^ & * _ - + = < > . ? /` alongside
/// letters and digits, so `bvf`, `bv`, `bvIsGood` and `bv2fp` are all symbols a
/// user may declare. Classifying them as interpreted dropped their Ackermann
/// clauses, and because both the Bool result and the FP arguments are
/// "representable" nothing set `unencodable`/`incomplete` — so the relaxation
/// was reported as a WRONG `sat`, with a self-refuting model asserting both
/// `N(+zero)` and `not N(+zero)`.
///
/// Each name below is UNSAT by congruence, and z3 5.0.0 agrees on all of them.
#[test]
#[timeout(60_000)]
fn user_functions_named_like_builtins_are_still_congruent() {
    for name in ["bvf", "bv", "bvIsGood", "bv2fp", "bvadd2", "fpx"] {
        let smt = format!(
            r#"
            (set-logic QF_UFFP)
            (declare-fun {name} ((_ FloatingPoint 8 24)) Bool)
            (declare-const x (_ FloatingPoint 8 24))
            (declare-const y (_ FloatingPoint 8 24))
            (assert (= x y))
            (assert ({name} x))
            (assert (not ({name} y)))
            (check-sat)
        "#
        );
        assert_eq!(
            crate::common::solve_vec(&smt),
            vec!["unsat"],
            "user function `{name}` must receive congruence clauses; a name that \
             merely LOOKS like a builtin must not be treated as interpreted"
        );
    }
}

/// The converse: genuine builtins must STAY interpreted, or the congruence pass
/// would bolt Ackermann clauses onto operators that already have semantics.
#[test]
#[timeout(30_000)]
fn genuine_fp_builtins_remain_interpreted() {
    // Congruence of a real operator still follows from `=`.
    let congruent = r"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const y (_ FloatingPoint 8 24))
        (assert (= x y))
        (assert (not (= (fp.add RNE x x) (fp.add RNE y y))))
        (check-sat)
    ";
    assert_eq!(crate::common::solve_vec(congruent), vec!["unsat"]);

    // And `fp.eq` keeps IEEE semantics: `(not (fp.eq x x))` is satisfiable
    // precisely because x may be NaN.
    let nan = r"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (not (fp.eq x x)))
        (check-sat)
    ";
    assert_eq!(crate::common::solve_vec(nan), vec!["sat"]);
}
