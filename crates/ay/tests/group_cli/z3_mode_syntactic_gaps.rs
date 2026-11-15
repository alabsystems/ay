// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Repros from the third label-conformance review, each with a twin that
//! differs in a line or two and answers sat. Three syntactic constructs were
//! read with a meaning here and rejected or read otherwise by z3: a nullary
//! symbol in parentheses, `(x)`; a bound variable applied to arguments,
//! `(let ((g 0)) (g 1))`; and `match` cases whose bodies differ in sort. z3
//! drops the assertion, so ay answered unsat where z3 answers sat, in every
//! mode, and a label in an untaken `ite` branch beside one no longer hid it.
//! Every mode now rejects all three, and a label in a subterm elaboration
//! passes over is trusted only under `--z3-mode` when the whole assertion is
//! in the vouched fragment; elsewhere it withholds the later answers. The
//! expected answers are z3 4.12.5's or `unknown`.

use ntest::timeout;

use super::label_answer_lanes::{assert_pairs, Case};

const A_NULLARY_SYMBOL_IN_PARENTHESES: &[(Case, Case)] = &[
    (
        (
            "nullary_parens_min",
            r#"(declare-const p Bool)
(declare-const x Int)
(assert (ite false (! p :named a) (= (x) 1)))
(assert (= x 2))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "nullary_parens_min_twin",
            r#"(declare-const p Bool)
(declare-const x Int)
(assert (ite false (! p :named a) (= x 2)))
(assert (= x 2))
(check-sat)
"#,
            "sat",
            "unknown",
        ),
    ),
    (
        (
            "nilparen_otherbranch",
            r#"(declare-datatypes ((D 0)) (((mk (fst Int)) (nil))))
(declare-const d D)
(declare-const p Bool)
(declare-const x Int)
(assert (ite false (! p :named a) (and (= x 1) (= (nil) d))))
(assert (= x 2))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "nilparen_otherbranch_twin",
            r#"(declare-datatypes ((D 0)) (((mk (fst Int)) (nil))))
(declare-const d D)
(declare-const p Bool)
(declare-const x Int)
(assert (ite false (! p :named a) (and (= x 2) (= nil d))))
(assert (= x 2))
(check-sat)
"#,
            "sat",
            "unknown",
        ),
    ),
    (
        (
            "nilparen_inbranch",
            r#"(declare-datatypes ((D 0)) (((mk (fst Int)) (nil))))
(declare-const d D)
(declare-const x Int)
(assert (and (= x 1) (ite false (! (= (nil) d) :named a) true)))
(assert (= x 2))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "nilparen_inbranch_twin",
            r#"(declare-datatypes ((D 0)) (((mk (fst Int)) (nil))))
(declare-const d D)
(declare-const x Int)
(assert (and (= x 2) (ite false (! (= nil d) :named a) true)))
(assert (= x 2))
(check-sat)
"#,
            "sat",
            "unknown",
        ),
    ),
    (
        (
            "dcparen_skiplabel",
            r#"(define-fun dc () Int 3)
(declare-const p Bool)
(declare-const x Int)
(assert (and (ite false (! p :named a) true) (= x 1) (= (dc) 3)))
(assert (= x 2))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "dcparen_skiplabel_twin",
            r#"(define-fun dc () Int 3)
(declare-const p Bool)
(declare-const x Int)
(assert (and (ite false (! p :named a) true) (= x 2) (= dc 3)))
(assert (= x 2))
(check-sat)
"#,
            "sat",
            "unknown",
        ),
    ),
    (
        (
            "allcharparen_skiplabel",
            r#"(declare-const p Bool)
(declare-const x Int)
(declare-const s String)
(assert (and (ite false (! p :named a) true) (= x 1) (str.in_re s (re.allchar))))
(assert (= x 2))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "allcharparen_skiplabel_twin",
            r#"(declare-const p Bool)
(declare-const x Int)
(declare-const s String)
(assert (and (ite false p true) (= x 2) (str.in_re s re.allchar)))
(assert (= x 2))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
    (
        (
            "nilparen_nolabel",
            r#"(declare-datatypes ((D 0)) (((mk (fst Int)) (nil))))
(declare-const d D)
(declare-const x Int)
(assert (and (= x 1) (= (nil) d)))
(assert (= x 2))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "nilparen_nolabel_twin",
            r#"(declare-datatypes ((D 0)) (((mk (fst Int)) (nil))))
(declare-const d D)
(declare-const x Int)
(assert (and (= x 2) (= nil d)))
(assert (= x 2))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
    (
        (
            "fuzz_skiplab811_s173_core",
            r#"(declare-const p0 Bool)
(declare-const s0 String)
(assert (= s0 ""))
(assert (and (= s0 "|") (p0) (= s0 "|")))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "fuzz_skiplab811_s173_core_twin",
            r#"(declare-const p0 Bool)
(declare-const s0 String)
(assert (= s0 ""))
(assert (or (= s0 "|") p0 (= s0 "|")))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
];

/// `(x)` applies `x` to no arguments. z3 rejects the command ("invalid
/// function application, arguments missing") whatever `x` names: a constant,
/// a nullary constructor, a nullary definition or `re.allchar`. ay read it
/// as `x` and kept an assertion z3 drops. It no longer parses, as in z3, so
/// the later answers are withheld. The last pair is the core of the review's
/// fuzz script skiplab811/s173.
#[test]
#[timeout(180_000)]
fn a_nullary_symbol_in_parentheses() {
    assert_pairs(A_NULLARY_SYMBOL_IN_PARENTHESES);
}

const A_BOUND_VARIABLE_APPLIED_TO_ARGUMENTS: &[(Case, Case)] = &[
    (
        (
            "letshadow_otherbranch",
            r#"(declare-fun g (Int) Int)
(declare-const p Bool)
(declare-const x Int)
(assert (ite false (! p :named a) (and (= x 1) (let ((g 0)) (= (g 1) (g 1))))))
(assert (= x 2))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "letshadow_otherbranch_twin",
            r#"(declare-fun g (Int) Int)
(declare-const p Bool)
(declare-const x Int)
(assert (ite false (! p :named a) (and (= x 2) (let ((v 0)) (= (g v) (g v))))))
(assert (= x 2))
(check-sat)
"#,
            "sat",
            "unknown",
        ),
    ),
    (
        (
            "letfun_skiplabel",
            r#"(declare-fun g (Int) Int)
(declare-const p Bool)
(declare-const x Int)
(assert (and (ite false (! p :named a) true) (= x 1) (let ((g 1)) (= (g g) (g g)))))
(assert (= x 2))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "letfun_skiplabel_twin",
            r#"(declare-fun g (Int) Int)
(declare-const p Bool)
(declare-const x Int)
(assert (and (ite false (! p :named a) true) (= x 2) (let ((v 1)) (= (g v) (g v)))))
(assert (= x 2))
(check-sat)
"#,
            "sat",
            "unknown",
        ),
    ),
    (
        (
            "shadow_array_select",
            r#"(declare-fun g (Int) Int)
(declare-const a (Array Int Int))
(assert (= (select a 1) 5))
(assert (= (g 1) 7))
(assert (let ((g a)) (= (g 1) 5)))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "shadow_array_select_twin",
            r#"(declare-fun g (Int) Int)
(declare-const a (Array Int Int))
(assert (= (select a 1) 5))
(assert (= (g 1) 7))
(assert (let ((g a)) (= (select g 1) 5)))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
    (
        (
            "forall_shadow",
            r#"(declare-fun g (Int) Int)
(declare-const x Int)
(assert (and (= x 1) (forall ((g Int)) (= (g 1) (g 1)))))
(assert (= x 2))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "forall_shadow_twin",
            r#"(declare-fun g (Int) Int)
(declare-const x Int)
(assert (and (= x 2) (forall ((v Int)) (= (g v) (g v)))))
(assert (= x 2))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
    (
        (
            "qualified_shadow_constant",
            r#"(declare-const k Int)
(assert (= k 0))
(assert (let ((k 5)) (= (as k Int) 5)))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "qualified_shadow_constant_twin",
            r#"(declare-const k Int)
(assert (= k 0))
(assert (let ((v 5)) (= (as k Int) (- v 5))))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
    (
        (
            "qualified_shadow_array_select",
            r#"(declare-fun g (Int) Int)
(declare-const a (Array Int Int))
(assert (= (select a 1) 5))
(assert (= (g 1) 7))
(assert (let ((g a)) (= ((as g Int) 1) 5)))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "qualified_shadow_array_select_twin",
            r#"(declare-fun g (Int) Int)
(declare-const a (Array Int Int))
(assert (= (select a 1) 5))
(assert (= (g 1) 7))
(assert (let ((v a)) (= ((as g Int) 1) 7)))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
];

/// A `let` or quantifier variable named like a function, then applied. z3
/// reads `(g 1)` as `select` on the variable: an error for an Int `g`, and
/// `(select a 1)` for an array `g`. ay applied the global function `g`,
/// which kept an assertion z3 drops or gave it another meaning. A sort
/// ascription does not change that: z3 reads `(as k Int)` as the variable
/// `k` and `((as g Int) 1)` as `g` applied, and ay resolved the global. Every
/// mode now rejects both. Each twin names the variable apart or writes
/// `select`, and answers sat.
#[test]
#[timeout(180_000)]
fn a_bound_variable_applied_to_arguments() {
    assert_pairs(A_BOUND_VARIABLE_APPLIED_TO_ARGUMENTS);
}

const MATCH_CASES_OF_DIFFERENT_SORTS: &[(Case, Case)] = &[
    (
        (
            "matchsort_otherbranch",
            r#"(declare-datatypes ((D 0)) (((mk (fst Int)) (nil))))
(declare-const d D)
(declare-const p Bool)
(declare-const x Int)
(assert (ite false (! p :named a) (and (= x 1) (match d (((mk z) true) (nil x))))))
(assert (= x 2))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "matchsort_otherbranch_twin",
            r#"(declare-datatypes ((D 0)) (((mk (fst Int)) (nil))))
(declare-const d D)
(declare-const p Bool)
(declare-const x Int)
(assert (ite false p (and (= x 2) (match d (((mk z) true) (nil (= x 2)))))))
(assert (= x 2))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
    (
        (
            "matchsort_nolabel",
            r#"(declare-datatypes ((D 0)) (((mk (fst Int)) (nil))))
(declare-const d D)
(declare-const x Int)
(assert (and (= x 1) (match d (((mk z) true) (nil x)))))
(assert (= x 2))
(check-sat)
"#,
            "unknown",
            "unknown",
        ),
        (
            "matchsort_nolabel_twin",
            r#"(declare-datatypes ((D 0)) (((mk (fst Int)) (nil))))
(declare-const d D)
(declare-const x Int)
(assert (and (= x 2) (match d (((mk z) true) (nil (= x 2))))))
(assert (= x 2))
(check-sat)
"#,
            "sat",
            "sat",
        ),
    ),
];

/// `match` cases whose bodies differ in sort. z3 4.12.5 rejects a Bool body
/// beside an Int one; ay kept the assertion. Every mode now rejects any
/// difference. The label variant keeps its label out of the twin: a label in
/// a skipped subterm beside a `match`, which the vouched walk does not read,
/// withholds the later answers.
#[test]
#[timeout(180_000)]
fn match_cases_of_different_sorts() {
    assert_pairs(MATCH_CASES_OF_DIFFERENT_SORTS);
}

const PLAIN_DIALECT_AFTER_A_SKIPPED_LABEL: &[(Case, Case)] = &[(
    (
        "plain_option_freeze_skiplabel",
        r#"(declare-const x Int)
(set-option :global-declarations true)
(push)
(assert (ite false (! (> x 5) :named a) true))
(pop)
(assert a)
(assert (< x 3))
(check-sat)
"#,
        "unknown",
        "unknown",
    ),
    (
        "plain_option_freeze_skiplabel_twin",
        r#"(declare-const x Int)
(set-option :global-declarations true)
(push)
(assert (ite false (! (> x 5) :named a) true))
(pop)
(assert (< x 3))
(check-sat)
"#,
        "sat",
        "unknown",
    ),
)];

/// z3 ignores a late `:global-declarations`, so the label `a` bound in the
/// untaken branch goes with the `pop` and `(assert a)` is an error (sat).
/// Plain mode honors the option and kept `a` (unsat). A label in a skipped
/// subterm is no longer trusted in plain mode, as on main, so the later
/// answers are withheld. The twin drops `(assert a)`: z3 mode answers sat.
#[test]
#[timeout(180_000)]
fn plain_dialect_after_a_skipped_label() {
    assert_pairs(PLAIN_DIALECT_AFTER_A_SKIPPED_LABEL);
}
