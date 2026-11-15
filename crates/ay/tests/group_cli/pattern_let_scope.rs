// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Repros from the fourth label-conformance review. A `:pattern` term is read
//! in the scope of the quantifier it annotates, but the `let` liveness scan
//! skipped attribute values: a `let` name used only in a pattern was left
//! unbound, and the pattern read the global of that name. `(let ((g 0))
//! (forall ((x Int)) (! (p x) :pattern ((g x)))))` applies the `let` value
//! 0, which z3 rejects, so z3 drops the assertion and answers sat; ay kept
//! it and answered unsat in every mode. Each repro has a twin that differs
//! in one line. The expected answers are z3 4.12.5's or `unknown`.

use ntest::timeout;

use super::label_answer_lanes::{assert_script_pairs_on_every_input, Script};

const A_LET_NAME_IN_A_PATTERN: &[(Script, Script)] = &[
    (
        (
            "dead_let_applied_in_pattern",
            r#"(declare-fun g (Int) Int)
(declare-fun p (Int) Bool)
(declare-const a (Array Int Int))
(assert (let ((g 0)) (forall ((x Int)) (! (p x) :pattern ((g x))))))
(assert (not (p 0)))
(check-sat)
"#,
            &["unknown"],
            &["unknown"],
        ),
        (
            "dead_let_applied_in_pattern_twin",
            r#"(declare-fun g (Int) Int)
(declare-fun p (Int) Bool)
(declare-const a (Array Int Int))
(assert (let ((g 0)) (forall ((x Int)) (! (=> (> x g) (p x)) :pattern ((p x))))))
(assert (not (p 0)))
(check-sat)
"#,
            &["sat"],
            &["sat"],
        ),
    ),
    (
        (
            "dead_let_applied_in_pattern_arg",
            r#"(declare-fun g (Int) Int)
(declare-fun p (Int) Bool)
(declare-const a (Array Int Int))
(assert (let ((g 0)) (forall ((x Int)) (! (p x) :pattern ((p (g x)))))))
(assert (not (p 0)))
(check-sat)
"#,
            &["unknown"],
            &["unknown"],
        ),
        (
            "dead_let_applied_in_pattern_arg_twin",
            r#"(declare-fun g (Int) Int)
(declare-fun p (Int) Bool)
(declare-const a (Array Int Int))
(assert (let ((g 0)) (forall ((x Int)) (! (=> (> x g) (p x)) :pattern ((p (+ x 1)))))))
(assert (not (p 0)))
(check-sat)
"#,
            &["sat"],
            &["sat"],
        ),
    ),
    (
        (
            "let_name_only_in_pattern",
            r#"(declare-fun f (Int Int) Int)
(declare-fun p (Int) Bool)
(declare-const g Int)
(assert (let ((g 0)) (forall ((x Int)) (! (p x) :pattern ((f x g))))))
(assert (not (p 0)))
(check-sat)
"#,
            &["unsat"],
            &["unsat"],
        ),
        (
            "let_name_only_in_pattern_twin",
            r#"(declare-fun f (Int Int) Int)
(declare-fun p (Int) Bool)
(declare-const g Int)
(assert (let ((g 0)) (forall ((x Int)) (! (=> (> x 0) (p x)) :pattern ((f x g))))))
(assert (not (p 0)))
(check-sat)
"#,
            &["sat"],
            &["sat"],
        ),
    ),
    (
        (
            "let_name_alone_as_pattern",
            r#"(declare-fun p (Int) Bool)
(declare-fun g () Int)
(assert (let ((g 0)) (forall ((x Int)) (! (p x) :pattern (g)))))
(assert (not (p 0)))
(check-sat)
"#,
            &["unknown"],
            &["unsat"],
        ),
        (
            "let_name_alone_as_pattern_twin",
            r#"(declare-fun p (Int) Bool)
(declare-fun g () Int)
(assert (let ((g 0)) (forall ((x Int)) (! (=> (> x g) (p x)) :pattern ((p x))))))
(assert (not (p 0)))
(check-sat)
"#,
            &["sat"],
            &["sat"],
        ),
    ),
    (
        (
            "label_over_a_quantifier_whose_pattern_names_an_outer_variable",
            r#"(declare-fun p (Int) Bool)
(declare-fun q (Int Int) Bool)
(assert (forall ((x Int)) (! (forall ((y Int)) (! (p y) :pattern ((q y x)))) :named L)))
(assert (not (p 0)))
(check-sat)
"#,
            &["unsat"],
            &["unsat"],
        ),
        (
            "label_over_a_quantifier_whose_pattern_names_an_outer_variable_twin",
            r#"(declare-fun p (Int) Bool)
(declare-fun q (Int Int) Bool)
(assert (forall ((x Int)) (! (forall ((y Int)) (! (p y) :pattern ((q y x)))) :named L)))
(assert (p 0))
(check-sat)
"#,
            &["sat"],
            &["sat"],
        ),
    ),
];

const A_LABEL_IN_A_PATTERN: &[(Script, Script)] = &[(
    (
        "named_label_in_a_pattern_over_a_bound_variable",
        r#"(declare-fun g (Int) Int)
(assert (forall ((z Int)) (! (> (g z) 0) :pattern ((! (g z) :named pn)))))
(assert (< (g 3) 0))
(check-sat)
"#,
        &["unknown"],
        &["unknown"],
    ),
    (
        "named_label_in_a_pattern_over_a_bound_variable_twin",
        r#"(declare-fun g (Int) Int)
(assert (forall ((z Int)) (! (> (g z) 0) :pattern ((g z)))))
(assert (< (g 3) 0))
(check-sat)
"#,
        &["unsat"],
        &["unsat"],
    ),
)];

/// z3 rejects a `:named` label over a bound variable inside a pattern
/// ("invalid named expression, expression contains free variables") and
/// answers sat. ay keeps the assertion but withholds the answer, since a
/// label in an attribute value is not reached in z3's order.
#[test]
#[timeout(180_000)]
fn a_label_in_a_pattern_withholds_the_answer() {
    assert_script_pairs_on_every_input(A_LABEL_IN_A_PATTERN);
}

/// A `let` name used only in a pattern means the `let` value. Applied, it is
/// rejected as z3 rejects it. Alone as a pattern, z3 mode rejects it as a
/// variable pattern, which z3 4.12.5 accepts (unknown, not a wrong answer).
/// A label over a quantifier whose pattern names an outer variable is bound,
/// as z3 binds it.
#[test]
#[timeout(300_000)]
fn a_let_name_in_a_pattern_means_the_let_value() {
    assert_script_pairs_on_every_input(A_LET_NAME_IN_A_PATTERN);
}
