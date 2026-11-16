// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The binder-capture scan on its own. The real-checker controls behind it
//! are `a_valid_verdict_on_a_problem_carcara_misreads_is_not_evidence` in the
//! ay-dpll `carcara_external_check` tests.

fn misread_pairs(problem: &str, proof: &str) -> Vec<(String, String)> {
    super::binder_capture::binders_pinned_carcara_misreads(problem, proof)
}

/// `(bound, definition)` pairs as [`binders_pinned_carcara_misreads`]
/// returns them.
fn pairs(expected: &[(&str, &str)]) -> Vec<(String, String)> {
    expected
        .iter()
        .map(|(bound, definition)| (bound.to_string(), definition.to_string()))
        .collect()
}

#[test]
fn binders_that_rebind_a_definition_name_are_flagged() {
    let problem = "(declare-const x Int)\n\
                   (define-fun c () Int 5)\n\
                   (define-fun f ((y Int)) Int (+ y c))\n\
                   (assert (! (> x 0) :named |lbl|))\n";
    let flagged = |proof: &str| misread_pairs(problem, proof);
    // Uses of definitions and a parameter of the definition's own are fine.
    assert_eq!(
        flagged("(assume t0 (> x 0))\n(step t1 (cl (= (f x) (+ x c))) :rule refl)\n"),
        Vec::<(String, String)>::new()
    );
    assert_eq!(
        flagged("(step t1 (cl (forall ((z Int)) (= (f z) z))) :rule hole)\n"),
        Vec::<(String, String)>::new()
    );
    for (proof, name) in [
        ("(step t1 (cl (forall ((c Int)) (= c 0))) :rule hole)", "c"),
        (
            "(step t1 (cl (exists ((|c| Int)) (= c 0))) :rule hole)",
            "c",
        ),
        (
            "(step t1 (cl (= (choice ((f Int)) (= f 0)) 0)) :rule hole)",
            "f",
        ),
        ("(step t1 (cl (lambda ((lbl Int)) lbl)) :rule hole)", "lbl"),
        ("(step t1 (cl (let ((lbl true)) lbl)) :rule hole)", "lbl"),
        ("(anchor :step t2 :args ((c Int)))", "c"),
        ("(anchor :step t2 :args ((:= (lbl Bool) true)))", "lbl"),
        ("(anchor :step t2 :args ((:= lbl true)))", "lbl"),
        ("(define-fun g ((c Int)) Int c)", "c"),
        (
            "(step t1 (cl (match l ((cons c rest) true) (nil false))) :rule hole)",
            "c",
        ),
        (
            "(step t1 (cl (match l ((cons h rest) true) (lbl false))) :rule hole)",
            "lbl",
        ),
        ("(assume t0 (! (forall ((n Int)) (> n 0)) :named n))", "n"),
    ] {
        assert_eq!(flagged(proof), pairs(&[(name, name)]), "{proof}");
    }
    // A rebinding in the PROBLEM misreads the problem itself.
    assert_eq!(
        misread_pairs(
            "(define-fun c () Int 5)\n(assert (exists ((c Int)) (= c 0)))\n",
            ""
        ),
        pairs(&[("c", "c")])
    );
    assert_eq!(
        misread_pairs(
            "(declare-const x Int)\n(assert (! (= x 5) :named c))\n\
             (assert (exists ((c Bool)) (not c)))\n",
            ""
        ),
        pairs(&[("c", "c")])
    );
    // Comments, strings and quoted symbols are not code.
    assert_eq!(
        flagged(
            "; (forall ((c Int)) true)\n\
             (step t1 (cl (= |(forall ((c Int)) true)| \"(let ((c 1)) c)\")) :rule hole)\n"
        ),
        Vec::<(String, String)>::new()
    );
}

/// The three measured capture shapes (the first in every mode, the other two
/// under `--apply-function-defs`), and the shapes that must stay unflagged.
#[test]
fn binders_that_capture_a_free_symbol_of_a_definition_are_flagged() {
    let named = "(declare-const y Int)\n(assert (! (= y 0) :named n))\n\
                 (assert (forall ((y Int)) n))\n";
    assert_eq!(misread_pairs(named, ""), pairs(&[("y", "n")]));
    let nullary = "(declare-const y Int)\n(define-fun g () Bool (= y 0))\n\
                   (assert g)\n(assert (forall ((y Int)) g))\n";
    assert_eq!(misread_pairs(nullary, ""), pairs(&[("y", "g")]));
    let parameter = "(declare-const y Int)\n(define-fun h ((x Int)) Bool (= x y))\n\
                     (assert (= y 0))\n(assert (forall ((y Int)) (h 0)))\n";
    assert_eq!(misread_pairs(parameter, ""), pairs(&[("y", "h")]));
    // Transitively: `m` names `n`, whose body is open in `y`.
    let nested = "(declare-const y Int)\n(assert (! (= y 0) :named n))\n\
                  (define-fun m () Bool (and n true))\n(assert (exists ((y Int)) m))\n";
    assert_eq!(misread_pairs(nested, ""), pairs(&[("y", "m")]));
    // In the proof: under a quantifier, a `let`, a proof `define-fun`
    // parameter, and an anchor variable (which scopes over the whole proof).
    for (proof, bound, definition) in [
        (
            "(step t1 (cl (not (forall ((y Int)) n))) :rule hole)",
            "y",
            "n",
        ),
        ("(step t1 (cl (let ((y 1)) n)) :rule hole)", "y", "n"),
        ("(define-fun k ((y Int)) Bool n)", "y", "n"),
        (
            "(anchor :step t3 :args ((y Int)))\n(step t3.1 (cl n) :rule hole)",
            "y",
            "n",
        ),
    ] {
        let problem = "(declare-const y Int)\n(assert (! (= y 0) :named n))\n";
        let mut flagged = misread_pairs(problem, proof);
        flagged.retain(|pair| pair.1 == definition);
        assert_eq!(flagged, pairs(&[(bound, definition)]), "{proof}");
    }
    // A label over a term its enclosing binder binds into: every later use of
    // the label names that binder's variable.
    assert_eq!(
        misread_pairs("(assert (forall ((z Int)) (! (> z 0) :named p)))\n", ""),
        pairs(&[("z", "p")])
    );
    // Proof `define-fun`s capture too (they expand in every mode).
    assert_eq!(
        misread_pairs(
            "(declare-const y Int)\n",
            "(define-fun d () Bool (= y 0))\n(step t1 (cl (forall ((y Int)) d)) :rule hole)\n"
        ),
        pairs(&[("y", "d")])
    );

    // NOT flagged: shadowing with no definition in scope, a definition whose
    // body binds the name itself, a free symbol the binder does not bind, a
    // binder that does not name the definition, and a `let` value (read
    // outside its bindings) naming the `let`'s own variable.
    for (problem, proof) in [
        (
            "(declare-const y Int)\n(assert (! (> y 0) :named a))\n\
             (assert (forall ((y Int)) (> y 1)))\n",
            "",
        ),
        (
            "(assert (! (forall ((z Int)) (> z 0)) :named p))\n\
             (assert (forall ((z Int)) (and p (> z 1))))\n",
            "",
        ),
        (
            "(declare-const y Int)\n(declare-const w Int)\n(assert (! (= y 0) :named n))\n\
             (assert (forall ((w Int)) n))\n",
            "",
        ),
        (
            "(declare-const y Int)\n(define-fun h ((x Int)) Bool (= x y))\n\
             (assert (forall ((x Int)) (h x)))\n",
            "",
        ),
        (
            "(declare-const y Int)\n",
            "(define-fun d () Int (let ((y 1)) y))\n(step t1 (cl (forall ((y Int)) (= d y))) :rule hole)\n",
        ),
        (
            "(declare-const x Int)\n(declare-const y Int)\n",
            "(define-fun __ay_p () Bool (= x y))\n(anchor :step t2)\n(step t2 (cl __ay_p) :rule hole)\n",
        ),
    ] {
        assert!(misread_pairs(problem, proof).is_empty(), "{problem}{proof}");
    }
}

/// A deeply nested document lexes and scans without recursion.
#[test]
fn a_deeply_nested_document_is_scanned_without_recursion() {
    let depth = 200_000;
    let problem = format!(
        "(declare-const y Bool)\n(assert (! (= y true) :named n))\n(assert (forall ((y Bool)) {}n{}))\n",
        "(not ".repeat(depth),
        ")".repeat(depth)
    );
    assert_eq!(misread_pairs(&problem, ""), pairs(&[("y", "n")]));
    let body = format!("{}y{}", "(not ".repeat(depth), ")".repeat(depth));
    let problem = format!("(declare-const y Bool)\n(assert (! {body} :named n))\n");
    assert_eq!(misread_pairs(&problem, ""), Vec::<(String, String)>::new());
    // Unbalanced input does not panic.
    assert!(misread_pairs("(assert (! (= y 0) :named n)\n(forall ((y Int)) n", "").len() <= 1);
}
