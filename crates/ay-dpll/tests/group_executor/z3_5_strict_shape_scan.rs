// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! `--z3-mode` selects `FiniteSetTypingMode::Z3_5Strict`, which validates the
//! retention shape of every assertion before any solving. That scan used to
//! cost `O(n · d²)` in the nested-`let` depth `d`, so a 121 KB QF_UFIDL
//! assertion with 554 nested `let`s and no set anywhere ran past a 12 s
//! deadline in `--z3-mode` while the default posture decided it in 0.4 s.
//! These tests pin, at the executor boundary, that the strict posture decides
//! such scripts exactly as the default posture does and still rejects every
//! unretained FiniteSet shape with the same diagnostic.

#![allow(clippy::panic)]

use ay_dpll::Executor;
use ay_frontend::{parse, FiniteSetTypingMode};
use ntest::timeout;

fn nested_let_script(depth: usize, leaf: &str) -> String {
    let mut script =
        String::from("(set-logic QF_LIA) (declare-const x Int) (declare-const y Int) (assert ");
    for i in 0..depth {
        script.push_str(&format!("(let ((v{i} (+ x {i}))) (and (< v{i} y) "));
    }
    script.push_str(leaf);
    for _ in 0..depth {
        script.push_str("))");
    }
    script.push_str(") (check-sat)");
    script
}

fn run(mode: FiniteSetTypingMode, smt: &str) -> Result<Vec<String>, String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut executor = Executor::new();
    executor.context_mut().set_finite_set_typing_mode(mode);
    executor
        .execute_all(&commands)
        .map_err(|err| err.to_string())
}

#[test]
#[timeout(120_000)]
fn z3_5_strict_decides_deep_nested_lets_like_the_default_posture() {
    let smt = nested_let_script(800, "(> x 0)");
    let legacy = run(FiniteSetTypingMode::LegacyCompatible, &smt)
        .expect("default posture decides the nested-let script");
    let strict =
        run(FiniteSetTypingMode::Z3_5Strict, &smt).expect("strict posture accepts plain lets");
    assert_eq!(strict, vec!["sat".to_string()]);
    assert_eq!(strict, legacy);
}

#[test]
#[timeout(120_000)]
fn z3_5_strict_still_rejects_unretained_shapes_under_deep_lets() {
    let shapes = [
        ("(declare-const s (FiniteSet Int)) ", "(set.in x s)", "let"),
        (
            "(declare-const s (FiniteSet Int)) ",
            "(forall ((z Int)) (set.in z s))",
            "let",
        ),
    ];
    for (declarations, leaf, shape) in shapes {
        let smt = nested_let_script(300, leaf).replacen("(set-logic QF_LIA) ", declarations, 1);
        let error = run(FiniteSetTypingMode::Z3_5Strict, &smt)
            .expect_err("a FiniteSet occurrence under a let fails closed in strict mode");
        assert!(
            error.contains(&format!(
                "Z3 5.0.0 FiniteSet public AST retention for {shape} is not yet available"
            )),
            "leaf {leaf}: {error}"
        );
        run(FiniteSetTypingMode::LegacyCompatible, &smt)
            .expect("the default posture keeps its legacy acceptance of the same script");
    }
    // The shape names are the ones the base binary actually prints, checked
    // file by file against `main` before this test was written: a set surface
    // inside a `:pattern` is reported as `quantifier/lambda body`, because the
    // binder arm's occurrence scan reaches the annotation before the validator
    // walks into it, and a `define-fun` whose body mentions a set is refused at
    // the definition, not at the call. Pinning the names the code *could*
    // produce rather than the ones it does would let the scan change silently.
    let top_level = [
        (
            "(assert (forall ((s (FiniteSet Int))) (= s s))) (check-sat)",
            "quantifier/lambda body",
        ),
        (
            "(declare-const s (FiniteSet Int)) (declare-fun p (Int) Bool) \
             (assert (forall ((x Int)) (! (p x) :pattern ((set.size s))))) (check-sat)",
            "quantifier/lambda body",
        ),
        (
            "(declare-fun p (Int) Bool) \
             (assert (forall ((x Int)) (! (p x) :no-pattern (set.in x (set.singleton x))))) (check-sat)",
            "quantifier/lambda body",
        ),
        (
            "(declare-datatypes ((Box 0)) (((mk (value Int))))) (declare-const b Box) \
             (assert (match b (((mk x) (set.in x (set.singleton x)))))) (check-sat)",
            "match",
        ),
        (
            "(declare-const s (FiniteSet Int)) (define-fun h ((a Int)) Bool (set.in a s)) \
             (assert (h 1)) (check-sat)",
            "define-fun body",
        ),
    ];
    for (smt, shape) in top_level {
        let error = run(FiniteSetTypingMode::Z3_5Strict, smt)
            .expect_err("an unretained top-level FiniteSet shape fails closed in strict mode");
        assert!(
            error.contains(&format!(
                "Z3 5.0.0 FiniteSet public AST retention for {shape} is not yet available"
            )),
            "{smt}: {error}"
        );
    }
    // A set used with no `let`/binder in the way stays accepted and decided.
    let smt = "(declare-const s (FiniteSet Int)) (declare-const x Int) \
               (assert (set.in x s)) (assert (= s (set.singleton x))) (check-sat)";
    assert_eq!(
        run(FiniteSetTypingMode::Z3_5Strict, smt).expect("retained shape is accepted"),
        vec!["sat".to_string()]
    );
}
