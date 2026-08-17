// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::Executor;
use ay_core::term::{Symbol, TermData, TermStore};
use ay_core::{Sort, TermId};
use ay_frontend::parse;
use num_bigint::BigInt;
use num_rational::BigRational;

mod ite_regressions;

fn run_script(input: &str) -> Vec<String> {
    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("SMT-LIB script should execute")
}

fn contains_mul_with_add_child(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) => {
            if name == "*"
                && args.iter().any(|&arg| {
                    matches!(
                        terms.get(arg),
                        TermData::App(Symbol::Named(child_name), child_args)
                            if child_name == "+" && child_args.len() >= 2
                    )
                })
            {
                return true;
            }
            args.iter()
                .any(|&arg| contains_mul_with_add_child(terms, arg))
        }
        TermData::Not(inner) => contains_mul_with_add_child(terms, *inner),
        TermData::Ite(cond, then_br, else_br) => {
            contains_mul_with_add_child(terms, *cond)
                || contains_mul_with_add_child(terms, *then_br)
                || contains_mul_with_add_child(terms, *else_br)
        }
        _ => false,
    }
}

// --- Core check-sat path tests ---

#[test]
fn lra_sat_simple_bound() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 0.0))
        (assert (< x 10.0))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn lra_unsat_contradictory_bounds() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 5.0))
        (assert (< x 3.0))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn lra_unsat_two_var_strict_contradiction() {
    // Regression test for #5405: x > y AND y > x should be UNSAT
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (> x y))
        (assert (> y x))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn lra_sat_equality() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= (+ x y) 10.0))
        (assert (>= x 0.0))
        (assert (>= y 0.0))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn lra_unsat_equality_with_bounds() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (= x 5.0))
        (assert (> x 5.0))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn lra_empty_assertions_sat() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn lra_sat_strict_bounds_fractional() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 0.0))
        (assert (< x 0.001))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn lra_preprocess_applies_som_normalization() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("x", Sort::Real);
    let y = exec.ctx.terms.mk_var("y", Sort::Real);
    let z = exec.ctx.terms.mk_var("z", Sort::Real);
    let two = exec
        .ctx
        .terms
        .mk_rational(BigRational::from(BigInt::from(2)));
    let sum = exec.ctx.terms.mk_add(vec![x, y]);
    let mul = exec
        .ctx
        .terms
        .mk_app(Symbol::named("*"), vec![two, sum], Sort::Real);
    let assertion = exec.ctx.terms.mk_le(mul, z);
    exec.ctx.assertions = vec![assertion];

    assert!(
        contains_mul_with_add_child(&exec.ctx.terms, assertion),
        "test setup must bypass existing term-store multiplication normalization"
    );

    let preprocessed = exec.preprocess_lra_assertions();
    assert_eq!(preprocessed.len(), 1);
    assert!(
        !contains_mul_with_add_child(&exec.ctx.terms, preprocessed[0]),
        "pure LRA preprocessing should route assertions through NormalizeArithSom"
    );
}

// --- Incremental / push-pop tests ---

#[test]
fn incremental_lra_push_pop_roundtrip() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (= x 0))
        (push 1)
        (assert (> x 0))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    assert_eq!(run_script(input), vec!["unsat", "sat"]);
}

/// Regression test for #2822: after a push/pop cycle, a second push scope
/// with a contradictory strict inequality was incorrectly reported as SAT.
/// Root cause: re-activation of global assertion root literals after pop()
/// incorrectly skipped assertions encoded at depth <= scope_depth, but
/// after pop+push the new scope has different SAT selectors so the old
/// scoped activation clauses are dead.
#[test]
fn incremental_lra_strict_ineq_after_push_pop_cycle() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 0.0))
        (assert (< x 1.0))
        (check-sat)
        (push 1)
        (assert (> x 0.5))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (>= x 1.0))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    let result = run_script(input);
    assert_eq!(
        result,
        vec!["sat", "sat", "unsat", "sat"],
        "third check-sat should be UNSAT: x<1 and x>=1 are contradictory, got {result:?}"
    );
}

/// Variant of #2822 where global assertions are first encoded inside a push
/// scope (no check-sat before push). The activations are scoped, so after
/// pop they are dead and must be re-added for subsequent check-sat calls.
#[test]
fn incremental_lra_deferred_encoding_after_push_pop() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 0.0))
        (assert (< x 1.0))
        (push 1)
        (assert (> x 0.5))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (>= x 1.0))
        (check-sat)
        (pop 1)
    "#;
    let result = run_script(input);
    assert_eq!(
        result,
        vec!["sat", "unsat"],
        "second check-sat should be UNSAT: x<1 and x>=1 are contradictory, got {result:?}"
    );
}

#[test]
fn incremental_lra_nested_push_pop() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 0.0))
        (push 1)
        (assert (< x 10.0))
        (push 1)
        (assert (> x 10.0))
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat", "sat", "sat"]);
}

#[test]
fn incremental_lra_multiple_check_sats_same_scope() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 0.0))
        (push 1)
        (check-sat)
        (assert (< x 0.0))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat", "unsat", "sat"]);
}

#[test]
fn incremental_lra_empty_assertions_are_sat() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (push 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    assert_eq!(run_script(input), vec!["sat", "sat"]);
}

// --- Disequality split tests (#4919) ---

#[test]
fn lra_disequality_sat_simple() {
    // x = 5 AND x != 3 → sat (x = 5 satisfies both)
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (= x 5.0))
        (assert (distinct x 3.0))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn lra_disequality_unsat_pinned() {
    // x = 5 AND x != 5 → unsat (forced violation)
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (= x 5.0))
        (assert (distinct x 5.0))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn lra_disequality_split_needed() {
    // 0 < x < 10 AND x != 5 → sat (split: x < 5 OR x > 5)
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 0.0))
        (assert (< x 10.0))
        (assert (distinct x 5.0))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn lra_multi_var_disequality_split_needed_issue_6586() {
    // 0 <= x,y <= 1 AND x != y → sat. The incremental split-loop may
    // request the same expression split repeatedly; the SAT mapping for
    // those split atoms must remain stable across iterations.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x 0.0))
        (assert (<= x 1.0))
        (assert (>= y 0.0))
        (assert (<= y 1.0))
        (assert (not (= x y)))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn lra_multiple_disequalities() {
    // 0 < x < 4 AND x != 1 AND x != 2 AND x != 3 → sat (e.g., x = 0.5)
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (> x 0.0))
        (assert (< x 4.0))
        (assert (distinct x 1.0))
        (assert (distinct x 2.0))
        (assert (distinct x 3.0))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

/// Regression test for #7935: QF_LRA false-UNSAT on satisfiable OR-clause formulas.
///
/// The formula is SAT (e.g., x=4, y=0, z=2 satisfies all constraints).
/// AY was incorrectly returning UNSAT because atoms inside OR clauses
/// were being forced true at decision level 0, creating a spurious
/// theory conflict.
#[test]
fn regression_7935_false_unsat_or_clauses() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-fun x () Real)
        (declare-fun y () Real)
        (declare-fun z () Real)
        (assert (<= (- x z) 8))
        (assert (or (>= (- x y) 1) (< (- x z) 7)))
        (assert (or (> (- x z) 10) (< (- y z) 8)))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}
