// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A problem symbol spelled like a theory operator is never read as that
//! operator.
//!
//! REGRESSION (measured 2026-10-07 on 7ae4f642c, the r17 verifier's
//! reproducers): AY's front end, like z3, accepts a `declare-fun` of a Core
//! connective's name at a new signature (`ite`, `=`, `distinct`, `and`, …:
//! they stay declarable as `(_ map f)` targets and get a private core
//! identity), and AY answers every problem in [`overloads`] `sat`. The
//! mirror's rules dispatched on the bare head name, so `evaluate` folded the
//! user's `(ite true 0)` to `0`, `(= 0)` and `(distinct 0)` to `true`, and
//! the `and` rule read the user's `(and false 0)` as a conjunction: a
//! refutation of each satisfiable problem was counted as checked. Clean
//! refused all five. Now the problem is refused as a query (it declares a
//! name the front end's operator tables hold) AND, independently, the step
//! `t1` that reads the user's function as the connective is not accepted.
//!
//! Why AY's own front end keeps accepting these declarations, although
//! SMT-LIB 2.6 forbids redeclaring a theory symbol: the Core and arithmetic
//! names are AY's `(_ map f)` targets (`((_ map not) s)` is set complement;
//! pinned by `test_core_connectives_not_reserved_for_map` and the
//! `array_map_8533` set union/intersection suites), and each such
//! declaration gets a private core identity, so AY itself never conflates it
//! with the builtin (it answers `sat` on every problem here).
//!
//! `false_quoted` is the same verifier's consumer-side finding: the quoted
//! symbol `|false|` is a user constant (z3 rejects the declaration, AY
//! answers `sat`), the mirror leaves the refutation undetermined, and the
//! pinned Clean accepted it; with `CLEAN_PATH` its verdict is printed.

use super::super::consumer_rules::{mirror_certificate, step_verdict};
use super::clean_accepts;

/// `(assume a0 T)` refuted by `evaluate` reading `T` as `false`.
fn evaluate_refutation(t: &str) -> String {
    format!(
        "(assume a0 {t})\n(step t1 (cl (= {t} false)) :rule evaluate)\n\
         (step t2 (cl (not (= {t} false)) (not {t}) false) :rule equiv_pos2)\n\
         (step t3 (cl (not false)) :rule false)\n\
         (step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))\n"
    )
}

fn problem(declaration: &str, assertion: &str) -> String {
    format!("(set-logic ALL)\n{declaration}\n(assert {assertion})\n(check-sat)\n")
}

/// `(name, problem, proof)`: every problem is satisfiable.
fn overloads() -> Vec<(&'static str, String, String)> {
    let evaluated = |name, declaration, assertion| {
        (
            name,
            problem(declaration, assertion),
            evaluate_refutation(assertion),
        )
    };
    vec![
        evaluated(
            "ite_overload_int",
            "(declare-fun ite (Bool Int) Int)",
            "(= (ite true 0) 1)",
        ),
        evaluated(
            "ite_overload_bool",
            "(declare-fun ite (Bool Bool) Bool)",
            "(not (ite true true))",
        ),
        evaluated(
            "eq_overload_unary",
            "(declare-fun = (Int) Bool)",
            "(not (= 0))",
        ),
        evaluated(
            "distinct_overload_unary",
            "(declare-fun distinct (Int) Bool)",
            "(not (distinct 0))",
        ),
        (
            "and_overload",
            problem("(declare-fun and (Bool Int) Bool)", "(and false 0)"),
            "(assume a0 (and false 0))\n(step t1 (cl false) :rule and :premises (a0) :args (0))\n\
             (step t2 (cl (not false)) :rule false)\n\
             (step t3 (cl) :rule resolution :premises (t1 t2))\n"
                .to_string(),
        ),
        // The verifier's scratch reproducers of the same shape.
        evaluated(
            "not_overload_int",
            "(declare-fun not (Int) Bool)",
            "(not 0)",
        ),
        evaluated(
            "and_overload_unary",
            "(declare-fun and (Int) Bool)",
            "(not (and 0))",
        ),
        (
            "false_quoted",
            problem("(declare-const |false| Bool)", "|false|"),
            "(assume a0 false)\n(step t1 (cl (not false)) :rule false)\n\
             (step t2 (cl) :rule resolution :premises (a0 t1))\n"
                .to_string(),
        ),
    ]
}

#[test]
#[ntest::timeout(600_000)]
fn a_problem_symbol_spelled_like_an_operator_is_not_that_operator() {
    let mut failures = Vec::new();
    for (name, problem, proof) in overloads() {
        let (verdict, _) = super::one_shot(&problem, &[]);
        if verdict != "sat" {
            failures.push(format!("{name}: ay answers {verdict:?}"));
        }
        let coverage = mirror_certificate(&problem, &proof);
        if coverage.checked() || coverage.refutation.is_some() {
            failures.push(format!(
                "{name}: a refutation of a satisfiable problem is checked"
            ));
        }
        if name != "false_quoted"
            && !coverage
                .refused
                .iter()
                .any(|refusal| refusal.contains("a name a theory operator is spelled"))
        {
            failures.push(format!(
                "{name}: the operator-named declaration is not refused: {:?}",
                coverage.refused
            ));
        }
        // Independently of the document-level refusal: the step that reads
        // the user's function as the connective is never accepted.
        if name != "false_quoted" {
            let t1 = step_verdict(&problem, &proof, "t1").unwrap_or_default();
            if t1 == "accepted" {
                failures.push(format!(
                    "{name}: t1 reads the problem's function as an operator"
                ));
            }
        }
        if let Some(accepts) = clean_accepts(&problem, &proof) {
            eprintln!("{name}: CLEAN_PATH accepts it: {accepts}");
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
