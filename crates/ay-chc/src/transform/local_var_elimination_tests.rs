// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ChcSort;

#[test]
fn get_linear_coefficient_sub_overflow_returns_none() {
    let x = ChcVar::new("x", ChcSort::Int);
    let lhs = ChcExpr::mul(ChcExpr::Int(i128::MAX), ChcExpr::var(x.clone()));
    let rhs = ChcExpr::neg(ChcExpr::var(x.clone()));
    let expr = ChcExpr::sub(lhs, rhs);
    assert_eq!(get_linear_coefficient(&expr, &x), None);
}

#[test]
fn get_linear_coefficient_neg_overflow_returns_none() {
    let x = ChcVar::new("x", ChcSort::Int);
    let inner = ChcExpr::mul(ChcExpr::Int(i128::MIN), ChcExpr::var(x.clone()));
    let expr = ChcExpr::neg(inner);
    assert_eq!(get_linear_coefficient(&expr, &x), None);
}

// Moved from tests/chc_regression_1615.rs — uses LocalVarEliminator (no longer pub)

fn parse_problem(smt: &str) -> ChcProblem {
    use crate::parser::ChcParser;
    let problem =
        ChcParser::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    problem
        .validate()
        .unwrap_or_else(|err| panic!("CHC validation failed: {err}\nSMT2:\n{smt}"));
    problem
}

const DTUC_000: &str = r#"(set-logic HORN)
(declare-fun |FUN| ( Int Int Int Int ) Bool)
(declare-fun |SAD| ( Int Int Int Int ) Bool)
(assert (forall ( (A Int) (B Int) (C Int) (D Int) ) (=> (and (and (= A 0) (= C 0))) (FUN A B C D))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) (=> (and (FUN A D B F) (and (= C (+ 1 A)) (not (<= F A)) (= E (+ 1 B)))) (FUN C D E F))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) (=> (and (FUN B A D E) (and (= B E) (= C E))) (SAD B C D E))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) (=> (and (SAD C B A F) (and (= D (+ (- 1) B)) (not (<= B 0)) (= E (+ (- 1) A)))) (SAD C D E F))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) ) (=> (and (SAD A C D B) (and (not (<= C 0)) (<= D 0))) false)))
(check-sat)
"#;

const S_MUTANTS_16_M_000: &str = r#"(set-logic HORN)
(declare-fun |itp| ( Int Int Int ) Bool)
(declare-fun |itp1| ( Int Int Int ) Bool)
(assert (forall ( (A Int) (B Int) (C Int) ) (=> (and (and (= A 0) (not (<= 5 C)) (not (<= C 0)) (= B (* 3 C)))) (itp A B C))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) (=> (and (itp A B E) (and (= C (+ 1 A)) (not (<= 100 A)) (= D (+ 1 B)))) (itp C D E))))
(assert (forall ( (A Int) (B Int) (C Int) ) (=> (and (itp A B C) (<= 100 A)) (itp1 A B C))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) (=> (and (itp1 A B E) (and (= C (+ 1 A)) (not (<= 120 A)) (= D (+ 1 B)))) (itp1 C D E))))
(assert (forall ( (A Int) (B Int) (C Int) ) (=> (and (itp1 B C A) (and (or (not (<= C 132)) (not (>= C 3))) (<= 120 B))) false)))
(check-sat)
"#;

const THREE_DOTS_MOVING_2_000: &str = r#"(set-logic HORN)
(declare-fun |inv| ( Int Int Int Int ) Bool)
(assert (forall ( (A Int) (B Int) (C Int) (D Int) ) (=> (and (and (>= D (+ B (* (- 1) C))) (>= D (+ B (* (- 1) A))) (not (<= B A)) (>= D (+ C (* (- 2) A) B)))) (inv A B C D))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) (=> (and (inv B C F A) (let ((a!1 (and (= D (ite (<= B F) (+ 1 B) (+ (- 1) B))) (= E D) (= B C)))) (let ((a!2 (or (and (= D B) (= E (+ (- 1) C)) (not (= B C))) a!1))) (and (= G (+ (- 1) A)) a!2 (not (= C F)))))) (inv D E F G))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) ) (=> (and (inv A B C D) (and (<= D 0) (not (= B C)))) false)))
(check-sat)
"#;

#[test]
fn test_local_var_elimination_dtuc() {
    let problem = parse_problem(DTUC_000);
    let eliminator = LocalVarEliminator::new();
    let result = eliminator.eliminate(&problem);
    result.validate().unwrap();
    assert!(result.clauses().len() <= problem.clauses().len());
    assert_eq!(problem.predicates().len(), result.predicates().len());
}

#[test]
fn test_local_var_elimination_s_mutants() {
    let problem = parse_problem(S_MUTANTS_16_M_000);
    let eliminator = LocalVarEliminator::new();
    let result = eliminator.eliminate(&problem);
    result.validate().unwrap();
    assert!(result.clauses().len() <= problem.clauses().len());
    assert_eq!(problem.predicates().len(), result.predicates().len());
}

#[test]
fn test_local_var_elimination_three_dots() {
    let problem = parse_problem(THREE_DOTS_MOVING_2_000);
    let eliminator = LocalVarEliminator::new();
    let result = eliminator.eliminate(&problem);
    result.validate().unwrap();
    assert!(result.clauses().len() <= problem.clauses().len());
    assert_eq!(problem.predicates().len(), result.predicates().len());
}
