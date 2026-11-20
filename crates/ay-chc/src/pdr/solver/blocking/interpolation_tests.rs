// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Workstream D ladder tests (the development design notes at 9598c4206, §4.1, WP-D1-M): the
//! per-clause stage 1 serves `∨_c I_c`, which every clause implies, even when
//! the conjunction of the clauses' A-sides is unsatisfiable (where the old
//! conjunctive call was skipped and stage 5 validated vacuously).

use super::*;
use crate::smt::{SmtContext, SmtResult};
use crate::{ChcSort, ChcVar};

fn int(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

fn real(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Real))
}

fn names(list: &[&str]) -> FxHashSet<String> {
    list.iter().map(|n| (*n).to_owned()).collect()
}

fn vars_of(exprs: &[ChcExpr]) -> FxHashSet<String> {
    exprs
        .iter()
        .flat_map(ChcExpr::vars)
        .map(|v| v.name)
        .collect()
}

/// Verification-lane validity: `a ⊨ i`.
fn entails(a: &[ChcExpr], i: &ChcExpr) -> bool {
    let query = ChcExpr::and(ChcExpr::and_all(a.iter().cloned()), ChcExpr::not(i.clone()));
    matches!(
        SmtContext::new().check_sat(&query),
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
    )
}

fn per_clause(
    clauses: &[Vec<ChcExpr>],
    b: &[ChcExpr],
    canonical: &[&str],
) -> InterpolatingSatResult {
    let raw: Vec<FxHashSet<String>> = clauses.iter().map(|c| vars_of(c)).collect();
    per_clause_interpolant(clauses, &raw, false, b, &vars_of(b), &names(canonical))
}

#[test]
fn per_clause_stage_one_serves_a_disjunction_every_clause_implies() {
    // Clause 1 (init): x = 0. Clause 2 (trans): x = y + 1 ∧ 1 ≤ y ≤ 5 over the
    // clause-local y, i.e. x ∈ [2, 6]. The POB is x ≥ 10.
    let x = int("x");
    let y = int("y");
    let init = vec![ChcExpr::eq(x.clone(), ChcExpr::Int(0))];
    let trans = vec![
        ChcExpr::eq(x.clone(), ChcExpr::add(y.clone(), ChcExpr::Int(1))),
        ChcExpr::le(ChcExpr::Int(1), y.clone()),
        ChcExpr::le(y, ChcExpr::Int(5)),
    ];
    let b = vec![ChcExpr::ge(x, ChcExpr::Int(10))];
    // ∧A is UNSAT here (x = 0 and x ≥ 2): the conjunctive stage 1 was skipped.
    let conj: Vec<ChcExpr> = init.iter().chain(&trans).cloned().collect();
    assert!(matches!(
        SmtContext::new().check_sat(&ChcExpr::and_all(conj)),
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
    ));
    let InterpolatingSatResult::Unsat(itp) = per_clause(&[init.clone(), trans.clone()], &b, &["x"])
    else {
        panic!("per-clause stage 1 must serve an interpolant");
    };
    assert!(entails(&init, &itp), "init must imply {itp}");
    assert!(entails(&trans, &itp), "trans must imply {itp}");
    assert!(
        entails(&[itp.clone()], &ChcExpr::not(b[0].clone())),
        "{itp} must block B"
    );
    assert!(itp.vars().iter().all(|v| v.name == "x"), "locality: {itp}");
}

#[test]
fn per_clause_stage_one_drops_an_unsatisfiable_clause_and_fails_closed() {
    let x = real("x");
    // Clause 1 is unsatisfiable on its own: it contributes no disjunct.
    let dead = vec![
        ChcExpr::lt(x.clone(), ChcExpr::Real(0, 1)),
        ChcExpr::gt(x.clone(), ChcExpr::Real(1, 1)),
    ];
    let live = vec![ChcExpr::le(x.clone(), ChcExpr::Real(1, 2))];
    let b = vec![ChcExpr::ge(x.clone(), ChcExpr::Real(3, 1))];
    let InterpolatingSatResult::Unsat(itp) = per_clause(&[dead, live.clone()], &b, &["x"]) else {
        panic!("a dead clause must not fail the stage");
    };
    assert!(entails(&live, &itp));
    assert!(entails(&[itp.clone()], &ChcExpr::not(b[0].clone())));
    // A clause that reaches B (A_c ∧ B satisfiable) fails the whole stage.
    let reaching = vec![ChcExpr::ge(x.clone(), ChcExpr::Real(5, 1))];
    assert!(matches!(
        per_clause(&[live, reaching], &b, &["x"]),
        InterpolatingSatResult::Unknown
    ));
}
