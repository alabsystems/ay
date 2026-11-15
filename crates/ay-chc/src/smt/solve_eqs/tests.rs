// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::smt::{SmtContext, SmtResult};
use num_bigint::BigInt;

fn rvar(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Real))
}

fn bvar(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Bool))
}

fn real(n: i64) -> ChcExpr {
    ChcExpr::Real(n, 1)
}

fn none() -> FxHashSet<String> {
    FxHashSet::default()
}

fn eval_bool(e: &ChcExpr, model: &FxHashMap<String, SmtValue>) -> Option<bool> {
    match crate::expr::evaluate_expr(e, model)? {
        SmtValue::Bool(b) => Some(b),
        _ => None,
    }
}

/// The residual never mentions an eliminated variable, and the completed
/// model of `residual_model` satisfies the original formula.
fn assert_completes(
    original: &ChcExpr,
    solved: &SolvedEqs,
    residual_model: FxHashMap<String, SmtValue>,
) {
    let mut model = residual_model;
    assert_eq!(
        eval_bool(&solved.residual, &{
            let mut m = model.clone();
            assert!(solved.complete_model(&solved.residual.vars(), &mut m));
            m
        }),
        Some(true),
        "the residual model must satisfy the residual"
    );
    assert!(solved.complete_model(&original.vars(), &mut model));
    assert_eq!(eval_bool(original, &model), Some(true), "model {model:?}");
    let residual_vars = solved.residual.vars();
    for (v, _) in &solved.defs {
        assert!(!residual_vars.contains(v), "{v:?} was eliminated");
    }
}

#[test]
fn init_constants_select_one_disjunct_and_refute_the_unrolling() {
    // round = 0 ∧ ((round = 0 ∧ round' = 1 ∧ y' = y) ∨ (round = 1 ∧ round' = 2 ∧ y' = 5))
    //   ∧ y = 3 ∧ round' = 1 ∧ y' > 4   — only the first disjunct fits, and it
    // forces y' = 3.
    let f = ChcExpr::and_all([
        ChcExpr::eq(rvar("round"), real(0)),
        ChcExpr::or(
            ChcExpr::and_all([
                ChcExpr::eq(rvar("round"), real(0)),
                ChcExpr::eq(rvar("round1"), real(1)),
                ChcExpr::eq(rvar("y1"), rvar("y")),
            ]),
            ChcExpr::and_all([
                ChcExpr::eq(rvar("round"), real(1)),
                ChcExpr::eq(rvar("round1"), real(2)),
                ChcExpr::eq(rvar("y1"), real(5)),
            ]),
        ),
        ChcExpr::eq(rvar("y"), real(3)),
        ChcExpr::gt(rvar("y1"), real(4)),
    ]);
    let solved = solve_eqs(&f, &none()).expect("changes");
    assert_eq!(solved.residual, ChcExpr::Bool(false));
}

#[test]
fn counter_chain_folds_through_substitution() {
    let mut conjuncts = vec![ChcExpr::eq(rvar("c0"), real(0))];
    for i in 1..=5 {
        conjuncts.push(ChcExpr::eq(
            rvar(&format!("c{i}")),
            ChcExpr::add(rvar(&format!("c{}", i - 1)), real(1)),
        ));
    }
    conjuncts.push(ChcExpr::ge(rvar("c5"), real(10)));
    let unsat = ChcExpr::and_all(conjuncts.clone());
    assert_eq!(
        solve_eqs(&unsat, &none()).expect("changes").residual,
        ChcExpr::Bool(false)
    );
    conjuncts.pop();
    conjuncts.push(ChcExpr::ge(rvar("c5"), real(5)));
    let sat = ChcExpr::and_all(conjuncts);
    let solved = solve_eqs(&sat, &none()).expect("changes");
    assert_eq!(solved.residual, ChcExpr::Bool(true));
    assert_completes(&sat, &solved, FxHashMap::default());
}

#[test]
fn chained_definitions_stay_idempotent_and_complete_the_model() {
    // x = y, then y = z + 1: x's definition must be rewritten to z + 1.
    let f = ChcExpr::and_all([
        ChcExpr::eq(rvar("x"), rvar("y")),
        ChcExpr::eq(rvar("y"), ChcExpr::add(rvar("z"), real(1))),
        ChcExpr::ge(rvar("z"), real(3)),
        ChcExpr::le(rvar("x"), real(10)),
    ]);
    let solved = solve_eqs(&f, &none()).expect("changes");
    assert_eq!(solved.eliminated(), 2);
    let vars = solved.residual.vars();
    assert_eq!(vars, vec![ChcVar::new("z", ChcSort::Real)]);
    let model: FxHashMap<String, SmtValue> = std::iter::once((
        "z".to_string(),
        SmtValue::Real(BigRational::from_integer(BigInt::from(4))),
    ))
    .collect();
    assert_completes(&f, &solved, model);
}

#[test]
fn definition_after_its_users_is_pushed_into_them() {
    // y = x + 1 is chosen first; x = 3 arrives later and must reach y.
    let f = ChcExpr::and_all([
        ChcExpr::eq(rvar("y"), ChcExpr::add(rvar("x"), real(1))),
        ChcExpr::eq(rvar("x"), real(3)),
        ChcExpr::lt(rvar("w"), rvar("y")),
    ]);
    let solved = solve_eqs(&f, &none()).expect("changes");
    let model: FxHashMap<String, SmtValue> = std::iter::once((
        "w".to_string(),
        SmtValue::Real(BigRational::from_integer(BigInt::from(2))),
    ))
    .collect();
    assert_completes(&f, &solved, model);
}

#[test]
fn bool_units_are_substituted() {
    let f = ChcExpr::and_all([
        bvar("b"),
        ChcExpr::implies(bvar("b"), ChcExpr::gt(rvar("x"), real(1))),
        ChcExpr::not(bvar("c")),
        ChcExpr::or(bvar("c"), ChcExpr::lt(rvar("x"), real(0))),
    ]);
    let solved = solve_eqs(&f, &none()).expect("changes");
    let vars = solved.residual.vars();
    assert!(
        !vars.iter().any(|v| v.name == "b" || v.name == "c"),
        "{vars:?}"
    );
    let mut m = FxHashMap::default();
    m.insert(
        "x".to_string(),
        SmtValue::Real(BigRational::from_integer(BigInt::from(2))),
    );
    // x = 2 satisfies x > 1 but not x < 0: the residual must say so.
    let mut completed = m.clone();
    assert!(solved.complete_model(&f.vars(), &mut completed));
    assert_eq!(eval_bool(&solved.residual, &completed), Some(false));
    assert_eq!(eval_bool(&f, &completed), Some(false));
}

#[test]
fn occurs_check_keeps_a_recursive_equality() {
    let f = ChcExpr::and(
        ChcExpr::eq(rvar("x"), ChcExpr::add(rvar("x"), real(1))),
        ChcExpr::ge(rvar("y"), real(0)),
    );
    assert!(solve_eqs(&f, &none()).is_none());
}

#[test]
fn nothing_to_do_is_none() {
    let f = ChcExpr::and(
        ChcExpr::le(rvar("x"), rvar("y")),
        ChcExpr::lt(rvar("y"), real(3)),
    );
    assert!(solve_eqs(&f, &none()).is_none());
}

#[test]
fn rational_constants_fold_exactly() {
    // x = 1/2 ∧ y = x + 1/2 ∧ y ≠ 1  ⇒  false
    let f = ChcExpr::and_all([
        ChcExpr::eq(rvar("x"), ChcExpr::Real(1, 2)),
        ChcExpr::eq(rvar("y"), ChcExpr::add(rvar("x"), ChcExpr::Real(1, 2))),
        ChcExpr::not(ChcExpr::eq(rvar("y"), real(1))),
    ]);
    assert_eq!(
        solve_eqs(&f, &none()).expect("changes").residual,
        ChcExpr::Bool(false)
    );
}

#[test]
fn ite_with_decided_condition_is_folded() {
    // b ∧ z = ite(b, x, y) ∧ x = 2 ∧ z > 3  ⇒  false
    let f = ChcExpr::and_all([
        bvar("b"),
        ChcExpr::eq(rvar("z"), ChcExpr::ite(bvar("b"), rvar("x"), rvar("y"))),
        ChcExpr::eq(rvar("x"), real(2)),
        ChcExpr::gt(rvar("z"), real(3)),
    ]);
    assert_eq!(
        solve_eqs(&f, &none()).expect("changes").residual,
        ChcExpr::Bool(false)
    );
}

#[test]
fn protected_variables_are_substituted_but_kept() {
    // x protected: x = 1 ∧ y = x + 1 ∧ y > z. x stays constrained (x = 1) in
    // the residual; y is eliminated.
    let protected: FxHashSet<String> = std::iter::once("x".to_string()).collect();
    let f = ChcExpr::and_all([
        ChcExpr::eq(rvar("x"), real(1)),
        ChcExpr::eq(rvar("y"), ChcExpr::add(rvar("x"), real(1))),
        ChcExpr::gt(rvar("y"), rvar("z")),
    ]);
    let solved = solve_eqs(&f, &protected).expect("changes");
    let vars = solved.residual.vars();
    assert!(vars.iter().any(|v| v.name == "x"), "{}", solved.residual);
    assert!(!vars.iter().any(|v| v.name == "y"), "{}", solved.residual);
    let mut m = FxHashMap::default();
    m.insert(
        "x".to_string(),
        SmtValue::Real(BigRational::from_integer(BigInt::from(1))),
    );
    m.insert(
        "z".to_string(),
        SmtValue::Real(BigRational::from_integer(BigInt::from(0))),
    );
    assert_eq!(eval_bool(&solved.residual, &m), Some(true));
    // The residual forces x = 1.
    m.insert(
        "x".to_string(),
        SmtValue::Real(BigRational::from_integer(BigInt::from(7))),
    );
    assert_eq!(eval_bool(&solved.residual, &m), Some(false));
}

#[test]
fn a_protected_equality_eliminates_the_local_side() {
    // x1 protected, x0 local: x1 = x0 ∧ x0 = 4 — the residual is x1 = 4.
    let protected: FxHashSet<String> = std::iter::once("x1".to_string()).collect();
    let f = ChcExpr::and(
        ChcExpr::eq(rvar("x1"), rvar("x0")),
        ChcExpr::eq(rvar("x0"), real(4)),
    );
    let solved = solve_eqs(&f, &protected).expect("changes");
    assert_eq!(
        solved.residual.vars(),
        vec![ChcVar::new("x1", ChcSort::Real)]
    );
}

#[test]
fn shared_subterms_are_simplified_once() {
    // A DAG whose tree expansion is 2^40 nodes: each level is (and l l).
    let mut e = Arc::new(ChcExpr::or(
        ChcExpr::eq(rvar("x"), real(1)),
        ChcExpr::eq(rvar("y"), real(2)),
    ));
    for _ in 0..40 {
        e = Arc::new(ChcExpr::Op(
            ChcOp::And,
            vec![Arc::clone(&e), Arc::clone(&e)],
        ));
    }
    let f = ChcExpr::Op(
        ChcOp::And,
        vec![Arc::new(ChcExpr::eq(rvar("x"), real(1))), Arc::clone(&e)],
    );
    let solved = solve_eqs(&f, &none()).expect("changes");
    assert_eq!(solved.residual, ChcExpr::Bool(true));
}

#[test]
fn shared_conjunctions_do_not_expand_their_tree() {
    let mut e = Arc::new(ChcExpr::or(
        ChcExpr::le(rvar("x"), rvar("y")),
        ChcExpr::eq(rvar("y"), real(2)),
    ));
    for _ in 0..40 {
        e = Arc::new(ChcExpr::Op(
            ChcOp::And,
            vec![Arc::clone(&e), Arc::clone(&e)],
        ));
    }
    let f = ChcExpr::Op(
        ChcOp::And,
        vec![Arc::new(ChcExpr::eq(rvar("z"), real(1))), Arc::clone(&e)],
    );
    let solved = solve_eqs(&f, &none()).expect("changes");
    assert_eq!(solved.eliminated(), 1);
    assert_eq!(solved.residual.vars().len(), 2);
}

#[test]
fn search_lane_check_sat_uses_the_pass_and_returns_complete_models() {
    // An unrolling the pass decides entirely, and one it leaves to the
    // executor: both must answer, SAT with a model of the ORIGINAL formula.
    let unsat = ChcExpr::and_all([
        ChcExpr::eq(rvar("a0"), real(0)),
        ChcExpr::eq(rvar("a1"), ChcExpr::add(rvar("a0"), real(1))),
        ChcExpr::eq(rvar("a2"), ChcExpr::add(rvar("a1"), real(1))),
        ChcExpr::gt(rvar("a2"), real(2)),
    ]);
    let mut smt = SmtContext::new_search();
    assert!(smt.check_sat(&unsat).is_unsat());

    let sat = ChcExpr::and_all([
        ChcExpr::eq(rvar("a0"), real(0)),
        ChcExpr::eq(rvar("a1"), ChcExpr::add(rvar("a0"), rvar("d"))),
        ChcExpr::le(rvar("d"), real(3)),
        ChcExpr::gt(rvar("a1"), real(2)),
    ]);
    let mut smt = SmtContext::new_search();
    match smt.check_sat(&sat) {
        SmtResult::Sat(model) => assert_eq!(eval_bool(&sat, &model), Some(true)),
        other => panic!("expected sat, got {other:?}"),
    }
}

#[test]
fn integer_only_and_non_scalar_queries_are_not_touched() {
    let ivar = |n: &str| ChcExpr::var(ChcVar::new(n, ChcSort::Int));
    let f = ChcExpr::and(
        ChcExpr::eq(ivar("x"), ChcExpr::Int(1)),
        ChcExpr::gt(ivar("x"), ChcExpr::Int(0)),
    );
    assert!(for_search_executor(&f).is_none());
    let g = ChcExpr::and(
        ChcExpr::eq(rvar("x"), real(1)),
        ChcExpr::gt(rvar("x"), real(0)),
    );
    assert!(for_search_executor(&g).is_some());
}

#[test]
fn split_equalities_are_rejoined_into_definitions() {
    // What interpolation callers hand over: `x = 0` and `y = x + 1` split into
    // pairs of inequalities (`collect_conjuncts_for_interpolation`).
    let split = |a: ChcExpr, b: ChcExpr| [ChcExpr::le(a.clone(), b.clone()), ChcExpr::le(b, a)];
    let mut parts = Vec::new();
    parts.extend(split(rvar("x"), real(0)));
    parts.extend(split(rvar("y"), ChcExpr::add(rvar("x"), real(1))));
    parts.push(ChcExpr::gt(rvar("y"), real(2)));
    let f = ChcExpr::and_all(parts);
    assert_eq!(
        solve_eqs(&f, &none()).expect("changes").residual,
        ChcExpr::Bool(false)
    );
}

#[test]
fn a_conditional_assignment_used_nowhere_else_disappears() {
    // ite(b, x = 1, x = y + 2) ∧ y > 0 ∧ (b ∨ y < 5): x is defined by the
    // conditional assignment and used nowhere else, so its definition leaves
    // the residual and comes back through the model.
    let f = ChcExpr::and_all([
        ChcExpr::ite(
            bvar("b"),
            ChcExpr::eq(rvar("x"), real(1)),
            ChcExpr::eq(rvar("x"), ChcExpr::add(rvar("y"), real(2))),
        ),
        ChcExpr::gt(rvar("y"), real(0)),
        ChcExpr::or(bvar("b"), ChcExpr::lt(rvar("y"), real(5))),
    ]);
    // The Search-lane reach leaves the conditional assignment alone.
    assert!(solve_eqs_with(&f, &none(), Reach::Plain).is_none());
    let solved = solve_eqs(&f, &none()).expect("changes");
    assert!(
        !solved.residual.vars().iter().any(|v| v.name == "x"),
        "{}",
        solved.residual
    );
    let mut model: FxHashMap<String, SmtValue> = FxHashMap::default();
    model.insert("b".to_string(), SmtValue::Bool(false));
    model.insert(
        "y".to_string(),
        SmtValue::Real(BigRational::from_integer(BigInt::from(3))),
    );
    assert_completes(&f, &solved, model);
}
