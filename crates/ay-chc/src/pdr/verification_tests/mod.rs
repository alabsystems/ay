// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Andrew Yates <andrewyates.name@gmail.com>

use super::PdrSolver;
use crate::pdr::verification::mod_div;
use crate::pdr::{InvariantModel, PdrConfig, PredicateInterpretation};
use crate::smt::{SmtResult, SmtValue};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
use ay_core::time::Instant;
use std::sync::Arc;
use std::time::Duration;

fn int_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

fn var(name: &str) -> ChcExpr {
    ChcExpr::var(int_var(name))
}

fn mod_eq(var_name: &str, modulus: i64, rhs: i64) -> ChcExpr {
    ChcExpr::eq(
        ChcExpr::Op(
            ChcOp::Mod,
            vec![Arc::new(var(var_name)), Arc::new(ChcExpr::int(modulus))],
        ),
        ChcExpr::int(rhs),
    )
}

#[test]
fn test_drop_mod_div_conjuncts_filters_nested_and() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let mod_conj = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(x.clone()), ChcExpr::int(2)),
        ChcExpr::int(0),
    );

    let div_expr = ChcExpr::Op(
        ChcOp::Div,
        vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(2))],
    );
    let div_conj = ChcExpr::eq(div_expr, ChcExpr::int(1));

    let keep_conj = ChcExpr::eq(ChcExpr::var(y), ChcExpr::int(7));

    let expr = ChcExpr::and(mod_conj, ChcExpr::and(keep_conj.clone(), div_conj));
    let dropped = mod_div::drop_mod_div_conjuncts(&expr);

    assert_eq!(dropped, keep_conj);
}

#[test]
fn test_drop_mod_div_conjuncts_all_dropped_returns_true() {
    let x = ChcVar::new("x", ChcSort::Int);

    let mod_conj = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(x.clone()), ChcExpr::int(2)),
        ChcExpr::int(0),
    );
    let div_conj = ChcExpr::eq(
        ChcExpr::Op(
            ChcOp::Div,
            vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(2))],
        ),
        ChcExpr::int(1),
    );

    let expr = ChcExpr::and(mod_conj, div_conj);
    let dropped = mod_div::drop_mod_div_conjuncts(&expr);

    assert_eq!(dropped, ChcExpr::Bool(true));
}

#[test]
fn test_instance_subst_var_and_value_uses_bool_sort() {
    let name = "x".to_string();
    let value = SmtValue::Bool(true);
    let mut saw_unknown = false;

    let (var, expr) =
        super::instance_subst_var_and_value(&name, &value, None, false, &mut saw_unknown);
    assert_eq!(var.sort, ChcSort::Bool);
    assert_eq!(expr, ChcExpr::Bool(true));
    assert!(!saw_unknown);

    let x = ChcVar::new("x", ChcSort::Bool);
    let substituted = ChcExpr::var(x).substitute(&[(var, expr)]);
    assert_eq!(substituted, ChcExpr::Bool(true));
}

#[test]
fn array_sat_cross_check_accepts_ground_array_store_formula_by_evaluation() {
    let mut smt = ChcProblem::new().make_smt_context();
    let array = ChcExpr::store(
        ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::int(0))),
        ChcExpr::int(5),
        ChcExpr::int(42),
    );
    let query = ChcExpr::eq(ChcExpr::select(array, ChcExpr::int(5)), ChcExpr::int(42));

    let result = super::array_sat_cross_check_result(&mut smt, &query, false, "unit test");

    assert_eq!(
        result, None,
        "ground select-store equality should be accepted as SAT by concrete evaluation"
    );
}

#[test]
fn array_sat_cross_check_rejects_false_ground_array_store_formula_by_evaluation() {
    let mut smt = ChcProblem::new().make_smt_context();
    let array = ChcExpr::store(
        ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::int(0))),
        ChcExpr::int(5),
        ChcExpr::int(42),
    );
    let query = ChcExpr::eq(ChcExpr::select(array, ChcExpr::int(5)), ChcExpr::int(43));

    let result = super::array_sat_cross_check_result(&mut smt, &query, false, "unit test");

    assert_eq!(
        result,
        Some(super::CexVerificationResult::Spurious),
        "false ground select-store equality should reject the witness as spurious"
    );
}

#[test]
fn ground_array_semantic_equality_accepts_redundant_store_over_const_array() {
    let stored_default = ChcExpr::store(
        ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::int(0))),
        ChcExpr::int(5),
        ChcExpr::int(0),
    );
    let const_array = ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::int(0)));

    assert_eq!(
        super::ground_exprs_semantically_equal(&stored_default, &const_array),
        Some(true),
        "premise/head alignment should accept semantically equal ground array terms"
    );
}

#[test]
fn test_instance_subst_var_and_value_opaque_marks_unknown_6289() {
    let name = "x";
    let value = SmtValue::Opaque("__au_k0".to_string());
    let mut saw_unknown = false;
    let bv8 = ChcSort::BitVec(8);

    let (var, expr) =
        super::instance_subst_var_and_value(name, &value, Some(&bv8), false, &mut saw_unknown);

    assert_eq!(var.sort, ChcSort::BitVec(8));
    assert_eq!(
        expr,
        ChcExpr::var(ChcVar::new("__au_k0", ChcSort::BitVec(8)))
    );
    assert!(saw_unknown);
}

#[test]
fn test_instance_subst_var_and_value_uses_declared_array_sort_6293() {
    let name = "arr";
    let value = SmtValue::ConstArray(Box::new(SmtValue::Int(3)));
    let mut saw_unknown = false;
    let declared_sort = ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::BitVec(16)));

    let (var, expr) = super::instance_subst_var_and_value(
        name,
        &value,
        Some(&declared_sort),
        false,
        &mut saw_unknown,
    );

    assert_eq!(var.sort, declared_sort);
    assert_eq!(
        expr,
        ChcExpr::ConstArray(ChcSort::BitVec(8), Arc::new(ChcExpr::BitVec(3, 16)))
    );
    assert!(!saw_unknown);
}

#[test]
fn test_smt_value_to_chc_expr_for_sort_canonicalizes_recursive_dt_backedge_9692() {
    let list_sort = ChcSort::Datatype {
        name: "listOfInt".to_string(),
        constructors: Arc::new(vec![
            crate::ChcDtConstructor {
                name: "conslistOfInt".to_string(),
                selectors: vec![
                    crate::ChcDtSelector {
                        name: "headlistOfInt".to_string(),
                        sort: ChcSort::Int,
                    },
                    crate::ChcDtSelector {
                        name: "taillistOfInt".to_string(),
                        sort: ChcSort::Uninterpreted("listOfInt".to_string()),
                    },
                ],
            },
            crate::ChcDtConstructor {
                name: "nillistOfInt".to_string(),
                selectors: vec![],
            },
        ]),
    };
    let value = SmtValue::Datatype(
        "conslistOfInt".to_string(),
        vec![
            SmtValue::Int(1),
            SmtValue::Datatype("nillistOfInt".to_string(), vec![]),
        ],
    );

    let expr = super::smt_value_to_chc_expr_for_sort(&value, &list_sort);
    let ChcExpr::FuncApp(ctor, sort, args) = &expr else {
        panic!("expected cons constructor expression");
    };
    assert_eq!(ctor, "conslistOfInt");
    assert_eq!(sort, &list_sort);
    assert_eq!(args.len(), 2);
    let ChcExpr::FuncApp(nil_ctor, nil_sort, nil_args) = args[1].as_ref() else {
        panic!("expected nil tail constructor expression");
    };
    assert_eq!(nil_ctor, "nillistOfInt");
    assert_eq!(nil_sort, &list_sort);
    assert!(nil_args.is_empty());
}

#[test]
fn test_query_clause_concrete_self_check_finds_mod_satisfying_assignment_5803() {
    // Matches the query-clause soundness fallback in model.rs:
    // transition_check(&body, &true, &body)
    let body = ChcExpr::and_all(vec![
        ChcExpr::eq(var("A"), ChcExpr::int(6)),
        ChcExpr::eq(var("B"), ChcExpr::int(3)),
        mod_eq("A", 2, 0),
        mod_eq("A", 3, 0),
        ChcExpr::eq(ChcExpr::add(var("A"), var("B")), ChcExpr::int(9)),
    ]);

    let result = super::concrete::transition_check(&body, &ChcExpr::Bool(true), &body);
    assert!(
        result.is_some(),
        "query-clause self-check should find the concrete SAT witness"
    );
    let model = result.unwrap();
    assert_eq!(model.get("A"), Some(&SmtValue::Int(6)));
    assert_eq!(model.get("B"), Some(&SmtValue::Int(3)));
}

#[test]
fn test_query_clause_concrete_self_check_rejects_unsat_mod_constraints_5803() {
    let body = ChcExpr::and_all(vec![
        ChcExpr::eq(var("A"), ChcExpr::int(6)),
        mod_eq("A", 4, 1),
        ChcExpr::eq(var("B"), ChcExpr::int(3)),
        ChcExpr::eq(ChcExpr::add(var("A"), var("B")), ChcExpr::int(9)),
    ]);

    let result = super::concrete::transition_check(&body, &ChcExpr::Bool(true), &body);
    assert!(
        result.is_none(),
        "contradictory mod constraints must not produce a fake counterexample"
    );
}

#[test]
fn test_verify_model_rejects_satisfiable_mod_query_clause_5803() {
    let body = ChcExpr::and_all(vec![
        ChcExpr::eq(var("A"), ChcExpr::int(6)),
        ChcExpr::eq(var("B"), ChcExpr::int(3)),
        mod_eq("A", 2, 0),
        mod_eq("A", 3, 0),
        ChcExpr::eq(ChcExpr::add(var("A"), var("B")), ChcExpr::int(9)),
    ]);

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![var("A"), var("B")])], Some(body)),
        ClauseHead::False,
    ));

    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(vec![int_var("A"), int_var("B")], ChcExpr::Bool(true)),
    );

    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };

    let mut verifier = PdrSolver::new(problem.clone(), config.clone());
    assert!(
        !verifier.verify_model(&model),
        "verify_model must reject a model whose query clause body is concretely satisfiable"
    );

    let mut fast_verifier = PdrSolver::new(problem, config);
    assert!(
        !fast_verifier.verify_model_fast(&model, Instant::now() + Duration::from_secs(2)),
        "verify_model_fast must reject a model whose query clause body is concretely satisfiable"
    );
}

#[test]
fn test_verify_model_query_clause_concrete_cross_check_rejects_forced_false_unsat_5803() {
    let body = ChcExpr::and_all(vec![
        ChcExpr::eq(var("A"), ChcExpr::int(6)),
        ChcExpr::eq(var("B"), ChcExpr::int(3)),
        mod_eq("A", 2, 0),
        mod_eq("A", 3, 0),
        ChcExpr::eq(ChcExpr::add(var("A"), var("B")), ChcExpr::int(9)),
    ]);

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![var("A"), var("B")])], Some(body)),
        ClauseHead::False,
    ));

    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(vec![int_var("A"), int_var("B")], ChcExpr::Bool(true)),
    );

    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };

    let mut verifier = PdrSolver::new(problem.clone(), config.clone());
    verifier
        .smt
        .push_forced_check_sat_result_for_tests(SmtResult::Unsat);
    assert!(
        !verifier.verify_model(&model),
        "verify_model must reject a forced false-UNSAT once the query-clause concrete cross-check finds the SAT witness"
    );

    let mut fast_verifier = PdrSolver::new(problem, config);
    fast_verifier
        .smt
        .push_forced_check_sat_result_for_tests(SmtResult::Unsat);
    assert!(
        !fast_verifier.verify_model_fast(
            &model,
            Instant::now() + Duration::from_secs(2)
        ),
        "verify_model_fast must reject a forced false-UNSAT once the query-clause concrete cross-check finds the SAT witness"
    );
}

#[test]
fn test_verify_model_applies_interpretation_binder_vars() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);
    let s = ChcVar::new("s", ChcSort::Int);

    // s = 0 => inv(s)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(s.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(s.clone())]),
    ));

    // inv(s) /\ s < 10 => inv(s + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(s.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(s.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(s.clone()), ChcExpr::int(1))],
        ),
    ));

    // inv(s) /\ s > 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(s.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(s), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    // Use a non-canonical binder name (x) to ensure verification substitutes model vars, not
    // solver canonical vars (__p{pred}_a{i}).
    let input = r#"(define-fun inv ((x Int)) Bool (<= x 10))"#;
    let model = InvariantModel::parse_smtlib(input, &problem).expect("valid smtlib model");

    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem, config);
    assert!(verifier.verify_model(&model));
}

/// Regression test for #2188: verify_model must reject invalid invariants.
///
/// This test constructs a simple CHC problem and a deliberately WRONG invariant,
/// then verifies that verify_model correctly rejects it.
#[test]
fn test_verify_model_rejects_wrong_invariant() {
    // Problem:
    //   s = 0 => inv(s)              (init)
    //   inv(s) /\ s < 5 => inv(s+1)  (transition)
    //   inv(s) /\ s > 6 => false     (safety)
    //
    // Correct invariant: s <= 5 (reachable values are 0,1,2,3,4,5)
    // Wrong invariant: s <= 10 (allows unreachable states s=6,7,8,9,10)
    //
    // The wrong invariant is NOT inductive: inv(s=5) /\ s < 5 is unsat (no issue)
    // But verify_model should still accept s <= 10 as it is SOUND (overapproximation).
    //
    // For a truly wrong invariant, use s <= 3 which is NOT inductive:
    // inv(s=3) /\ s < 5 => inv(s+1=4) requires s <= 3 to imply 4 <= 3 which is false.

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);
    let s = ChcVar::new("s", ChcSort::Int);

    // s = 0 => inv(s)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(s.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(s.clone())]),
    ));

    // inv(s) /\ s < 5 => inv(s + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(s.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(s.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(s.clone()), ChcExpr::int(1))],
        ),
    ));

    // inv(s) /\ s > 6 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(s.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(s), ChcExpr::int(6))),
        ),
        ClauseHead::False,
    ));

    // Wrong invariant: s <= 3 (too tight - not preserved by transition)
    // When s = 3 and s < 5, we get s' = 4, but 4 <= 3 is false.
    let wrong_input = r#"(define-fun inv ((x Int)) Bool (<= x 3))"#;
    let wrong_model =
        InvariantModel::parse_smtlib(wrong_input, &problem).expect("valid smtlib model");

    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem.clone(), config.clone());

    // Wrong invariant should be REJECTED (not inductive)
    assert!(
        !verifier.verify_model(&wrong_model),
        "verify_model should reject non-inductive invariant s <= 3"
    );

    // Correct invariant: s <= 5 (precise - exactly the reachable states)
    let correct_input = r#"(define-fun inv ((x Int)) Bool (<= x 5))"#;
    let correct_model =
        InvariantModel::parse_smtlib(correct_input, &problem).expect("valid smtlib model");

    let mut verifier2 = PdrSolver::new(problem, config);
    assert!(
        verifier2.verify_model(&correct_model),
        "verify_model should accept correct invariant s <= 5"
    );
}

use crate::pdr::counterexample::{
    Counterexample, CounterexampleStep, DerivationWitness, DerivationWitnessEntry,
};
use crate::PredicateId;
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Build an UNSAFE problem:
///   clause 0: s = 0 => P(s)              (init/fact)
///   clause 1: P(s) => P(s + 1)           (unconditional transition)
///   clause 2: P(s) /\ s >= 2 => false    (query)
///
/// CEX: P(0) -> P(1) -> P(2), and 2 >= 2 triggers query.
fn unsafe_problem() -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let s = ChcVar::new("s", ChcSort::Int);

    // Clause 0: s = 0 => P(s)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(s.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(s.clone())]),
    ));

    // Clause 1: P(s) => P(s + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(s.clone())])], None),
        ClauseHead::Predicate(
            p,
            vec![ChcExpr::add(ChcExpr::var(s.clone()), ChcExpr::int(1))],
        ),
    ));

    // Clause 2: P(s) /\ s >= 2 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(s.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(s), ChcExpr::int(2))),
        ),
        ClauseHead::False,
    ));

    (problem, p)
}

/// Build a chain where middle clauses use clause-local vars that must be recovered from
/// premise canonical instances.
///
///   clause 0: a = 0 => P(a)
///   clause 1: P(x) => Q(x + 1)
///   clause 2: Q(1) => R(2)
///   clause 3: R(r) /\ r = 2 => false
fn multilevel_mapping_problem() -> (ChcProblem, PredicateId, PredicateId, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let r = problem.declare_predicate("R", vec![ChcSort::Int]);

    let a = ChcVar::new("a", ChcSort::Int);
    let x = ChcVar::new("x", ChcSort::Int);
    let rq = ChcVar::new("rq", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(a)]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1))]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![ChcExpr::int(1)])], None),
        ClauseHead::Predicate(r, vec![ChcExpr::int(2)]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(r, vec![ChcExpr::var(rq.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(rq), ChcExpr::int(2))),
        ),
        ClauseHead::False,
    ));

    (problem, p, q, r)
}

/// Build a hyperedge query where body-argument substitution must use canonical instances.
///
///   clause 0: x = 4 => P(x)
///   clause 1: y = 7 => Q(y)
///   clause 2: P(x) /\ Q(y) /\ x + y <= 5 => false
fn hyperedge_query_problem() -> (ChcProblem, PredicateId, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(4))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(7))),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (p, vec![ChcExpr::var(x.clone())]),
                (q, vec![ChcExpr::var(y.clone())]),
            ],
            Some(ChcExpr::le(
                ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y)),
                ChcExpr::int(5),
            )),
        ),
        ClauseHead::False,
    ));

    (problem, p, q)
}

fn canonical_var(solver: &PdrSolver, pred: PredicateId) -> ChcVar {
    solver
        .canonical_vars(pred)
        .expect("predicate should have canonical vars")[0]
        .clone()
}

fn canonical_instances(
    solver: &PdrSolver,
    pred: PredicateId,
    value: i128,
) -> FxHashMap<String, SmtValue> {
    let mut instances: FxHashMap<String, SmtValue> = FxHashMap::default();
    instances.insert(canonical_var(solver, pred).name, SmtValue::Int(value));
    instances
}

#[test]
fn verify_counterexample_accepts_valid_witness_via_query() {
    // Test the witness-based query clause verification path.
    // Witness has a single root entry with instances that satisfy the query constraint.
    let (problem, pred) = unsafe_problem();
    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    // Root entry: P with __p0_a0 = 3 (satisfies query s >= 2 since 3 >= 2)
    let canon = canonical_var(&solver, pred);
    let instances = canonical_instances(&solver, pred, 3);

    let cex = Counterexample {
        steps: vec![CounterexampleStep::new(
            pred,
            [("s".to_string(), 3)].into_iter().collect(),
        )],
        witness: Some(DerivationWitness {
            query_clause: Some(2), // clause 2: P(s) /\ s >= 2 => false
            root: 0,
            entries: vec![DerivationWitnessEntry {
                predicate: pred,
                level: 0,
                state: ChcExpr::eq(ChcExpr::var(canon), ChcExpr::int(3)),
                incoming_clause: None, // root
                premises: vec![],
                instances,
            }],
        }),
        ground_derivation: None,
    };
    let result = solver.verify_counterexample(&cex);
    assert_eq!(
        result,
        super::CexVerificationResult::Valid,
        "witness with instances satisfying query constraint should be Valid"
    );
}

#[test]
fn verify_counterexample_rejects_empty_trace_when_query_not_init_reachable_6293() {
    let (problem, _pred) = unsafe_problem();
    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);
    let cex = Counterexample {
        steps: Vec::new(),
        witness: None,
        ground_derivation: None,
    };

    let result = solver.verify_counterexample(&cex);
    assert_eq!(
        result,
        super::CexVerificationResult::Spurious,
        "empty witnessless trace must be checked against depth-0 reachability"
    );
}

#[test]
fn verify_counterexample_rejects_spurious_witness() {
    let (problem, pred) = unsafe_problem();
    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    let canon = canonical_var(&solver, pred);

    // Spurious witness: root says s=0, but 0 >= 2 is false (query not satisfied)
    let inst_0 = canonical_instances(&solver, pred, 0);

    let cex = Counterexample {
        steps: vec![CounterexampleStep::new(
            pred,
            [("s".to_string(), 0)].into_iter().collect(),
        )],
        witness: Some(DerivationWitness {
            query_clause: Some(2),
            root: 0,
            entries: vec![DerivationWitnessEntry {
                predicate: pred,
                level: 0,
                state: ChcExpr::eq(ChcExpr::var(canon), ChcExpr::int(0)),
                incoming_clause: None,
                premises: vec![],
                instances: inst_0,
            }],
        }),
        ground_derivation: None,
    };
    let result = solver.verify_counterexample(&cex);
    assert_eq!(
        result,
        super::CexVerificationResult::Spurious,
        "spurious CEX (s=0 does not satisfy s>=2) should be rejected"
    );
}

#[test]
fn verify_counterexample_accepts_multilevel_witness_with_canonical_mapping() {
    let (problem, p, q, r) = multilevel_mapping_problem();
    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    let p_canon = canonical_var(&solver, p);
    let q_canon = canonical_var(&solver, q);
    let r_canon = canonical_var(&solver, r);

    let p_instances = canonical_instances(&solver, p, 0);
    // No need to include clause-local var `x` — the body_subst fix maps
    // clause-local body variables to premise canonical values automatically.

    let q_instances = canonical_instances(&solver, q, 1);
    let r_instances = canonical_instances(&solver, r, 2);

    let cex = Counterexample {
        steps: vec![
            CounterexampleStep::new(p, [("x".to_string(), 0)].into_iter().collect()),
            CounterexampleStep::new(q, [("x".to_string(), 1)].into_iter().collect()),
            CounterexampleStep::new(r, [("x".to_string(), 2)].into_iter().collect()),
        ],
        witness: Some(DerivationWitness {
            query_clause: Some(3),
            root: 0,
            entries: vec![
                DerivationWitnessEntry {
                    predicate: r,
                    level: 2,
                    state: ChcExpr::eq(ChcExpr::var(r_canon), ChcExpr::int(2)),
                    incoming_clause: Some(2),
                    premises: vec![1],
                    instances: r_instances,
                },
                DerivationWitnessEntry {
                    predicate: q,
                    level: 1,
                    state: ChcExpr::eq(ChcExpr::var(q_canon), ChcExpr::int(1)),
                    incoming_clause: Some(1),
                    premises: vec![2],
                    instances: q_instances,
                },
                DerivationWitnessEntry {
                    predicate: p,
                    level: 0,
                    state: ChcExpr::eq(ChcExpr::var(p_canon), ChcExpr::int(0)),
                    incoming_clause: Some(0),
                    premises: vec![],
                    instances: p_instances,
                },
            ],
        }),
        ground_derivation: None,
    };

    let result = solver.verify_counterexample(&cex);
    assert_eq!(
        result,
        super::CexVerificationResult::Valid,
        "multi-level witness with canonical instances should verify"
    );
}

#[test]
fn verify_counterexample_hyperedge_query_uses_body_arg_to_canonical_mapping() {
    let (problem, p, q) = hyperedge_query_problem();
    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    let p_canon = canonical_var(&solver, p);
    let q_canon = canonical_var(&solver, q);

    let cex = Counterexample {
        steps: vec![
            CounterexampleStep::new(p, [("x".to_string(), 4)].into_iter().collect()),
            CounterexampleStep::new(q, [("y".to_string(), 7)].into_iter().collect()),
        ],
        witness: Some(DerivationWitness {
            query_clause: Some(2),
            root: 0,
            entries: vec![
                DerivationWitnessEntry {
                    predicate: p,
                    level: 0,
                    state: ChcExpr::eq(ChcExpr::var(p_canon), ChcExpr::int(4)),
                    incoming_clause: Some(0),
                    premises: vec![1],
                    instances: canonical_instances(&solver, p, 4),
                },
                DerivationWitnessEntry {
                    predicate: q,
                    level: 0,
                    state: ChcExpr::eq(ChcExpr::var(q_canon), ChcExpr::int(7)),
                    incoming_clause: Some(1),
                    premises: vec![],
                    instances: canonical_instances(&solver, q, 7),
                },
            ],
        }),
        ground_derivation: None,
    };

    let result = solver.verify_counterexample(&cex);
    assert_eq!(
        result,
        super::CexVerificationResult::Spurious,
        "query-body variables must be substituted from canonical witness instances"
    );
}

#[test]
fn verify_counterexample_transition_chain_canonical_only() {
    // Regression test: verify a multi-step transition chain using ONLY canonical
    // instances (no clause-local variable workarounds). This tests the body_subst
    // fix that maps clause-local body variables to premise canonical values.
    //
    // Problem: s=0 => P(s), P(s) => P(s+1), P(s) /\ s>=2 => false
    // CEX: P(0) -> P(1) -> P(2), query s>=2 satisfied by P(2)
    let (problem, pred) = unsafe_problem();
    let config = PdrConfig {
        verbose: true,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    let canon = canonical_var(&solver, pred);

    // Only canonical instances — no clause-local "s" in any entry
    let inst_0 = canonical_instances(&solver, pred, 0);
    let inst_1 = canonical_instances(&solver, pred, 1);
    let inst_2 = canonical_instances(&solver, pred, 2);

    let cex = Counterexample {
        steps: vec![
            CounterexampleStep::new(pred, [("s".to_string(), 0)].into_iter().collect()),
            CounterexampleStep::new(pred, [("s".to_string(), 1)].into_iter().collect()),
            CounterexampleStep::new(pred, [("s".to_string(), 2)].into_iter().collect()),
        ],
        witness: Some(DerivationWitness {
            query_clause: Some(2),
            root: 0,
            entries: vec![
                // Entry 0 (root): P(2) at level 2 — the "bad" state
                DerivationWitnessEntry {
                    predicate: pred,
                    level: 2,
                    state: ChcExpr::eq(ChcExpr::var(canon.clone()), ChcExpr::int(2)),
                    incoming_clause: Some(1), // transition clause P(s)=>P(s+1)
                    premises: vec![1],
                    instances: inst_2,
                },
                // Entry 1: P(1) at level 1 — derived via transition (clause 1)
                DerivationWitnessEntry {
                    predicate: pred,
                    level: 1,
                    state: ChcExpr::eq(ChcExpr::var(canon.clone()), ChcExpr::int(1)),
                    incoming_clause: Some(1), // transition clause
                    premises: vec![2],
                    instances: inst_1,
                },
                // Entry 2: P(0) at level 0 — init (clause 0: s=0 => P(s))
                DerivationWitnessEntry {
                    predicate: pred,
                    level: 0,
                    state: ChcExpr::eq(ChcExpr::var(canon), ChcExpr::int(0)),
                    incoming_clause: Some(0), // init clause
                    premises: vec![],
                    instances: inst_0,
                },
            ],
        }),
        ground_derivation: None,
    };
    let result = solver.verify_counterexample(&cex);
    assert_eq!(
        result,
        super::CexVerificationResult::Valid,
        "transition chain with canonical-only instances should verify; \
             body_subst must map clause-local vars to premise canonical values"
    );
}

#[test]
fn verify_counterexample_state_implication_fallback_accepts_when_state_implies_query() {
    // Force fallback by making instance substitution fail (s=0), then accept because
    // the root state implies the query constraint (s=5 => s>=2).
    let (problem, pred) = unsafe_problem();
    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    let canon = canonical_var(&solver, pred);
    let failing_instances = canonical_instances(&solver, pred, 0);
    let cex = Counterexample {
        steps: vec![CounterexampleStep::new(pred, FxHashMap::default())],
        witness: Some(DerivationWitness {
            query_clause: Some(2),
            root: 0,
            entries: vec![DerivationWitnessEntry {
                predicate: pred,
                level: 0,
                // State says __p0_a0 = 5, which substituted into s >= 2 gives 5 >= 2 (true)
                state: ChcExpr::eq(ChcExpr::var(canon), ChcExpr::int(5)),
                incoming_clause: None,
                premises: vec![],
                instances: failing_instances,
            }],
        }),
        ground_derivation: None,
    };
    let result = solver.verify_counterexample(&cex);
    assert_eq!(
        result,
        super::CexVerificationResult::Valid,
        "state-implication fallback should accept when root state implies query constraint"
    );
}

#[test]
fn verify_counterexample_state_implication_fallback_rejects_when_state_does_not_imply_query() {
    let (problem, pred) = unsafe_problem();
    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    let canon = canonical_var(&solver, pred);
    let failing_instances = canonical_instances(&solver, pred, 0);
    let cex = Counterexample {
        steps: vec![CounterexampleStep::new(pred, FxHashMap::default())],
        witness: Some(DerivationWitness {
            query_clause: Some(2),
            root: 0,
            entries: vec![DerivationWitnessEntry {
                predicate: pred,
                level: 0,
                state: ChcExpr::eq(ChcExpr::var(canon), ChcExpr::int(0)),
                incoming_clause: None,
                premises: vec![],
                instances: failing_instances,
            }],
        }),
        ground_derivation: None,
    };
    let result = solver.verify_counterexample(&cex);
    assert_eq!(
        result,
        super::CexVerificationResult::Spurious,
        "fallback must reject when root state does not imply query constraint"
    );
}

#[test]
fn verify_counterexample_rejects_empty_instances_when_state_violates_query() {
    let (problem, pred) = unsafe_problem();
    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    let canon = canonical_var(&solver, pred);
    let cex = Counterexample {
        steps: vec![CounterexampleStep::new(pred, FxHashMap::default())],
        witness: Some(DerivationWitness {
            query_clause: Some(2),
            root: 0,
            entries: vec![DerivationWitnessEntry {
                predicate: pred,
                level: 0,
                state: ChcExpr::eq(ChcExpr::var(canon), ChcExpr::int(0)),
                incoming_clause: None,
                premises: vec![],
                instances: FxHashMap::default(),
            }],
        }),
        ground_derivation: None,
    };

    let result = solver.verify_counterexample(&cex);
    assert_eq!(
        result,
        super::CexVerificationResult::Spurious,
        "empty instances must not make query checks vacuously SAT"
    );
}

#[test]
fn verify_counterexample_accepts_empty_instances_when_state_implies_query() {
    let (problem, pred) = unsafe_problem();
    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    let canon = canonical_var(&solver, pred);
    let cex = Counterexample {
        steps: vec![CounterexampleStep::new(pred, FxHashMap::default())],
        witness: Some(DerivationWitness {
            query_clause: Some(2),
            root: 0,
            entries: vec![DerivationWitnessEntry {
                predicate: pred,
                level: 0,
                state: ChcExpr::eq(ChcExpr::var(canon), ChcExpr::int(3)),
                incoming_clause: None,
                premises: vec![],
                instances: FxHashMap::default(),
            }],
        }),
        ground_derivation: None,
    };

    let result = solver.verify_counterexample(&cex);
    assert_eq!(
        result,
        super::CexVerificationResult::Valid,
        "empty instances are acceptable only when root state still proves query violation"
    );
}

#[test]
fn verify_counterexample_transition_empty_instances_returns_unknown() {
    // Regression test for #3086: transition step with empty instances should
    // NOT vacuously pass verification. When both entry and premise have empty
    // instances, the substitution is empty and the SAT check becomes vacuous.
    let (problem, pred) = unsafe_problem();
    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    let canon = canonical_var(&solver, pred);
    // Entry 0: fact clause (clause 0: s=0 => P(s)), empty instances
    // Entry 1: transition clause (clause 1: P(s) => P(s+1)), empty instances
    // Both empty => vacuous acceptance would be a bug.
    let cex = Counterexample {
        steps: vec![CounterexampleStep::new(pred, FxHashMap::default())],
        witness: Some(DerivationWitness {
            query_clause: Some(2),
            root: 1,
            entries: vec![
                DerivationWitnessEntry {
                    predicate: pred,
                    level: 0,
                    state: ChcExpr::eq(ChcExpr::var(canon.clone()), ChcExpr::int(0)),
                    incoming_clause: Some(0), // fact clause
                    premises: vec![],
                    instances: FxHashMap::default(), // empty!
                },
                DerivationWitnessEntry {
                    predicate: pred,
                    level: 1,
                    state: ChcExpr::eq(ChcExpr::var(canon), ChcExpr::int(1)),
                    incoming_clause: Some(1), // transition clause
                    premises: vec![0],
                    instances: FxHashMap::default(), // empty!
                },
            ],
        }),
        ground_derivation: None,
    };

    let result = solver.verify_counterexample(&cex);
    // Should NOT be Valid — empty instances means verification is inconclusive.
    // The fix in #3086 makes this return Unknown instead of vacuously Valid.
    assert_ne!(
        result,
        super::CexVerificationResult::Valid,
        "transition step with empty instances must not vacuously pass as Valid"
    );
}

// ========================================================================
// BV soft degradation soundness gap test (#5643)
// ========================================================================

/// Construct a BV CHC problem where a non-inductive invariant blocks all errors.
///
/// Problem (with BitVec(8) sorts):
///   clause 0: x = #x00 => Inv(x)                                  (init)
///   clause 1: Inv(x) AND bvult(x, #x05) => Inv(bvadd(x, #x01))   (transition)
///   clause 2: Inv(x) AND bvugt(x, #x09) => false                  (safety)
///
/// Reachable states: {0, 1, 2, 3, 4, 5}
/// Correct invariant: bvule(x, #x05) (x <= 5)
///
/// Non-inductive model: (x = 0 OR x = 2)
///   - Satisfies init: x=0, (0=0 OR 0=2) = true
///   - Blocks errors: (0=0 OR 0=2) AND x>9 is impossible
///   - NOT inductive: x=0 AND x<5 => x'=1, but (1=0 OR 1=2) = false
fn bv_problem_with_non_inductive_model() -> (ChcProblem, PredicateId, InvariantModel) {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::BitVec(8)]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));

    // clause 0: x = #x00 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::Var(x.clone()), ChcExpr::BitVec(0, 8))),
        ClauseHead::Predicate(inv, vec![ChcExpr::Var(x.clone())]),
    ));

    // clause 1: Inv(x) AND bvult(x, #x05) => Inv(bvadd(x, #x01))
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::Var(x.clone())])],
            Some(ChcExpr::Op(
                ChcOp::BvULt,
                vec![
                    Arc::new(ChcExpr::Var(x.clone())),
                    Arc::new(ChcExpr::BitVec(5, 8)),
                ],
            )),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::Op(
                ChcOp::BvAdd,
                vec![
                    Arc::new(ChcExpr::Var(x.clone())),
                    Arc::new(ChcExpr::BitVec(1, 8)),
                ],
            )],
        ),
    ));

    // clause 2: Inv(x) AND bvugt(x, #x09) => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::Var(x.clone())])],
            Some(ChcExpr::Op(
                ChcOp::BvUGt,
                vec![
                    Arc::new(ChcExpr::Var(x.clone())),
                    Arc::new(ChcExpr::BitVec(9, 8)),
                ],
            )),
        ),
        ClauseHead::False,
    ));

    // Non-inductive model: Inv(x) = (x = 0 OR x = 2)
    // Blocks errors (neither 0 nor 2 is > 9) but NOT inductive
    // (x=0 AND x<5 => x'=1, and 1!=0 AND 1!=2)
    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::or(
                ChcExpr::eq(ChcExpr::Var(x.clone()), ChcExpr::BitVec(0, 8)),
                ChcExpr::eq(ChcExpr::Var(x), ChcExpr::BitVec(2, 8)),
            ),
        ),
    );

    (problem, inv, model)
}

/// Construct an Int CHC problem where a non-inductive invariant blocks all
/// error states, but the only transition clause contains mod/div.
///
/// Problem:
///   clause 0: x = 0 => Inv(x)
///   clause 1: Inv(x) AND x mod 2 = 0 => Inv(x + 1)
///   clause 2: Inv(x) AND x > 9 => false
///
/// Non-inductive model: Inv(x) = (x = 0)
///   - Satisfies init
///   - Blocks the error clause
///   - Fails inductiveness: x=0 and 0 mod 2 = 0 implies Inv(1), but Inv(1) is false
fn mod_div_problem_with_non_inductive_model() -> (ChcProblem, PredicateId, InvariantModel) {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::Var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::Var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::Var(x.clone())])],
            Some(mod_eq("x", 2, 0)),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::Var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::Var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::Var(x.clone()), ChcExpr::int(9))),
        ),
        ClauseHead::False,
    ));

    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::eq(ChcExpr::Var(x), ChcExpr::int(0)),
        ),
    );

    (problem, inv, model)
}

/// BV soft degradation soundness gap (#5643): verify_model correctly rejects
/// a non-inductive BV invariant that blocks all error states.
#[test]
fn test_bv_verify_model_rejects_non_inductive_error_blocking_invariant_5643() {
    let (problem, _inv, model) = bv_problem_with_non_inductive_model();

    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem, config);
    assert!(
        !verifier.verify_model(&model),
        "verify_model must reject non-inductive BV invariant (x=0 OR x=2)"
    );
}

/// BV soft degradation code path coverage (#5643): exercise verify_model_with_budget
/// with a near-zero budget on a BV problem to trigger the soft degradation path.
///
/// FIXED (#C1, sound-by-default): when the budget exhausts before transition
/// clause verification, the BV soft-degradation branch now REJECTS the model
/// UNCONDITIONALLY (no longer gated on strict_proofs) — see
/// `model_inductive.rs` and `model_inductive_unknown.rs`. Previously it fell
/// open (skipped the unverified transition clause), which could let a
/// non-inductive invariant pass when it blocks all error states, because the
/// public discharge gate only checks query/safety clauses and skips
/// transitions. This test still exercises the path and the skip counter; the
/// dedicated rejection contract is asserted by
/// `test_non_strict_also_rejects_bv_soft_degradation_8555`.
///
/// The bv_soft_degradation_skips counter tracks how many clauses were rejected.
#[test]
fn test_bv_soft_degradation_budget_path_coverage_5643() {
    let (problem, _inv, model) = bv_problem_with_non_inductive_model();

    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem, config);

    // Near-zero budget forces immediate exhaustion, exercising the BV soft
    // degradation code path. The result is non-deterministic (depends on
    // whether budget expires before or after the transition clause check),
    // so we don't assert a specific outcome — we just ensure no panic.
    let _result = verifier.verify_model_with_budget(&model, Duration::from_nanos(1));

    // The counter tracks skipped transition clauses. With near-zero budget on
    // a BV problem, soft degradation should trigger on the transition clause.
    // Note: counter may be 0 if budget expired during the early check (before
    // reaching the BV soft degradation code path) or if the SMT query completed
    // before the budget expired.
    let skips = verifier.bv_soft_degradation_skips();
    // Not asserting skips > 0 because timing is non-deterministic, but verify
    // the accessor works and the counter is a reasonable value.
    assert!(
        skips <= 1,
        "at most 1 transition clause in test problem, got {skips}"
    );
}

/// BV soft degradation counter is zero when budget is not exhausted (#5643).
#[test]
fn test_bv_soft_degradation_counter_zero_without_budget_pressure() {
    let (problem, _inv, model) = bv_problem_with_non_inductive_model();

    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem, config);

    // Full verify_model (no budget) — should reject on inductiveness failure,
    // not trigger soft degradation.
    let rejected = !verifier.verify_model(&model);
    assert!(
        rejected,
        "non-inductive model must be rejected without budget pressure"
    );
    assert_eq!(
        verifier.bv_soft_degradation_skips(),
        0,
        "no soft degradation should occur without budget pressure"
    );
}

/// #7546: budget exhaustion before SMT on a mod/div transition clause must
/// reject the model instead of silently accepting an unverified clause.
#[test]
fn test_mod_div_budget_exhaustion_before_smt_rejects_clause_7546() {
    let (problem, _inv, model) = mod_div_problem_with_non_inductive_model();

    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem, config);
    let clause_idx = 1;
    let clause = verifier.problem.clauses()[clause_idx].clone();
    let body = verifier
        .clause_body_under_model(&clause.body, &model)
        .expect("body under model");
    let body = verifier.bound_int_vars(body);
    let (head_pred, head_args) = match &clause.head {
        ClauseHead::Predicate(pred, args) => (pred, args.as_slice()),
        ClauseHead::False => panic!("expected transition clause"),
    };

    let mut used_filtered_invariant = false;
    let mut concrete_elapsed = Duration::ZERO;
    let mut concrete_unsat_count = 0;
    let failure = verifier.verify_transition_clause(
        &clause,
        clause_idx,
        &body,
        head_pred,
        head_args,
        &model,
        Duration::from_millis(10),
        Some(
            Instant::now()
                .checked_sub(Duration::from_millis(1))
                .unwrap(),
        ),
        Some(Duration::from_nanos(1)),
        &mut used_filtered_invariant,
        Duration::ZERO,
        &mut concrete_elapsed,
        &mut concrete_unsat_count,
    );

    assert!(
        failure.is_some(),
        "mod/div transition clause whose budget expired before SMT must reject"
    );
}

/// Create a CHC problem with Int+Real predicate args for #5930 guard tests.
/// P(x: Int, r: Real): x=0,r=0 => P; P,x<5 => P(x+1,r+1); P,x>10 => false
fn real_sort_guard_problem() -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Real]);
    let x = ChcVar::new("x", ChcSort::Int);
    let r = ChcVar::new("r", ChcSort::Real);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(r.clone()), ChcExpr::Real(0, 1)),
        )),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(r.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(r.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                ChcExpr::add(ChcExpr::var(r.clone()), ChcExpr::Real(1, 1)),
            ],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(r)])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));
    (problem, inv)
}

/// #5930: verify_model rejects Bool/Int-only invariants for Real-sorted predicates.
#[test]
fn test_verify_model_rejects_bool_only_invariant_for_real_sorted_pred_5930() {
    let (problem, inv) = real_sort_guard_problem();
    let binder_x = ChcVar::new("__p0_a0", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![
                ChcVar::new("__p0_a0", ChcSort::Int),
                ChcVar::new("__p0_a1", ChcSort::Real),
            ],
            ChcExpr::le(ChcExpr::var(binder_x), ChcExpr::int(10)), // Int-only formula
        ),
    );
    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem, config);
    assert!(
        !verifier.verify_model(&model),
        "verify_model must reject Bool/Int-only invariant for Real-sorted predicate (#5930)"
    );
}

/// #5930 control: model mentioning Real vars should pass the guard (may still
/// fail SMT verification for other reasons).
#[test]
fn test_verify_model_accepts_real_including_invariant_5930() {
    let (problem, inv) = real_sort_guard_problem();
    let binder_x = ChcVar::new("__p0_a0", ChcSort::Int);
    let binder_r = ChcVar::new("__p0_a1", ChcSort::Real);
    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![
                ChcVar::new("__p0_a0", ChcSort::Int),
                ChcVar::new("__p0_a1", ChcSort::Real),
            ],
            ChcExpr::and(
                ChcExpr::le(ChcExpr::var(binder_x), ChcExpr::int(10)),
                ChcExpr::ge(ChcExpr::var(binder_r), ChcExpr::Real(0, 1)),
            ),
        ),
    );
    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem, config);
    // Don't assert result — SMT may reject for LRA reasons. Just verify no crash.
    let _ = verifier.verify_model_with_budget(&model, Duration::from_secs(5));
}

// ========================================================================
// BV-to-Int sort mismatch regression tests (#6249)
// ========================================================================

/// Regression test for #6249: instance_subst_var_and_value with declared_sort
/// overrides the sort inferred from SmtValue.
///
/// When BV-to-Int abstraction is active, SmtValue::Int values represent BV-sorted
/// predicate arguments. Without declared_sort, the ChcVar gets sort=Int, which
/// fails to match clause variables with sort=BitVec(w) during substitution.
#[test]
fn test_instance_subst_var_and_value_declared_sort_overrides_inferred_6249() {
    let name = "x";
    let value = SmtValue::Int(42); // Int value from BV-to-Int abstraction
    let mut saw_unknown = false;

    // Without declared sort: infers Int
    let (var_no_decl, _) =
        super::instance_subst_var_and_value(name, &value, None, false, &mut saw_unknown);
    assert_eq!(var_no_decl.sort, ChcSort::Int);

    // With declared sort BitVec(8): uses the declared sort
    let bv8 = ChcSort::BitVec(8);
    let (var_with_decl, expr) =
        super::instance_subst_var_and_value(name, &value, Some(&bv8), false, &mut saw_unknown);
    assert_eq!(var_with_decl.sort, ChcSort::BitVec(8));
    // The expression is coerced to BitVec(42, 8) to match the declared sort
    assert_eq!(expr, ChcExpr::BitVec(42, 8));

    // The declared-sort var should match a BV-sorted clause variable
    let clause_var = ChcVar::new("x", ChcSort::BitVec(8));
    assert_eq!(
        var_with_decl, clause_var,
        "declared sort must match clause variable sort"
    );

    // The no-decl var should NOT match the BV clause variable (the bug)
    assert_ne!(
        var_no_decl, clause_var,
        "inferred Int sort must not match BitVec(8)"
    );
}

/// Regression test for #6249: verify_counterexample with Int-sorted predicates
/// and Int-domain instance values builds correct substitutions when canonical
/// vars provide the declared sort.
///
/// This exercises the sort_map path in verify_counterexample without the
/// complication of BV operators applied to Int values (which would produce
/// SMT Unknown). The key property: canonical vars' declared sorts are used
/// for ChcVar construction in substitution maps.
#[test]
fn test_verify_counterexample_sort_map_from_canonical_vars_6249() {
    // Use the standard Int problem (unsafe_problem) but verify that the
    // sort_map path works correctly — canonical vars have Int sort, instances
    // have Int values, and substitution succeeds.
    let (problem, pred) = unsafe_problem();
    let config = PdrConfig {
        verbose: true,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    let canon = canonical_var(&solver, pred);
    assert_eq!(canon.sort, ChcSort::Int, "canonical var should be Int");

    // Construct a valid witness with canonical instances
    let inst_3 = canonical_instances(&solver, pred, 3);

    let cex = Counterexample {
        steps: vec![CounterexampleStep::new(
            pred,
            [("s".to_string(), 3)].into_iter().collect(),
        )],
        witness: Some(DerivationWitness {
            query_clause: Some(2),
            root: 0,
            entries: vec![DerivationWitnessEntry {
                predicate: pred,
                level: 0,
                state: ChcExpr::eq(ChcExpr::var(canon), ChcExpr::int(3)),
                incoming_clause: None,
                premises: vec![],
                instances: inst_3,
            }],
        }),
        ground_derivation: None,
    };

    // This should be Valid (3 >= 2 satisfies the query constraint)
    let result = solver.verify_counterexample(&cex);
    assert_eq!(
        result,
        super::CexVerificationResult::Valid,
        "sort_map from canonical_vars should produce correct substitution"
    );
}

/// Build a BV-sorted UNSAFE problem (BitVec(8)):
///   clause 0: x = #x00 => P(x)                        (init)
///   clause 1: P(x) AND bvult(x, #x05) => P(bvadd(x, #x01))  (transition)
///   clause 2: P(x) AND bvuge(x, #x03) => false        (safety)
///
/// CEX: P(#x00) -> P(#x01) -> P(#x02) -> P(#x03), and #x03 >= #x03 triggers query.
fn bv_unsafe_problem() -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::BitVec(8)]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));

    // Clause 0: x = #x00 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::Var(x.clone()), ChcExpr::BitVec(0, 8))),
        ClauseHead::Predicate(p, vec![ChcExpr::Var(x.clone())]),
    ));

    // Clause 1: P(x) AND bvult(x, #x05) => P(bvadd(x, #x01))
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::Var(x.clone())])],
            Some(ChcExpr::Op(
                ChcOp::BvULt,
                vec![
                    Arc::new(ChcExpr::Var(x.clone())),
                    Arc::new(ChcExpr::BitVec(5, 8)),
                ],
            )),
        ),
        ClauseHead::Predicate(
            p,
            vec![ChcExpr::Op(
                ChcOp::BvAdd,
                vec![
                    Arc::new(ChcExpr::Var(x.clone())),
                    Arc::new(ChcExpr::BitVec(1, 8)),
                ],
            )],
        ),
    ));

    // Clause 2: P(x) AND bvuge(x, #x03) => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::Var(x.clone())])],
            Some(ChcExpr::Op(
                ChcOp::BvUGe,
                vec![Arc::new(ChcExpr::Var(x)), Arc::new(ChcExpr::BitVec(3, 8))],
            )),
        ),
        ClauseHead::False,
    ));

    (problem, p)
}

/// Regression test for #6249: verify_counterexample with BV-sorted predicates
/// where canonical vars have BitVec(8) sort. Instances use SmtValue::BitVec to
/// exercise the sort_map path that maps canonical var names to their declared
/// BV sorts.
///
/// This is the BV companion to the Int-only test above. Without the #6249 fix,
/// `instance_subst_var_and_value` would create `ChcVar{sort: Int}` from
/// `SmtValue::Int` values, causing substitution to silently fail against clause
/// variables with `ChcSort::BitVec(8)`.
#[test]
fn test_verify_counterexample_sort_map_bv_sorted_problem_6249() {
    let (problem, pred) = bv_unsafe_problem();
    let config = PdrConfig {
        verbose: true,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    let canon = canonical_var(&solver, pred);
    assert_eq!(
        canon.sort,
        ChcSort::BitVec(8),
        "canonical var should be BitVec(8)"
    );

    // Construct instances with SmtValue::BitVec (native BV values)
    let bv_inst = |val: u128| -> FxHashMap<String, SmtValue> {
        let mut m: FxHashMap<String, SmtValue> = FxHashMap::default();
        m.insert(canon.name.clone(), SmtValue::BitVec(val, 8));
        m
    };

    // A COMPLETE forward-reachable derivation over bv_unsafe_problem, so the
    // witness replays as a real refutation rather than asserting P(#x03) as a
    // bare level-0 axiom (the vacuous single-axiom shape that 019c5900 closed:
    // P(#x03) is NOT a fact of this problem — the only fact clause is P(#x00)).
    // Chain: entry3 P(#x00) fact via clause 0 (x=#x00 => P(x)); entry2 P(#x01),
    // entry1 P(#x02), entry0 P(#x03) each via clause 1 (transition); query
    // clause 2 (P(x) /\ bvuge(x,#x03) => false) fires on the root P(#x03).
    // Every entry pins its canonical instance with SmtValue::BitVec, so the
    // #6249 sort_map / instance_subst_var_and_value BV path is exercised at
    // each step.
    let bv_state = |val: u128| ChcExpr::eq(ChcExpr::Var(canon.clone()), ChcExpr::BitVec(val, 8));
    let cex = Counterexample {
        steps: vec![
            CounterexampleStep::new(pred, [("x".to_string(), 0)].into_iter().collect()),
            CounterexampleStep::new(pred, [("x".to_string(), 1)].into_iter().collect()),
            CounterexampleStep::new(pred, [("x".to_string(), 2)].into_iter().collect()),
            CounterexampleStep::new(pred, [("x".to_string(), 3)].into_iter().collect()),
        ],
        witness: Some(DerivationWitness {
            query_clause: Some(2),
            root: 0,
            entries: vec![
                // Entry 0 (root): P(#x03) at level 3 — the "bad" state.
                DerivationWitnessEntry {
                    predicate: pred,
                    level: 3,
                    state: bv_state(3),
                    incoming_clause: Some(1),
                    premises: vec![1],
                    instances: bv_inst(3),
                },
                // Entry 1: P(#x02) at level 2 — transition (clause 1).
                DerivationWitnessEntry {
                    predicate: pred,
                    level: 2,
                    state: bv_state(2),
                    incoming_clause: Some(1),
                    premises: vec![2],
                    instances: bv_inst(2),
                },
                // Entry 2: P(#x01) at level 1 — transition (clause 1).
                DerivationWitnessEntry {
                    predicate: pred,
                    level: 1,
                    state: bv_state(1),
                    incoming_clause: Some(1),
                    premises: vec![3],
                    instances: bv_inst(1),
                },
                // Entry 3: P(#x00) at level 0 — init fact (clause 0).
                DerivationWitnessEntry {
                    predicate: pred,
                    level: 0,
                    state: bv_state(0),
                    incoming_clause: Some(0),
                    premises: vec![],
                    instances: bv_inst(0),
                },
            ],
        }),
        ground_derivation: None,
    };

    let result = solver.verify_counterexample(&cex);
    assert_eq!(
        result,
        super::CexVerificationResult::Valid,
        "BV-sorted sort_map from canonical_vars should produce correct substitution \
         over a complete init->transition* derivation chain"
    );
}

/// Regression test for #6249: verify_counterexample with BV-sorted predicates
/// where instances use SmtValue::Int (as produced by BV-to-Int abstraction).
/// The sort_map from canonical vars must coerce Int values to BitVec via
/// instance_subst_var_and_value's declared_sort parameter.
///
/// This is the critical path that #6249 fixed: BV-to-Int abstraction passes
/// Int values through to verify_counterexample, but the clause variables are
/// BitVec-sorted. Without sort coercion, substitution fails silently.
#[test]
fn test_verify_counterexample_bv_to_int_coercion_6249() {
    let (problem, pred) = bv_unsafe_problem();
    let config = PdrConfig {
        verbose: true,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    let canon = canonical_var(&solver, pred);
    assert_eq!(
        canon.sort,
        ChcSort::BitVec(8),
        "canonical var should be BitVec(8)"
    );

    // Instances use SmtValue::Int (simulating BV-to-Int abstraction output).
    // The sort_map must coerce these to BitVec(8) via declared_sort.
    let int_inst = |val: i128| -> FxHashMap<String, SmtValue> {
        let mut m: FxHashMap<String, SmtValue> = FxHashMap::default();
        m.insert(canon.name.clone(), SmtValue::Int(val));
        m
    };

    // A COMPLETE forward-reachable derivation over bv_unsafe_problem (same
    // sound chain as the BV-sorted companion), but every entry pins its
    // canonical instance with SmtValue::Int — as BV-to-Int abstraction emits —
    // so the sort_map MUST coerce each Int to BitVec(8) via declared_sort at
    // every step (the #6249 path). Chain: entry3 P(#x00) fact via clause 0;
    // entry2/entry1/entry0 P(#x01)/P(#x02)/P(#x03) via clause 1; query clause 2
    // fires on the root. This replays as a real refutation, not the vacuous
    // single-axiom shape 019c5900 closed.
    let bv_state = |val: u128| ChcExpr::eq(ChcExpr::Var(canon.clone()), ChcExpr::BitVec(val, 8));
    let cex = Counterexample {
        steps: vec![
            CounterexampleStep::new(pred, [("x".to_string(), 0)].into_iter().collect()),
            CounterexampleStep::new(pred, [("x".to_string(), 1)].into_iter().collect()),
            CounterexampleStep::new(pred, [("x".to_string(), 2)].into_iter().collect()),
            CounterexampleStep::new(pred, [("x".to_string(), 3)].into_iter().collect()),
        ],
        witness: Some(DerivationWitness {
            query_clause: Some(2),
            root: 0,
            entries: vec![
                // Entry 0 (root): P(#x03) at level 3, Int instance coerced to BV.
                DerivationWitnessEntry {
                    predicate: pred,
                    level: 3,
                    state: bv_state(3),
                    incoming_clause: Some(1),
                    premises: vec![1],
                    instances: int_inst(3),
                },
                // Entry 1: P(#x02) at level 2 — transition (clause 1).
                DerivationWitnessEntry {
                    predicate: pred,
                    level: 2,
                    state: bv_state(2),
                    incoming_clause: Some(1),
                    premises: vec![2],
                    instances: int_inst(2),
                },
                // Entry 2: P(#x01) at level 1 — transition (clause 1).
                DerivationWitnessEntry {
                    predicate: pred,
                    level: 1,
                    state: bv_state(1),
                    incoming_clause: Some(1),
                    premises: vec![3],
                    instances: int_inst(1),
                },
                // Entry 3: P(#x00) at level 0 — init fact (clause 0).
                DerivationWitnessEntry {
                    predicate: pred,
                    level: 0,
                    state: bv_state(0),
                    incoming_clause: Some(0),
                    premises: vec![],
                    instances: int_inst(0),
                },
            ],
        }),
        ground_derivation: None,
    };

    let result = solver.verify_counterexample(&cex);
    assert_eq!(
        result,
        super::CexVerificationResult::Valid,
        "BV-to-Int coercion path: Int instances must be coerced to BitVec(8) via sort_map \
         over a complete init->transition* derivation chain"
    );
}

#[test]
fn test_current_verify_step_timeout_caps_requested_to_remaining_clause_budget() {
    let problem = ChcProblem::new();
    let solver = PdrSolver::new(problem, PdrConfig::default());
    let budget = Duration::from_secs(2);
    let budget_start = Instant::now()
        .checked_sub(Duration::from_millis(1950))
        .unwrap();

    let timeout = solver.current_verify_step_timeout(
        Duration::from_secs(2),
        Some(budget_start),
        Some(budget),
    );

    assert!(
        timeout <= Duration::from_millis(100),
        "timeout should be capped to remaining budget, got {timeout:?}"
    );
}

#[test]
fn test_current_verify_step_timeout_preserves_requested_without_budget() {
    let problem = ChcProblem::new();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    let timeout = solver.current_verify_step_timeout(Duration::from_secs(2), None, None);

    assert_eq!(
        timeout,
        Duration::from_secs(2),
        "without a verification budget, the requested timeout should be preserved"
    );
}

#[test]
fn test_set_validation_deadline_initializes_direct_verification_deadline() {
    let problem = ChcProblem::new();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    solver.set_validation_deadline(Duration::from_secs(5));

    let remaining = solver
        .solve_deadline
        .expect("validation deadline should be initialized")
        .saturating_duration_since(Instant::now());
    assert!(
        remaining <= Duration::from_secs(5),
        "validation deadline should be bounded by requested budget, got {remaining:?}"
    );
    assert!(
        remaining > Duration::ZERO,
        "nonzero validation budget should leave positive remaining time"
    );
}

#[test]
fn test_set_validation_deadline_preserves_shorter_config_timeout() {
    let problem = ChcProblem::new();
    let config = PdrConfig {
        solve_timeout: Some(Duration::from_millis(25)),
        ..Default::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    solver.set_validation_deadline(Duration::from_secs(30));

    assert_eq!(solver.config.solve_timeout, Some(Duration::from_millis(25)));
    let remaining = solver
        .solve_deadline
        .expect("validation deadline should be initialized")
        .saturating_duration_since(Instant::now());
    assert!(
        remaining <= Duration::from_millis(25),
        "configured solve_timeout should cap validation budget, got {remaining:?}"
    );
}

/// #8555: strict_proofs mode rejects BV soft degradation.
///
/// When strict_proofs=true, verify_model_with_budget must reject a model if
/// any transition clause was skipped by BV soft degradation (budget exhaustion).
/// Without strict_proofs, the soft degradation silently accepts the unverified
/// clause (trust-proof fallback). With strict_proofs, this is a soundness error.
#[test]
fn test_strict_proofs_rejects_bv_soft_degradation_8555() {
    let (problem, _inv, model) = bv_problem_with_non_inductive_model();

    let config = PdrConfig {
        verbose: false,
        strict_proofs: true,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem, config);

    // Near-zero budget forces BV soft degradation. With strict_proofs=true,
    // the soft degradation path must reject instead of silently accepting.
    let result = verifier.verify_model_with_budget(&model, Duration::from_nanos(1));
    assert!(
        !result,
        "strict_proofs must reject model when BV soft degradation fires (#8555)"
    );
}

/// #8555 / #C1: BV soft degradation is now sound-by-default.
///
/// Previously, without strict_proofs the soft-degradation path fell open
/// (silently accepted the unverified BV transition clause). That fail-open was
/// a latent false-SAFE the public discharge gate cannot catch (the gate only
/// checks query/safety clauses and skips transitions). Both strict and
/// non-strict now reject an unverified BV transition clause.
#[test]
fn test_non_strict_also_rejects_bv_soft_degradation_8555() {
    let (problem, _inv, model) = bv_problem_with_non_inductive_model();

    let config = PdrConfig {
        verbose: false,
        strict_proofs: false,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem, config);

    // Near-zero budget forces BV soft degradation. Sound-by-default: even
    // without strict_proofs the unverified BV transition clause is rejected,
    // so the (non-inductive) model is not accepted.
    let result = verifier.verify_model_with_budget(&model, Duration::from_nanos(1));
    assert!(
        !result,
        "BV soft degradation must reject the unverified model even without \
         strict_proofs (sound-by-default, #C1)"
    );
}
