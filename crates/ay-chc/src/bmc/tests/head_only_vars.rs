// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Flat-rule binders must include variables occurring only inside head terms.
//! Synthetic models below test reconstruction, not SAT search. The last test
//! separately requires a real flat SMT solve and strict original-source replay.

use super::*;

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}

fn name(expr: &ChcExpr) -> &str {
    let ChcExpr::Var(variable) = expr else {
        panic!("expected a fresh variable, got {expr:?}");
    };
    &variable.name
}

fn array_fact() -> (BmcSolver, PredicateId) {
    let mut problem = ChcProblem::new();
    let array = ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(32)));
    let pred = problem.declare_predicate("Head", vec![array.clone()]);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(
            pred,
            vec![ChcExpr::ConstArray(
                ChcSort::BitVec(64),
                Arc::new(var("x", ChcSort::BitVec(32))),
            )],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(pred, vec![var("a", array)])]),
        ClauseHead::False,
    ));
    (BmcSolver::new(problem, BmcConfig::default()), pred)
}

fn array_model(solver: &BmcSolver, pred: PredicateId) -> FxHashMap<String, SmtValue> {
    let fact = &solver.problem.clauses()[0];
    let subst = solver.mk_rule_vars(fact, pred, 0, 0);
    FxHashMap::from_iter([
        (name(&subst["x"]).to_owned(), SmtValue::BitVec(7, 32)),
        (
            name(&solver.level_arg(pred, 0, 0)).to_owned(),
            SmtValue::ConstArray(Box::new(SmtValue::BitVec(7, 32))),
        ),
        (
            name(&solver.level_predicate(pred, 0)).to_owned(),
            SmtValue::Bool(true),
        ),
    ])
}

#[test]
fn nested_const_array_head_variable_is_freshened_at_level_zero() {
    let (solver, pred) = array_fact();
    let fact = &solver.problem.clauses()[0];
    assert!(fact.body.vars().is_empty());
    let subst = solver.mk_rule_vars(fact, pred, 0, 0);
    assert_eq!(subst.len(), 1);
    assert_eq!(name(&subst["x"]), "Head#0_0_0");
    assert_eq!(subst["x"].sort(), ChcSort::BitVec(32));
    let ClauseHead::Predicate(_, args) = &fact.head else {
        panic!("fact head");
    };
    let rewritten = args[0].substitute_name_map(&subst);
    assert_eq!(
        rewritten.vars(),
        vec![ChcVar::new("Head#0_0_0", ChcSort::BitVec(32))]
    );
}

#[test]
fn nested_arithmetic_head_variables_are_complete_and_shared_occurrences_stay_shared() {
    for sort in [ChcSort::Int, ChcSort::BitVec(8)] {
        let mut problem = ChcProblem::new();
        let pred = problem.declare_predicate("Arith", vec![sort.clone()]);
        let x = var("x", sort.clone());
        let y = var("y", sort.clone());
        let op = if sort == ChcSort::Int {
            ChcOp::Add
        } else {
            ChcOp::BvAdd
        };
        let inner = ChcExpr::Op(op.clone(), vec![Arc::new(x.clone()), Arc::new(y)]);
        let head = ChcExpr::Op(op, vec![Arc::new(inner), Arc::new(x)]);
        let fact = HornClause::new(
            ClauseBody::constraint(ChcExpr::Bool(true)),
            ClauseHead::Predicate(pred, vec![head.clone()]),
        );
        let solver = BmcSolver::new(problem, BmcConfig::default());
        let subst = solver.mk_rule_vars(&fact, pred, 4, 2);
        assert_eq!(subst.len(), 2);
        assert_ne!(subst["x"], subst["y"]);
        assert!(subst.values().all(|value| value.sort() == sort));
        let rewritten = head.substitute_name_map(&subst);
        assert_eq!(rewritten.vars().len(), 2);
        assert!(rewritten
            .vars()
            .iter()
            .all(|v| v.name.starts_with("Arith#2_4_")));
        let ChcExpr::Op(_, args) = &rewritten else {
            panic!("arithmetic head")
        };
        let ChcExpr::Op(_, inner) = args[0].as_ref() else {
            panic!("nested arithmetic")
        };
        assert_eq!(inner[0], args[1]);
    }
}

#[test]
fn head_only_binders_are_fresh_across_rules_and_levels() {
    let (solver, pred) = array_fact();
    let fact = &solver.problem.clauses()[0];
    let mut names = FxHashSet::default();
    for rule in [0, 1] {
        for level in [0, 1, 3] {
            let subst = solver.mk_rule_vars(fact, pred, rule, level);
            assert!(names.insert(name(&subst["x"]).to_owned()));
        }
    }
    assert_eq!(names.len(), 6);
}

#[test]
fn existing_head_body_and_local_mappings_keep_their_old_order() {
    let mut problem = ChcProblem::new();
    let head = problem.declare_predicate("Head", vec![ChcSort::Int, ChcSort::Int]);
    let body = problem.declare_predicate("Body", vec![ChcSort::Int, ChcSort::Int]);
    let clause = HornClause::new(
        ClauseBody::new(
            vec![(body, vec![var("h", ChcSort::Int), var("b", ChcSort::Int)])],
            Some(ChcExpr::eq(var("z", ChcSort::Int), var("a", ChcSort::Int))),
        ),
        ClauseHead::Predicate(
            head,
            vec![
                var("h", ChcSort::Int),
                ChcExpr::add(var("new", ChcSort::Int), ChcExpr::int(1)),
            ],
        ),
    );
    let solver = BmcSolver::new(problem, BmcConfig::default());
    let subst = solver.mk_rule_vars(&clause, head, 7, 3);
    assert_eq!(subst["h"], solver.level_arg(head, 0, 3));
    assert_eq!(subst["b"], solver.level_arg(body, 1, 2));
    let old_locals: Vec<_> = clause
        .body
        .vars()
        .into_iter()
        .filter(|variable| variable.name != "h" && variable.name != "b")
        .collect();
    assert_eq!(old_locals.len(), 2);
    for (index, variable) in old_locals.iter().enumerate() {
        assert_eq!(
            subst[&variable.name],
            solver.level_var(head, 7, index, 3, variable.sort.clone())
        );
    }
    assert_eq!(subst["new"], solver.level_var(head, 7, 2, 3, ChcSort::Int));
    assert_eq!(subst.len(), 5);
}

#[test]
fn complete_synthetic_model_retains_head_only_clause_instances() {
    let (solver, pred) = array_fact();
    let model = array_model(&solver, pred);
    let env = BmcSolver::model_i128_env(&model);
    let instances =
        solver.model_clause_instances(pred, 0, &solver.problem.clauses()[0], 0, &model, &env);
    assert_eq!(instances.len(), 1);
    assert_eq!(instances["x"], SmtValue::BitVec(7, 32));
}

#[test]
fn head_only_instances_make_a_complete_source_checked_ground_witness() {
    let (solver, pred) = array_fact();
    let model = array_model(&solver, pred);
    let queries: Vec<_> = solver.problem.queries().collect();
    let candidates = solver.model_derivation_witnesses(&model, 0, &queries);
    assert_eq!(candidates.len(), 1);
    let derivation = solver
        .ground_derivation_from_witness(&candidates[0], &model, 0)
        .unwrap();
    assert_eq!(derivation.steps.len(), 2);
    assert_eq!(derivation.steps[0].env["x"], SmtValue::BitVec(7, 32));
    assert!(
        crate::ground_derivation::validate_ground_derivation(&solver.problem, &derivation).is_ok()
    );
    let mut missing = derivation.clone();
    missing.steps[0].env.remove("x");
    assert!(
        crate::ground_derivation::validate_ground_derivation(&solver.problem, &missing).is_err()
    );
    let mut wrong = derivation;
    wrong.steps[0]
        .env
        .insert("x".to_owned(), SmtValue::BitVec(8, 32));
    assert!(crate::ground_derivation::validate_ground_derivation(&solver.problem, &wrong).is_err());
}

#[test]
fn flat_head_only_arithmetic_fact_requires_real_sat_and_strict_source_replay() {
    let problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (P (+ x 1))))
(assert (forall ((y Int)) (=> (and (P y) (= y 7)) false)))
(check-sat)
"#,
    )
    .unwrap();
    let until = ay_core::time::Instant::now() + std::time::Duration::from_secs(10);
    let _solve = crate::smt::ScopedSolveDeadline::new(Some(until));
    let _smt = crate::smt::ScopedSmtDeadline::install_until(until);
    let solver = BmcSolver::new(
        problem.clone(),
        BmcConfig {
            max_depth: 0,
            per_depth_timeout: Some(std::time::Duration::from_secs(5)),
            time_budget: Some(std::time::Duration::from_secs(10)),
            ..BmcConfig::default()
        },
    );
    let queries: Vec<_> = solver.problem.queries().collect();
    let result = solver
        .solve_per_depth_fresh(&queries, 0, 0, 0, false)
        .unwrap();
    let ChcEngineResult::Unsafe(cex) = result else {
        panic!("expected checked Unsafe, got {result:?}")
    };
    assert!(cex
        .witness
        .as_ref()
        .is_some_and(|witness| !witness.entries.is_empty()));
    let mut verifier = PdrSolver::new(
        problem,
        PdrConfig {
            strict_proofs: true,
            preserve_original_clauses: true,
            disable_array_scalarization: true,
            disable_cex_replay: true,
            ..PdrConfig::default()
        },
    );
    assert!(verifier.confirm_counterexample(cex).is_ok());
}
