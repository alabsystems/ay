use super::*;
use crate::{ChcSort, ClauseBody, PredicateId, PredicateInterpretation};
use std::sync::Arc;

fn variable(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Bool)
}

fn fact(head: &[ChcVar], constraint: ChcExpr) -> HornClause {
    HornClause::new(
        ClauseBody::constraint(constraint),
        ClauseHead::Predicate(
            PredicateId::new(0),
            head.iter().cloned().map(ChcExpr::var).collect(),
        ),
    )
}

#[test]
fn duplicate_formals_reserve_later_source_names_and_suffixes() {
    let head = [variable("x"), variable("x"), variable("__dedup_a1_x")];
    let clause = fact(&head, ChcExpr::var(variable("__dedup_a1_x_")));
    let (formals, equalities) = build(&clause, &head, &ValidityWitness::new());
    assert_eq!(formals[0], head[0]);
    assert_eq!(formals[2], head[2]);
    assert_eq!(formals[1].name, "__dedup_a1_x__");
    assert_eq!(
        equalities,
        vec![ChcExpr::eq(
            ChcExpr::var(formals[1].clone()),
            ChcExpr::var(formals[0].clone()),
        )],
    );
    let retried = build(&clause, &head, &ValidityWitness::new());
    assert_eq!((formals, equalities), retried);
}

#[test]
fn duplicate_formals_keep_existing_names_when_there_is_no_collision() {
    let head = [variable("x"), variable("x"), variable("x")];
    let clause = fact(&head, ChcExpr::Bool(true));
    let (formals, equalities) = build(&clause, &head, &ValidityWitness::new());
    let names: Vec<_> = formals.iter().map(|var| var.name.as_str()).collect();
    assert_eq!(names, ["x", "__dedup_a1_x", "__dedup_a2_x"]);
    assert_eq!(equalities.len(), 2);
}

#[test]
fn distinct_formals_are_unchanged() {
    let head = [variable("x"), variable("__dedup_a0_x")];
    let clause = fact(&head, ChcExpr::Bool(true));
    let (formals, equalities) = build(&clause, &head, &ValidityWitness::new());
    assert_eq!(formals, head);
    assert_eq!(equalities, [] as [ChcExpr; 0]);
}

#[test]
fn duplicate_formals_reserve_body_arguments_and_supplied_formula_names() {
    let head = [variable("x"), variable("x")];
    let predicate = PredicateId::new(1);
    let mut clause = fact(&head, ChcExpr::Bool(true));
    clause
        .body
        .predicates
        .push((predicate, vec![ChcExpr::var(variable("__dedup_a1_x"))]));
    let mut model = ValidityWitness::new();
    // Deliberately incomplete model: the name census must not turn its free
    // local into a kept formal. This does not grant the model proof authority.
    model.set(
        predicate,
        PredicateInterpretation::new(
            vec![variable("formal")],
            ChcExpr::var(variable("__dedup_a1_x_")),
        ),
    );
    let (formals, _) = build(&clause, &head, &model);
    assert_eq!(formals[1].name, "__dedup_a1_x__");
}

#[test]
fn name_census_is_complete_beyond_the_legacy_variable_depth_limit() {
    let head = [variable("x"), variable("x")];
    let mut expression = ChcExpr::var(variable("__dedup_a1_x"));
    for _ in 0..2048 {
        expression = ChcExpr::Op(super::super::ChcOp::Not, vec![Arc::new(expression)]);
    }
    // Raw constructors retain the well-sorted Boolean depth without eager
    // simplification; no synthesis or SMT qualification is claimed here.
    let mut clause = fact(&head, expression);
    let (formals, _) = build(&clause, &head, &ValidityWitness::new());
    assert_eq!(formals[1].name, "__dedup_a1_x_");
    ChcExpr::iterative_drop(clause.body.constraint.take().unwrap());
}

#[test]
fn name_census_visits_shared_dag_nodes_without_tree_expansion() {
    let mut expression = Arc::new(ChcExpr::var(variable("__dedup_a1_x")));
    for _ in 0..48 {
        expression = Arc::new(ChcExpr::Op(
            super::super::ChcOp::And,
            vec![expression.clone(), expression],
        ));
    }
    let mut census = NameCensus::default();
    census.enqueue(&expression);
    census.enqueue(&expression);
    assert_eq!(census.pending.len(), 1);
    assert_eq!(
        census.finish(),
        FxHashSet::from_iter(["__dedup_a1_x".to_owned()])
    );
}

#[test]
fn name_census_reserves_function_and_predicate_symbols() {
    let head = [variable("x"), variable("x")];
    let constraint = ChcExpr::Op(
        super::super::ChcOp::And,
        vec![
            Arc::new(ChcExpr::FuncApp(
                "__dedup_a1_x".into(),
                ChcSort::Bool,
                Vec::new(),
            )),
            Arc::new(ChcExpr::PredicateApp(
                "__dedup_a1_x_".into(),
                PredicateId::new(1),
                Vec::new(),
            )),
        ],
    );
    let clause = fact(&head, constraint);
    let (formals, _) = build(&clause, &head, &ValidityWitness::new());
    assert_eq!(formals[1].name, "__dedup_a1_x__");
}
