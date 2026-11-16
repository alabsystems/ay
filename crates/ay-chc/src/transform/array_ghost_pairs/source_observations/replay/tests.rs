// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]
#![allow(clippy::unwrap_used)]

use super::*;
use crate::quantified::{QuantifiedHornClause, UniversalPremise};
use crate::smt::SmtValue;
use crate::{CancellationToken, ChcProblem, ClauseBody, PredicateInterpretation};
use ay_core::kani_compat::DetHashMap;

mod functions;
mod identity;
mod progress;
mod wide;
mod wide_dispatch;

fn bv() -> ChcSort {
    ChcSort::BitVec(1)
}
fn variable(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}
fn operation(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}
fn read(array: ChcExpr, row: ChcExpr, column: ChcExpr) -> ChcExpr {
    operation(
        ChcOp::Select,
        vec![operation(ChcOp::Select, vec![array, row]), column],
    )
}

fn source(fill_name: &str) -> QuantifiedChcProblem {
    let inner = ChcSort::Array(Box::new(bv()), Box::new(ChcSort::Bool));
    let array = ChcSort::Array(Box::new(bv()), Box::new(inner));
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![array.clone(), ChcSort::Bool]);
    let a = variable("a", array);
    let fill = variable(fill_name, ChcSort::Bool);
    let args = vec![a.clone(), fill.clone()];
    let matrix = operation(
        ChcOp::Eq,
        vec![
            read(a.clone(), variable("i", bv()), variable("j", bv())),
            fill.clone(),
        ],
    );
    let premise = UniversalPremise::with_binders(
        vec![ChcVar::new("i", bv()), ChcVar::new("j", bv())],
        matrix,
    )
    .unwrap();
    let fact = HornClause::new(ClauseBody::empty(), ClauseHead::Predicate(p, args.clone()));
    let bad = operation(
        ChcOp::Ne,
        vec![read(a, variable("r", bv()), variable("c", bv())), fill],
    );
    let query = HornClause::query(ClauseBody::new(vec![(p, args)], Some(bad)));
    QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(fact, vec![premise]),
            QuantifiedHornClause::new(query, vec![]),
        ],
    )
    .unwrap()
}

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(60), token)
}

fn model(source: &QuantifiedChcProblem, control: &SourceControl<'_>) -> ObservationModel {
    let layout = super::super::Layout::analyze(source, control).unwrap();
    let mut model = InvariantModel::new();
    for predicate in source.source_problem().predicates() {
        let vars = layout.canonical(predicate.id).unwrap().to_vec();
        assert_eq!(layout.axes(predicate.id).unwrap().len(), 2);
        assert_eq!(vars.len(), 5); // original array/fill, two axes, one Bool cell.
        let formula = operation(
            ChcOp::Eq,
            vec![ChcExpr::var(vars[4].clone()), ChcExpr::var(vars[1].clone())],
        );
        model.set(predicate.id, PredicateInterpretation::new(vars, formula));
    }
    ObservationModel { layout, model }
}

fn original_args(source: &QuantifiedChcProblem) -> &[ChcExpr] {
    let ClauseHead::Predicate(_, args) = &source.source_problem().clauses()[0].head else {
        panic!("P fact")
    };
    args
}

fn elaborate_replay_without_solving(text: &str) {
    let mut commands = ay_frontend::parse(text).unwrap();
    assert!(matches!(
        commands.pop(),
        Some(ay_frontend::Command::CheckSat)
    ));
    let mut context = ay_frontend::Context::new();
    for command in &commands {
        context.process_command(command).unwrap();
    }
    assert_ne!(context.assertions, [] as [ay_core::TermId; 0]);
}

#[test]
fn scalar_pullback_preserves_the_complete_ordered_index_tuple() {
    let source = source("fill");
    let token = CancellationToken::new();
    let control = control(&token);
    let model = model(&source, &control);
    validate(&source, &model, &control).unwrap();
    let args = original_args(&source);
    let axes = [variable("row", bv()), variable("column", bv())];
    let pulled = pullback::instance(&model, PredicateId::new(0), args, &axes, &control).unwrap();
    assert_eq!(
        pulled,
        operation(
            ChcOp::Eq,
            vec![
                read(args[0].clone(), axes[0].clone(), axes[1].clone()),
                args[1].clone()
            ]
        )
    );
    assert_ne!(
        pulled,
        operation(
            ChcOp::Eq,
            vec![
                read(args[0].clone(), axes[1].clone(), axes[0].clone()),
                args[1].clone()
            ]
        )
    );
    let swapped = pullback::instance(
        &model,
        PredicateId::new(0),
        args,
        &[axes[1].clone(), axes[0].clone()],
        &control,
    )
    .unwrap();
    assert_ne!(pulled, swapped);
}

#[test]
fn independent_axis_pullback_rejects_the_diagonal_only_countermodel() {
    let source = source("fill");
    let token = CancellationToken::new();
    let control = control(&token);
    let model = model(&source, &control);
    let bit = |n| SmtValue::BitVec(n, 1);
    let row0 = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Bool(false)),
        entries: vec![(bit(1), SmtValue::Bool(true))],
    };
    let row1 = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Bool(false)),
        entries: vec![(bit(0), SmtValue::Bool(true))],
    };
    let array = SmtValue::ArrayMap {
        default: Box::new(row0),
        entries: vec![(bit(1), row1)],
    };
    let env: DetHashMap<_, _> = [
        ("a".to_owned(), array),
        ("fill".to_owned(), SmtValue::Bool(false)),
    ]
    .into_iter()
    .collect();
    for row in 0..2 {
        for column in 0..2 {
            let axes = [ChcExpr::BitVec(row, 1), ChcExpr::BitVec(column, 1)];
            let pulled = pullback::instance(
                &model,
                PredicateId::new(0),
                original_args(&source),
                &axes,
                &control,
            )
            .unwrap();
            assert_eq!(
                crate::expr::evaluate_expr(&pulled, &env),
                Some(SmtValue::Bool(row == column))
            );
        }
    }
}

#[test]
fn replay_declares_all_head_axes_and_retains_original_grouped_premises() {
    let source = source("fill");
    let token = CancellationToken::new();
    let control = control(&token);
    let model = model(&source, &control);
    validate(&source, &model, &control).unwrap();
    let prepared = prepare(&source, &model, 0, &control).unwrap();
    let text = &prepared.obligation.smtlib;
    assert_eq!(
        prepared.obligation.kind,
        ChcReplayObligationKind::Initiation
    );
    assert_eq!(prepared.obligation.clause_index, 0);
    for axis in 0..2 {
        assert!(text.contains(&format!(
            "(declare-const ay!observation!replay!{axis} (_ BitVec 1))"
        )));
    }
    assert!(text.contains(
        "(assert (forall ((i (_ BitVec 1)) (j (_ BitVec 1))) (= (select (select a i) j) fill)))"
    ));
    assert!(text.contains("(assert (not (= (select (select a ay!observation!replay!0) ay!observation!replay!1) fill)))"));
    assert!(!text.contains("(declare-const i "));
    assert!(!text.contains("(declare-const j "));
    assert!(text.ends_with("(check-sat)\n"));
    elaborate_replay_without_solving(text);
}

#[test]
fn body_interpretation_quantifies_both_axes_without_capturing_source_names() {
    let source = source("ay!observation!replay!0");
    let token = CancellationToken::new();
    let control = control(&token);
    let model = model(&source, &control);
    let prepared = prepare(&source, &model, 1, &control).unwrap();
    let text = &prepared.obligation.smtlib;
    assert!(text.contains("(declare-const ay!observation!replay!0 Bool)"));
    assert!(text.contains("(assert (forall ((ay!observation!replay!1 (_ BitVec 1)) (ay!observation!replay!2 (_ BitVec 1))) (= (select (select a ay!observation!replay!1) ay!observation!replay!2) ay!observation!replay!0)))"));
    assert!(!text.contains("(declare-const ay!observation!replay!1 "));
    assert!(!text.contains("(declare-const ay!observation!replay!2 "));
    assert!(text.contains("(assert (distinct (select (select a r) c) ay!observation!replay!0))"));
    // Finite instances include the actual off-diagonal tuple, not just r=r/c=c.
    assert!(text.contains("(assert (= (select (select a r) c) ay!observation!replay!0))"));
    elaborate_replay_without_solving(text);
}

#[test]
fn generated_replay_free_axes_avoid_source_name_capture() {
    let source = source("ay!observation!replay!0");
    let token = CancellationToken::new();
    let control = control(&token);
    let model = model(&source, &control);
    let prepared = prepare(&source, &model, 0, &control).unwrap();
    let text = &prepared.obligation.smtlib;
    assert!(text.contains("(declare-const ay!observation!replay!0 Bool)"));
    for axis in 1..=2 {
        assert!(text.contains(&format!(
            "(declare-const ay!observation!replay!{axis} (_ BitVec 1))"
        )));
    }
    assert!(!text.contains("(declare-const ay!observation!replay!0 (_ BitVec"));
    elaborate_replay_without_solving(text);
}

#[test]
fn replay_internal_namespace_remains_reserved_by_frontend() {
    let commands =
        ay_frontend::parse("(declare-const __ay_observation_replay_0 (_ BitVec 72))").unwrap();
    assert_eq!(commands.len(), 1);
    let mut context = ay_frontend::Context::new();
    assert!(matches!(
        context.process_command(&commands[0]),
        Err(ay_frontend::ElaborateError::ReservedSymbol(name))
            if name == "__ay_observation_replay_0"
    ));
    assert!(context.symbol_info("__ay_observation_replay_0").is_none());
}

#[test]
fn model_validation_rejects_source_scope_signature_and_theory_mutations() {
    let source = source("fill");
    let token = CancellationToken::new();
    let live = control(&token);
    let mut model = model(&source, &live);
    let id = PredicateId::new(0);
    let original = model.model.get(&id).unwrap().clone();
    for bad in [
        variable("outside", ChcSort::Bool),
        operation(
            ChcOp::Eq,
            vec![
                ChcExpr::var(original.vars[0].clone()),
                ChcExpr::var(original.vars[0].clone()),
            ],
        ),
        ChcExpr::FuncApp("unknown".into(), ChcSort::Bool, vec![]),
        operation(
            ChcOp::Eq,
            vec![ChcExpr::BitVec(2, 1), ChcExpr::BitVec(0, 1)],
        ),
    ] {
        model
            .model
            .set(id, PredicateInterpretation::new(original.vars.clone(), bad));
        assert!(validate(&source, &model, &live).is_none());
    }
    let mut swapped = original.clone();
    swapped.vars.swap(2, 3);
    model.model.set(id, swapped);
    assert!(validate(&source, &model, &live).is_none());
    let mut wrong_sort = original.clone();
    wrong_sort.vars[2].sort = ChcSort::Bool;
    model.model.set(id, wrong_sort);
    assert!(validate(&source, &model, &live).is_none());
    model.model.set(id, original.clone());
    let changed_source = super::tests::source("different_fill");
    assert!(validate(&changed_source, &model, &live).is_none());
    assert!(prepare(&changed_source, &model, 0, &live).is_none());
    assert!(prepare(&source, &model, 2, &live).is_none());
    model.model.set(PredicateId::new(9), original);
    assert!(validate(&source, &model, &live).is_none());
    model.model = InvariantModel::new();
    assert!(validate(&source, &model, &live).is_none());
}
