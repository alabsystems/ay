// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::super::{candidate, rewrite, Layout};
use super::*;

mod fixtures;
mod validation;
use fixtures::*;

#[test]
fn mixed_width_layout_preserves_independent_axes_and_high_bit_actuals() {
    let source = wide_source();
    let token = CancellationToken::new();
    let control = control(&token);
    let layout = Layout::analyze(&source, &control).unwrap();
    let p = PredicateId::new(0);
    assert_eq!(layout.axes(p).unwrap(), &[bits(64), bits(72), bits(136)]);
    let vars = layout.canonical(p).unwrap();
    assert_eq!(vars.len(), 10);
    assert_eq!(vars[3].sort, bits(136));
    assert_eq!(vars[7].sort, bits(8));
    assert_eq!(vars[8].sort, bits(32));
    assert_eq!(vars[9].sort, bits(136));
    let axes = [
        ChcExpr::BitVec(33, 64),
        ChcExpr::BitVec((1_u128 << 71) + 1, 72),
        high136(),
    ];
    let args = original_args(&source);
    let actuals = layout.actuals(p, args, &axes, &control).unwrap();
    assert_eq!(&actuals[..4], args);
    assert_eq!(&actuals[4..7], &axes);
    for index in 0..3 {
        assert_eq!(
            actuals[7 + index],
            operation(
                ChcOp::Select,
                vec![args[index].clone(), axes[index].clone()]
            )
        );
    }
    assert_ne!(
        actuals[9],
        operation(
            ChcOp::Select,
            vec![args[2].clone(), ChcExpr::BitVec(0, 136)]
        )
    );
    let wrong = [axes[0].clone(), axes[2].clone(), axes[1].clone()];
    assert!(layout.actuals(p, args, &wrong, &control).is_none());
}

#[test]
fn wide_pullback_keeps_exact_original_reads_and_full_generated_binder_sorts() {
    let source = wide_source();
    let token = CancellationToken::new();
    let control = control(&token);
    let model = wide_model(&source, &control);
    validate(&source, &model, &control).unwrap();
    let axes = [ChcExpr::BitVec(0, 64), ChcExpr::BitVec(0, 72), high136()];
    let args = original_args(&source);
    let pulled = pullback::instance(&model, PredicateId::new(0), args, &axes, &control).unwrap();
    assert_eq!(
        pulled,
        operation(
            ChcOp::Eq,
            vec![
                operation(ChcOp::Select, vec![args[2].clone(), high136()]),
                args[3].clone(),
            ]
        )
    );
    let mut fresh = pullback::Fresh::new(source.source_smtlib());
    let (head, head_axes) = pullback::head(
        &model,
        &source.source_problem().clauses()[0],
        &mut fresh,
        &control,
    )
    .unwrap();
    assert!(head.is_some());
    assert_eq!(
        head_axes
            .iter()
            .map(|var| var.sort.clone())
            .collect::<Vec<_>>(),
        [bits(64), bits(72), bits(136)]
    );
    let (bodies, _) = pullback::bodies(
        &model,
        &source.source_problem().clauses()[1],
        &axes,
        &[],
        &mut fresh,
        &control,
    )
    .unwrap();
    assert_eq!(bodies.len(), 1);
    assert_eq!(
        bodies[0]
            .0
            .iter()
            .map(|var| var.sort.clone())
            .collect::<Vec<_>>(),
        [bits(64), bits(72), bits(136)]
    );
    assert!(bodies[0]
        .0
        .iter()
        .all(|var| head_axes.iter().all(|head| head.name != var.name)));
}

#[test]
fn full_original_replay_renders_wide_invariant_axes_without_widening_source_binders() {
    let source = wide_source();
    let token = CancellationToken::new();
    let control = control(&token);
    let model = wide_model(&source, &control);
    validate(&source, &model, &control).unwrap();
    let fact = prepare(&source, &model, 0, &control).unwrap();
    assert!(fact
        .obligation
        .smtlib
        .contains(&InvariantModel::expr_to_smtlib(
            source.premises()[0][0].matrix()
        )));
    assert!(fact
        .obligation
        .smtlib
        .contains("(forall ((i (_ BitVec 64)))"));
    assert!(fact
        .obligation
        .smtlib
        .contains("(as const (Array (_ BitVec 136) (_ BitVec 136)))"));
    let query = prepare(&source, &model, 1, &control).unwrap();
    assert!(query
        .obligation
        .smtlib
        .contains("(ay!observation!replay!0 (_ BitVec 64))"));
    assert!(query
        .obligation
        .smtlib
        .contains("(ay!observation!replay!1 (_ BitVec 72))"));
    assert!(query
        .obligation
        .smtlib
        .contains("(ay!observation!replay!2 (_ BitVec 136))"));
    elaborate_replay_without_solving(&fact.obligation.smtlib);
    elaborate_replay_without_solving(&query.obligation.smtlib);
    for width in [65, 72, 136] {
        let premise = UniversalPremise::new(ChcVar::new("i", bits(width)), ChcExpr::Bool(true));
        assert!(QuantifiedChcProblem::new(
            ChcProblem::new(),
            vec![QuantifiedHornClause::new(
                HornClause::query(ClauseBody::empty()),
                vec![premise],
            )]
        )
        .is_err());
    }
}

#[test]
fn actual_candidate_pipeline_keeps_wide_local_keys_and_scalar_observations() {
    let source = wide_source();
    let token = CancellationToken::new();
    let control = control(&token);
    let layout = Layout::analyze(&source, &control).unwrap();
    let raw = rewrite::problem(&source, &layout, &control).unwrap();
    let query = &raw.clauses()[1];
    let actuals = &query.body.predicates[0].1;
    assert_eq!(
        &actuals[4..7],
        &[
            variable("j", bits(64)),
            variable("key72", bits(72)),
            variable("key136", bits(136))
        ]
    );
    let pools = candidate::pools(&source, &raw, &layout, &control).unwrap();
    let pool = pools.get(&PredicateId::new(0)).unwrap();
    assert!(!pool.is_empty());
    for atom in pool {
        let vars =
            super::super::super::super::certify::certificate_formula_vars(&atom.formula).unwrap();
        assert!(vars
            .iter()
            .all(|var| layout.canonical(PredicateId::new(0)).unwrap().contains(var)));
        assert!(vars.iter().any(|var| var.sort == bits(72)));
        assert!(vars.iter().any(|var| var.sort == bits(136)));
    }
}
