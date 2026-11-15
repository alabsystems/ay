// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn reflexive(expr: ChcExpr) -> ChcExpr {
    operation(ChcOp::Eq, vec![expr.clone(), expr])
}

#[test]
fn exact_wide_literals_and_typed_operations_validate_without_128_bit_shifts() {
    let source = wide_source();
    let token = CancellationToken::new();
    let control = control(&token);
    let mut model = wide_model(&source, &control);
    for width in [72, 128, 136, crate::MAX_BITVECTOR_WIDTH] {
        let value = if width < 128 {
            (1_u128 << width) - 1
        } else {
            u128::MAX
        };
        set_formula(&mut model, reflexive(ChcExpr::BitVec(value, width)));
        validate(&source, &model, &control).unwrap();
    }
    let vars = model.layout.canonical(PredicateId::new(0)).unwrap();
    let wide = ChcExpr::var(vars[9].clone());
    let expected = ChcExpr::var(vars[3].clone());
    let choice = operation(
        ChcOp::Ite,
        vec![
            operation(ChcOp::BvULt, vec![wide.clone(), high136()]),
            wide.clone(),
            high136(),
        ],
    );
    set_formula(&mut model, operation(ChcOp::Eq, vec![choice, expected]));
    validate(&source, &model, &control).unwrap();
    set_formula(
        &mut model,
        reflexive(operation(ChcOp::BvExtract(135, 128), vec![wide])),
    );
    validate(&source, &model, &control).unwrap();
}

#[test]
fn malformed_widths_results_and_aggregate_or_function_candidates_still_refuse() {
    let source = wide_source();
    let token = CancellationToken::new();
    let control = control(&token);
    let mut model = wide_model(&source, &control);
    let vars = model
        .layout
        .canonical(PredicateId::new(0))
        .unwrap()
        .to_vec();
    for bad in [
        reflexive(ChcExpr::BitVec(0, 0)),
        reflexive(ChcExpr::BitVec(0, crate::MAX_BITVECTOR_WIDTH + 1)),
        reflexive(ChcExpr::BitVec(256, 8)),
        operation(
            ChcOp::Eq,
            vec![ChcExpr::BitVec(0, 136), ChcExpr::BitVec(0, 128)],
        ),
        reflexive(operation(
            ChcOp::BvExtract(136, 128),
            vec![ChcExpr::var(vars[9].clone())],
        )),
        reflexive(operation(
            ChcOp::BvConcat,
            vec![
                ChcExpr::BitVec(0, crate::MAX_BITVECTOR_WIDTH),
                ChcExpr::BitVec(0, 1),
            ],
        )),
        reflexive(operation(
            ChcOp::BvZeroExtend(u32::MAX),
            vec![ChcExpr::BitVec(0, 136)],
        )),
        reflexive(ChcExpr::var(vars[0].clone())),
        reflexive(ChcExpr::FuncApp("invented".into(), bits(136), vec![])),
        reflexive(variable("outside", bits(136))),
        reflexive(variable(&vars[9].name, bits(128))),
    ] {
        set_formula(&mut model, bad);
        assert!(validate(&source, &model, &control).is_none());
    }
    assert!(
        control.poll().is_some(),
        "shape errors are not resource errors"
    );
    set_formula(&mut model, ChcExpr::Bool(true));
    validate(&source, &model, &control).unwrap();
}

#[test]
fn max_width_layout_copies_refuse_under_shared_budget_and_fresh_attempt_retries() {
    let mut declarations = ChcProblem::new();
    declarations.declare_predicate(
        "Wide",
        vec![array(
            crate::MAX_BITVECTOR_WIDTH,
            crate::MAX_BITVECTOR_WIDTH,
        )],
    );
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![QuantifiedHornClause::new(
            HornClause::query(ClauseBody::empty()),
            vec![],
        )],
    )
    .unwrap();
    let token = CancellationToken::new();
    let limited = control(&token);
    limited.bytes(64 * 1024 * 1024 - 128 * 1024).unwrap();
    assert!(Layout::analyze(&source, &limited).is_none());
    assert!(limited.poll().is_none());
    assert!(Layout::analyze(&wide_source(), &limited).is_none());
    let fresh = control(&token);
    let layout = Layout::analyze(&source, &fresh).unwrap();
    let p = PredicateId::new(0);
    assert_eq!(layout.axes(p).unwrap(), &[bits(crate::MAX_BITVECTOR_WIDTH)]);
    assert_eq!(
        layout.canonical(p).unwrap().last().unwrap().sort,
        bits(crate::MAX_BITVECTOR_WIDTH)
    );
    let stopped = control(&token);
    token.cancel();
    assert!(Layout::analyze(&source, &stopped).is_none());
    token.reset();
    assert!(Layout::analyze(&source, &stopped).is_none());
    assert!(Layout::analyze(&source, &control(&token)).is_some());
}

#[test]
fn wide_literal_validation_uses_the_same_copy_budget_without_a_fresh_allowance() {
    let mut declarations = ChcProblem::new();
    declarations.declare_predicate("P", vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![QuantifiedHornClause::new(
            HornClause::query(ClauseBody::empty()),
            vec![],
        )],
    )
    .unwrap();
    let token = CancellationToken::new();
    let build = control(&token);
    let layout = Layout::analyze(&source, &build).unwrap();
    let mut model = ObservationModel {
        layout,
        model: InvariantModel::new(),
    };
    set_formula(&mut model, reflexive(ChcExpr::BitVec(0, 8)));
    let narrow = control(&token);
    narrow.bytes(64 * 1024 * 1024 - 8 * 1024).unwrap();
    validate(&source, &model, &narrow).unwrap();
    set_formula(
        &mut model,
        reflexive(ChcExpr::BitVec(0, crate::MAX_BITVECTOR_WIDTH)),
    );
    let limited = control(&token);
    limited.bytes(64 * 1024 * 1024 - 8 * 1024).unwrap();
    assert!(validate(&source, &model, &limited).is_none());
    assert!(limited.poll().is_none());
    set_formula(&mut model, ChcExpr::Bool(true));
    assert!(validate(&source, &model, &limited).is_none());
    validate(&source, &model, &control(&token)).unwrap();
}
