// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::clause::{ClauseBody, ClauseHead, HornClause};
use crate::engines::{validate_external_invariant_model_typed, ExternalInvariantValidation};
use crate::{
    ChcError, ChcExpr, ChcOp, ChcProblem, ChcResult, ChcSort, ChcVar, InvariantModel, PdrConfig,
};
use std::sync::Arc;
use std::time::Duration;

fn parsed(literal: &str, width: u32) -> ChcResult<ChcExpr> {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("wide", vec![ChcSort::BitVec(width)]);
    let text = format!("(define-fun wide ((value (_ BitVec {width}))) Bool (= value {literal}))");
    let model = InvariantModel::parse_smtlib(&text, &problem)?;
    model
        .get(&pred)
        .map(|interpretation| interpretation.formula.clone())
        .ok_or_else(|| ChcError::Parse("Missing test interpretation".into()))
}

fn equals(value: ChcExpr, width: u32) -> ChcExpr {
    ChcExpr::eq(
        ChcExpr::var(ChcVar::new("value", ChcSort::BitVec(width))),
        value,
    )
}

fn identity_problem(width: u32, bad: impl FnOnce(ChcExpr) -> ChcExpr) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("wide", vec![ChcSort::BitVec(width)]);
    let value = ChcExpr::var(ChcVar::new("value", ChcSort::BitVec(width)));
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pred, vec![ChcExpr::BitVec(0, width)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(pred, vec![value.clone()])]),
        ClauseHead::Predicate(pred, vec![value.clone()]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(pred, vec![value.clone()])], Some(bad(value))),
        ClauseHead::False,
    ));
    problem
}

fn config() -> PdrConfig {
    PdrConfig {
        solve_timeout: Some(Duration::from_secs(20)),
        ..PdrConfig::production(false)
    }
    .with_memory_budget(Some(64 * 1024 * 1024))
}

#[test]
fn binary_literal_ast_preserves_value_width_and_leading_zeroes() {
    for (text, value, width) in [("#b0", 0, 1), ("#b1", 1, 1), ("#b000101", 5, 6)] {
        let formula = parsed(text, width).unwrap();
        assert_eq!(formula, equals(ChcExpr::BitVec(value, width), width));
        assert_eq!(
            formula.vars(),
            vec![ChcVar::new("value", ChcSort::BitVec(width))]
        );
    }
}

#[test]
fn hexadecimal_literal_ast_preserves_case_value_and_width() {
    for (text, value, width) in [("#x0", 0, 4), ("#xaF", 175, 8), ("#x00AF", 175, 16)] {
        assert_eq!(
            parsed(text, width).unwrap(),
            equals(ChcExpr::BitVec(value, width), width)
        );
    }
}

#[test]
fn hexadecimal_comparator_keeps_native_bv_operator_and_literal() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("wide", vec![ChcSort::BitVec(8)]);
    let model = InvariantModel::parse_smtlib(
        "(define-fun wide ((value (_ BitVec 8))) Bool (bvult value #x0A))",
        &problem,
    )
    .unwrap();
    assert_eq!(
        model.get(&pred).unwrap().formula,
        ChcExpr::Op(
            ChcOp::BvULt,
            vec![
                Arc::new(ChcExpr::var(ChcVar::new("value", ChcSort::BitVec(8)))),
                Arc::new(ChcExpr::BitVec(10, 8)),
            ],
        )
    );
}

#[test]
fn radix_literals_at_128_bits_have_exact_compact_u128_carrier() {
    for text in [
        format!("#b{}", "1".repeat(128)),
        format!("#x{}", "F".repeat(32)),
    ] {
        assert_eq!(
            parsed(&text, 128).unwrap(),
            equals(ChcExpr::BitVec(u128::MAX, 128), 128)
        );
    }
}

#[test]
fn wider_radix_literals_keep_the_existing_exact_concat_carrier() {
    for (text, high_width, width) in [
        (format!("#b1{}", "0".repeat(128)), 1, 129),
        (format!("#x1{}", "0".repeat(32)), 4, 132),
    ] {
        let literal = ChcExpr::Op(
            ChcOp::BvConcat,
            vec![
                Arc::new(ChcExpr::BitVec(1, high_width)),
                Arc::new(ChcExpr::BitVec(0, 128)),
            ],
        );
        assert_eq!(parsed(&text, width).unwrap(), equals(literal, width));
    }
}

#[test]
fn empty_invalid_signed_and_trailing_radix_tokens_are_parse_errors() {
    for text in [
        "#", "#b", "#x", "#B0", "#X0", "#q0", "#b2", "#b01bad", "#b+1", "#b-1", "#xg", "#x0g",
        "#x-1", "#x+1", "#b0#b1", "#b0_", "#x0z", "#b0é",
    ] {
        assert!(matches!(parsed(text, 8), Err(ChcError::Parse(_))), "{text}");
    }
}

#[test]
fn derived_width_overflow_is_refused_even_when_every_digit_is_zero() {
    for text in [
        format!("#b{}", "0".repeat(crate::MAX_BITVECTOR_WIDTH as usize + 1)),
        format!(
            "#x{}",
            "0".repeat(crate::MAX_BITVECTOR_WIDTH as usize / 4 + 1)
        ),
    ] {
        assert!(matches!(parsed(&text, 8), Err(ChcError::Parse(_))));
    }
}

#[test]
fn indexed_decimal_value_overflow_remains_rejected() {
    for text in [
        "(_ bv256 8)",
        "(_ bv340282366920938463463374607431768211456 128)",
        "(_ bv+1 8)",
    ] {
        assert!(matches!(parsed(text, 8), Err(ChcError::Parse(_))), "{text}");
    }
}

#[test]
fn malformed_unused_or_unchosen_literal_is_not_ignored() {
    for text in [
        "(let ((unused #b2)) (= value (_ bv0 1)))",
        "(ite true (= value (_ bv0 1)) (= value #x0g))",
    ] {
        let mut problem = ChcProblem::new();
        problem.declare_predicate("wide", vec![ChcSort::BitVec(1)]);
        let input = format!("(define-fun wide ((value (_ BitVec 1))) Bool {text})");
        assert!(matches!(
            InvariantModel::parse_smtlib(&input, &problem),
            Err(ChcError::Parse(_))
        ));
    }
}

#[test]
fn literal_comment_boundary_and_quoted_literal_named_binder_stay_distinct() {
    assert_eq!(
        parsed("#b0; after literal\n", 1).unwrap(),
        equals(ChcExpr::BitVec(0, 1), 1)
    );
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("wide", vec![ChcSort::BitVec(1)]);
    let model = InvariantModel::parse_smtlib(
        "(define-fun wide ((|#b0| (_ BitVec 1))) Bool (= |#b0| #b0))",
        &problem,
    )
    .unwrap();
    assert_eq!(
        model.get(&pred).unwrap().formula,
        ChcExpr::eq(
            ChcExpr::var(ChcVar::new("#b0", ChcSort::BitVec(1))),
            ChcExpr::BitVec(0, 1),
        )
    );
}

#[test]
fn binary_bv1_original_invariant_is_typed_valid_not_a_free_variable() {
    let problem = identity_problem(1, |value| {
        let observed = ChcExpr::Op(ChcOp::BvExtract(0, 0), vec![Arc::new(value)]);
        ChcExpr::ne(observed, ChcExpr::BitVec(0, 1))
    });
    let model = InvariantModel::parse_smtlib(
        "(define-fun wide ((value (_ BitVec 1))) Bool (= value #b0))",
        &problem,
    )
    .unwrap();
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &config()).unwrap(),
        ExternalInvariantValidation::Valid
    );
}

#[test]
fn hexadecimal_original_comparison_invariant_is_typed_valid() {
    let problem = identity_problem(4, |value| {
        ChcExpr::Op(
            ChcOp::BvUGt,
            vec![Arc::new(value), Arc::new(ChcExpr::BitVec(0, 4))],
        )
    });
    let model = InvariantModel::parse_smtlib(
        "(define-fun wide ((value (_ BitVec 4))) Bool (= value #x0))",
        &problem,
    )
    .unwrap();
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &config()).unwrap(),
        ExternalInvariantValidation::Valid
    );
}

#[test]
fn genuine_nonbinder_variables_still_report_typed_rejected() {
    let problem = identity_problem(1, |value| ChcExpr::ne(value, ChcExpr::BitVec(0, 1)));
    let model = InvariantModel::parse_smtlib(
        "(define-fun wide ((value (_ BitVec 1))) Bool (= value outside))",
        &problem,
    )
    .unwrap();
    assert_eq!(
        validate_external_invariant_model_typed(&problem, &model, &config()).unwrap(),
        ExternalInvariantValidation::Rejected
    );
}
