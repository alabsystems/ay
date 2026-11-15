// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::eval::Evaluator;
use crate::ModelView;
use ay_core::TermStore;
use std::cell::Cell;

mod paths;

struct EmptyModel;

impl ModelView for EmptyModel {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        None
    }
}

fn analysis<'a, 'model>(
    evaluator: &'a Evaluator<'model>,
    sort: &'a Sort,
) -> SupportAnalysis<'a, 'model> {
    SupportAnalysis {
        evaluator,
        name: "i",
        sort,
        unavailable: &[],
        eval_depth: 0,
        saw_bound_comparison: Cell::new(false),
    }
}

#[test]
fn finite_quantifier_guarded_endpoint_rejects_forged_literal_width_before_normalizing() {
    let terms = TermStore::new();
    let model = EmptyModel;
    let evaluator = Evaluator::new(&terms, &model);
    let sort = Sort::bitvec(64);
    let analysis = analysis(&evaluator, &sort);
    for width in [0, 63, 128, u32::MAX] {
        // The public TermStore API correctly prevents this inconsistent pair.
        // Exercise the internal preflight directly with a tiny raw payload;
        // neither the fixture nor preflight may allocate the forged width.
        let constant = Constant::BitVec {
            value: BigInt::from(0u8),
            width,
        };
        assert_eq!(
            analysis.endpoint_literal_preflight(&constant),
            Err(QuantifierRejection::BindingSortMismatch)
        );
    }
}

#[test]
fn finite_quantifier_guarded_endpoint_rejects_wrong_numeric_constant_kind() {
    let terms = TermStore::new();
    let model = EmptyModel;
    let evaluator = Evaluator::new(&terms, &model);
    for (sort, constant) in [
        (
            Sort::Int,
            Constant::BitVec {
                value: BigInt::from(0u8),
                width: 64,
            },
        ),
        (Sort::bitvec(64), Constant::Int(BigInt::from(0u8))),
        (Sort::Int, Constant::Bool(false)),
    ] {
        assert_eq!(
            analysis(&evaluator, &sort).endpoint_literal_preflight(&constant),
            Err(QuantifierRejection::BindingSortMismatch)
        );
    }
}

#[test]
fn finite_quantifier_compound_raw_literal_bit_limit_precedes_normalization() {
    let terms = TermStore::new();
    let model = EmptyModel;
    let evaluator = Evaluator::new(&terms, &model);
    let sort = Sort::bitvec(64);
    let analysis = analysis(&evaluator, &sort);
    let at_limit = Constant::BitVec {
        width: 64,
        value: BigInt::from(1u8) << 4095usize,
    };
    let over_limit = Constant::BitVec {
        width: 64,
        value: BigInt::from(1u8) << 4096usize,
    };
    assert_eq!(analysis.endpoint_literal_preflight(&at_limit), Ok(()));
    assert_eq!(
        analysis.endpoint_literal_preflight(&over_limit),
        Err(QuantifierRejection::EvaluationBudget)
    );
}

#[test]
fn finite_quantifier_compound_small_bv_arithmetic_matches_modular_reference() {
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(3);
    let mut cases = Vec::new();
    for left in 0u8..8 {
        for right in 0u8..8 {
            let lhs = terms.mk_bitvec(BigInt::from(left), 3);
            let rhs = terms.mk_bitvec(BigInt::from(right), 3);
            for (operator, expected) in [
                ("bvadd", (left + right) % 8),
                ("bvsub", (left + 8 - right) % 8),
            ] {
                let term = terms.mk_app(Symbol::named(operator), &[lhs, rhs], sort.clone());
                cases.push((term, BigInt::from(expected)));
            }
        }
    }
    let model = EmptyModel;
    let evaluator = Evaluator::new(&terms, &model);
    evaluator.quantifier_state.nesting.set(1);
    let analysis = analysis(&evaluator, &sort);
    for (term, expected) in cases {
        assert_eq!(analysis.endpoint(term), Ok(Some(expected)));
    }
}

#[test]
fn finite_quantifier_compound_endpoint_reuse_spends_the_same_work_envelope() {
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(64);
    let one = terms.mk_bitvec(BigInt::from(1u8), 64);
    let sum = terms.mk_app(Symbol::named("bvadd"), &[one, one], sort.clone());
    let model = EmptyModel;
    let evaluator = Evaluator::new(&terms, &model);
    evaluator.quantifier_state.nesting.set(1);
    evaluator.quantifier_state.work_left.set(100);
    let analysis = analysis(&evaluator, &sort);
    assert_eq!(analysis.endpoint(sum), Ok(Some(BigInt::from(2u8))));
    let mut exhausted = false;
    for _ in 0..100 {
        match analysis.endpoint(sum) {
            Ok(Some(value)) => assert_eq!(value, BigInt::from(2u8)),
            Err(_) => {
                exhausted = true;
                break;
            }
            Ok(None) => panic!("a fully supported bound must not lose its grammar"),
        }
    }
    assert!(exhausted);
    assert_eq!(evaluator.quantifier_state.work_left.get(), 0);
}
