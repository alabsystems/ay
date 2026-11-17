// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Whole native relation checks, not Rust replay or native ownership credentials.
use super::*;
use ay_chc::{SmtContext, SmtResult};
use std::sync::Arc;

mod chc;
mod numeric;
mod policies;
mod resources;
mod semantics;
mod source_controls;

use raw_words::native::original_owner;

const FIXTURE: usize = 16 * 1024 * 1024;

fn raw(name: &str, width: u32) -> (Expr, ChcVar) {
    (
        Expr::var(name, crate::Sort::bitvec(width)),
        ChcVar::new(name, ChcSort::BitVec(width)),
    )
}

fn layout(width: u32) -> (u64, u64, u64, u64) {
    if width == 32 {
        (0x80000000, 0x7f800000, 0x00400000, 0x3f800000)
    } else {
        (
            0x8000000000000000,
            0x7ff0000000000000,
            0x0008000000000000,
            0x3ff0000000000000,
        )
    }
}

fn pin(target: &ChcVar, bits: u64, width: u32) -> ChcExpr {
    ChcExpr::Op(
        ChcOp::Eq,
        vec![
            Arc::new(ChcExpr::Var(target.clone())),
            Arc::new(ChcExpr::BitVec(u128::from(bits), width)),
        ],
    )
}

fn negate(value: ChcExpr) -> ChcExpr {
    ChcExpr::Op(ChcOp::Not, vec![Arc::new(value)])
}

fn conjunction(values: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(ChcOp::And, values.into_iter().map(Arc::new).collect())
}

fn native(body: ClauseBody, expected: bool, budget: &mut WorkBudget<'_>, end: Instant) {
    budget.charge(0).unwrap();
    let mut context = SmtContext::new();
    context.set_term_memory_budget(Some(128 * 1024 * 1024));
    let remaining = end.saturating_duration_since(Instant::now());
    assert!(!remaining.is_zero());
    let result = context.check_sat_with_timeout(body.constraint.as_ref().unwrap(), remaining);
    if expected {
        assert!(matches!(result, SmtResult::Sat(_)));
    } else {
        assert!(result.is_unsat());
    }
    drop(result);
    drop(context);
    drop(body);
    budget.charge(0).unwrap();
}

fn arithmetic(
    width: u32,
    operation: RustFpArithmetic,
    bits: &[u64],
    policy: RustNanPolicy,
    condition: impl FnOnce(&ChcVar) -> ChcExpr,
    expected: bool,
    budget: &mut WorkBudget<'_>,
    end: Instant,
) {
    budget.admit(FIXTURE, FIXTURE).unwrap();
    let words = bits
        .iter()
        .map(|&b| Expr::bitvec_const(b, width))
        .collect::<Vec<_>>();
    let inputs = words.iter().collect::<Vec<_>>();
    let (output, target) = raw("raw_result", width);
    let results = [FpRawResultRelation {
        operation: FpRawOperation::Arithmetic {
            operation,
            inputs: &inputs,
            nan_policy: policy,
        },
        output: &output,
    }];
    let bindings = [FpExprInputBinding {
        source: &output,
        target: &target,
    }];
    let problem = ChcProblem::new();
    let old = ClauseBody::constraint(condition(&target));
    let body = {
        let (body, source) = lower_fp_raw_result_clause(&[], &results, &bindings, &problem, budget)
            .unwrap()
            .into_body(old)
            .unwrap()
            .into_parts()
            .unwrap();
        assert!(std::ptr::eq(source.raw_results(), results.as_slice()));
        assert!(std::ptr::eq(
            source.raw_results()[0].output,
            &raw const output
        ));
        assert_eq!(source.bindings()[0].target, &target);
        body
    };
    native(body, expected, budget, end);
    drop(inputs);
    drop(words);
    drop(output);
    drop(target);
    drop(problem);
    budget.charge(0).unwrap();
}

fn result_bits(
    width: u32,
    operation: RustFpArithmetic,
    inputs: &[u64],
    policy: RustNanPolicy,
    bits: u64,
    expected: bool,
    budget: &mut WorkBudget<'_>,
    end: Instant,
) {
    arithmetic(
        width,
        operation,
        inputs,
        policy,
        |target| pin(target, bits, width),
        expected,
        budget,
        end,
    );
}

fn mantissa(target: &ChcVar, width: u32, bits: u64) -> ChcExpr {
    let fraction = if width == 32 { 23 } else { 52 };
    ChcExpr::Op(
        ChcOp::Eq,
        vec![
            Arc::new(ChcExpr::Op(
                ChcOp::BvExtract(fraction - 1, 0),
                vec![Arc::new(ChcExpr::Var(target.clone()))],
            )),
            Arc::new(ChcExpr::BitVec(u128::from(bits), fraction)),
        ],
    )
}
