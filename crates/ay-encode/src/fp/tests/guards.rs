// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Whole source-bound DATA controls; no CHC Safe/Unsafe or compiler credential.

use super::*;
use std::sync::Arc;

mod native;
mod ownership;
mod validation;

fn inputs(width: u32) -> ([Expr; 2], [ChcVar; 2]) {
    (
        [
            Expr::var("guard_a", crate::Sort::bitvec(width)),
            Expr::var("guard_b", crate::Sort::bitvec(width)),
        ],
        [
            ChcVar::new("guard_a", ChcSort::BitVec(width)),
            ChcVar::new("guard_b", ChcSort::BitVec(width)),
        ],
    )
}

fn fields(word: Expr, width: u32) -> Expr {
    let fraction = if width == 32 { 23 } else { 52 };
    Expr::fp_from_bvs(
        word.clone().extract(width - 1, width - 1),
        word.clone().extract(width - 2, fraction),
        word.extract(fraction - 1, 0),
    )
}

fn links<'a>(words: &'a [Expr; 2], targets: &'a [ChcVar; 2]) -> [FpExprInputBinding<'a>; 2] {
    [
        FpExprInputBinding {
            source: &words[0],
            target: &targets[0],
        },
        FpExprInputBinding {
            source: &words[1],
            target: &targets[1],
        },
    ]
}

fn attempt(budget: &mut WorkBudget<'_>) -> Result<(), FpAdapterError> {
    let (words, targets) = inputs(32);
    let roots = [words[0]
        .clone()
        .bvult(words[1].clone())
        .or(fields(words[0].clone(), 32).fp_is_nan())];
    let bindings = links(&words, &targets);
    let namespace = ChcProblem::new();
    let output = lower_fp_expr_clause(&roots, &bindings, &namespace, budget)?;
    let (body, source) = output.into_body(ClauseBody::empty())?.into_parts()?;
    drop(body);
    drop(source);
    budget.charge(0)?;
    Ok(())
}

fn assert_input_links(
    body: &ClauseBody,
    targets: &[ChcVar; 2],
    width: u32,
    budget: &mut WorkBudget<'_>,
) {
    let ChcExpr::Op(ChcOp::And, outer) = body.constraint.as_ref().unwrap() else {
        panic!()
    };
    let ChcExpr::Op(ChcOp::And, entries) = outer[0].as_ref() else {
        panic!()
    };
    budget.admit(8192, 8192).unwrap();
    for (index, target) in targets.iter().enumerate() {
        for (offset, entry) in entries[entries.len() - 2 * width as usize..]
            .iter()
            .skip(index * width as usize)
            .take(width as usize)
            .enumerate()
        {
            budget.charge(512).unwrap();
            let ChcExpr::Op(ChcOp::Eq, pair) = entry.as_ref() else {
                panic!()
            };
            let ChcExpr::Op(ChcOp::Eq, bit) = pair[1].as_ref() else {
                panic!()
            };
            let ChcExpr::Op(ChcOp::BvExtract(high, low), args) = bit[0].as_ref() else {
                panic!()
            };
            assert_eq!((*high, *low), (offset as u32, offset as u32));
            assert_eq!(args[0].as_ref(), &ChcExpr::Var(target.clone()));
        }
    }
}

#[test]
fn both_full_raw_inputs_and_every_repeated_mixed_root_survive_consumption() {
    with_owner(|budget| {
        for width in [32, 64] {
            let (words, targets) = inputs(width);
            let guard = words[0].clone().bvslt(words[1].clone());
            let root = guard.or(fields(words[0].clone(), width).fp_is_nan());
            let roots = [root.clone(), root];
            let bindings = links(&words, &targets);
            let namespace = ChcProblem::new();
            let output = lower_fp_expr_clause(&roots, &bindings, &namespace, budget).unwrap();
            let (body, source) = output
                .into_body(ClauseBody::empty())
                .unwrap()
                .into_parts()
                .unwrap();
            assert!(std::ptr::eq(source.roots(), roots.as_slice()));
            assert_eq!(source.bindings().len(), 2);
            assert!(std::ptr::eq(
                source.bindings()[0].source.value(),
                words[0].value()
            ));
            assert!(std::ptr::eq(
                source.bindings()[1].source.value(),
                words[1].value()
            ));
            assert_input_links(&body, &targets, width, budget);
            drop(body);
            drop(source);
            budget.charge(0).unwrap();
        }
    });
}
