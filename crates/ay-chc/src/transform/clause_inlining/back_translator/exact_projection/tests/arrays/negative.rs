// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn coupled_array_or_index_locals_without_definitions_decline() {
    let memory = array("memory", ChcSort::BitVec(1), ChcSort::Bool);
    let index = var("index", 1);
    declined(
        &select(expr(&memory), expr(&index)),
        std::slice::from_ref(&memory),
    );
    declined(&select(expr(&memory), ChcExpr::BitVec(0, 1)), &[]);
    let kept = array("kept", ChcSort::BitVec(1), ChcSort::Bool);
    declined(
        &eq(
            expr(&kept),
            store(expr(&memory), ChcExpr::BitVec(0, 1), ChcExpr::Bool(true)),
        ),
        &[kept],
    );
}

#[test]
fn self_and_mutual_store_cycles_never_become_defining_substitutions() {
    let a = array("a", ChcSort::BitVec(1), ChcSort::Bool);
    let b = array("b", ChcSort::BitVec(1), ChcSort::Bool);
    let update = store(expr(&a), ChcExpr::BitVec(0, 1), ChcExpr::Bool(true));
    declined(&eq(expr(&a), update.clone()), &[]);
    declined(
        &op(
            ChcOp::And,
            vec![eq(expr(&a), expr(&b)), eq(expr(&b), update)],
        ),
        &[],
    );
    let hidden = constant(ChcSort::BitVec(1), select(expr(&a), ChcExpr::BitVec(0, 1)));
    declined(&eq(expr(&a), hidden), &[]);
}

#[test]
fn hidden_raw_scalar_in_constant_array_blocks_a_quotient_image() {
    let memory = array("memory", ChcSort::BitVec(1), ChcSort::BitVec(2));
    let result = var("result", 2);
    let local = var("local", 2);
    let formula = op(
        ChcOp::And,
        vec![
            eq(expr(&result), quotient(&local, 2)),
            eq(expr(&memory), constant(ChcSort::BitVec(1), expr(&local))),
        ],
    );
    declined(&formula, &[memory, result]);
}

#[test]
fn hidden_raw_scalar_blocks_joint_sum_and_checked_product_images() {
    for arithmetic in [ChcOp::BvAdd, ChcOp::BvMul] {
        let memory = array("memory", ChcSort::BitVec(1), ChcSort::BitVec(2));
        let result = var("result", 2);
        let left = var("left", 2);
        let right = var("right", 2);
        let overflow = ChcVar::new("overflow", ChcSort::Bool);
        let computed = op(arithmetic, vec![expr(&left), expr(&right)]);
        let observed = match arithmetic {
            ChcOp::BvAdd => op(ChcOp::BvULt, vec![computed.clone(), expr(&left)]),
            ChcOp::BvMul => op(
                ChcOp::Not,
                vec![eq(
                    op(
                        ChcOp::BvExtract(3, 2),
                        vec![op(
                            ChcOp::BvMul,
                            vec![
                                op(ChcOp::BvZeroExtend(2), vec![expr(&left)]),
                                op(ChcOp::BvZeroExtend(2), vec![expr(&right)]),
                            ],
                        )],
                    ),
                    ChcExpr::BitVec(0, 2),
                )],
            ),
            _ => unreachable!(),
        };
        let formula = op(
            ChcOp::And,
            vec![
                eq(expr(&result), computed),
                eq(expr(&overflow), observed),
                eq(expr(&memory), constant(ChcSort::BitVec(1), expr(&left))),
            ],
        );
        declined(&formula, &[memory, result, overflow]);
    }
}

#[test]
fn full_array_source_typing_precedes_false_arm_simplification() {
    let memory = array("memory", ChcSort::BitVec(1), ChcSort::Bool);
    let malformed = [
        op(ChcOp::Select, vec![expr(&memory)]),
        select(expr(&memory), ChcExpr::BitVec(0, 2)),
        store(expr(&memory), ChcExpr::BitVec(0, 1), ChcExpr::BitVec(0, 1)),
        op(ChcOp::Store, vec![expr(&memory), ChcExpr::BitVec(0, 1)]),
        eq(
            constant(ChcSort::Bool, ChcExpr::Bool(true)),
            constant(ChcSort::BitVec(1), ChcExpr::Bool(true)),
        ),
        eq(
            expr(&memory),
            constant(ChcSort::BitVec(0), ChcExpr::Bool(false)),
        ),
    ];
    for bad in malformed {
        declined(
            &op(ChcOp::And, vec![ChcExpr::Bool(false), bad]),
            std::slice::from_ref(&memory),
        );
    }
}

#[test]
fn opaque_functions_markers_and_nested_array_sorts_remain_unsupported() {
    let inner = ChcSort::Array(Box::new(ChcSort::BitVec(1)), Box::new(ChcSort::Bool));
    for (key, value) in [
        (inner.clone(), ChcSort::Bool),
        (ChcSort::BitVec(1), inner),
        (ChcSort::Int, ChcSort::Bool),
        (ChcSort::BitVec(1), ChcSort::Uninterpreted("opaque".into())),
    ] {
        declined(&ChcExpr::Bool(true), &[array("unused", key, value)]);
    }
    let bad = ChcExpr::FuncApp("opaque".into(), ChcSort::Bool, Vec::new());
    declined(&op(ChcOp::Or, vec![ChcExpr::Bool(true), bad]), &[]);
    let nested = constant(
        ChcSort::BitVec(1),
        constant(ChcSort::BitVec(1), ChcExpr::Bool(true)),
    );
    declined(&eq(nested.clone(), nested), &[]);
    let marker = ChcExpr::ConstArrayMarker(ChcSort::BitVec(1));
    declined(
        &op(
            ChcOp::And,
            vec![ChcExpr::Bool(false), eq(marker.clone(), marker)],
        ),
        &[],
    );
}

#[test]
fn conflicting_array_names_and_unsupported_partial_alternatives_decline() {
    let memory = array("memory", ChcSort::BitVec(1), ChcSort::Bool);
    let conflict = array("memory", ChcSort::BitVec(2), ChcSort::Bool);
    declined(
        &select(expr(&conflict), ChcExpr::BitVec(0, 2)),
        std::slice::from_ref(&memory),
    );
    let local = array("local", ChcSort::BitVec(1), ChcSort::Bool);
    let formula = op(
        ChcOp::Or,
        vec![
            select(expr(&memory), ChcExpr::BitVec(0, 1)),
            select(expr(&local), ChcExpr::BitVec(0, 1)),
        ],
    );
    declined(&formula, &[memory]);
}
