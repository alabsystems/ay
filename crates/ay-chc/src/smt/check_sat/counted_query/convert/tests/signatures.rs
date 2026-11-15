// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn subject(opcode: ChcOp, args: Vec<ChcExpr>, expected: Sort, symbol: &str) {
    let node = Arc::new(op(opcode, args));
    let source = ChcExpr::Op(ChcOp::Eq, vec![node.clone(), node.clone()]);
    let built = convert(&source, &ample()).unwrap();
    let id = built.term_for(&node).unwrap();
    assert_eq!(built.terms().sort(id), &expected);
    assert!(matches!(built.terms().get(id), TermData::App(name, _) if name.name() == symbol));
}

#[test]
fn every_binary_bv_source_operator_preserves_its_native_signature_and_symbol() {
    use ChcOp::*;
    for (opcode, symbol) in [
        (BvAdd, "bvadd"),
        (BvSub, "bvsub"),
        (BvMul, "bvmul"),
        (BvUDiv, "bvudiv"),
        (BvURem, "bvurem"),
        (BvSDiv, "bvsdiv"),
        (BvSRem, "bvsrem"),
        (BvSMod, "bvsmod"),
        (BvAnd, "bvand"),
        (BvOr, "bvor"),
        (BvXor, "bvxor"),
        (BvNand, "bvnand"),
        (BvNor, "bvnor"),
        (BvXnor, "bvxnor"),
        (BvShl, "bvshl"),
        (BvLShr, "bvlshr"),
        (BvAShr, "bvashr"),
    ] {
        subject(
            opcode,
            vec![var("a", ChcSort::BitVec(13)), var("b", ChcSort::BitVec(13))],
            Sort::bitvec(13),
            symbol,
        );
    }
    for (opcode, symbol) in [
        (BvULt, "bvult"),
        (BvULe, "bvule"),
        (BvUGt, "bvugt"),
        (BvUGe, "bvuge"),
        (BvSLt, "bvslt"),
        (BvSLe, "bvsle"),
        (BvSGt, "bvsgt"),
        (BvSGe, "bvsge"),
    ] {
        subject(
            opcode,
            vec![ChcExpr::BitVec(1, 13), ChcExpr::BitVec(2, 13)],
            Sort::Bool,
            symbol,
        );
    }
    subject(
        BvComp,
        vec![ChcExpr::BitVec(1, 13), ChcExpr::BitVec(2, 13)],
        Sort::bitvec(1),
        "bvcomp",
    );
    subject(
        BvConcat,
        vec![ChcExpr::BitVec(1, 13), ChcExpr::BitVec(2, 7)],
        Sort::bitvec(20),
        "concat",
    );
}

#[test]
fn indexed_and_unary_bv_operators_keep_all_indices_without_folding() {
    use ChcOp::*;
    for (opcode, width, symbol, indices) in [
        (BvNot, 13, "bvnot", vec![]),
        (BvNeg, 13, "bvneg", vec![]),
        (BvExtract(12, 4), 9, "extract", vec![12, 4]),
        (BvZeroExtend(5), 18, "zero_extend", vec![5]),
        (BvSignExtend(7), 20, "sign_extend", vec![7]),
        (BvRotateLeft(30), 13, "rotate_left", vec![30]),
        (BvRotateRight(31), 13, "rotate_right", vec![31]),
        (BvRepeat(3), 39, "repeat", vec![3]),
    ] {
        let node = Arc::new(op(opcode, vec![ChcExpr::BitVec(1, 13)]));
        let source = ChcExpr::Op(Eq, vec![node.clone(), node.clone()]);
        let built = convert(&source, &ample()).unwrap();
        let id = built.term_for(&node).unwrap();
        assert_eq!(built.terms().sort(id), &Sort::bitvec(width));
        let TermData::App(name, _) = built.terms().get(id) else {
            panic!("raw app missing")
        };
        assert_eq!(name.name(), symbol);
        match name {
            Symbol::Indexed(_, actual) => assert_eq!(actual, &indices),
            _ => assert!(indices.is_empty()),
        }
    }
}

#[test]
fn boolean_literals_negation_conditionals_and_relations_remain_raw() {
    use ChcOp::*;
    for (opcode, name) in [
        (And, "and"),
        (Or, "or"),
        (Implies, "=>"),
        (Iff, "="),
        (Eq, "="),
        (Ne, "distinct"),
    ] {
        subject(
            opcode,
            vec![ChcExpr::Bool(true), ChcExpr::Bool(false)],
            Sort::Bool,
            name,
        );
    }
    let negated = Arc::new(op(Not, vec![ChcExpr::Bool(true)]));
    let source = ChcExpr::Op(
        Ite,
        vec![
            Arc::new(ChcExpr::Bool(false)),
            negated.clone(),
            Arc::new(ChcExpr::Bool(true)),
        ],
    );
    let built = convert(&source, &ample()).unwrap();
    assert!(matches!(built.terms().get(built.root()), TermData::Ite(..)));
    assert!(matches!(
        built.terms().get(built.term_for(&negated).unwrap()),
        TermData::Not(_)
    ));
    assert!(matches!(
        built.terms().get(built.node_terms[0]),
        TermData::Const(Constant::Bool(false))
    ));
}

#[test]
fn malformed_empty_singleton_and_dead_arm_syntax_stays_rejected_before_conversion() {
    for bad in [
        op(ChcOp::And, vec![]),
        op(ChcOp::Or, vec![ChcExpr::Bool(true)]),
        op(ChcOp::Not, vec![ChcExpr::BitVec(1, 8)]),
        op(
            ChcOp::BvAdd,
            vec![ChcExpr::BitVec(1, 8), ChcExpr::BitVec(1, 16)],
        ),
        op(
            ChcOp::Eq,
            vec![ChcExpr::BitVec(256, 8), ChcExpr::BitVec(0, 8)],
        ),
    ] {
        let source = op(ChcOp::And, vec![ChcExpr::Bool(false), bad]);
        assert!(matches!(convert(&source, &ample()), Err(Error::IllTyped)));
    }
    let source = op(
        ChcOp::And,
        vec![
            ChcExpr::Bool(false),
            ChcExpr::FuncApp("f".into(), ChcSort::Bool, vec![]),
        ],
    );
    assert!(matches!(
        convert(&source, &ample()),
        Err(Error::Unsupported)
    ));
}
