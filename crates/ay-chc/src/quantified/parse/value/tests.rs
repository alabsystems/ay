// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use crate::{ChcError, ChcVar};

fn sexp(text: &str) -> SExpr {
    let mut expressions = ay_frontend::sexp::parse_sexps(text).unwrap();
    assert_eq!(expressions.len(), 1);
    expressions.pop().unwrap()
}

fn symbol(text: &str) -> SExpr {
    SExpr::Symbol(text.into())
}

fn var(name: &str, sort: ChcSort) -> Arc<ChcExpr> {
    Arc::new(ChcExpr::Var(ChcVar::new(name, sort)))
}

fn literal(expr: &SExpr) -> ChcResult<Option<Arc<ChcExpr>>> {
    super::literal(expr, &mut Budget::default())
}

fn call(head: &str, sorts: &[ChcSort]) -> ChcResult<(Arc<ChcExpr>, ChcSort)> {
    let args = sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| var(&format!("v{i}"), sort.clone()))
        .collect();
    application(&sexp(head), args, sorts)
}

fn array() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(2)), Box::new(ChcSort::Bool))
}

#[test]
fn exact_literals_preserve_width_and_never_truncate() {
    for (text, expected) in [
        ("true", ChcExpr::Bool(true)),
        ("false", ChcExpr::Bool(false)),
        ("#b0", ChcExpr::BitVec(0, 1)),
        ("#b00001", ChcExpr::BitVec(1, 5)),
        ("#x00Af", ChcExpr::BitVec(175, 16)),
        ("#xffffffffffffffff", ChcExpr::BitVec(u64::MAX.into(), 64)),
        ("(_ bv0 1)", ChcExpr::BitVec(0, 1)),
        ("(_ bv1 1)", ChcExpr::BitVec(1, 1)),
        ("(_ bv0007 4)", ChcExpr::BitVec(7, 4)),
        (
            "(_ bv18446744073709551615 64)",
            ChcExpr::BitVec(u64::MAX.into(), 64),
        ),
    ] {
        let input = sexp(text);
        let before = input.clone();
        assert_eq!(literal(&input).unwrap().unwrap().as_ref(), &expected);
        assert_eq!(input, before);
    }
    let binary = SExpr::Binary(format!("#b{}", "1".repeat(64)));
    assert_eq!(
        literal(&binary).unwrap().unwrap().as_ref(),
        &ChcExpr::BitVec(u64::MAX.into(), 64)
    );
}

#[test]
fn malformed_or_oversized_literals_are_typed_refusals() {
    let mut invalid = vec![
        SExpr::Binary("#b".into()),
        SExpr::Binary("#b2".into()),
        SExpr::Binary("#b+1".into()),
        SExpr::Binary("#x1".into()),
        SExpr::Binary(format!(
            "#b{}",
            "0".repeat(crate::MAX_BITVECTOR_WIDTH as usize + 1)
        )),
        SExpr::Hexadecimal("#x".into()),
        SExpr::Hexadecimal("#xg".into()),
        SExpr::Hexadecimal("#X1".into()),
        SExpr::Hexadecimal(format!(
            "#x{}",
            "0".repeat(crate::MAX_BITVECTOR_WIDTH as usize / 4 + 1)
        )),
    ];
    for text in [
        "(_ bv2 1)",
        "(_ bv16 4)",
        "(_ bv18446744073709551616 64)",
        "(_ bv-1 8)",
        "(_ bv+1 8)",
        "(_ bv 8)",
        "(_ bv1 0)",
        "(_ bv1 1048577)",
        "(_ bv1 8 0)",
        "(_ bv1)",
        "(_ bv1 x)",
        "(_ bv1 4294967296)",
    ] {
        invalid.push(sexp(text));
    }
    invalid.push(SExpr::List(vec![
        symbol("_"),
        symbol("bv1"),
        SExpr::Numeral("01".into()),
    ]));
    for input in invalid {
        let before = input.clone();
        for _ in 0..2 {
            let error = literal(&input).unwrap_err();
            assert!(matches!(error, ChcError::Parse(_)));
            assert!(error.to_string().len() < 160);
        }
        assert_eq!(input, before);
    }
}

#[test]
fn nonliterals_are_not_reinterpreted_from_symbol_text() {
    for input in [
        symbol("true"),
        symbol("false"),
        symbol("123"),
        symbol("#x1"),
        symbol("bv7"),
        SExpr::Numeral("1".into()),
        SExpr::Decimal("1.0".into()),
        sexp("(_ extract 3 0)"),
        sexp("(forall ((i Bool)) i)"),
        sexp("(let ((x true)) x)"),
    ] {
        assert!(literal(&input).unwrap().is_none());
    }
}

#[test]
fn sorts_accept_only_the_shallow_scalar_array_fragment() {
    for (text, expected) in [
        ("Bool", ChcSort::Bool),
        ("(_ BitVec 1)", ChcSort::BitVec(1)),
        ("(_ BitVec 64)", ChcSort::BitVec(64)),
        ("(Array (_ BitVec 2) Bool)", array()),
        (
            "(Array (_ BitVec 64) (_ BitVec 1))",
            ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(1))),
        ),
    ] {
        assert_eq!(sort(&sexp(text)).unwrap(), expected);
    }
    for text in [
        "Int",
        "Real",
        "U",
        "(Bool)",
        "(_ BitVec)",
        "(_ BitVec 0)",
        "(_ BitVec 1048577)",
        "(_ BitVec 4294967296)",
        "(_ BitVec 8 1)",
        "(Array Bool Bool)",
        "(Array (_ BitVec 2) Int)",
        "(Array (_ BitVec 2) (Array (_ BitVec 2) Bool))",
        "(Array (Array (_ BitVec 2) Bool) Bool)",
        "(Array (_ BitVec 2))",
    ] {
        assert!(matches!(sort(&sexp(text)), Err(ChcError::Parse(_))));
    }
}

#[test]
fn all_binary_bv_operators_retain_operator_order_and_child_identity() {
    let bv = ChcSort::BitVec(8);
    let left = Arc::new(ChcExpr::BitVec(0, 8));
    let right = Arc::new(ChcExpr::BitVec(1, 8));
    for (name, expected) in [
        ("bvadd", ChcOp::BvAdd),
        ("bvsub", ChcOp::BvSub),
        ("bvmul", ChcOp::BvMul),
        ("bvudiv", ChcOp::BvUDiv),
        ("bvurem", ChcOp::BvURem),
        ("bvsdiv", ChcOp::BvSDiv),
        ("bvsrem", ChcOp::BvSRem),
        ("bvsmod", ChcOp::BvSMod),
        ("bvand", ChcOp::BvAnd),
        ("bvor", ChcOp::BvOr),
        ("bvxor", ChcOp::BvXor),
        ("bvnand", ChcOp::BvNand),
        ("bvnor", ChcOp::BvNor),
        ("bvxnor", ChcOp::BvXnor),
        ("bvshl", ChcOp::BvShl),
        ("bvlshr", ChcOp::BvLShr),
        ("bvashr", ChcOp::BvAShr),
    ] {
        let (value, result) = application(
            &symbol(name),
            vec![left.clone(), right.clone()],
            &[bv.clone(), bv.clone()],
        )
        .unwrap();
        let ChcExpr::Op(op, children) = value.as_ref() else {
            panic!("constant folding is forbidden")
        };
        assert_eq!(*op, expected);
        assert!(Arc::ptr_eq(&children[0], &left));
        assert!(Arc::ptr_eq(&children[1], &right));
        assert_eq!(result, bv);
    }
    for (name, expected) in [("bvnot", ChcOp::BvNot), ("bvneg", ChcOp::BvNeg)] {
        let (value, result) = call(name, &[bv.clone()]).unwrap();
        assert!(matches!(value.as_ref(), ChcExpr::Op(op, _) if *op == expected));
        assert_eq!(result, bv);
    }
}

#[test]
fn comparisons_and_boolean_ops_use_exact_signatures_without_simplification() {
    for (name, expected) in [
        ("bvult", ChcOp::BvULt),
        ("bvule", ChcOp::BvULe),
        ("bvugt", ChcOp::BvUGt),
        ("bvuge", ChcOp::BvUGe),
        ("bvslt", ChcOp::BvSLt),
        ("bvsle", ChcOp::BvSLe),
        ("bvsgt", ChcOp::BvSGt),
        ("bvsge", ChcOp::BvSGe),
        ("=", ChcOp::Eq),
        ("distinct", ChcOp::Ne),
    ] {
        let (value, result) = call(name, &[ChcSort::BitVec(8), ChcSort::BitVec(8)]).unwrap();
        assert_eq!(result, ChcSort::Bool);
        assert!(matches!(value.as_ref(), ChcExpr::Op(op, _) if *op == expected));
    }
    assert_eq!(
        call("bvcomp", &[ChcSort::BitVec(8), ChcSort::BitVec(8)])
            .unwrap()
            .1,
        ChcSort::BitVec(1)
    );
    for (name, expected, count) in [
        ("not", ChcOp::Not, 1),
        ("and", ChcOp::And, 3),
        ("or", ChcOp::Or, 3),
        ("=>", ChcOp::Implies, 2),
        ("xor", ChcOp::Ne, 2),
    ] {
        let child = Arc::new(ChcExpr::Bool(false));
        let (value, result) = application(
            &symbol(name),
            vec![child.clone(); count],
            &vec![ChcSort::Bool; count],
        )
        .unwrap();
        let ChcExpr::Op(op, args) = value.as_ref() else {
            panic!("Boolean expression was simplified")
        };
        assert_eq!(*op, expected);
        assert_eq!(result, ChcSort::Bool);
        assert!(args.iter().all(|arg| Arc::ptr_eq(arg, &child)));
    }
}

#[test]
fn operator_arity_and_unsupported_metadata_refuse_before_construction() {
    for name in ["bvadd", "bvsub", "bvand", "=", "distinct", "xor", "concat"] {
        for count in [0, 1, 3] {
            assert!(call(name, &vec![ChcSort::BitVec(2); count]).is_err());
        }
    }
    for name in ["and", "or"] {
        for count in [0, 1] {
            assert!(call(name, &vec![ChcSort::Bool; count]).is_err());
        }
    }
    for (name, sorts) in [
        ("bvadd", vec![ChcSort::BitVec(1), ChcSort::BitVec(2)]),
        ("bvadd", vec![ChcSort::Bool, ChcSort::Bool]),
        ("xor", vec![ChcSort::BitVec(2), ChcSort::BitVec(2)]),
        ("=", vec![ChcSort::Int, ChcSort::Int]),
        ("=", vec![ChcSort::BitVec(0), ChcSort::BitVec(0)]),
        (
            "=",
            vec![ChcSort::BitVec(crate::MAX_BITVECTOR_WIDTH + 1); 2],
        ),
        (
            "=",
            vec![ChcSort::Array(Box::new(array()), Box::new(ChcSort::Bool)); 2],
        ),
    ] {
        assert!(matches!(call(name, &sorts), Err(ChcError::Parse(_))));
    }
    assert!(application(&symbol("not"), vec![], &[ChcSort::Bool]).is_err());
    assert!(application(&symbol("not"), vec![Arc::new(ChcExpr::Bool(true))], &[]).is_err());
    for name in [
        "+", "-", "bv2nat", "int2bv", "forall", "exists", "let", "f", "iff",
    ] {
        assert!(call(name, &[ChcSort::BitVec(2)]).is_err());
    }
}

#[test]
fn indexed_operators_preserve_parameters_and_enforce_result_widths() {
    for (head, op, input, result) in [
        ("(_ extract 7 0)", ChcOp::BvExtract(7, 0), 8, 8),
        ("(_ extract 3 2)", ChcOp::BvExtract(3, 2), 8, 2),
        ("(_ zero_extend 0)", ChcOp::BvZeroExtend(0), 64, 64),
        ("(_ zero_extend 63)", ChcOp::BvZeroExtend(63), 1, 64),
        ("(_ sign_extend 56)", ChcOp::BvSignExtend(56), 8, 64),
        ("(_ rotate_left 0)", ChcOp::BvRotateLeft(0), 8, 8),
        (
            "(_ rotate_left 4294967295)",
            ChcOp::BvRotateLeft(u32::MAX),
            8,
            8,
        ),
        ("(_ rotate_right 65)", ChcOp::BvRotateRight(65), 8, 8),
        ("(_ repeat 8)", ChcOp::BvRepeat(8), 8, 64),
    ] {
        let (value, actual) = call(head, &[ChcSort::BitVec(input)]).unwrap();
        assert!(matches!(value.as_ref(), ChcExpr::Op(actual, _) if *actual == op));
        assert_eq!(actual, ChcSort::BitVec(result));
    }
    for head in [
        "(_ extract 8 0)",
        "(_ extract 0 1)",
        "(_ extract 1)",
        "(_ extract 1 0 0)",
        "(_ extract -1 0)",
        "(_ extract 4294967296 0)",
        "(_ zero_extend 1048576)",
        "(_ sign_extend 4294967295)",
        "(_ repeat 0)",
        "(_ repeat 131073)",
        "(_ repeat 4294967295)",
        "(_ rotate_left 4294967296)",
        "(_ rotate_right 1 2)",
        "(_ int2bv 8)",
        "(_ unknown 0)",
        "(rotate_left 1)",
    ] {
        assert!(call(head, &[ChcSort::BitVec(8)]).is_err());
    }
    assert_eq!(
        call("concat", &[ChcSort::BitVec(32), ChcSort::BitVec(32)])
            .unwrap()
            .1,
        ChcSort::BitVec(64)
    );
    assert!(call(
        "concat",
        &[
            ChcSort::BitVec(crate::MAX_BITVECTOR_WIDTH),
            ChcSort::BitVec(1)
        ]
    )
    .is_err());
}

#[test]
fn arrays_and_conditionals_check_every_declared_sort_and_remain_raw() {
    let key = ChcSort::BitVec(2);
    assert_eq!(
        call("select", &[array(), key.clone()]).unwrap().1,
        ChcSort::Bool
    );
    assert_eq!(
        call("store", &[array(), key.clone(), ChcSort::Bool])
            .unwrap()
            .1,
        array()
    );
    assert_eq!(
        call("ite", &[ChcSort::Bool, array(), array()]).unwrap().1,
        array()
    );
    assert_eq!(call("=", &[array(), array()]).unwrap().1, ChcSort::Bool);
    for (head, sorts) in [
        ("select", vec![array(), ChcSort::BitVec(1)]),
        ("store", vec![array(), key.clone(), key.clone()]),
        ("ite", vec![key.clone(), array(), array()]),
        ("ite", vec![ChcSort::Bool, array(), ChcSort::Bool]),
    ] {
        assert!(call(head, &sorts).is_err());
    }
    let input = Arc::new(ChcExpr::Bool(true));
    let (constant, actual) = application(
        &sexp("(as const (Array (_ BitVec 2) Bool))"),
        vec![input.clone()],
        &[ChcSort::Bool],
    )
    .unwrap();
    let ChcExpr::ConstArray(actual_key, value) = constant.as_ref() else {
        panic!("expected a raw constant array")
    };
    assert_eq!(*actual_key, key);
    assert!(Arc::ptr_eq(value, &input));
    assert_eq!(actual, array());
    let (read, _) = application(
        &symbol("select"),
        vec![constant.clone(), Arc::new(ChcExpr::BitVec(0, 2))],
        &[array(), key],
    )
    .unwrap();
    assert!(
        matches!(read.as_ref(), ChcExpr::Op(ChcOp::Select, args) if Arc::ptr_eq(&args[0], &constant))
    );
}

#[test]
fn constant_array_qualifiers_cannot_launder_wrong_width_or_arity() {
    for (head, sorts) in [
        ("(as const Bool)", vec![ChcSort::Bool]),
        (
            "(as const (Array (_ BitVec 2) Bool))",
            vec![ChcSort::BitVec(1)],
        ),
        ("(as const (Array (_ BitVec 2) Bool))", vec![]),
        (
            "(as const (Array (_ BitVec 2) Bool))",
            vec![ChcSort::Bool, ChcSort::Bool],
        ),
        (
            "(as const (Array (_ BitVec 2) (_ BitVec 8)))",
            vec![ChcSort::BitVec(7)],
        ),
        ("(as const (Array Bool Bool))", vec![ChcSort::Bool]),
        (
            "(as const (Array (_ BitVec 1048577) Bool))",
            vec![ChcSort::Bool],
        ),
        ("(as other (Array (_ BitVec 2) Bool))", vec![ChcSort::Bool]),
        (
            "(as const (Array (_ BitVec 2) Bool) extra)",
            vec![ChcSort::Bool],
        ),
    ] {
        assert!(matches!(call(head, &sorts), Err(ChcError::Parse(_))));
    }
    assert_eq!(
        call(
            "(as const (Array (_ BitVec 64) (_ BitVec 8)))",
            &[ChcSort::BitVec(8)]
        )
        .unwrap()
        .1,
        ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(8)))
    );
}
