// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn array_equality_and_disequality_remain_unavailable_even_with_total_free_witnesses() {
    for relation in [ChcOp::Eq, ChcOp::Ne] {
        let a = array("a", ChcSort::Bool, ChcSort::Bool);
        let b = array("b", ChcSort::Bool, ChcSort::Bool);
        let source = op(
            ChcOp::Or,
            vec![ChcExpr::Bool(true), op(relation, vec![a, b])],
        );
        let mut built = convert(&source, &ample()).unwrap();
        let mut reached = false;
        assert_eq!(
            built.with_scalar_encoding(|_| {
                reached = true;
                Ok(())
            }),
            Err(Error::Unsupported)
        );
        assert!(!reached);
        built.finish().unwrap();
    }
}

#[test]
fn nested_free_arrays_do_not_enter_scalar_attachment() {
    let inner = ChcSort::Array(Box::new(ChcSort::Bool), Box::new(ChcSort::Bool));
    let nested = array("a", ChcSort::Bool, inner);
    let source = select(select(nested, ChcExpr::Bool(false)), ChcExpr::Bool(true));
    let mut built = convert(&source, &ample()).unwrap();
    assert_eq!(
        built.with_scalar_encoding(|_| Ok(())),
        Err(Error::Unsupported)
    );
    built.finish().unwrap();
}

#[test]
fn wider_than_128_bit_free_models_remain_explicitly_unsupported() {
    let a = array("a", ChcSort::Bool, ChcSort::BitVec(129));
    let source = eq(
        select(a, ChcExpr::Bool(false)),
        var("v", ChcSort::BitVec(129)),
    );
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            assert!(matches!(
                encoding.check_scalar_candidate(&sat_model(encoding)),
                Err(Error::Unsupported)
            ));
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}
