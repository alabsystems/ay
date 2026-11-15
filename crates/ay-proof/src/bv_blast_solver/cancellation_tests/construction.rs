// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

type Construction = (Vec<u32>, VarTable, Vec<BitLemma>, Vec<Clause>);

fn construct(
    expr: &BvExpr,
    poll: &mut dyn FnMut() -> bool,
) -> Result<Construction, BvExprExportError> {
    let mut vars = VarTable::default();
    let mut lemmas = Vec::new();
    let mut clauses = Vec::new();
    let mut blaster = ExprBlaster::new(None, poll);
    let bits = blaster.blast(expr, &mut vars, &mut lemmas, &mut clauses)?;
    Ok((bits, vars, lemmas, clauses))
}

fn expressions() -> Vec<BvExpr> {
    let a = BvExpr::leaf("a", 3);
    let b = BvExpr::leaf("b", 3);
    vec![
        a.clone(),
        BvExpr::const_val(5, 3),
        BvExpr::add(a.clone(), b.clone()),
        BvExpr::sub(a.clone(), b.clone()),
        BvExpr::mul(a.clone(), b.clone()),
        BvExpr::shl(a.clone(), b.clone()),
        BvExpr::lshr(a.clone(), b.clone()),
        BvExpr::ashr(a.clone(), b.clone()),
        BvExpr::or(a.clone(), b.clone()),
        BvExpr::and(a.clone(), b.clone()),
        BvExpr::xor(a.clone(), b.clone()),
        BvExpr::not(a.clone()),
        BvExpr::zero_ext(a.clone(), 2),
        BvExpr::sign_ext(a.clone(), 2),
        BvExpr::extract(a.clone(), 2, 1),
        BvExpr::Eq(Box::new(a.clone()), Box::new(b.clone())),
        BvExpr::CarryOut {
            lhs: Box::new(a.clone()),
            rhs: Box::new(b),
            is_sub: true,
        },
        BvExpr::add(a.clone(), a), // repeated leaf-bit copy and gate-cache hits
    ]
}

#[test]
fn every_expression_construction_poll_refuses_and_fresh_retries_match() {
    for expression in expressions() {
        let mut polls = 0;
        let expected = construct(&expression, &mut || {
            polls += 1;
            true
        })
        .unwrap();
        assert!(polls > 3);
        if matches!(
            &expression,
            BvExpr::Shl(..) | BvExpr::Lshr(..) | BvExpr::Ashr(..)
        ) {
            assert!(polls > 30, "barrel-shift inner loops must poll");
        }
        for stop in 1..=polls {
            let mut calls = 0;
            assert_eq!(
                construct(&expression, &mut || {
                    calls += 1;
                    calls != stop
                }),
                Err(BvExprExportError::Cancelled)
            );
            assert_eq!(calls, stop);
        }
        assert_eq!(construct(&expression, &mut || true), Ok(expected));
    }
}

#[test]
fn constant_construction_retains_frozen_gate_and_cnf_order() {
    // The pre-cancellation builder first allocates ConstTrue for bit 0,
    // ConstFalse for bit 1, then reuses the first variable for bit 2.
    let expected = (
        vec![0, 1, 0],
        VarTable {
            roles: vec![VarRole::Aux { bit: 0 }, VarRole::Aux { bit: 0 }],
        },
        vec![
            BitLemma {
                id: 0,
                kind: BitLemmaKind::ConstTrue,
                out: 0,
                ins: vec![],
            },
            BitLemma {
                id: 1,
                kind: BitLemmaKind::ConstFalse,
                out: 1,
                ins: vec![],
            },
        ],
        vec![
            Clause {
                id: 0,
                lits: vec![Lit::pos(0)],
                provenance: ClauseProvenance::BitLemmaCnf { lemma: 0 },
            },
            Clause {
                id: 1,
                lits: vec![Lit::neg(1)],
                provenance: ClauseProvenance::BitLemmaCnf { lemma: 1 },
            },
        ],
    );
    assert_eq!(
        construct(&BvExpr::const_val(5, 3), &mut || true),
        Ok(expected)
    );
}

#[test]
fn malformed_construction_is_not_replaced_by_a_later_poll() {
    let mut calls = 0;
    let error = construct(&BvExpr::const_val(8, 3), &mut || {
        calls += 1;
        assert_eq!(calls, 1);
        true
    })
    .unwrap_err();
    assert_eq!(calls, 1);
    assert_eq!(
        error,
        BvExprExportError::Malformed("constant 8 does not fit in 3 bits".to_owned())
    );
}
