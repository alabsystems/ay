// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcExpr, ChcOp, ClauseBody, HornClause};
use std::sync::Arc;

fn operation(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}

fn query(guard: ChcExpr) -> (ChcProblem, CompactDerivation) {
    let problem = ChcProblem::new()
        .with_raw_source_clauses(vec![HornClause::query(ClauseBody::constraint(guard))])
        .expect("unsimplified original source");
    (
        problem,
        CompactDerivation {
            arena: Arena::new(),
            steps: vec![CompactStep {
                clause_index: 0,
                env: DetHashMap::default(),
                premises: vec![],
            }],
            query_step: 0,
        },
    )
}

#[test]
fn scalar_replay_uses_existing_unsigned_and_signed_bv_semantics() {
    let cases = [
        (ChcOp::BvAdd, 255, 2, 1),
        (ChcOp::BvUDiv, 7, 0, 255),
        (ChcOp::BvAShr, 128, 1, 192),
        (ChcOp::BvSRem, 255, 2, 255),
    ];
    for (op, left, right, result) in cases {
        let term = operation(
            op,
            vec![ChcExpr::BitVec(left, 8), ChcExpr::BitVec(right, 8)],
        );
        let (problem, derivation) =
            query(operation(ChcOp::Eq, vec![term, ChcExpr::BitVec(result, 8)]));
        assert_eq!(check(&problem, &derivation), Ok(()), "{op:?}");
    }
}

#[test]
fn wide_scalar_result_and_max_width_literal_do_not_expand_datatypes() {
    let wide = operation(ChcOp::BvZeroExtend(248), vec![ChcExpr::BitVec(5, 8)]);
    let (problem, derivation) = query(operation(ChcOp::Eq, vec![wide, ChcExpr::BitVec(5, 256)]));
    assert_eq!(check(&problem, &derivation), Ok(()));
    let zero = ChcExpr::BitVec(0, crate::MAX_BITVECTOR_WIDTH);
    let (problem, derivation) = query(operation(ChcOp::Eq, vec![zero.clone(), zero]));
    assert_eq!(check(&problem, &derivation), Ok(()));
}

#[test]
fn declared_width_expansion_is_admitted_before_opaque_scalar_evaluation() {
    let wide = operation(
        ChcOp::BvRepeat(crate::MAX_BITVECTOR_WIDTH),
        vec![ChcExpr::BitVec(1, 1)],
    );
    let (problem, derivation) = query(operation(ChcOp::Eq, vec![wide.clone(), wide]));
    let mut owner = Owner::capture().expect("owner");
    assert_eq!(
        validate(&problem, &derivation, &mut owner),
        Err(Error::Resource)
    );
    assert_eq!(owner.poll(), Err(Error::Resource));
}

#[test]
fn unchosen_ite_branch_and_boolean_bitvector_coercion_are_rejected() {
    let malformed = operation(
        ChcOp::Ite,
        vec![
            ChcExpr::Bool(true),
            ChcExpr::Bool(true),
            ChcExpr::BitVec(1, 1),
        ],
    );
    let (problem, derivation) = query(malformed);
    assert_eq!(check(&problem, &derivation), Err(Error::InvalidSource));
    let (problem, derivation) = query(operation(
        ChcOp::Eq,
        vec![ChcExpr::Bool(true), ChcExpr::BitVec(1, 1)],
    ));
    assert_eq!(check(&problem, &derivation), Err(Error::InvalidSource));
}
