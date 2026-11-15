// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use crate::{ChcVar, ClauseBody, ClauseHead, HornClause};

pub(super) fn truth() -> (ChcProblem, GroundDerivation) {
    let mut problem = ChcProblem::new();
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        true,
    ))));
    let derivation = GroundDerivation {
        steps: vec![GroundDerivationStep {
            clause_index: 0,
            env: Default::default(),
            premises: vec![],
        }],
        query_step: 0,
    };
    (problem, derivation)
}

pub(super) fn wide_recursive() -> (ChcProblem, GroundDerivation) {
    let sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Real));
    let mut problem = ChcProblem::new();
    let predicate = problem.declare_predicate("P", vec![ChcSort::BitVec(129), sort.clone()]);
    let names = [["bits", "array"], ["wide", "nested"]];
    for (index, names) in names.iter().enumerate() {
        let arguments = vec![
            ChcExpr::var(ChcVar::new(names[0], ChcSort::BitVec(129))),
            ChcExpr::var(ChcVar::new(names[1], sort.clone())),
        ];
        let clause = if index == 0 {
            HornClause::new(
                ClauseBody::empty(),
                ClauseHead::Predicate(predicate, arguments),
            )
        } else {
            HornClause::query(ClauseBody::predicates_only(vec![(predicate, arguments)]))
        };
        problem.add_clause(clause);
    }
    let wide =
        SmtValue::try_bitvec_from_biguint((BigUint::from(1_u8) << 128_u32) + 3_u8, 129).unwrap();
    let value = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Real(BigRational::from_integer(BigInt::from(0)))),
        entries: vec![
            (
                SmtValue::int_from_bigint(BigInt::from(i128::MAX) + 9),
                SmtValue::Real(BigRational::new(BigInt::from(-7), BigInt::from(11))),
            ),
            (
                SmtValue::int_from_bigint(BigInt::from(i128::MAX) + 9),
                SmtValue::Real(BigRational::from_integer(BigInt::from(4))),
            ),
        ],
    };
    let steps = names
        .into_iter()
        .enumerate()
        .map(|(index, names)| GroundDerivationStep {
            clause_index: index,
            env: [
                (names[0].to_string(), wide.clone()),
                (names[1].to_string(), value.clone()),
            ]
            .into_iter()
            .collect(),
            premises: if index == 0 { vec![] } else { vec![0] },
        })
        .collect();
    (
        problem,
        GroundDerivation {
            steps,
            query_step: 1,
        },
    )
}
