// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::quantified::UniversalPremise;
use crate::smt::SmtValue;

pub(super) fn resize() -> String {
    // Source-derived scalar projection of MODEL_CHECKER_CONSUMER 22278991c4d8e731's
    // resize.rs:269-300, not a retained datatype-bearing compiler artifact.
    // The unchanged symbolic universal entails the omitted 32 low-index hints.
    "(set-logic HORN)
     (declare-var a (Array (_ BitVec 64) (_ BitVec 8)))
     (declare-var b (Array (_ BitVec 64) (_ BitVec 8)))
     (declare-var old (_ BitVec 64))
     (declare-var new (_ BitVec 64))
     (declare-var fill (_ BitVec 8))
     (declare-var j (_ BitVec 64))
     (declare-rel R ((Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64) (_ BitVec 64) (_ BitVec 8)))
     (declare-rel error ())
     (rule (=> (and (bvult old new)
          (forall ((i (_ BitVec 64)))
            (and (=> (bvult i old) (= (select b i) (select a i)))
                 (=> (and (bvuge i old) (bvult i new)) (= (select b i) fill)))))
          (R b old new fill)))
     (rule (=> (and (R b old new fill) (bvuge j old) (bvult j new)
                   (bvuge j (_ bv32 64)) (not (= (select b j) fill))) error))
     (query error)"
        .to_owned()
}

pub(super) fn check_matrix(premise: &UniversalPremise) {
    for index in [0u128, 31, 32, 40, 64, 65, u64::MAX as u128] {
        for actual in [0u128, 7] {
            let env = [
                (premise.binder().name.clone(), SmtValue::BitVec(index, 64)),
                ("old".to_owned(), SmtValue::BitVec(32, 64)),
                ("new".to_owned(), SmtValue::BitVec(65, 64)),
                ("fill".to_owned(), SmtValue::BitVec(7, 8)),
                (
                    "a".to_owned(),
                    SmtValue::ConstArray(Box::new(SmtValue::BitVec(0, 8))),
                ),
                (
                    "b".to_owned(),
                    SmtValue::ConstArray(Box::new(SmtValue::BitVec(actual, 8))),
                ),
            ]
            .into_iter()
            .collect();
            let expected =
                (index >= 32 || actual == 0) && (!(32..65).contains(&index) || actual == 7);
            assert_eq!(
                crate::expr::evaluate::evaluate_expr(premise.matrix(), &env),
                Some(SmtValue::Bool(expected))
            );
        }
    }
}

pub(super) fn typed() -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let sort = ChcSort::BitVec(2);
    let predicate = declarations.declare_predicate("P", vec![sort.clone()]);
    let x = ChcExpr::var(ChcVar::new("x", sort.clone()));
    let binder = ChcVar::new("i", sort);
    let matrix = ChcExpr::Op(
        ChcOp::BvULe,
        vec![Arc::new(ChcExpr::var(binder.clone())), Arc::new(x.clone())],
    );
    QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(
                HornClause::new(
                    ClauseBody::empty(),
                    ClauseHead::Predicate(predicate, vec![x.clone()]),
                ),
                vec![UniversalPremise::new(binder, matrix)],
            ),
            QuantifiedHornClause::new(
                HornClause::query(ClauseBody::new(vec![(predicate, vec![x])], None)),
                vec![],
            ),
            QuantifiedHornClause::new(
                HornClause::query(ClauseBody::constraint(ChcExpr::Bool(false))),
                vec![],
            ),
        ],
    )
    .unwrap()
}
