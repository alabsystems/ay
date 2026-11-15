// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
pub(super) enum Cells {
    Filled,
    CorruptLast,
}

pub(super) fn loop_source(cells: Cells, expected: u8) -> QuantifiedChcProblem {
    let filled = "((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv7 8))";
    let data = match cells {
        Cells::Filled => filled.to_owned(),
        Cells::CorruptLast => format!("(store {filled} (_ bv9 64) (_ bv8 8))"),
    };
    let premise = "(forall ((i (_ BitVec 64)))
      (=> (bvult i (len v)) (= (select (data v) i) (_ bv7 8))))";
    QuantifiedChcProblem::parse_smtlib(&format!(
        "(set-logic HORN)
         (declare-datatype Vec ((mkVec (ptr (_ BitVec 64)) (len (_ BitVec 64))
           (cap (_ BitVec 64)) (data (Array (_ BitVec 64) (_ BitVec 8))))))
         (declare-fun P (Vec (_ BitVec 4)) Bool)
         (assert (forall ((v Vec))
           (=> (and (= v (mkVec (_ bv0 64) (_ bv10 64) (_ bv10 64) {data}))
                    {premise}) (P v (_ bv0 4)))))
         (assert (forall ((v Vec) (pos (_ BitVec 4)))
           (=> (and (P v pos) (bvult pos (_ bv9 4)) {premise})
               (P v (bvadd pos (_ bv1 4))))))
         (assert (forall ((v Vec) (pos (_ BitVec 4)))
           (=> (and (P v pos) (= pos (_ bv9 4))
                    (distinct (select (data v) (_ bv9 64)) (_ bv{expected} 8))) false)))
         (check-sat)"
    ))
    .expect("authored bounded Vec iteration source")
}

pub(super) fn wide_source() -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-fun P () Bool)
         (assert (=> (forall ((i (_ BitVec 1))) (= i i)) P))
         (assert (=> (and P P P P P P P P) false))
         (check-sat)",
    )
    .unwrap()
}

pub(super) fn decoy_source() -> QuantifiedChcProblem {
    let mut source = String::from("(set-logic HORN) (declare-fun P ((_ BitVec 8)) Bool)");
    for value in 0..66 {
        source.push_str(&format!(
            "(assert (=> (forall ((i (_ BitVec 1))) (= i i)) (P (_ bv{value} 8))))"
        ));
    }
    source.push_str("(assert (=> (P (_ bv65 8)) false)) (check-sat)");
    QuantifiedChcProblem::parse_smtlib(&source).unwrap()
}
