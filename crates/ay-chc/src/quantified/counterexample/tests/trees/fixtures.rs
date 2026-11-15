// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

#[derive(Clone, Copy)]
pub(super) enum Cells {
    Filled,
    CorruptLast,
}

#[derive(Clone, Copy)]
pub(super) enum Join {
    Query,
    Internal,
}

#[derive(Clone, Copy)]
pub(super) enum Comparison {
    Different,
    Equal,
}

pub(super) fn source(cells: Cells, join: Join, comparison: Comparison) -> QuantifiedChcProblem {
    // Authored composition, NOT a retained MODEL_CHECKER_CONSUMER compiler export. Vec's
    // full ptr/len/cap/data schema and resize-style premise are producer-shaped;
    // using the same summary twice deliberately exercises nonlinear freshness.
    let data = "((as const (Array (_ BitVec 64) (_ BitVec 8))) f)";
    let data = match cells {
        Cells::Filled => data.to_owned(),
        Cells::CorruptLast => format!("(store {data} (_ bv64 64) (bvadd f (_ bv1 8)))"),
    };
    let comparison = match comparison {
        Comparison::Different => "distinct",
        Comparison::Equal => "=",
    };
    let condition = format!(
        "(and (bvult (_ bv64 64) (fld_len a))
              (bvult (_ bv64 64) (fld_len b))
              ({comparison} (select (fld_data a) (_ bv64 64))
                            (select (fld_data b) (_ bv64 64))))"
    );
    let declarations = match join {
        Join::Query => "",
        Join::Internal => "(declare-fun Q (Vec Vec) Bool)",
    };
    let finish = match join {
        Join::Query => format!(
            "(assert (forall ((a Vec) (b Vec))
               (=> (and (P a (_ bv7 8)) (P b (_ bv9 8)) {condition}) false)))"
        ),
        Join::Internal => format!(
            "(assert (forall ((a Vec) (b Vec))
               (=> (and (P a (_ bv7 8)) (P b (_ bv9 8))) (Q a b))))
             (assert (forall ((a Vec) (b Vec))
               (=> (and (Q a b) {condition}) false)))"
        ),
    };
    QuantifiedChcProblem::parse_smtlib(&format!(
        "(set-logic HORN)
         (declare-datatype Vec ((mkVec
           (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
           (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8))))))
         (declare-fun P (Vec (_ BitVec 8)) Bool)
         {declarations}
         (assert (forall ((v Vec) (f (_ BitVec 8)))
           (=> (and (= v (mkVec (_ bv0 64) (_ bv65 64) (_ bv65 64) {data}))
                    (forall ((i (_ BitVec 64)))
                      (=> (bvult i (fld_len v)) (= (select (fld_data v) i) f))))
               (P v f))))
         {finish}
         (check-sat)"
    ))
    .expect("authored bounded nonlinear Vec source")
}
