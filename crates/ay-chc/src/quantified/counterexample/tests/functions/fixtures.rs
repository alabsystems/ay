// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored shapes from MC 22278991c4's call_uf_table.rs, not captured exports.
//! A source UF witness does not establish the real callee's implementation or
//! purity; the producer, not this solver fixture, owns that abstraction claim.

use super::*;

#[derive(Clone, Copy)]
pub(super) enum Calls {
    Congruent,
    DistinctArgument,
    DistinctSymbol,
}

#[derive(Clone, Copy)]
pub(super) enum Cells {
    Filled,
    CorruptLast,
}

#[derive(Clone, Copy)]
pub(super) enum Query {
    DifferentOutputs,
    ContradictoryInput,
}

#[derive(Clone, Copy)]
pub(super) enum Point {
    Unconstrained,
    Contradiction,
}

pub(super) fn linear(calls: Calls, cells: Cells, query: Query) -> QuantifiedChcProblem {
    let second = match calls {
        Calls::Congruent => "(uf_call_0_pure gate x)",
        Calls::DistinctArgument => "(uf_call_0_pure gate (bvadd x (_ bv1 8)))",
        Calls::DistinctSymbol => "(uf_call_1_other gate x)",
    };
    let filled = "((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv7 8))";
    let data = match cells {
        Cells::Filled => filled.to_owned(),
        Cells::CorruptLast => format!("(store {filled} (_ bv64 64) (_ bv8 8))"),
    };
    let query = match query {
        Query::DifferentOutputs => "(and first (not second))",
        Query::ContradictoryInput => "(and first (not second) (= x (_ bv8 8)))",
    };
    QuantifiedChcProblem::parse_smtlib(&format!(
        "(set-logic HORN)
         (declare-fun uf_call_0_pure (Bool (_ BitVec 8)) (_ BitVec 1))
         (declare-fun uf_call_1_other (Bool (_ BitVec 8)) (_ BitVec 1))
         (declare-fun ay_qcex_0 ((_ BitVec 8)) (_ BitVec 8))
         (declare-var gate Bool) (declare-var x (_ BitVec 8))
         (declare-var first Bool) (declare-var second Bool)
         (declare-var data (Array (_ BitVec 64) (_ BitVec 8)))
         (declare-rel P (Bool (_ BitVec 8) Bool (Array (_ BitVec 64) (_ BitVec 8))))
         (declare-rel Q (Bool (_ BitVec 8) Bool Bool (Array (_ BitVec 64) (_ BitVec 8))))
         (declare-rel bad ())
         (rule (=> (and gate (= x (_ bv7 8))
             (let ((saved (uf_call_0_pure gate x))) (= first (= saved (_ bv1 1))))
             (= data {data})
             (forall ((i (_ BitVec 64)))
               (=> (bvult i (_ bv65 64)) (= (select data i) (_ bv7 8)))))
           (P gate x first data)))
         (rule (=> (and (P gate x first data) (= second (= {second} (_ bv1 1))))
           (Q gate x first second data)))
         (rule (=> (and (Q gate x first second data) {query}) bad))
         (query bad)"
    ))
    .expect("neutral ordinary UF declarations in fixedpoint source")
}

pub(super) fn grouped(point: Point) -> QuantifiedChcProblem {
    let point = match point {
        Point::Contradiction => "(= (uf_range true (_ bv33 64) (_ bv1 64)) (_ bv0 1))",
        Point::Unconstrained => "true",
    };
    QuantifiedChcProblem::parse_smtlib(&format!(
        "(set-logic HORN)
         (declare-fun uf_range (Bool (_ BitVec 64) (_ BitVec 64)) (_ BitVec 1))
         (declare-rel P ()) (declare-rel bad ())
         (rule (=> (and {point}
           (forall ((row (_ BitVec 64)) (column (_ BitVec 64)))
             (=> (and (bvult row (_ bv34 64)) (bvult column (_ bv2 64)))
               (= (uf_range true row column) (_ bv1 1))))) P))
         (rule (=> P bad)) (query bad)"
    ))
    .expect("function appearing only inside a complete joint premise")
}

pub(super) fn shadowed() -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-fun uf_saved ((_ BitVec 8)) (_ BitVec 1))
         (declare-fun P ((_ BitVec 8)) Bool)
         (assert (forall ((x (_ BitVec 8)))
           (=> (and (= x (_ bv7 8))
              (let ((saved (uf_saved x)))
                (forall ((x (_ BitVec 8)))
                  (=> (= x (_ bv3 8)) (= saved (_ bv1 1)))))) (P x))))
         (assert (forall ((x (_ BitVec 8)))
           (=> (and (P x) (not (= (uf_saved x) (_ bv1 1)))) false)))
         (check-sat)",
    )
    .expect("resolved let argument must retain the outer lexical variable")
}
