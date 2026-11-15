// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

pub(super) const DECLARATIONS: &str = "(declare-datatype Inner ((mkInner
       (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
       (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8))))))
     (declare-datatype Outer ((mkOuter
       (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
       (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) Inner)))))";

fn value(bad_premise: bool) -> String {
    let cells = "((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv7 8))";
    let occupied = if bad_premise {
        format!("(store {cells} (_ bv64 64) (_ bv9 8))")
    } else {
        cells.to_owned()
    };
    let empty = format!("(mkInner (_ bv0 64) (_ bv0 64) (_ bv0 64) {cells})");
    let row = format!("(mkInner (_ bv0 64) (_ bv65 64) (_ bv65 64) {occupied})");
    format!(
        "(mkOuter (_ bv0 64) (_ bv34 64) (_ bv34 64)
           (store ((as const (Array (_ BitVec 64) Inner)) {empty}) (_ bv33 64) {row}))"
    )
}

pub(super) fn nested(bad_premise: bool, expected: u8) -> QuantifiedChcProblem {
    // Authored composition of retained Vec schemas and resize-style guards,
    // not a compiler-exported harness. Only row 33 is nonempty, so the exact
    // two-index support is small while its bad cell is beyond 32 low hints.
    let input = format!(
        "(set-logic HORN)
         {DECLARATIONS}
         (declare-fun P (Outer) Bool)
         (assert (forall ((outer Outer))
           (=> (and (= outer {})
                    (forall ((r (_ BitVec 64)) (c (_ BitVec 64)))
                      (=> (and (bvult r (fld_len outer))
                               (bvult c (fld_len (select (fld_data outer) r))))
                          (= (select (fld_data (select (fld_data outer) r)) c)
                             (_ bv7 8)))))
               (P outer))))
         (assert (forall ((outer Outer) (row (_ BitVec 64)) (col (_ BitVec 64)))
           (=> (and (P outer) (= row (_ bv33 64)) (= col (_ bv64 64))
                    (bvult row (fld_len outer))
                    (bvult col (fld_len (select (fld_data outer) row)))
                    (distinct (select (fld_data (select (fld_data outer) row)) col)
                              (_ bv{expected} 8))) false)))
         (check-sat)",
        value(bad_premise),
    );
    QuantifiedChcProblem::parse_smtlib(&input).expect("bounded nested Vec source")
}

pub(super) fn bodyless(reachable: bool, extra: bool) -> QuantifiedChcProblem {
    let declaration = if extra {
        "(declare-datatype Unused ((mkUnused (unused Bool))))"
    } else {
        ""
    };
    let value = if reachable { "true" } else { "false" };
    QuantifiedChcProblem::parse_smtlib(&format!(
        "(set-logic HORN) {declaration}
         (assert (=> {value} false)) (check-sat)"
    ))
    .expect("raw bodyless query source")
}

pub(super) fn variable(expression: &ChcExpr) -> &str {
    let ChcExpr::Var(variable) = expression else {
        panic!("expected source variable")
    };
    &variable.name
}

pub(super) fn operand(expression: &ChcExpr, index: usize) -> &ChcExpr {
    let ChcExpr::Op(_, arguments) = expression else {
        panic!("expected raw source operation")
    };
    &arguments[index]
}
