// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use crate::expr::Expr;
use crate::program::AYProgram;
use crate::sort::Sort;

#[test]
fn test_chc_program() {
    // Simple CHC program: prove that x stays positive
    // (declare-rel Inv (Int))
    // (rule (=> (= x 0) (Inv x)))  ; initial state
    // (rule (=> (and (Inv x) (< x 10)) (Inv (+ x 1))))  ; transition
    // (query (and (Inv x) (< x 0)))  ; error: x negative
    let mut program = AYProgram::horn();

    // Declare relation
    program.declare_rel("Inv", vec![Sort::int()]);

    // Create symbolic variable
    let x = program.declare_const("x", Sort::int());

    // Fact: x = 0 => Inv(x)
    let inv_x = Expr::var("Inv_x", Sort::bool());
    program.fact(inv_x.clone());

    // Rule: Inv(x) && x < 10 => Inv(x+1)
    let inv_next = Expr::var("Inv_next", Sort::bool());
    let cond = x.clone().int_lt(Expr::int_const(10));
    program.rule(inv_next, inv_x.clone().and(cond));

    // Query: is Inv(x) && x < 0 reachable?
    let error = inv_x.and(x.int_lt(Expr::int_const(0)));
    program.query(error);

    let output = program.to_string();
    assert!(output.contains("(set-logic HORN)"));
    assert!(output.contains("(declare-rel Inv (Int))"));
    assert!(output.contains("(rule"));
    assert!(output.contains("(query"));
}
