// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #3421: Bool-sorted eq must behave as biconditional (iff).
//!
//! verification-consumer reported that `eq(a, b)` for Bool-sorted terms acted as an uninterpreted
//! function. Investigation shows ay's implementation is correct (Tseitin encoding
//! produces proper biconditional clauses), but these tests guard against regressions.

use crate::api::*;

/// Bool eq: eq(a,b) + a=true forces b=true in model.
#[test]
fn test_bool_eq_biconditional_3421() {
    let mut solver = Solver::new(Logic::QfUf);

    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);

    // Assert a = b
    let eq = solver.eq(a, b);
    solver.assert_term(eq);

    // Assert a = true  (mk_eq simplifies (= a true) to just a)
    let t = solver.bool_const(true);
    let a_true = solver.eq(a, t);
    solver.assert_term(a_true);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model = solver
        .model()
        .expect("Expected model for SAT result")
        .into_inner();
    let a_val = model.bool_val("a").expect("a should be in model");
    let b_val = model.bool_val("b").expect("b should be in model");

    assert!(a_val, "a should be true");
    assert!(b_val, "b should be true (eq(a,b) asserted and a=true)");
}

/// Bool eq constrains in the false direction too.
#[test]
fn test_bool_eq_biconditional_false_3421() {
    let mut solver = Solver::new(Logic::QfUf);

    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);

    let eq = solver.eq(a, b);
    solver.assert_term(eq);

    let f = solver.bool_const(false);
    let a_false = solver.eq(a, f);
    solver.assert_term(a_false);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model = solver
        .model()
        .expect("Expected model for SAT result")
        .into_inner();
    let a_val = model.bool_val("a").expect("a should be in model");
    let b_val = model.bool_val("b").expect("b should be in model");

    assert!(!a_val, "a should be false");
    assert!(!b_val, "b should be false (eq(a,b) asserted and a=false)");
}

/// Bool eq with conflicting assignments is UNSAT.
#[test]
fn test_bool_eq_conflict_unsat_3421() {
    let mut solver = Solver::new(Logic::QfUf);

    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);

    let eq = solver.eq(a, b);
    solver.assert_term(eq);

    let t = solver.bool_const(true);
    let a_true = solver.eq(a, t);
    solver.assert_term(a_true);

    let f = solver.bool_const(false);
    let b_false = solver.eq(b, f);
    solver.assert_term(b_false);

    assert!(solver.check_sat().is_unsat());
}

/// Bool eq with compound (non-variable) Bool terms (verification-consumer pattern).
#[test]
fn test_bool_eq_compound_expr_3421() {
    let mut solver = Solver::new(Logic::QfUf);

    let p = solver.declare_const("p", Sort::Bool);
    let q = solver.declare_const("q", Sort::Bool);
    let result = solver.declare_const("result", Sort::Bool);

    let p_and_q = solver.and(p, q);
    let eq = solver.eq(result, p_and_q);
    solver.assert_term(eq);

    let t1 = solver.bool_const(true);
    let p_true = solver.eq(p, t1);
    solver.assert_term(p_true);
    let t2 = solver.bool_const(true);
    let q_true = solver.eq(q, t2);
    solver.assert_term(q_true);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let model = solver
        .model()
        .expect("Expected model for SAT result")
        .into_inner();
    let result_val = model.bool_val("result").expect("result should be in model");
    assert!(
        result_val,
        "result should be true (eq(result, p AND q) with p=q=true)"
    );
}

/// Bool eq via SMT-LIB frontend path.
#[test]
fn test_bool_eq_smtlib_3421() {
    use crate::executor::Executor;
    use ay_frontend::parse;

    let input = r#"
        (set-logic QF_UF)
        (set-option :produce-models true)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (= a b))
        (assert a)
        (check-sat)
        (get-value (b))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].contains("true"),
        "b must be true when a=b and a is true, got: {}",
        outputs[1]
    );
}

/// Bool eq with push/pop incremental solving.
#[test]
fn test_bool_eq_incremental_push_pop_3421() {
    use crate::executor::Executor;
    use ay_frontend::parse;

    let input = r#"
        (set-logic QF_UF)
        (set-option :produce-models true)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (= a b))
        (push 1)
        (assert a)
        (check-sat)
        (get-value (b))
        (pop 1)
        (push 1)
        (assert (not a))
        (check-sat)
        (get-value (b))
        (pop 1)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].contains("true"),
        "b must be true when a=b and a=true, got: {}",
        outputs[1]
    );
    assert_eq!(outputs[2], "sat");
    assert!(
        outputs[3].contains("false"),
        "b must be false when a=b and a=false, got: {}",
        outputs[3]
    );
}

/// Bool eq between a variable and a UF predicate (verification-consumer pattern).
#[test]
fn test_bool_eq_uf_predicate_3421() {
    use crate::executor::Executor;
    use ay_frontend::parse;

    let input = r#"
        (set-logic QF_UF)
        (set-option :produce-models true)
        (declare-sort U 0)
        (declare-const x U)
        (declare-fun p (U) Bool)
        (declare-const result Bool)
        (assert (= result (p x)))
        (assert (p x))
        (check-sat)
        (get-value (result))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].contains("true"),
        "result must be true when result=(p x) and (p x) asserted, got: {}",
        outputs[1]
    );
}
