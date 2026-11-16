// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::api::{Logic, Solver, Tactic};

#[test]
fn owned_solve_eqs_reconstructs_reverse_integer_definitions_and_replays_source() {
    let mut solver = Solver::new(Logic::All);
    let x = solver.declare_const("equation_x", Sort::Int);
    let y = solver.declare_const("equation_y", Sort::Int);
    let two = solver.int_const(2);
    let five = solver.int_const(5);
    let sum = solver.add(y, two);
    let roots = [solver.eq(x, sum), solver.eq(y, five)];
    let mut goals = solver
        .apply_tactic_subgoals_converted(
            &Tactic::Simplify
                .then(Tactic::SolveEqs)
                .then(Tactic::SolveEqs),
            &roots,
            0,
            None,
        )
        .unwrap();
    let goal = goals.remove(0);
    assert_eq!(goal.formulas.as_slice(), &[] as &[crate::api::Term]);
    assert_eq!(goal.depth, 3);
    let model = solver
        .convert_tactic_model(goal.model_converter.as_ref().unwrap(), &Model::empty())
        .unwrap();
    assert_eq!(model.int_val("equation_x"), Some(&7.into()));
    assert_eq!(model.int_val("equation_y"), Some(&5.into()));

    #[cfg(any(
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    if let Some(normalized) = bounded_reference(
        "(set-logic QF_LIA)\n(declare-const equation_x Int)\n(declare-const equation_y Int)\n(assert (= equation_x (+ equation_y 2)))\n(assert (= equation_y 5))\n(check-sat-using (then simplify solve-eqs smt))\n(get-value (equation_x equation_y))\n",
        "owned solve-eqs reconstruction") {
        assert_eq!(normalized, "sat ((equation_x 7) (equation_y 5))");
    }
}

#[test]
fn owned_solve_eqs_materializes_free_defaults_and_refuses_a_violated_residual() {
    let mut solver = Solver::new(Logic::All);
    let x = solver.declare_const("equation_x", Sort::Int);
    let y = solver.declare_const("equation_y", Sort::Int);
    let two = solver.int_const(2);
    let sum = solver.add(y, two);
    let roots = [solver.eq(x, sum)];
    let goals = solver
        .apply_tactic_subgoals_converted(&Tactic::SolveEqs, &roots, 0, None)
        .unwrap();
    let converter = goals[0].model_converter.as_ref().unwrap();
    let model = solver
        .convert_tactic_model(converter, &Model::empty())
        .unwrap();
    assert_eq!(model.int_val("equation_y"), Some(&0.into()));
    assert_eq!(model.int_val("equation_x"), Some(&2.into()));

    let p = solver.bool_var("equation_residual");
    let roots = [roots[0], p];
    let goals = solver
        .apply_tactic_subgoals_converted(&Tactic::SolveEqs, &roots, 0, None)
        .unwrap();
    assert!(solver
        .convert_tactic_model(goals[0].model_converter.as_ref().unwrap(), &Model::empty())
        .is_err());
    let mut witness = Model::empty();
    witness.bool_values.insert("equation_residual".into(), true);
    assert!(solver
        .convert_tactic_model(goals[0].model_converter.as_ref().unwrap(), &witness)
        .is_ok());
}

#[test]
fn owned_solve_eqs_transports_exact_rational_wide_bv_field_and_boolean_values() {
    let mut solver = Solver::new(Logic::All);
    let field = ay_core::FiniteFieldSort::new(7).unwrap();
    let real = solver.declare_const("equation_real", Sort::Real);
    let bv = solver.declare_const("equation_bv", Sort::BitVec(ay_core::BitVecSort::new(137)));
    let ff = solver.declare_const("equation_field", Sort::FiniteField(field));
    let p = solver.bool_var("equation_p");
    let q = solver.bool_var("equation_q");
    let third = solver.rational_const(1, 3);
    let wide: num_bigint::BigInt = (num_bigint::BigInt::from(1u32) << 135usize) + 1u32;
    let bits = solver.bv_const_bigint(&wide, 137);
    let four = solver.finite_field_const(&4.into(), field);
    let negative = solver.not(q);
    let roots = [
        solver.eq(real, third),
        solver.eq(bv, bits),
        solver.eq(ff, four),
        solver.eq(p, negative),
        q,
    ];
    let goals = solver
        .apply_tactic_subgoals_converted(&Tactic::SolveEqs, &roots, 0, None)
        .unwrap();
    let mut witness = Model::empty();
    witness.bool_values.insert("equation_q".into(), true);
    let model = solver
        .convert_tactic_model(goals[0].model_converter.as_ref().unwrap(), &witness)
        .unwrap();
    assert_eq!(
        model.real_val("equation_real"),
        Some(&num_rational::BigRational::new(1.into(), 3.into()))
    );
    assert_eq!(model.bv_val("equation_bv"), Some((wide, 137)));
    assert_eq!(
        model.finite_field_val("equation_field"),
        Some(&ModelValue::FiniteField { value: 4, field })
    );
    assert_eq!(model.bool_val("equation_p"), Some(false));
    assert_eq!(model.bool_val("equation_q"), Some(true));
}
