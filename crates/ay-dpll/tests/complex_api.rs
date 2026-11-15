// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{Logic, ModelValue, SolveResult, Solver, SolverError, Sort};

#[test]
fn native_complex_arithmetic_preserves_exact_components() -> Result<(), SolverError> {
    let mut solver = Solver::try_new(Logic::All)?;
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let three = solver.int_const(3);
    let four = solver.int_const(4);
    let minus_three = solver.try_neg(three)?;
    let expected_real = solver.try_int_to_real(minus_three)?;
    let expected_imaginary = solver.try_int_to_real(four)?;
    let z = solver.try_complex(one, two)?;
    assert_eq!(solver.try_term_sort(z)?, Sort::Complex);
    let square = solver.try_mul(z, z)?;
    let real = solver.try_real_part(square)?;
    let imaginary = solver.try_imag_part(square)?;
    assert_eq!(solver.try_term_sort(real)?, Sort::Real);
    for (actual, expected) in [(real, expected_real), (imaginary, expected_imaginary)] {
        let equality = solver.try_eq(actual, expected)?;
        assert_eq!(solver.try_render_term_canonical(equality)?, "true");
    }
    let negated = solver.try_neg(z)?;
    let restored = solver.try_neg(negated)?;
    let equality = solver.try_eq(restored, z)?;
    assert_eq!(solver.try_render_term_canonical(equality)?, "true");
    let sum = solver.try_add_many(&[one, z, two])?;
    let difference = solver.try_sub(sum, one)?;
    let product = solver.try_mul_many(&[two, difference, three])?;
    let quotient = solver.try_div(product, two)?;
    assert_eq!(solver.try_term_sort(quotient)?, Sort::Complex);
    Ok(())
}

#[test]
fn native_complex_model_reconstructs_both_committed_components() -> Result<(), SolverError> {
    let mut solver = Solver::try_new(Logic::All)?;
    let z = solver.declare_const("z", Sort::Complex);
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let value = solver.try_complex(one, two)?;
    let equality = solver.try_eq(z, value)?;
    solver.try_assert_term(equality)?;
    let details = solver.check_sat_with_details();
    let accepted = details.accept_for_consumer();
    assert!(matches!(accepted, Ok(SolveResult::Sat)), "{details:?}");
    let Some(ModelValue::Datatype { constructor, args }) = solver.value(z) else {
        panic!("missing typed Complex model value");
    };
    assert_eq!(constructor, "complex.make");
    assert_eq!(
        args,
        vec![
            ModelValue::Real(num_rational::BigRational::from_integer(1.into())),
            ModelValue::Real(num_rational::BigRational::from_integer(2.into()))
        ]
    );
    Ok(())
}

#[test]
fn native_unused_complex_variable_has_a_typed_zero_pair_default() -> Result<(), SolverError> {
    let mut solver = Solver::try_new(Logic::All)?;
    let z = solver.declare_const("z", Sort::Complex);
    let details = solver.check_sat_with_details();
    assert!(
        matches!(details.accept_for_consumer(), Ok(SolveResult::Sat)),
        "{details:?}"
    );
    let Some(ModelValue::Datatype { constructor, args }) = solver.value(z) else {
        panic!("missing unused Complex default");
    };
    assert_eq!(constructor, "complex.make");
    assert_eq!(
        args,
        vec![
            ModelValue::Real(num_rational::BigRational::from_integer(0.into())),
            ModelValue::Real(num_rational::BigRational::from_integer(0.into()))
        ]
    );
    Ok(())
}

#[test]
fn native_complex_model_completes_an_unassigned_component() -> Result<(), SolverError> {
    let mut solver = Solver::try_new(Logic::All)?;
    let z = solver.declare_const("z", Sort::Complex);
    let real = solver.try_real_part(z)?;
    let one = solver.int_const(1);
    let one = solver.try_int_to_real(one)?;
    let equality = solver.try_eq(real, one)?;
    solver.try_assert_term(equality)?;
    let details = solver.check_sat_with_details();
    assert!(
        matches!(details.accept_for_consumer(), Ok(SolveResult::Sat)),
        "{details:?}"
    );
    let Some(ModelValue::Datatype { constructor, args }) = solver.value(z) else {
        panic!("missing partially constrained Complex value");
    };
    assert_eq!(constructor, "complex.make");
    assert_eq!(args.len(), 2);
    assert_eq!(
        args[0],
        ModelValue::Real(num_rational::BigRational::from_integer(1.into()))
    );
    assert!(matches!(args[1], ModelValue::Real(_)));
    Ok(())
}

#[test]
fn native_complex_builders_reject_wrong_sorts_and_foreign_handles() -> Result<(), SolverError> {
    let mut solver = Solver::try_new(Logic::All)?;
    let mut foreign = Solver::try_new(Logic::All)?;
    let one = solver.int_const(1);
    let boolean = solver.bool_const(true);
    let alien = foreign.int_const(1);
    let z = solver.try_complex(one, one)?;
    assert!(solver.try_complex(boolean, one).is_err());
    assert!(solver.try_real_part(boolean).is_err());
    assert!(solver.try_imag_part(boolean).is_err());
    assert!(solver.try_add(z, boolean).is_err());
    assert!(solver.try_gt(z, z).is_err());
    assert!(solver.try_int_div(z, z).is_err());
    assert!(matches!(
        solver.try_complex(one, alien),
        Err(SolverError::InvalidTermHandle { .. })
    ));
    assert!(matches!(
        solver.try_real_part(alien),
        Err(SolverError::InvalidTermHandle { .. })
    ));
    Ok(())
}

#[test]
fn native_complex_components_determine_function_arguments() -> Result<(), SolverError> {
    let mut solver = Solver::try_new(Logic::All)?;
    let x = solver.declare_const("x", Sort::Complex);
    let y = solver.declare_const("y", Sort::Complex);
    let f = solver.declare_fun("f", &[Sort::Complex], Sort::Int);
    for imaginary in [false, true] {
        let a = if imaginary {
            solver.try_imag_part(x)?
        } else {
            solver.try_real_part(x)?
        };
        let b = if imaginary {
            solver.try_imag_part(y)?
        } else {
            solver.try_real_part(y)?
        };
        let equal = solver.try_eq(a, b)?;
        solver.try_assert_term(equal)?;
    }
    let fx = solver.try_apply(&f, &[x])?;
    let fy = solver.try_apply(&f, &[y])?;
    let equal = solver.try_eq(fx, fy)?;
    let different = solver.try_not(equal)?;
    solver.try_assert_term(different)?;
    let details = solver.check_sat_with_details();
    assert!(
        matches!(details.accept_for_consumer(), Ok(SolveResult::Unsat(_))),
        "{details:?}"
    );
    Ok(())
}
