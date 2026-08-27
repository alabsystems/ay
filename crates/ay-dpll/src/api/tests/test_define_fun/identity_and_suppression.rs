// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn native_constant_and_fresh_variable_apis_reject_reserved_identities() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();

    for name in ["__ay_ext_diff!0", "select"] {
        assert!(matches!(
            solver.try_declare_const(name, Sort::Int),
            Err(SolverError::InvalidArgument {
                operation: "declare_const",
                ..
            })
        ));
    }
    assert!(matches!(
        solver.try_declare_const_with_fresh_identity(
            "display-name",
            "__ay_ext_diff!adapter",
            Sort::Int,
        ),
        Err(SolverError::InvalidArgument {
            operation: "declare_const_with_fresh_identity",
            ..
        })
    ));
    assert!(matches!(
        solver.try_fresh_var("__ay", Sort::Int),
        Err(SolverError::InvalidArgument {
            operation: "fresh_var",
            ..
        })
    ));

    // `let` is lexical syntax, not a core structural operator identity, and a
    // prefix only becomes reserved when its generated `<prefix>_<id>` name is.
    assert!(solver.try_declare_const("let", Sort::Int).is_ok());
    assert!(solver.try_fresh_var("select", Sort::Int).is_ok());
}

#[test]
fn native_function_definition_apis_reject_reserved_identities() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();

    for name in ["__ay_reserved_definition", "select"] {
        assert!(matches!(
            solver.try_define_fun(name, &[], Sort::Int, |solver, _| {
                Ok(solver.int_const(0))
            }),
            Err(SolverError::InvalidArgument {
                operation: "define_fun",
                ..
            })
        ));

        let body = solver.int_const(0);
        assert!(matches!(
            solver.try_define_fun_body(name, &[], Sort::Int, body),
            Err(SolverError::InvalidArgument {
                operation: "define_fun",
                ..
            })
        ));
    }
}

/// `suppress_definitional_adoption` keeps a defining `forall` asserted
/// verbatim instead of discharging it into an exact macro, so the head stays
/// a real UF whose applications survive as E-matching triggers — the
/// Hilbert-`choose` embedders' contract (deductive-checks PATH-B marks its choose
/// axioms `no_mbqi`, and adoption would expand away both the axiom's trigger
/// and the ground witness it is meant to match).
#[test]
fn suppressed_definitional_forall_stays_asserted_and_uninterpreted() {
    let mut solver = Solver::try_new(Logic::Uflia).unwrap();
    solver.suppress_definitional_adoption("native_positive");
    let predicate = solver
        .try_declare_fun("native_positive", &[Sort::Int], Sort::Bool)
        .unwrap();
    let parameter = solver.fresh_var("native_definition_x", Sort::Int);
    let application = solver.try_apply(&predicate, &[parameter]).unwrap();
    let zero = solver.int_const(0);
    let positive = solver.try_gt(parameter, zero).unwrap();
    let definition = solver.try_eq(application, positive).unwrap();
    let axiom = solver
        .try_forall_with_triggers(&[parameter], definition, &[&[application]])
        .unwrap();

    solver.try_assert_term(axiom).unwrap();

    assert!(
        !solver.defined_funs.contains_key("native_positive"),
        "a suppressed head must not be adopted as a macro"
    );
    assert_eq!(
        solver.assertions(),
        vec![axiom],
        "the defining forall stays asserted verbatim"
    );

    // The definition remains fully authoritative through the quantifier.
    let one = solver.int_const(1);
    let at_one = solver.try_apply(&predicate, &[one]).unwrap();
    let not_at_one = solver.try_not(at_one).unwrap();
    solver.try_assert_term(not_at_one).unwrap();
    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "not(native_positive(1)) contradicts the asserted definition: {result:?}"
    );
}
