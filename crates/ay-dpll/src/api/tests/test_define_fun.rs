// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for define-fun API (#8613).

use num_bigint::BigInt;

use ay_core::term::TermData;

use crate::api::*;

fn has_validated_sat_model(solver: &mut Solver, label: &str) -> bool {
    let result = solver.check_sat();
    assert!(
        !result.is_unsat(),
        "{label}: expected SAT or Unknown, got {result:?}"
    );
    result.is_sat() && result.was_model_validated()
}

fn assert_private_native_constant_identity(solver: &Solver, surface: &str, term: Term) {
    let context = solver.executor.context();
    let core_name = match context.terms.get(term.id()) {
        TermData::Var(name, _) => name,
        other => panic!("native constant must be a Var, got {other:?}"),
    };
    let info = context
        .symbol_info(surface)
        .expect("native constant symbol metadata");
    assert_ne!(core_name, surface);
    assert_eq!(info.internal_name.as_deref(), Some(core_name.as_str()));
    assert_eq!(context.symbol_identity_name(surface, info), core_name);
    assert_eq!(
        context.effective_declaration_kind(info.declaration_id()),
        Some(ay_frontend::DeclarationKind::Uninterpreted)
    );
    assert!(
        context.symbol_info_by_identity(surface).is_none(),
        "the canonical theory identity must have no native constant owner"
    );
}

/// Basic define-fun: sum(a, b) = a + b, verify inline expansion.
#[test]
fn test_define_fun_sum() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);

    // define-fun sum(a: Int, b: Int) -> Int = a + b
    let sum = solver
        .try_define_fun(
            "sum",
            &[("a", Sort::Int), ("b", Sort::Int)],
            Sort::Int,
            |s, params| s.try_add(params[0], params[1]),
        )
        .unwrap();

    // sum(x, 1) == 5  =>  x + 1 == 5  =>  x == 4
    let one = solver.int_const(1);
    let result = solver.try_apply(&sum, &[x, one]).unwrap();
    let five = solver.int_const(5);
    let eq = solver.try_eq(result, five).unwrap();
    solver.try_assert_term(eq).unwrap();

    if !has_validated_sat_model(&mut solver, "sum(x, 1) == 5") {
        return;
    }
    match solver.value(x) {
        Some(ModelValue::Int(v)) => assert_eq!(v, BigInt::from(4)),
        other => panic!("expected Int(4), got {other:?}"),
    }
}

/// Define-fun with Bool return: is_positive(x) = x > 0.
#[test]
fn test_define_fun_bool_return() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);

    let is_positive = solver
        .try_define_fun(
            "is_positive",
            &[("n", Sort::Int)],
            Sort::Bool,
            |s, params| {
                let zero = s.int_const(0);
                s.try_gt(params[0], zero)
            },
        )
        .unwrap();

    // assert is_positive(x) => x > 0
    let check = solver.try_apply(&is_positive, &[x]).unwrap();
    solver.try_assert_term(check).unwrap();

    // assert x < 2 => x == 1
    let two = solver.int_const(2);
    let lt = solver.try_lt(x, two).unwrap();
    solver.try_assert_term(lt).unwrap();

    let result = solver.check_sat();
    assert!(
        !result.is_unsat(),
        "is_positive(x) && x < 2 should be SAT or Unknown, got {result:?}"
    );
}

/// Nullary define-fun: constant alias.
#[test]
fn test_define_fun_nullary() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);

    // define-fun forty_two() -> Int = 42
    let forty_two = solver
        .try_define_fun(
            "forty_two",
            &[],
            Sort::Int,
            |s, _params| Ok(s.int_const(42)),
        )
        .unwrap();

    let val = solver.try_apply(&forty_two, &[]).unwrap();
    let eq = solver.try_eq(x, val).unwrap();
    solver.try_assert_term(eq).unwrap();

    if !has_validated_sat_model(&mut solver, "x == forty_two()") {
        return;
    }
    match solver.value(x) {
        Some(ModelValue::Int(v)) => assert_eq!(v, BigInt::from(42)),
        other => panic!("expected Int(42), got {other:?}"),
    }
}

/// Multiple applications of the same defined function produce correct
/// independent expansions (each application gets its own let-binding).
#[test]
fn test_define_fun_multiple_applications() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    let double = solver
        .try_define_fun("double", &[("n", Sort::Int)], Sort::Int, |s, params| {
            let two = s.int_const(2);
            s.try_mul(params[0], two)
        })
        .unwrap();

    // assert double(x) == 10 => x == 5
    let dx = solver.try_apply(&double, &[x]).unwrap();
    let ten = solver.int_const(10);
    let eq1 = solver.try_eq(dx, ten).unwrap();
    solver.try_assert_term(eq1).unwrap();

    // assert double(y) == 6 => y == 3
    let dy = solver.try_apply(&double, &[y]).unwrap();
    let six = solver.int_const(6);
    let eq2 = solver.try_eq(dy, six).unwrap();
    solver.try_assert_term(eq2).unwrap();

    if !has_validated_sat_model(&mut solver, "double(x) and double(y)") {
        return;
    }
    match solver.value(x) {
        Some(ModelValue::Int(v)) => assert_eq!(v, BigInt::from(5)),
        other => panic!("expected Int(5) for x, got {other:?}"),
    }
    match solver.value(y) {
        Some(ModelValue::Int(v)) => assert_eq!(v, BigInt::from(3)),
        other => panic!("expected Int(3) for y, got {other:?}"),
    }
}

/// Return sort mismatch is detected.
#[test]
fn test_define_fun_sort_mismatch() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();

    // Try to define a function with Bool return but Int body
    let result = solver.try_define_fun(
        "bad",
        &[("n", Sort::Int)],
        Sort::Bool,                 // declared Bool
        |_s, params| Ok(params[0]), // body is Int
    );

    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(err, SolverError::SortMismatch { .. }));
}

/// Arity mismatch on apply is detected.
#[test]
fn test_define_fun_arity_mismatch() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();

    let f = solver
        .try_define_fun(
            "f",
            &[("a", Sort::Int), ("b", Sort::Int)],
            Sort::Int,
            |s, params| s.try_add(params[0], params[1]),
        )
        .unwrap();

    let one = solver.int_const(1);
    let result = solver.try_apply(&f, &[one]); // 1 arg, expects 2
    assert!(result.is_err());
}

/// Lower-level define-fun body API supports facade translators that already
/// created parameter variables before translating the body.
#[test]
fn test_define_fun_body_api() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let n = solver.fresh_var("n", Sort::Int);
    let one = solver.int_const(1);
    let body = solver.try_add(n, one).unwrap();

    let inc = solver
        .try_define_fun_body("inc", &[("n", n)], Sort::Int, body)
        .unwrap();

    let result = solver.try_apply(&inc, &[x]).unwrap();
    assert!(
        matches!(solver.term_kind(result), TermKind::App { name, .. } if name == "+"),
        "define-fun application should be structurally inlined"
    );
    let five = solver.int_const(5);
    let eq = solver.try_eq(result, five).unwrap();
    solver.try_assert_term(eq).unwrap();

    if !has_validated_sat_model(&mut solver, "inc(x) == 5") {
        return;
    }
    match solver.value(x) {
        Some(ModelValue::Int(v)) => assert_eq!(v, BigInt::from(4)),
        other => panic!("expected Int(4), got {other:?}"),
    }
}

#[test]
fn test_define_fun_body_rejects_non_variable_param() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let one = solver.int_const(1);

    let result = solver.try_define_fun_body("bad", &[("n", one)], Sort::Int, one);

    assert!(matches!(
        result,
        Err(SolverError::InvalidArgument {
            operation: "define_fun",
            ..
        })
    ));
}

#[test]
fn native_api_rejects_same_name_definition_and_declaration_aliases() {
    let mut solver = Solver::try_new(Logic::QfUflia).unwrap();
    let defined = solver
        .try_define_fun("f", &[("x", Sort::Int)], Sort::Int, |_solver, params| {
            Ok(params[0])
        })
        .unwrap();

    assert!(matches!(
        solver.try_declare_fun("f", &[Sort::Bool], Sort::Bool),
        Err(SolverError::InvalidArgument {
            operation: "declare_fun",
            ..
        })
    ));
    assert!(matches!(
        solver.try_define_fun("f", &[("x", Sort::Bool)], Sort::Bool, |_solver, params| {
            Ok(params[0])
        }),
        Err(SolverError::InvalidArgument {
            operation: "define_fun",
            ..
        })
    ));

    let one = solver.int_const(1);
    assert_eq!(solver.try_apply(&defined, &[one]).unwrap(), one);

    let declared = solver
        .try_declare_fun("g", &[Sort::Int], Sort::Int)
        .unwrap();
    assert!(matches!(
        solver.try_declare_fun("g", &[Sort::Bool], Sort::Bool),
        Err(SolverError::InvalidArgument {
            operation: "declare_fun",
            ..
        })
    ));
    assert!(matches!(
        solver.try_define_fun("g", &[("x", Sort::Bool)], Sort::Bool, |_solver, params| {
            Ok(params[0])
        }),
        Err(SolverError::InvalidArgument {
            operation: "define_fun",
            ..
        })
    ));
    assert_eq!(declared.domain(), &[Sort::Int]);
}

#[test]
fn forged_same_name_handle_cannot_select_definition_with_wrong_signature() {
    let mut solver = Solver::try_new(Logic::QfUflia).unwrap();
    solver
        .try_define_fun("f", &[("x", Sort::Int)], Sort::Int, |_solver, params| {
            Ok(params[0])
        })
        .unwrap();

    let forged = FuncDecl::new("f".to_string(), vec![Sort::Bool], Sort::Bool);
    let value = solver.bool_const(true);
    assert!(matches!(
        solver.try_apply(&forged, &[value]),
        Err(SolverError::InvalidArgument {
            operation: "apply",
            ..
        })
    ));
}

#[test]
fn forged_same_name_handle_cannot_select_definition_with_exact_signature() {
    let mut solver = Solver::try_new(Logic::QfUflia).unwrap();
    solver
        .try_define_fun("f", &[("x", Sort::Int)], Sort::Int, |_solver, params| {
            Ok(params[0])
        })
        .unwrap();

    let forged = FuncDecl::new("f".to_string(), vec![Sort::Int], Sort::Int);
    let value = solver.int_const(1);
    assert!(matches!(
        solver.try_apply(&forged, &[value]),
        Err(SolverError::InvalidArgument {
            operation: "apply",
            ..
        })
    ));
}

#[test]
fn forged_undeclared_function_handle_cannot_create_an_application() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    let forged = FuncDecl::new("missing".to_string(), vec![Sort::Int], Sort::Int);
    let value = solver.int_const(1);
    assert!(matches!(
        solver.try_apply(&forged, &[value]),
        Err(SolverError::InvalidArgument {
            operation: "apply",
            ..
        })
    ));
}

#[test]
fn define_fun_body_builder_cannot_introduce_same_name_declaration() {
    let mut solver = Solver::try_new(Logic::QfUflia).unwrap();
    let result = solver.try_define_fun("f", &[("x", Sort::Int)], Sort::Int, |solver, params| {
        solver.try_declare_fun("f", &[Sort::Bool], Sort::Bool)?;
        Ok(params[0])
    });

    assert!(matches!(
        result,
        Err(SolverError::InvalidArgument {
            operation: "define_fun",
            ..
        })
    ));
}

#[test]
fn reset_assertions_preserves_inline_function_definitions() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let increment = solver
        .try_define_fun(
            "increment",
            &[("x", Sort::Int)],
            Sort::Int,
            |solver, params| {
                let one = solver.int_const(1);
                solver.try_add(params[0], one)
            },
        )
        .unwrap();

    solver.try_reset_assertions().unwrap();

    let two = solver.int_const(2);
    let applied = solver.try_apply(&increment, &[two]).unwrap();
    assert!(
        matches!(solver.term_kind(applied), TermKind::App { name, .. } if name == "+"),
        "reset-assertions must not turn a defined function into an uninterpreted application"
    );
    let three = solver.int_const(3);
    let equality = solver.try_eq(applied, three).unwrap();
    solver.try_assert_term(equality).unwrap();
    assert!(!solver.check_sat().is_unsat());
}

#[test]
fn repeated_native_constant_declaration_is_idempotent() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let first = solver.declare_const("x", Sort::Int);
    let second = solver.declare_const("x", Sort::Int);
    assert_eq!(first, second);
}

#[test]
fn ordinary_native_map_target_constant_has_private_core_and_public_keys() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    solver.try_push().unwrap();
    let constant = solver.try_declare_const("div", Sort::Int).unwrap();
    solver.try_pop().unwrap();

    assert_private_native_constant_identity(&solver, "div", constant);
    assert!(
        solver.executor.context().symbol_info("div").is_some(),
        "native declarations remain global across assertion-scope pop"
    );

    let seven = solver.int_const(7);
    let equality = solver.try_eq(constant, seven).unwrap();
    solver.try_assert_term(equality).unwrap();
    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_sat());
    let model = solver
        .try_get_model_for_consumer()
        .expect("validated native constant model");
    assert_eq!(model.model().int_val_i64("div"), Some(7));

    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let declaration = artifact
        .declarations
        .iter()
        .find(|declaration| declaration.term == constant.id() && declaration.name == "div")
        .expect("public declaration with private core identity");
    assert!(declaration.core_name.starts_with("__ay_overload_"));
    assert!(matches!(
        solver.terms().get(constant.id()),
        TermData::Var(core_name, _) if core_name == &declaration.core_name
    ));
    assert!(artifact
        .declarations
        .iter()
        .all(|declaration| !declaration.name.starts_with("__ay_overload_")));
    let replay = Solver::replay_native_replay_artifact(&artifact)
        .expect("public native constant replay key remains valid");
    assert!(replay.result.result().is_sat());
    let replay_from_json = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("private-core native constant JSON replay remains valid");
    assert!(replay_from_json.result.result().is_sat());
}

#[test]
fn fresh_identity_native_map_target_constant_has_private_core_and_identity_keys() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let constant = solver
        .try_declare_const_with_fresh_identity("adapter-display-div", "mod", Sort::Int)
        .unwrap();

    assert_private_native_constant_identity(&solver, "mod", constant);
    let nine = solver.int_const(9);
    let equality = solver.try_eq(constant, nine).unwrap();
    solver.try_assert_term(equality).unwrap();
    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_sat());
    let model = solver
        .try_get_model_for_consumer()
        .expect("validated fresh-identity model");
    assert_eq!(model.model().int_val_i64("mod"), Some(9));

    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let declaration = artifact
        .declarations
        .iter()
        .find(|declaration| declaration.term == constant.id() && declaration.name == "mod")
        .expect("identity-name declaration with private core identity");
    assert!(declaration.core_name.starts_with("__ay_overload_"));
    assert!(matches!(
        solver.terms().get(constant.id()),
        TermData::Var(core_name, _) if core_name == &declaration.core_name
    ));
    assert!(artifact
        .declarations
        .iter()
        .all(|declaration| declaration.name != "adapter-display-div"));
    let replay = Solver::replay_native_replay_artifact(&artifact)
        .expect("documented identity-name replay key remains valid");
    assert!(replay.result.result().is_sat());
    let replay_from_json = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("fresh identity-name private-core JSON replay remains valid");
    assert!(replay_from_json.result.result().is_sat());
}

#[test]
fn repeated_native_constant_uses_its_exact_identity_after_function_alias() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let constant = solver.declare_const("surface", Sort::Int);
    let function = solver
        .try_declare_fun("private_surface", &[Sort::Int], Sort::Int)
        .unwrap();
    solver
        .try_register_native_function_alias("surface", &function)
        .unwrap();

    assert_eq!(solver.declare_const("surface", Sort::Int), constant);
}

#[test]
fn native_function_alias_rejects_forged_declaration_handles() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let missing = FuncDecl::new("missing".to_string(), vec![Sort::Int], Sort::Int);
    assert!(matches!(
        solver.try_register_native_function_alias("surface", &missing),
        Err(SolverError::InvalidArgument {
            operation: "register_native_function_alias",
            ..
        })
    ));

    let declared = solver
        .try_declare_fun("actual", &[Sort::Int], Sort::Int)
        .unwrap();
    let wrong_signature = FuncDecl::new(declared.name().to_string(), vec![Sort::Bool], Sort::Bool);
    assert!(matches!(
        solver.try_register_native_function_alias("surface", &wrong_signature),
        Err(SolverError::InvalidArgument {
            operation: "register_native_function_alias",
            ..
        })
    ));

    let exact_signature = FuncDecl::new(declared.name().to_string(), vec![Sort::Int], Sort::Int);
    let one = solver.int_const(1);
    assert!(matches!(
        solver.try_apply(&exact_signature, &[one]),
        Err(SolverError::InvalidArgument {
            operation: "apply",
            ..
        })
    ));
    assert!(matches!(
        solver.try_register_native_function_alias("surface", &exact_signature),
        Err(SolverError::InvalidArgument {
            operation: "register_native_function_alias",
            ..
        })
    ));
    assert!(matches!(
        solver.try_register_native_public_function_alias(
            "surface",
            &exact_signature,
            vec![ay_frontend::PublicSort::Core(Sort::Int)],
            ay_frontend::PublicSort::Core(Sort::Int),
        ),
        Err(SolverError::InvalidArgument {
            operation: "register_native_public_function_alias",
            ..
        })
    ));
}

#[test]
fn native_function_handles_reject_same_signature_reincarnations_after_reset() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let stale = solver
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .unwrap();

    solver.try_reset().unwrap();
    let current = solver
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .unwrap();
    let one = solver.int_const(1);

    assert!(matches!(
        solver.try_apply(&stale, &[one]),
        Err(SolverError::InvalidArgument {
            operation: "apply",
            ..
        })
    ));
    assert!(solver.try_apply(&current, &[one]).is_ok());
}

#[test]
fn native_function_handles_are_bound_to_their_frontend_context() {
    let mut source = Solver::try_new(Logic::All).unwrap();
    let source_function = source
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .unwrap();
    let mut target = Solver::try_new(Logic::All).unwrap();
    let target_function = target
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .unwrap();
    let one = target.int_const(1);

    assert!(matches!(
        target.try_apply(&source_function, &[one]),
        Err(SolverError::InvalidArgument {
            operation: "apply",
            ..
        })
    ));
    assert!(target.try_apply(&target_function, &[one]).is_ok());
}

#[test]
fn native_definition_handles_reject_same_signature_reincarnations_after_reset() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let stale = solver
        .try_define_fun("f", &[("x", Sort::Int)], Sort::Int, |_solver, params| {
            Ok(params[0])
        })
        .unwrap();

    solver.try_reset().unwrap();
    let current = solver
        .try_define_fun("f", &[("x", Sort::Int)], Sort::Int, |_solver, params| {
            Ok(params[0])
        })
        .unwrap();
    let one = solver.int_const(1);

    assert!(matches!(
        solver.try_apply(&stale, &[one]),
        Err(SolverError::InvalidArgument {
            operation: "apply",
            ..
        })
    ));
    assert_eq!(solver.try_apply(&current, &[one]).unwrap(), one);
}

#[test]
fn builtin_colliding_core_name_reuse_cannot_capture_a_stale_handle() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let stale_rem = solver
        .try_declare_fun("rem", &[Sort::Int, Sort::Int], Sort::Int)
        .unwrap();
    let stale_core_name = stale_rem.core_name().to_string();

    solver.try_reset().unwrap();
    let current_div = solver
        .try_declare_fun("div", &[Sort::Int, Sort::Int], Sort::Int)
        .unwrap();
    assert_eq!(
        stale_core_name,
        current_div.core_name(),
        "reset must exercise the private-core-name reuse that used to capture stale handles"
    );

    assert!(matches!(
        solver.try_register_native_function_alias("captured", &stale_rem),
        Err(SolverError::InvalidArgument {
            operation: "register_native_function_alias",
            ..
        })
    ));
    assert!(matches!(
        solver.try_register_native_public_function_alias(
            "captured_public",
            &stale_rem,
            vec![
                ay_frontend::PublicSort::Core(Sort::Int),
                ay_frontend::PublicSort::Core(Sort::Int),
            ],
            ay_frontend::PublicSort::Core(Sort::Int),
        ),
        Err(SolverError::InvalidArgument {
            operation: "register_native_public_function_alias",
            ..
        })
    ));

    let one = solver.int_const(1);
    let current_application = solver
        .try_apply(&current_div, &[one, one])
        .expect("current declaration remains applicable");
    assert!(matches!(
        solver.try_apply(&stale_rem, &[one, one]),
        Err(SolverError::InvalidArgument {
            operation: "apply",
            ..
        })
    ));

    let replacement = solver.int_const(7);
    assert_eq!(
        solver.substitute_funs(current_application, &[stale_rem], &[replacement]),
        current_application,
        "stale identity must not rewrite a reincarnated core symbol"
    );
    assert_eq!(
        solver.substitute_funs(current_application, &[current_div], &[replacement]),
        replacement,
        "the exact current declaration remains eligible for substitution"
    );
}

#[test]
#[should_panic(expected = "already declared with sort")]
fn native_constant_rejects_same_name_at_different_sort() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let _ = solver.declare_const("x", Sort::Int);
    let _ = solver.declare_const("x", Sort::Bool);
}

#[test]
#[should_panic(expected = "already bound to a different declaration")]
fn native_constant_rejects_existing_function_name() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    let _ = solver.declare_fun("f", &[Sort::Int], Sort::Int);
    let _ = solver.declare_const("f", Sort::Int);
}

#[test]
#[should_panic(expected = "identity '__private_x' is already in use")]
fn adapter_constant_identity_must_be_unique() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let _ = solver.declare_const_with_fresh_identity("x", "__private_x", Sort::Int);
    let _ = solver.declare_const_with_fresh_identity("x", "__private_x", Sort::Bool);
}

/// The verification-consumer `__upgraded` prophecy path may refine an opaque
/// `Uninterpreted("T")` placeholder to the concrete same-named `Datatype`.
/// This one narrow metadata upgrade reuses the existing core term.
#[test]
fn native_constant_refines_uninterpreted_to_same_named_datatype() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let opaque = solver.declare_const("opt", Sort::Uninterpreted("OptionInt".to_string()));
    let option_int = Sort::Datatype(DatatypeSort::new(
        "OptionInt",
        vec![
            DatatypeConstructor::unit("None"),
            DatatypeConstructor::new(
                "Some",
                vec![DatatypeField::new("option_some_value", Sort::Int)],
            ),
        ],
    ));
    let refined = solver.declare_const("opt", option_int.clone());
    // Both surface sorts lower to `Uninterpreted("OptionInt")`, so the same
    // underlying core identity is reused rather than a fresh term minted.
    assert_eq!(opaque, refined);
    // The more informative datatype surface sort is adopted.
    assert_eq!(solver.term_sort(refined), option_int);
    // The reverse spelling likewise reuses the term, but MUST retain the more
    // informative datatype rather than downgrading its schema.
    let back = solver.declare_const("opt", Sort::Uninterpreted("OptionInt".to_string()));
    assert_eq!(back, refined);
    assert_eq!(solver.term_sort(back), option_int);
}

#[test]
#[should_panic(expected = "already declared with sort")]
fn native_constant_rejects_int_char_same_core_redeclaration() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let _ = solver.declare_const("codepoint", Sort::Int);
    let _ = solver.declare_const("codepoint", Sort::Char);
}

#[test]
#[should_panic(expected = "already declared with sort")]
fn native_constant_rejects_finite_domains_with_different_cardinality() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let _ = solver.declare_const("fd", Sort::FiniteDomain("FD".to_string(), 3));
    let _ = solver.declare_const("fd", Sort::FiniteDomain("FD".to_string(), 4));
}

#[test]
#[should_panic(expected = "already declared with sort")]
fn native_constant_rejects_type_variable_as_uninterpreted_same_name() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let _ = solver.declare_const("generic", Sort::TypeVar("T".to_string()));
    let _ = solver.declare_const("generic", Sort::Uninterpreted("T".to_string()));
}

#[test]
#[should_panic(expected = "already declared with sort")]
fn native_constant_rejects_arrays_whose_surface_elements_differ() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let chars = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Char)));
    let ints = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    let _ = solver.declare_const("array", chars);
    let _ = solver.declare_const("array", ints);
}

#[test]
#[should_panic(expected = "already declared with sort")]
fn native_constant_rejects_conflicting_same_named_datatype_schema() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let first = Sort::Datatype(DatatypeSort::new(
        "Choice",
        vec![DatatypeConstructor::unit("A")],
    ));
    let conflicting = Sort::Datatype(DatatypeSort::new(
        "Choice",
        vec![
            DatatypeConstructor::unit("A"),
            DatatypeConstructor::unit("B"),
        ],
    ));
    let _ = solver.declare_const("choice", first);
    let _ = solver.declare_const("choice", conflicting);
}

#[test]
fn adapter_display_name_cannot_alias_later_native_constant() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let adapter = solver.declare_const_with_fresh_identity("x", "__private_x", Sort::Bool);
    let native = solver.declare_const("x", Sort::Int);

    assert_ne!(adapter, native);
    assert_eq!(solver.term_sort(adapter), Sort::Bool);
    assert_eq!(solver.term_sort(native), Sort::Int);
}

#[test]
fn native_declarations_survive_assertion_scope_pop() {
    let mut solver = Solver::try_new(Logic::QfUflia).unwrap();
    solver.try_push().unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let function = solver
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .unwrap();
    solver.try_pop().unwrap();

    assert_eq!(solver.declare_const("x", Sort::Int), x);
    assert!(matches!(
        solver.try_declare_fun("f", &[Sort::Bool], Sort::Bool),
        Err(SolverError::InvalidArgument {
            operation: "declare_fun",
            ..
        })
    ));
    let one = solver.int_const(1);
    let application = solver.try_apply(&function, &[one]).unwrap();
    let equality = solver.try_eq(application, one).unwrap();
    solver.try_assert_term(equality).unwrap();
    assert!(!solver.check_sat().is_unsat());
}

#[test]
fn native_declarations_invalidate_the_preceding_decision() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();

    let _ = solver.check_sat();
    let _ = solver.declare_const("x", Sort::Int);
    assert!(matches!(solver.try_get_model(), Err(SolverError::NoResult)));

    let _ = solver.check_sat();
    let function = solver
        .try_declare_fun("private_f", &[Sort::Int], Sort::Int)
        .unwrap();
    assert!(matches!(solver.try_get_model(), Err(SolverError::NoResult)));

    let _ = solver.check_sat();
    solver
        .try_register_native_function_alias("f", &function)
        .unwrap();
    assert!(matches!(solver.try_get_model(), Err(SolverError::NoResult)));

    let _ = solver.check_sat();
    solver
        .try_register_native_function_alias("f", &function)
        .unwrap();
    assert!(
        solver.try_get_model().is_ok(),
        "an exact alias re-registration is a semantic no-op"
    );

    let _ = solver.check_sat();
    solver
        .try_define_fun(
            "identity",
            &[("x", Sort::Int)],
            Sort::Int,
            |_solver, params| Ok(params[0]),
        )
        .unwrap();
    assert!(matches!(solver.try_get_model(), Err(SolverError::NoResult)));

    let parameter = solver.declare_const("definition_parameter", Sort::Int);
    let _ = solver.check_sat();
    solver
        .try_define_fun_body("identity_body", &[("x", parameter)], Sort::Int, parameter)
        .unwrap();
    assert!(matches!(solver.try_get_model(), Err(SolverError::NoResult)));
}

#[test]
fn repeated_native_function_declaration_is_an_exact_no_op() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    let first = solver
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .unwrap();
    let event_count = solver.native_replay_events().len();
    let _ = solver.check_sat();
    let second = solver
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .unwrap();

    assert_eq!(first, second);
    assert_eq!(solver.native_replay_events().len(), event_count + 1);
    assert!(
        solver.try_get_model().is_ok(),
        "an exact primary redeclaration must preserve the preceding result"
    );
}

#[test]
fn native_definitional_forall_adopts_exact_macro_and_prints_model() {
    let mut solver = Solver::try_new(Logic::Uflia).unwrap();
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
    assert!(solver.defined_funs["native_positive"].assertion_derived);
    assert_eq!(
        solver.assertions(),
        vec![solver.wrap_term(solver.terms().true_term())]
    );

    // Later applications use the exact body rather than a disconnected UF.
    let one = solver.int_const(1);
    let at_one = solver.try_apply(&predicate, &[one]).unwrap();
    solver.try_assert_term(at_one).unwrap();
    let result = solver.check_sat();
    assert!(
        result.is_sat() && result.was_model_validated(),
        "exact definitional macro should have a certified SAT model: {result:?}"
    );
    let model = solver.try_get_model_str().unwrap();
    assert!(model.contains("define-fun native_positive"), "{model}");
    assert!(model.contains("native_definition_x"), "{model}");
}

/// A PREDICATE definition keeps REFUSING on an earlier constrained use.
///
/// Ground pre-definition applications are otherwise PINNED to their own
/// definitional instance rather than refused, but a Bool-ranged pin is an
/// equality strict UNSAT certification cannot currently reconstruct, so for
/// predicates the original refusal stands and the `forall` is left asserted.
#[test]
fn native_definitional_forall_refuses_an_earlier_constrained_use() {
    let mut solver = Solver::try_new(Logic::Uflia).unwrap();
    let predicate = solver
        .try_declare_fun("native_constrained", &[Sort::Int], Sort::Bool)
        .unwrap();
    let zero = solver.int_const(0);
    let at_zero = solver.try_apply(&predicate, &[zero]).unwrap();
    solver.try_assert_term(at_zero).unwrap();

    let parameter = solver.fresh_var("native_constrained_x", Sort::Int);
    let application = solver.try_apply(&predicate, &[parameter]).unwrap();
    let body = solver.try_gt(parameter, zero).unwrap();
    let equality = solver.try_eq(application, body).unwrap();
    let axiom = solver.try_forall(&[parameter], equality).unwrap();
    solver.try_assert_term(axiom).unwrap();

    assert!(!solver.defined_funs.contains_key("native_constrained"));
    assert_eq!(solver.assertions().last(), Some(&axiom));
}

#[test]
fn native_definitional_forall_refuses_a_discarded_raw_application() {
    let mut solver = Solver::try_new(Logic::Uflia).unwrap();
    let predicate = solver
        .try_declare_fun("native_prebuilt", &[Sort::Int], Sort::Bool)
        .unwrap();
    let zero = solver.int_const(0);
    let _retained_raw_application = solver.try_apply(&predicate, &[zero]).unwrap();

    let parameter = solver.fresh_var("native_prebuilt_x", Sort::Int);
    let application = solver.try_apply(&predicate, &[parameter]).unwrap();
    let body = solver.try_gt(parameter, zero).unwrap();
    let equality = solver.try_eq(application, body).unwrap();
    let axiom = solver.try_forall(&[parameter], equality).unwrap();
    solver.try_assert_term(axiom).unwrap();

    assert!(!solver.defined_funs.contains_key("native_prebuilt"));
    assert_eq!(solver.assertions(), vec![axiom]);
}

/// A NON-predicate definition PINS instead: the retained raw application —
/// asserted after adoption, bypassing `try_apply` expansion entirely, which is
/// the exact hazard the whole-arena refusal was protecting against — is fixed
/// at the value the definition gives it, so a contradicting claim still
/// refutes. A stranded uninterpreted `native_pinned` would have been
/// satisfiable.
#[test]
fn native_definitional_forall_pins_a_retained_ground_application() {
    let mut solver = Solver::try_new(Logic::Uflia).unwrap();
    let function = solver
        .try_declare_fun("native_pinned", &[Sort::Int], Sort::Int)
        .unwrap();
    let zero = solver.int_const(0);
    let retained_raw_application = solver.try_apply(&function, &[zero]).unwrap();

    let one = solver.int_const(1);
    let parameter = solver.fresh_var("native_pinned_x", Sort::Int);
    let application = solver.try_apply(&function, &[parameter]).unwrap();
    let body = solver.try_add(parameter, one).unwrap();
    let equality = solver.try_eq(application, body).unwrap();
    let axiom = solver.try_forall(&[parameter], equality).unwrap();
    solver.try_assert_term(axiom).unwrap();

    assert!(solver.defined_funs.contains_key("native_pinned"));
    assert_ne!(
        solver.assertions(),
        vec![axiom],
        "the quantifier is discharged, not left standing"
    );

    // `native_pinned(0)` is 1 under the definition; claim 2 through the
    // RETAINED handle and the pin must refute it.
    let two = solver.int_const(2);
    let wrong = solver.try_eq(retained_raw_application, two).unwrap();
    solver.try_assert_term(wrong).unwrap();
    let result = solver.check_sat();
    assert!(result.is_unsat(), "pin must still constrain: {result:?}");
}

/// TWIN: the same retained handle with the TRUE value stays satisfiable, so the
/// pin refutes because of the value, not because it is contradictory.
#[test]
fn native_definitional_forall_pin_admits_the_true_value() {
    let mut solver = Solver::try_new(Logic::Uflia).unwrap();
    let function = solver
        .try_declare_fun("native_pinned_ok", &[Sort::Int], Sort::Int)
        .unwrap();
    let zero = solver.int_const(0);
    let retained_raw_application = solver.try_apply(&function, &[zero]).unwrap();

    let one = solver.int_const(1);
    let parameter = solver.fresh_var("native_pinned_ok_x", Sort::Int);
    let application = solver.try_apply(&function, &[parameter]).unwrap();
    let body = solver.try_add(parameter, one).unwrap();
    let equality = solver.try_eq(application, body).unwrap();
    let axiom = solver.try_forall(&[parameter], equality).unwrap();
    solver.try_assert_term(axiom).unwrap();

    let right = solver.try_eq(retained_raw_application, one).unwrap();
    solver.try_assert_term(right).unwrap();
    let result = solver.check_sat();
    assert!(result.is_sat(), "the true value must remain: {result:?}");
}

/// NARROWNESS PIN: a pre-definition application over a VARIABLE argument cannot
/// be pinned (the enclosing quantifier's other instances are applications at
/// points no ground pin covers), so adoption keeps REFUSING there.
#[test]
fn native_definitional_forall_still_refuses_a_variable_argument_use() {
    let mut solver = Solver::try_new(Logic::Uflia).unwrap();
    let predicate = solver
        .try_declare_fun("native_varuse", &[Sort::Int], Sort::Bool)
        .unwrap();
    let subject = solver
        .try_declare_const("native_varuse_c", Sort::Int)
        .unwrap();
    let _retained_raw_application = solver.try_apply(&predicate, &[subject]).unwrap();

    let zero = solver.int_const(0);
    let parameter = solver.fresh_var("native_varuse_x", Sort::Int);
    let application = solver.try_apply(&predicate, &[parameter]).unwrap();
    let body = solver.try_gt(parameter, zero).unwrap();
    let equality = solver.try_eq(application, body).unwrap();
    let axiom = solver.try_forall(&[parameter], equality).unwrap();
    solver.try_assert_term(axiom).unwrap();

    assert!(!solver.defined_funs.contains_key("native_varuse"));
    assert_eq!(solver.assertions(), vec![axiom]);
}

#[test]
fn reset_assertions_removes_only_assertion_derived_native_definitions() {
    let mut solver = Solver::try_new(Logic::Uflia).unwrap();
    let explicit = solver
        .try_define_fun(
            "explicit_identity",
            &[("x", Sort::Int)],
            Sort::Int,
            |_solver, params| Ok(params[0]),
        )
        .unwrap();
    let predicate = solver
        .try_declare_fun("native_reset_predicate", &[Sort::Int], Sort::Bool)
        .unwrap();
    let parameter = solver.fresh_var("native_reset_x", Sort::Int);
    let application = solver.try_apply(&predicate, &[parameter]).unwrap();
    let zero = solver.int_const(0);
    let body = solver.try_gt(parameter, zero).unwrap();
    let equality = solver.try_eq(application, body).unwrap();
    let axiom = solver.try_forall(&[parameter], equality).unwrap();
    solver.try_assert_term(axiom).unwrap();
    assert!(solver.defined_funs.contains_key("native_reset_predicate"));

    solver.try_reset_assertions().unwrap();
    assert!(!solver.defined_funs.contains_key("native_reset_predicate"));
    assert!(solver.defined_funs.contains_key("explicit_identity"));
    let one = solver.int_const(1);
    assert_eq!(solver.try_apply(&explicit, &[one]).unwrap(), one);
}

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
