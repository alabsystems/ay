// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::Command;

#[test]
fn test_elaborate_assert_soft_records_soft_constraint() {
    let input = r#"
            (declare-const a Bool)
            (declare-const b Bool)
            (assert (or a b))
            (assert-soft (not a) :weight 3)
            (assert-soft (not b))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    // The hard `(or a b)` is the only hard assertion; softs go to soft_constraints.
    assert_eq!(
        ctx.assertions.len(),
        1,
        "soft constraints are not hard asserts"
    );
    let softs = ctx.soft_constraints();
    assert_eq!(softs.len(), 2);
    assert_eq!(softs[0].weight, 3);
    assert_eq!(softs[1].weight, 1, "default weight is 1");
}

#[test]
fn test_elaborate_assert_soft_rejects_non_bool() {
    let input = r#"
            (declare-const x Int)
            (assert-soft x :weight 1)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let mut err = None;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            err = Some(e);
        }
    }
    assert!(
        matches!(err, Some(ElaborateError::SortMismatch { .. })),
        "assert-soft on Int term must be a sort mismatch, got {err:?}"
    );
}

#[test]
fn test_elaborate_assert_soft_scoped_by_push_pop() {
    let input = r#"
            (declare-const a Bool)
            (assert-soft a :weight 1)
            (push 1)
            (assert-soft (not a) :weight 2)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.soft_constraints().len(), 2);
    assert!(ctx.pop(), "pop should succeed");
    assert_eq!(
        ctx.soft_constraints().len(),
        1,
        "pop must drop the scoped soft constraint"
    );
}

#[test]
fn test_elaborate_simple() {
    let input = r#"
            (declare-const x Int)
            (declare-const y Int)
            (assert (= x y))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn declared_function_applications_enforce_arity_and_domain_sorts() {
    for input in [
        "(declare-fun f (Int) Bool) (assert (f true))",
        "(declare-fun f (Int) Bool) (assert (f 1 2))",
        "(declare-fun f ((Array Int Int)) Bool) (assert (f 1))",
        "(declare-const c Bool) (assert (c true))",
    ] {
        let commands = parse(input).expect("ill-sorted application still parses");
        let mut ctx = Context::new();
        let error = commands
            .iter()
            .try_for_each(|command| ctx.process_command(command).map(|_| ()))
            .expect_err("declared signature mismatch must fail elaboration");
        assert!(
            matches!(
                error,
                ElaborateError::SortMismatch { .. } | ElaborateError::InvalidConstant(_)
            ),
            "expected a typed application error for `{input}`, got {error:?}"
        );
    }
}

#[test]
fn bare_symbols_reject_non_nullary_and_ambiguous_nullary_declarations() {
    for input in [
        "(declare-fun f (Int) Bool) (assert f)",
        "(declare-const c Int) (declare-const c Bool) (assert c)",
    ] {
        let commands = parse(input).expect("symbol script parses");
        let mut ctx = Context::new();
        let error = commands
            .iter()
            .try_for_each(|command| ctx.process_command(command).map(|_| ()))
            .expect_err("bare symbol must not select an inapplicable/ambiguous declaration");
        assert!(
            matches!(
                error,
                ElaborateError::InvalidConstant(_) | ElaborateError::Unsupported(_)
            ),
            "unexpected bare-symbol error for `{input}`: {error:?}"
        );
    }
}

#[test]
fn defined_function_applications_enforce_arity_and_parameter_sorts() {
    for input in [
        "(define-fun f ((x Int)) Bool true) (assert (f true))",
        "(define-fun f ((x Int)) Bool true) (assert (f))",
        "(define-fun-rec f ((x Int)) Bool true) (assert (f true))",
        "(define-funs-rec ((f ((x Int)) Bool)) (true)) (assert (f true))",
    ] {
        let commands = parse(input).expect("ill-sorted macro application still parses");
        let mut ctx = Context::new();
        let error = commands
            .iter()
            .try_for_each(|command| ctx.process_command(command).map(|_| ()))
            .expect_err("macro parameter mismatch must fail before body expansion");
        assert!(
            matches!(
                error,
                ElaborateError::SortMismatch { .. } | ElaborateError::InvalidConstant(_)
            ),
            "expected typed macro application error for `{input}`, got {error:?}"
        );
    }
}

#[test]
fn defined_function_application_coerces_int_to_real_parameter() {
    let commands = parse("(define-fun f ((x Real)) Bool (= x 1.0)) (assert (f 1))")
        .expect("well-sorted macro application parses");
    let mut ctx = Context::new();
    for command in &commands {
        ctx.process_command(command)
            .expect("Int argument must coerce to the Real parameter");
    }
    assert_eq!(ctx.terms.sort(ctx.assertions[0]), &Sort::Bool);
}

#[test]
fn defined_function_bodies_enforce_declared_result_sort() {
    for input in [
        "(define-fun f ((x Int)) Bool x)",
        "(define-fun f () Bool 0)",
        "(define-fun-rec f ((x Int)) Bool x)",
        "(define-funs-rec ((f ((x Int)) Bool)) (x))",
    ] {
        let commands = parse(input).expect("ill-sorted definition parses");
        let mut ctx = Context::new();
        let error = commands
            .iter()
            .try_for_each(|command| ctx.process_command(command).map(|_| ()))
            .expect_err("definition result-sort mismatch must fail during registration");
        assert!(
            matches!(error, ElaborateError::SortMismatch { .. }),
            "unexpected definition error for `{input}`: {error:?}"
        );
    }
}

#[test]
fn defined_function_body_coerces_int_result_to_declared_real() {
    let commands = parse("(define-fun f ((x Int)) Real x) (assert (= (f 1) 1.0))").unwrap();
    let mut ctx = Context::new();
    for command in &commands {
        ctx.process_command(command).unwrap();
    }
    assert!(ctx.terms.is_true(ctx.assertions[0]));
}

#[test]
fn declared_function_application_coerces_int_to_real_and_prefers_exact_overload() {
    let input = r#"
        (declare-fun real_pred (Real) Bool)
        (assert (real_pred 1))
        (declare-fun overloaded (Int) Bool)
        (declare-fun overloaded (Real) Int)
        (assert (overloaded 1))
    "#;
    let commands = parse(input).expect("well-sorted overload script parses");
    let mut ctx = Context::new();
    for command in &commands {
        ctx.process_command(command)
            .expect("valid applications must elaborate");
    }

    let TermData::App(_, real_args) = ctx.terms.get(ctx.assertions[0]) else {
        panic!("real_pred assertion must remain an application");
    };
    assert_eq!(ctx.terms.sort(real_args[0]), &Sort::Real);
    assert_eq!(ctx.terms.sort(ctx.assertions[1]), &Sort::Bool);
}

#[test]
fn native_function_alias_keeps_private_identity_after_int_to_real_coercion() {
    let mut ctx = Context::new();
    ctx.register_native_function_alias(
        "surface".to_string(),
        "!private-function".to_string(),
        vec![Sort::Real],
        Sort::Bool,
    )
    .expect("native alias registers");
    let commands = parse("(assert (surface 1))").expect("alias application parses");
    ctx.process_command(&commands[0])
        .expect("Int argument coerces to the Real domain");

    let TermData::App(Symbol::Named(name), args) = ctx.terms.get(ctx.assertions[0]) else {
        panic!("alias assertion must be a named application");
    };
    assert_eq!(name, "!private-function");
    assert_eq!(ctx.terms.sort(args[0]), &Sort::Real);
}

#[test]
fn overloaded_native_aliases_keep_the_selected_private_identity() {
    let mut ctx = Context::new();
    ctx.register_native_function_alias(
        "exact".to_string(),
        "!private-exact-int".to_string(),
        vec![Sort::Int],
        Sort::Bool,
    )
    .unwrap();
    ctx.register_native_function_alias(
        "exact".to_string(),
        "!private-exact-real".to_string(),
        vec![Sort::Real],
        Sort::Bool,
    )
    .unwrap();
    ctx.register_native_function_alias(
        "coercive".to_string(),
        "!private-coercive-real".to_string(),
        vec![Sort::Real],
        Sort::Bool,
    )
    .unwrap();
    ctx.register_native_function_alias(
        "coercive".to_string(),
        "!private-coercive-bool".to_string(),
        vec![Sort::Bool],
        Sort::Bool,
    )
    .unwrap();

    let commands = parse("(assert (exact 1)) (assert (coercive 1))").unwrap();
    for command in &commands {
        ctx.process_command(command).unwrap();
    }

    let TermData::App(Symbol::Named(exact_name), exact_args) = ctx.terms.get(ctx.assertions[0])
    else {
        panic!("exact overload must remain an application");
    };
    assert_eq!(exact_name, "!private-exact-int");
    assert_eq!(ctx.terms.sort(exact_args[0]), &Sort::Int);

    let TermData::App(Symbol::Named(coercive_name), coercive_args) =
        ctx.terms.get(ctx.assertions[1])
    else {
        panic!("coercive overload must remain an application");
    };
    assert_eq!(coercive_name, "!private-coercive-real");
    assert_eq!(ctx.terms.sort(coercive_args[0]), &Sort::Real);
}

#[test]
fn ordinary_overloads_get_disjoint_core_identities_and_complete_iteration() {
    let commands = parse(
        "(declare-fun f (Int) Bool) (declare-fun f (Bool) Bool) \
         (assert (f 0)) (assert (f true))",
    )
    .unwrap();
    let mut ctx = Context::new();
    for command in &commands {
        ctx.process_command(command).unwrap();
    }

    let heads: Vec<&str> = ctx
        .assertions
        .iter()
        .map(|term| match ctx.terms.get(*term) {
            TermData::App(Symbol::Named(name), _) => name.as_str(),
            other => panic!("expected declared application, got {other:?}"),
        })
        .collect();
    assert_eq!(
        heads[0], "f",
        "the first declaration keeps its surface identity"
    );
    assert!(heads[1].starts_with(INTERNAL_SYMBOL_PREFIX));
    assert_ne!(heads[0], heads[1]);
    assert_eq!(ctx.dt_surface_name(heads[1]), Some("f"));

    let overloads: Vec<_> = ctx
        .symbol_iter()
        .filter(|(name, _)| name.as_str() == "f")
        .collect();
    assert_eq!(overloads.len(), 2, "iteration must expose every signature");
    assert_eq!(overloads[0].1.arg_sorts, vec![Sort::Int]);
    assert_eq!(overloads[1].1.arg_sorts, vec![Sort::Bool]);
}

#[test]
fn result_sort_overloads_selected_by_ascription_have_disjoint_identities() {
    let commands = parse(
        "(declare-fun f (Int) Int) (declare-fun f (Int) Bool) \
         (assert (= ((as f Int) 0) 0)) (assert (not ((as f Bool) 0)))",
    )
    .unwrap();
    let mut ctx = Context::new();
    for command in &commands {
        ctx.process_command(command).unwrap();
    }

    let TermData::App(_, equality_args) = ctx.terms.get(ctx.assertions[0]) else {
        panic!("first assertion must be equality");
    };
    let int_head = equality_args
        .iter()
        .find_map(|term| match ctx.terms.get(*term) {
            TermData::App(Symbol::Named(name), _) => Some(name),
            _ => None,
        })
        .expect("qualified Int overload must be an application");
    let TermData::Not(bool_app) = ctx.terms.get(ctx.assertions[1]) else {
        panic!("second assertion must be negated");
    };
    let TermData::App(Symbol::Named(bool_head), _) = ctx.terms.get(*bool_app) else {
        panic!("qualified Bool overload must be an application");
    };
    assert_eq!(int_head, "f");
    assert_ne!(int_head, bool_head);
    assert_eq!(ctx.dt_surface_name(bool_head), Some("f"));
}

#[test]
fn pop_removes_only_scoped_overload_and_restores_outer_declaration() {
    let commands = parse(
        "(declare-fun f (Int) Bool) (push 1) \
         (declare-fun f (Bool) Bool) (assert (f true)) (pop 1) (assert (f 0))",
    )
    .unwrap();
    let mut ctx = Context::new();
    for command in &commands {
        ctx.process_command(command).unwrap();
    }

    let remaining: Vec<_> = ctx
        .symbol_iter()
        .filter(|(name, _)| name.as_str() == "f")
        .collect();
    assert_eq!(remaining.len(), 1);
    assert_eq!(remaining[0].1.arg_sorts, vec![Sort::Int]);
    assert_eq!(remaining[0].1.internal_name, None);

    let bad = parse("(assert (f false))").unwrap();
    assert!(
        ctx.process_command(&bad[0]).is_err(),
        "popped Bool overload must no longer resolve"
    );
}

#[test]
fn multi_pop_underflow_is_atomic() {
    let setup = parse(
        "(declare-sort Outer 0) (push 1) (define-sort Scoped () Int) \
         (declare-const local Bool) (assert local) (assert-soft local) (maximize 1)",
    )
    .expect("scope setup parses");
    let mut ctx = Context::new();
    for command in &setup {
        ctx.process_command(command).expect("scope setup executes");
    }

    let before = (
        ctx.scopes.len(),
        ctx.assertions.len(),
        ctx.soft_constraints.len(),
        ctx.objectives.len(),
    );
    let error = ctx
        .process_command(&parse("(pop 2)").expect("pop parses")[0])
        .expect_err("pop beyond the current depth must fail");
    assert!(matches!(error, ElaborateError::ScopeUnderflow));
    assert_eq!(
        (
            ctx.scopes.len(),
            ctx.assertions.len(),
            ctx.soft_constraints.len(),
            ctx.objectives.len(),
        ),
        before,
        "a failed multi-pop must not consume a valid scope prefix"
    );
    assert!(ctx.sort_defs.contains_key("Outer"));
    assert!(ctx.sort_defs.contains_key("Scoped"));
    assert!(ctx.symbols.contains_key("local"));

    ctx.process_command(&parse("(pop 1)").expect("pop parses")[0])
        .expect("the preserved scope remains poppable");
    assert!(ctx.sort_defs.contains_key("Outer"));
    assert!(!ctx.sort_defs.contains_key("Scoped"));
    assert!(!ctx.symbols.contains_key("local"));
    assert!(ctx.assertions.is_empty());
    assert!(ctx.soft_constraints.is_empty());
    assert!(ctx.objectives.is_empty());
}

#[test]
fn oversized_push_is_rejected_before_allocating_or_changing_depth() {
    let mut ctx = Context::new();
    let error = ctx
        .process_command(&Command::Push(u32::MAX))
        .expect_err("compact push amplification must be bounded");
    assert!(matches!(error, ElaborateError::Unsupported(_)));
    assert!(ctx.scopes.is_empty());

    ctx.process_command(&Command::Push(2))
        .expect("ordinary scope depth remains usable after rejection");
    assert_eq!(ctx.scopes.len(), 2);
    ctx.process_command(&Command::Pop(2))
        .expect("ordinary multi-pop succeeds");
    assert!(ctx.scopes.is_empty());
}

#[test]
fn sort_declarations_share_one_collision_checked_namespace() {
    for input in [
        "(declare-sort S 0) (declare-sort S 0)",
        "(declare-sort S 0) (define-sort S () Int)",
        "(define-sort S () Int) (declare-sort S 0)",
        "(define-sort S (T) T) (define-sort S () Int)",
        "(declare-datatype S ((mk-S))) (define-sort S () Int)",
    ] {
        let commands = parse(input).expect("sort collision script parses");
        let mut ctx = Context::new();
        ctx.process_command(&commands[0])
            .expect("first sort binding succeeds");
        let error = ctx
            .process_command(&commands[1])
            .expect_err("second sort binding must not overwrite the first");
        assert!(
            matches!(error, ElaborateError::SortRedeclaration(ref name) if name == "S"),
            "expected SortRedeclaration for `{input}`, got {error:?}"
        );
    }
}

#[test]
fn unsupported_declare_sort_arity_and_duplicate_alias_parameters_fail_without_mutation() {
    for input in ["(declare-sort Higher 1)", "(define-sort Higher (T T) T)"] {
        let command = parse(input).expect("sort command parses");
        let mut ctx = Context::new();
        assert!(
            ctx.process_command(&command[0]).is_err(),
            "unsupported sort declaration must fail: {input}"
        );
        assert!(!ctx.sort_defs.contains_key("Higher"));
        assert!(!ctx.parametric_sort_defs.contains_key("Higher"));
    }
}

#[test]
fn sort_synonym_recursion_guard_is_restored_after_unwind() {
    let mut ctx = Context::new();
    let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        ctx.with_sort_synonym_expansion("Outer".to_string(), |context| {
            context.with_sort_synonym_expansion("Alias".to_string(), |_| {
                panic!("injected recursive sort elaboration panic");
            });
        });
    }));
    assert!(unwind.is_err());
    assert!(
        ctx.expanding_sort_synonyms.is_empty(),
        "every active synonym guard must unwind with the panic"
    );

    let valid = parse("(define-sort Alias (T) T) (declare-const value (Alias Int))")
        .expect("valid synonym script parses");
    for command in &valid {
        ctx.process_command(command)
            .expect("a caught panic must not poison later synonym expansion");
    }
    assert_eq!(ctx.symbols["value"].sort, Sort::Int);
}

#[test]
fn native_global_declaration_preserves_options_and_survives_scoped_overload_pop() {
    let mut ctx = Context::new();
    let setup = parse("(declare-fun f (Int) Bool) (push 1) (declare-fun f (Bool) Bool)")
        .expect("parse setup");
    for command in &setup {
        ctx.process_command(command).expect("execute setup");
    }

    let native = parse("(declare-fun f (Real) Bool)").expect("parse native declaration");
    ctx.execute_native_global_declaration(&native[0])
        .expect("execute native declaration");
    assert_eq!(
        ctx.get_option(":global-declarations"),
        Some(&OptionValue::Bool(false))
    );
    assert_eq!(
        ctx.get_option(":global-decls"),
        Some(&OptionValue::Bool(false))
    );

    ctx.process_command(&parse("(pop 1)").expect("parse pop")[0])
        .expect("pop scope");
    let remaining: Vec<_> = ctx
        .symbol_iter()
        .filter(|(name, _)| name.as_str() == "f")
        .map(|(_, info)| info.arg_sorts.clone())
        .collect();
    assert_eq!(remaining, vec![vec![Sort::Int], vec![Sort::Real]]);
}

#[test]
fn native_global_declaration_tracking_restores_after_unwind() {
    let mut ctx = Context::new();
    ctx.push();
    let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        ctx.with_native_global_declaration_tracking(|_| panic!("injected native panic"));
    }));
    assert!(unwind.is_err());

    let scoped = parse("(declare-const scoped Bool)").expect("parse scoped declaration");
    ctx.process_command(&scoped[0])
        .expect("execute scoped declaration after unwind");
    assert!(ctx.symbols.contains_key("scoped"));
    assert!(ctx.pop());
    assert!(
        !ctx.symbols.contains_key("scoped"),
        "a panic in native tracking must not make later declarations global"
    );
}

#[test]
fn ordinary_overload_identity_skips_native_alias_collision() {
    let mut ctx = Context::new();
    let base = parse("(declare-fun f (Int) Bool)").expect("parse base declaration");
    ctx.process_command(&base[0])
        .expect("declare base overload");

    ctx.register_native_global_function_alias(
        "native_alias".to_string(),
        "__ay_overload_0".to_string(),
        vec![Sort::Int],
        Sort::Bool,
    )
    .expect("register colliding native identity");

    let overload = parse("(declare-fun f (Bool) Bool)").expect("parse overload");
    ctx.process_command(&overload[0]).expect("declare overload");
    let bool_overload = ctx
        .symbol_iter()
        .find(|(name, info)| name.as_str() == "f" && info.arg_sorts == vec![Sort::Bool])
        .expect("Bool overload");
    assert_eq!(
        bool_overload.1.internal_name.as_deref(),
        Some("__ay_overload_1")
    );
}

#[test]
fn same_name_native_alias_is_an_exact_no_op() {
    let mut ctx = Context::new();
    let declaration = parse("(declare-fun same_name (Int) Bool)").expect("parse declaration");
    ctx.execute_native_global_declaration(&declaration[0])
        .expect("declare native function");
    ctx.register_native_global_function_alias(
        "same_name".to_string(),
        "same_name".to_string(),
        vec![Sort::Int],
        Sort::Bool,
    )
    .expect("register exact alias");

    assert_eq!(
        ctx.symbol_iter()
            .filter(|(name, _)| name.as_str() == "same_name")
            .count(),
        1
    );
}

#[test]
fn boolean_connectives_require_smtlib_arity_and_bool_operands() {
    for input in [
        "(assert (and true))",
        "(assert (or true))",
        "(assert (=> true))",
        "(assert (implies true))",
        "(assert (xor true))",
    ] {
        let commands = parse(input).expect("malformed-arity term still parses");
        let mut ctx = Context::new();
        let error = commands
            .iter()
            .try_for_each(|command| ctx.process_command(command).map(|_| ()))
            .expect_err("binary Boolean connective must reject fewer than two operands");
        assert!(
            matches!(error, ElaborateError::InvalidConstant(_)),
            "expected arity error for `{input}`, got {error:?}"
        );
    }

    for input in [
        "(assert (and true 1))",
        "(assert (or 0 false))",
        "(assert (=> true 0))",
        "(assert (implies 0 true))",
        "(assert (xor true 0))",
    ] {
        let commands = parse(input).expect("wrong-sort term still parses");
        let mut ctx = Context::new();
        let error = commands
            .iter()
            .try_for_each(|command| ctx.process_command(command).map(|_| ()))
            .expect_err("Boolean connective must reject a non-Bool operand");
        assert!(
            matches!(error, ElaborateError::SortMismatch { .. }),
            "expected Bool sort error for `{input}`, got {error:?}"
        );
    }
}

#[test]
fn test_elaborate_forall_preserves_termdata_and_binds_var() {
    let input = r#"
            (assert (forall ((x Int)) (> x 0)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    let (vars, body) = match ctx.terms.get(assertion) {
        TermData::Forall(vars, body, _) => (vars, *body),
        other => panic!("Expected TermData::Forall, got {other:?}"),
    };

    assert_eq!(vars.len(), 1);
    let binder_name = vars[0].0.clone();

    let mut names_in_body = Vec::new();
    collect_var_names(&ctx.terms, body, &mut names_in_body);
    assert!(
        names_in_body.contains(&binder_name),
        "Binder {binder_name} not found in body vars: {names_in_body:?}"
    );
}

#[test]
fn test_elaborate_exists_preserves_termdata_and_binds_var() {
    let input = r#"
            (assert (exists ((x Int)) (> x 0)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    let (vars, body) = match ctx.terms.get(assertion) {
        TermData::Exists(vars, body, _) => (vars, *body),
        other => panic!("Expected TermData::Exists, got {other:?}"),
    };

    assert_eq!(vars.len(), 1);
    let binder_name = vars[0].0.clone();

    let mut names_in_body = Vec::new();
    collect_var_names(&ctx.terms, body, &mut names_in_body);
    assert!(
        names_in_body.contains(&binder_name),
        "Binder {binder_name} not found in body vars: {names_in_body:?}"
    );
}

#[test]
fn test_elaborate_nested_quantifiers_preserves_structure() {
    let input = r#"
            (assert (forall ((x Int)) (exists ((y Int)) (= (+ x y) 0))))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    let (outer_vars, outer_body) = match ctx.terms.get(assertion) {
        TermData::Forall(vars, body, _) => (vars, *body),
        other => panic!("Expected TermData::Forall, got {other:?}"),
    };
    assert_eq!(outer_vars.len(), 1);

    match ctx.terms.get(outer_body) {
        TermData::Exists(inner_vars, _, _) => assert_eq!(inner_vars.len(), 1),
        other => panic!("Expected nested TermData::Exists, got {other:?}"),
    }
}

#[test]
fn test_elaborate_forall_with_user_triggers_from_pattern_annotation() {
    let input = r#"
            (declare-fun P (Int) Bool)
            (declare-fun Q (Int) Bool)
            (assert (forall ((x Int))
              (! (=> (P x) (Q x))
                 :pattern ((P x)) )))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    let assertion = ctx.assertions[0];
    let (vars, triggers) = match ctx.terms.get(assertion) {
        TermData::Forall(vars, _body, triggers) => (vars, triggers),
        other => panic!("Expected TermData::Forall, got {other:?}"),
    };

    assert_eq!(vars.len(), 1);
    assert_eq!(triggers.len(), 1);
    assert_eq!(triggers[0].len(), 1);

    let trigger_term = triggers[0][0];
    let TermData::App(Symbol::Named(sym), args) = ctx.terms.get(trigger_term) else {
        panic!(
            "Expected trigger term to be App, got {:?}",
            ctx.terms.get(trigger_term)
        );
    };
    assert_eq!(sym, "P");
    assert_eq!(args.len(), 1);

    let TermData::Var(var_name, _) = ctx.terms.get(args[0]) else {
        panic!(
            "Expected trigger arg to be bound Var, got {:?}",
            ctx.terms.get(args[0])
        );
    };
    assert_eq!(var_name, &vars[0].0);
}

#[test]
fn test_elaborate_bool_ops() {
    let input = r#"
            (declare-const a Bool)
            (declare-const b Bool)
            (assert (and a b))
            (assert (or a (not b)))
            (assert (=> a b))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 3);
}

#[test]
fn test_elaborate_let() {
    let input = r#"
            (declare-const x Int)
            (assert (let ((y x)) (= y x)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    // let (y = x) in (= y x) should simplify to (= x x) = true
    assert_eq!(ctx.assertions.len(), 1);
    assert!(ctx.terms.is_true(ctx.assertions[0]));
}

#[test]
fn test_elaborate_define_fun() {
    let input = r#"
            (define-fun double ((x Int)) Int (+ x x))
            (declare-const a Int)
            (assert (= (double a) (+ a a)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_define_fun_nullary() {
    let input = r#"
            (declare-sort U 0)
            (declare-fun a () U)
            (declare-fun b () U)
            (define-fun my_eq () Bool (= a b))
            (assert my_eq)
            (assert (not (= a b)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 2);
}

#[test]
fn test_push_pop() {
    let input = r#"
            (declare-const x Int)
            (push 1)
            (declare-const y Int)
            (assert (= x y))
            (pop 1)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 0);
    assert!(ctx.symbols.contains_key("x"));
    assert!(!ctx.symbols.contains_key("y"));
}

#[test]
fn test_global_declarations_keep_const_after_pop() {
    let input = r#"
            (set-option :global-declarations true)
            (push 1)
            (declare-const x Int)
            (pop 1)
            (assert (= x 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert!(ctx.symbols.contains_key("x"));
    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_global_decls_alias_updates_global_declarations_option() {
    let input = r#"
            (set-option :global-decls true)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(
        ctx.get_option(":global-declarations"),
        Some(&OptionValue::Bool(true))
    );
    assert_eq!(
        ctx.get_option(":global-decls"),
        Some(&OptionValue::Bool(true))
    );
}

#[test]
fn test_global_declarations_option_changes_apply_to_future_declarations() {
    let input = r#"
            (push 1)
            (set-option :global-decls true)
            (declare-const x Int)
            (set-option :global-declarations false)
            (declare-const y Int)
            (pop 1)
            (assert (= x 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert!(ctx.symbols.contains_key("x"));
    assert!(!ctx.symbols.contains_key("y"));
    assert_eq!(
        ctx.get_option(":global-declarations"),
        Some(&OptionValue::Bool(false))
    );
    assert_eq!(
        ctx.get_option(":global-decls"),
        Some(&OptionValue::Bool(false))
    );
    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_redeclare_after_pop_gets_fresh_term_id_6813() {
    let input = r#"
            (push 1)
            (declare-const x Int)
            (pop 1)
            (push 1)
            (declare-const x Int)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let mut first_x = None;

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
        if first_x.is_none() {
            first_x = ctx.symbols.get("x").and_then(|info| info.term);
        }
    }

    let second_x = ctx
        .symbols
        .get("x")
        .and_then(|info| info.term)
        .expect("x should be declared in the second scope");
    let first_x = first_x.expect("x should be declared in the first scope");

    assert_ne!(
        first_x, second_x,
        "redeclaring x after pop must allocate a fresh internal term id"
    );
}

#[test]
fn test_reserved_symbol_const_rejected() {
    let input = r#"
            (declare-const __ay_internal Int)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(err, ElaborateError::ReservedSymbol(_)),
        "Expected ReservedSymbol error, got: {err:?}"
    );
}

#[test]
fn test_reserved_symbol_fun_rejected() {
    let input = r#"
            (declare-fun __ay_myfunc (Int) Bool)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ElaborateError::ReservedSymbol(_)
    ));
}

#[test]
fn test_reserved_symbol_define_fun_rejected() {
    let input = r#"
            (define-fun __ay_helper ((x Int)) Int (+ x 1))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ElaborateError::ReservedSymbol(_)
    ));
}

#[test]
fn test_reserved_symbol_datatype_rejected() {
    let input = r#"
            (declare-datatype __ay_MyDT ((ctor)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ElaborateError::ReservedSymbol(_)
    ));
}

#[test]
fn test_reserved_symbol_constructor_rejected() {
    let input = r#"
            (declare-datatype MyDT ((__ay_badctor)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ElaborateError::ReservedSymbol(_)
    ));
}

#[test]
fn test_reserved_symbol_selector_rejected() {
    let input = r#"
            (declare-datatype MyDT ((ctor (__ay_badsel Int))))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let result = ctx.process_command(&commands[0]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ElaborateError::ReservedSymbol(_)
    ));
}

/// Soundness: a builtin theory-operator name that AY matches STRUCTURALLY on
/// `App(Named(name), ..)` (array `const-array`/`select`/`store`, a BV op, a set
/// op, …) must be rejected at declaration. Otherwise the user-symbol
/// elaboration path builds the very `App(Named(name), ..)` shape the theory
/// then conflates with the builtin op — for arrays that is a *wrong-UNSAT*
/// (a false claim "proved"), the cardinal soundness failure.
#[test]
fn test_reserved_theory_op_names_rejected() {
    for (form, name) in [
        (
            "(declare-fun const-array (Bool) (Array Int Bool))",
            "const-array",
        ),
        ("(declare-fun select ((Array Int Int) Int) Int)", "select"),
        (
            "(declare-fun store ((Array Int Int) Int Int) (Array Int Int))",
            "store",
        ),
        ("(declare-fun default ((Array Int Int)) Int)", "default"),
        (
            "(declare-fun bvadd ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))",
            "bvadd",
        ),
        (
            "(declare-fun set.union ((Array Int Bool) (Array Int Bool)) (Array Int Bool))",
            "set.union",
        ),
        // FP classification predicates: forging fp.isZero/fp.isNaN/fp.isInfinite
        // was a CONFIRMED wrong-UNSAT (e.g. `(not (fp.isZero (_ +zero 8 24)))`
        // answered unsat, the forged symbol conflated with the builtin).
        (
            "(declare-fun fp.isZero ((_ FloatingPoint 8 24)) Bool)",
            "fp.isZero",
        ),
        (
            "(declare-fun fp.isNaN ((_ FloatingPoint 8 24)) Bool)",
            "fp.isNaN",
        ),
        (
            "(declare-fun fp.isInfinite ((_ FloatingPoint 8 24)) Bool)",
            "fp.isInfinite",
        ),
        (
            "(declare-fun fp.isNormal ((_ FloatingPoint 8 24)) Bool)",
            "fp.isNormal",
        ),
        (
            "(declare-fun fp.isSubnormal ((_ FloatingPoint 8 24)) Bool)",
            "fp.isSubnormal",
        ),
        // Multiset pointwise/higher-order ops: same conflation surface
        // (fail-closed `unknown` downstream today, sealed uniformly here).
        (
            "(declare-fun multiset.union ((Array Int Int) (Array Int Int)) (Array Int Int))",
            "multiset.union",
        ),
        (
            "(declare-fun multiset.sum ((Array Int Int)) Int)",
            "multiset.sum",
        ),
        (
            "(declare-const const-array (Array Int Bool))",
            "const-array (declare-const)",
        ),
        (
            "(define-fun select ((a (Array Int Int)) (i Int)) Int 0)",
            "select (define-fun)",
        ),
    ] {
        let commands = parse(form).unwrap();
        let mut ctx = Context::new();
        let result = ctx.process_command(&commands[0]);
        assert!(
            matches!(result, Err(ElaborateError::ReservedSymbol(_))),
            "expected ReservedSymbol rejecting forged builtin op `{name}` via `{form}`, got: {result:?}"
        );
    }
}

/// The confirmed cardinal wrong-UNSAT repro: forging `const-array` as a user
/// function used to let AY treat `(const-array false)` as the all-false builtin
/// array and "prove" a satisfiable query UNSAT. It must now be REJECTED at
/// elaboration (never reach the solver as a false UNSAT).
#[test]
fn test_forged_const_array_impl_repro_rejected() {
    let input = r#"
            (declare-fun const-array (Bool) (Array Int Bool))
            (declare-const V (Array Int Bool))
            (declare-const len Int)
            (assert (= V (const-array false)))
            (assert (= len (ite (select V 0) 0 1)))
            (assert (= len 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    let mut saw_reserved = false;
    for cmd in &commands {
        if let Err(ElaborateError::ReservedSymbol(_)) = ctx.process_command(cmd) {
            saw_reserved = true;
            break;
        }
    }
    assert!(
        saw_reserved,
        "forged const-array declaration must be rejected as ReservedSymbol"
    );
}

/// The SMT-LIB Core connectives and arithmetic operators are NOT reserved: AY's
/// higher-order `(_ map f)` feature legitimately `declare-fun`s them as map
/// targets (`((_ map not) s)` = set complement over `(Array _ Bool)`). Reserving
/// them would reject legitimate input, so they must stay declarable.
#[test]
fn test_core_connectives_not_reserved_for_map() {
    let input = r#"
            (declare-fun not (Bool) Bool)
            (declare-fun and (Bool Bool) Bool)
            (declare-fun or (Bool Bool) Bool)
            (declare-const s (Array Int Bool))
            (declare-const i Int)
            (assert (select ((_ map not) s) i))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("core connective declarations must be accepted (map targets)");
    }
    assert!(ctx.symbols.contains_key("not"));
    assert!(ctx.symbols.contains_key("and"));
    assert!(ctx.symbols.contains_key("or"));
}

/// Qualified-(as)-path names (elaborate/qualified.rs, matched BEFORE the
/// declared-symbol fallback) are reserved: forging each via declare-fun +
/// `(as <name> <sort>)` was a confirmed wrong-UNSAT on clean HEAD
/// (rc_setempty_as.smt2 / rc_msempty_as.smt2 / rc_mapempty_as.smt2 — e.g. a
/// declared `set.empty` used under `(as set.empty (Array Int Bool))` was
/// treated as the builtin constant-false array).
#[test]
fn test_forged_qualified_as_path_names_rejected() {
    for decl in [
        "(declare-fun set.empty () (Array Int Bool))",
        "(declare-fun multiset.empty () (Array Int Int))",
        "(declare-fun map.empty () (Array Int Int))",
        "(declare-const set.empty (Array Int Bool))",
        "(define-fun map.empty () Int 0)",
        "(declare-fun seq.empty () (Seq Int))",
    ] {
        let commands = parse(decl).unwrap();
        let mut ctx = Context::new();
        let result = ctx.process_command(&commands[0]);
        assert!(
            matches!(result, Err(ElaborateError::ReservedSymbol(_))),
            "expected ReservedSymbol rejection for `{decl}`, got: {result:?}"
        );
    }
}

/// `const` is handled by SHADOWING, not reservation: real-world QF_UF
/// benchmarks legitimately declare it (the CLEARSY B-method fixtures declare
/// `(declare-fun |const| (U U) U)`), so the declaration must stay accepted —
/// and once declared, `(as const <sort>)` must resolve to the USER symbol (a
/// plain uninterpreted application), not the builtin constant array (the
/// rc_const_as wrong-UNSAT conflation).
#[test]
fn test_declared_const_shadows_builtin_constant_array() {
    // Declaration accepted (CLEARSY pattern).
    let input = r#"
            (declare-fun const (Int) (Array Int Int))
            (assert (= (select ((as const (Array Int Int)) 7) 3) 7))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("declared `const` must stay accepted and usable under (as ...)");
    }
    assert!(ctx.symbols.contains_key("const"));
    // The elaborated assertion must contain the USER's `const` application —
    // NOT a folded builtin constant array (whose select would already have
    // reduced to the constant 7, collapsing the equality to `true`).
    use ay_core::term::TermData;
    let assertion = *ctx.assertions.last().expect("assertion recorded");
    assert!(
        !matches!(ctx.terms.get(assertion), TermData::Const(_)),
        "(as const ...) over a DECLARED `const` must stay an uninterpreted \
         application, not fold to the builtin constant array"
    );
    // Without a declaration, the builtin constant array still folds:
    // select(const-array(7), 3) = 7 elaborates to a trivially-true equality.
    let builtin_input = r#"
            (assert (= (select ((as const (Array Int Int)) 7) 3) 7))
        "#;
    let commands = parse(builtin_input).unwrap();
    let mut ctx2 = Context::new();
    for cmd in &commands {
        ctx2.process_command(cmd)
            .expect("builtin (as const ...) must keep elaborating when undeclared");
    }
}

/// The builtin `(as …)` USE path is unaffected by reserving the qualified
/// names: the dedicated match arms in `elaborate_qualified_app` fire before
/// any symbol lookup and never require a declaration.
#[test]
fn test_legit_qualified_as_builtin_uses_still_work() {
    let input = r#"
            (declare-const s (Set Int))
            (declare-const m (Multiset Int))
            (declare-const mp (Map Int Int))
            (assert (= s (as set.empty (Set Int))))
            (assert (= m (as multiset.empty (Multiset Int))))
            (assert (= mp (as map.empty (Map Int Int))))
            (assert (= (select ((as const (Array Int Int)) 7) 3) 7))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("builtin (as ...) uses must keep elaborating");
    }
    assert_eq!(ctx.assertions.len(), 4);
}

#[test]
fn qualified_builtin_paths_validate_arity_and_carrier_sorts() {
    for input in [
        "(assert (= ((as seq.empty (Seq Int)) 0) (as seq.empty (Seq Int))))",
        "(assert (= (as seq.empty Int) 0))",
        "(assert (= (as set.empty (Array Int Int)) (as set.empty (Array Int Int))))",
        "(assert (= (as multiset.empty (Array Int Bool)) (as multiset.empty (Array Int Bool))))",
        "(assert (= ((as const (Array Int Int)) true) ((as const (Array Int Int)) true)))",
    ] {
        let commands = parse(input).expect("malformed qualified use should still parse");
        let mut ctx = Context::new();
        assert!(
            commands
                .iter()
                .try_for_each(|command| ctx.process_command(command).map(|_| ()))
                .is_err(),
            "qualified builtin must reject malformed use: {input}"
        );
    }
}

#[test]
fn qualified_const_array_performs_int_to_real_value_coercion() {
    let commands = parse("(assert (= (select ((as const (Array Int Real)) 0) 1) 0.0))").unwrap();
    let mut ctx = Context::new();
    for command in &commands {
        ctx.process_command(command).unwrap();
    }
    assert!(ctx.terms.is_true(ctx.assertions[0]));
}

#[test]
fn qualified_declared_app_resolves_full_signature_and_result_sort() {
    let commands = parse(
        "(declare-fun f (Int) Bool) (declare-fun f (Int) Int) \
         (assert ((as f Bool) 0)) (assert (= ((as f Int) 0) 0)) \
         (declare-fun real_pred (Real) Bool) (assert ((as real_pred Bool) 0))",
    )
    .unwrap();
    let mut ctx = Context::new();
    for command in &commands {
        ctx.process_command(command).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 3);
}

#[test]
fn qualified_declared_app_rejects_bad_domain_result_and_constructor_sorts() {
    for input in [
        "(declare-fun f (Int) Bool) (assert ((as f Bool) true))",
        "(declare-fun f (Int) Bool) (assert (= ((as f Int) 0) 0))",
        "(declare-datatype D ((C (field Int)))) \
         (assert (= ((as C D) true) ((as C D) true)))",
    ] {
        let commands = parse(input).unwrap();
        let mut ctx = Context::new();
        assert!(
            commands
                .iter()
                .try_for_each(|command| ctx.process_command(command).map(|_| ()))
                .is_err(),
            "qualified identifier must reject mismatched signature: {input}"
        );
    }
}

#[test]
fn qualified_declared_app_preserves_selected_private_identity_and_rejects_ambiguity() {
    let mut ctx = Context::new();
    ctx.register_native_function_alias(
        "surface".to_string(),
        "!qualified-private".to_string(),
        vec![Sort::Int],
        Sort::Bool,
    )
    .unwrap();
    let commands = parse("(assert ((as surface Bool) 0))").unwrap();
    ctx.process_command(&commands[0]).unwrap();
    let TermData::App(Symbol::Named(name), _) = ctx.terms.get(ctx.assertions[0]) else {
        panic!("qualified alias application must remain an application");
    };
    assert_eq!(name, "!qualified-private");

    ctx.register_native_function_alias(
        "ambiguous".to_string(),
        "!qualified-one".to_string(),
        vec![Sort::Int],
        Sort::Bool,
    )
    .unwrap();
    ctx.register_native_function_alias(
        "ambiguous".to_string(),
        "!qualified-two".to_string(),
        vec![Sort::Int],
        Sort::Bool,
    )
    .unwrap();
    let commands = parse("(assert ((as ambiguous Bool) 0))").unwrap();
    assert!(ctx.process_command(&commands[0]).is_err());
}

#[test]
fn qualified_defined_function_expands_body_and_checks_result_ascription() {
    let commands = parse(
        "(define-fun positive ((x Int)) Bool (> x 0)) \
         (assert ((as positive Bool) 1))",
    )
    .unwrap();
    let mut ctx = Context::new();
    for command in &commands {
        ctx.process_command(command).unwrap();
    }
    assert!(ctx.terms.is_true(ctx.assertions[0]));

    let commands = parse(
        "(define-fun positive ((x Int)) Bool (> x 0)) \
         (assert (= ((as positive Int) 1) 1))",
    )
    .unwrap();
    let mut ctx = Context::new();
    assert!(commands
        .iter()
        .try_for_each(|command| ctx.process_command(command).map(|_| ()))
        .is_err());
}

#[test]
fn test_is_reserved_op_name_classification() {
    use crate::elaborate::{is_excluded_declarable_op_name, is_reserved_op_name};
    // Structurally-matched theory ops: reserved.
    for op in [
        "const-array",
        "select",
        "store",
        "default",
        "as-array",
        "bvadd",
        "concat",
        "int2bv",
        "bv2nat",
        "set.union",
        "map.get",
        "seq.len",
        "str.len",
        "re.union",
        "fp.add",
        "multiset.count",
        // Qualified-(as)-path names (elaborate/qualified.rs).
        "set.empty",
        "multiset.empty",
        "map.empty",
        "seq.empty",
        // FP classification predicates (fp.isZero/isNaN/isInfinite were
        // confirmed wrong-UNSAT forgeries before being reserved).
        "fp.isNaN",
        "fp.isInfinite",
        "fp.isZero",
        "fp.isNormal",
        "fp.isSubnormal",
        // Multiset pointwise/higher-order ops.
        "multiset.union",
        "multiset.inter",
        "multiset.diff",
        "multiset.map",
        "multiset.filter",
        "multiset.fold",
        "multiset.comprehension",
        "multiset.sum",
    ] {
        assert!(is_reserved_op_name(op), "`{op}` should be reserved");
    }
    // Core/arith (map-target-eligible) and ordinary names: NOT reserved.
    for ok in [
        "and",
        "or",
        "not",
        "xor",
        "=",
        "distinct",
        "ite",
        "+",
        "-",
        "*",
        "div",
        "mod",
        "abs",
        "min",
        "max",
        "to_real",
        "union",
        "member",
        "subset",
        "count",
        "map",
        "foo",
        "my_select",
        "Option",
        // `const` is declared-shadowed, not reserved (CLEARSY declares it).
        "const",
        // Declaration-activated collection ops: deductive-checks's encoder
        // declares these via try_declare_fun to activate the native
        // collection solvers — they must stay declarable.
        "set.subset",
        "map.dom",
        "map.subset",
        "multiset.subset",
    ] {
        assert!(!is_reserved_op_name(ok), "`{ok}` should NOT be reserved");
    }
    // The explicit exclusion table matches the helper, and no name is in both
    // tables.
    for &(op, reason) in EXCLUDED_DECLARABLE_OP_NAMES {
        assert!(is_excluded_declarable_op_name(op));
        assert!(
            !is_reserved_op_name(op),
            "`{op}` ({reason}) is in BOTH the reserved and excluded tables"
        );
    }
    assert!(!is_excluded_declarable_op_name("select"));
    assert!(!is_excluded_declarable_op_name("foo"));
}

/// BLOCKER-2 regression (deductive-checks compatibility): the declaration-activated
/// collection predicates must remain user-declarable. deductive-checks-core declares
/// exactly these four names via the ay-dpll programmatic API
/// (`try_declare_fun`) — which funnels through this same
/// `Context::declare_fun`/`is_reserved_symbol` choke point — as the documented
/// activation route for the native set/map/multiset solvers:
///   - `set.subset`       (encoder/collection_set.rs)
///   - `map.dom`          (encoder/collection_map.rs)
///   - `map.subset`       (encoder/collection_map.rs)
///   - `multiset.subset`  (encoder/ir_encoder/multiset.rs)
///
/// Reserving them hard-fails those default (no-fallback) encodings on the
/// first collection proof. Misuse of the declared name fails CLOSED (probed:
/// mismatched Int-sorted declarations answer unknown/sat, never a bogus
/// unsat).
#[test]
fn test_declaration_activated_collection_ops_declarable() {
    let input = r#"
            (declare-fun set.subset ((Array Int Bool) (Array Int Bool)) Bool)
            (declare-fun map.dom ((Array Int Int)) (Array Int Bool))
            (declare-fun map.subset ((Array Int Int) (Array Int Int)) Bool)
            (declare-fun multiset.subset ((Array Int Int) (Array Int Int)) Bool)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("declaration-activated collection op must stay declarable");
    }
    for name in ["set.subset", "map.dom", "map.subset", "multiset.subset"] {
        assert!(ctx.symbols.contains_key(name), "`{name}` not declared");
    }
}

/// The declaration-activated names are declarable ONLY via `declare-fun` at
/// the native collection signature (the activation contract). Every other
/// declaration form must be rejected fail-closed: a mismatched signature
/// previously reached the native subset rule — `(declare-fun set.subset (Int
/// Int) Bool)` + `(assert (not (set.subset 0 0)))` answered a definitive
/// `unsat` via ground-identity reflexivity on the forged symbol.
#[test]
fn test_declaration_activated_wrong_signature_rejected() {
    // Wrong signatures via declare-fun: rejected by the signature gate.
    for (form, name) in [
        (
            "(declare-fun set.subset (Int Int) Bool)",
            "set.subset over Int",
        ),
        (
            "(declare-fun map.subset (Int Int) Bool)",
            "map.subset over Int",
        ),
        (
            "(declare-fun multiset.subset (Int Int) Bool)",
            "multiset.subset over Int",
        ),
        ("(declare-fun map.dom (Int) Int)", "map.dom over Int"),
        (
            "(declare-fun set.subset ((Array Int Bool)) Bool)",
            "set.subset arity 1",
        ),
        (
            "(declare-fun set.subset ((Array Int Bool) (Array Int Bool)) Int)",
            "set.subset non-Bool result",
        ),
        (
            "(declare-fun map.dom ((Array Int Int)) Int)",
            "map.dom non-array result",
        ),
        // Mixed-index carriers: previously ACCEPTED by the gate and then
        // PANICKED in ay-core (`mk_select index sort mismatch`) when the
        // native subset rule instantiated a shared element variable across
        // both carriers — a user-triggerable crash, now rejected fail-closed.
        (
            "(declare-fun set.subset ((Array Int Bool) (Array Bool Bool)) Bool)",
            "set.subset mixed index sorts",
        ),
        (
            "(declare-fun multiset.subset ((Array Int Int) (Array Bool Int)) Bool)",
            "multiset.subset mixed index sorts",
        ),
        (
            "(declare-fun map.dom ((Array Int Int)) (Array Bool Bool))",
            "map.dom result indexed by non-key sort",
        ),
    ] {
        let commands = parse(form).unwrap();
        let mut ctx = Context::new();
        let result = ctx.process_command(&commands[0]);
        assert!(
            matches!(result, Err(ElaborateError::Unsupported(_))),
            "expected signature-gate rejection for {name} via `{form}`, got: {result:?}"
        );
    }
    // Non-declare-fun forms: rejected as reserved outright.
    for (form, name) in [
        (
            "(declare-const set.subset Bool)",
            "declare-const set.subset",
        ),
        (
            "(declare-const map.dom (Array Int Bool))",
            "declare-const map.dom",
        ),
        (
            "(define-fun map.subset ((a (Array Int Int)) (b (Array Int Int))) Bool true)",
            "define-fun map.subset",
        ),
        (
            "(declare-datatype D ((multiset.subset (f Int))))",
            "datatype ctor multiset.subset",
        ),
    ] {
        let commands = parse(form).unwrap();
        let mut ctx = Context::new();
        let result = ctx.process_command(&commands[0]);
        assert!(
            matches!(result, Err(ElaborateError::ReservedSymbol(_))),
            "expected ReservedSymbol rejection for {name} via `{form}`, got: {result:?}"
        );
    }
}

/// DRIFT-PROOF: mechanically re-extract every operator name the elaborators
/// match structurally (string-literal match arms and `== "…"` comparisons in
/// `src/elaborate/app/*.rs`, `src/elaborate/indexed.rs`,
/// `src/elaborate/qualified.rs`, and `src/elaborate/term.rs`) and assert each
/// one is classified in exactly one of [`RESERVED_OP_NAMES`] or
/// [`EXCLUDED_DECLARABLE_OP_NAMES`]. A future match-arm addition whose name is
/// in neither table fails here, so the reserved set cannot silently drift from
/// the true structural-match vocabulary (that drift is exactly how the
/// fp.isZero/fp.isNaN/fp.isInfinite wrong-UNSAT forgeries slipped past the
/// first hand-curated table, and how the qualified-(as)-path names
/// set.empty/multiset.empty/map.empty/const — matched in `qualified.rs`, a
/// file the first drift test did not scan — stayed forgeable wrong-UNSATs
/// after the app-arm vocabulary was sealed).
///
/// Scan scope: every `src/elaborate/*.rs` file that matches TERM-LEVEL
/// operator/identifier names. Deliberately excluded from the scan:
/// `sorts.rs` (matches SORT names — a separate namespace; declaring a
/// function named `Set`/`Array` is legitimate and cannot conflate with sort
/// elaboration), `commands.rs` (matches option keywords), and
/// `declarations.rs`/`datatypes.rs`/`commands.rs` symbol handling (no
/// structural op-name matching; datatype member names are USER-defined
/// vocabulary gated dynamically by the `DatatypeMemberCollision` /
/// `SortRedeclaration` checks, not by these static tables).
#[test]
fn test_reserved_op_table_covers_all_elaborator_match_arms() {
    use crate::elaborate::{
        is_excluded_declarable_op_name, is_reserved_op_name, EXCLUDED_DECLARABLE_OP_NAMES,
    };
    use std::path::{Path, PathBuf};

    /// Extract the string literals of a match-arm pattern line: a line that
    /// (after trimming and an optional leading `|`) consists ONLY of one or
    /// more `"…"` literals separated by `|`, terminated by `=>`, an `if …`
    /// match-arm guard (e.g. the declared-symbol guard on the `"const"` arm
    /// in `qualified.rs`), a trailing `|`, or end-of-line (multi-line arm
    /// continuation). Everything else — error-message strings, function-call
    /// arguments, `.to_string()` receivers — is rejected by the terminator
    /// check.
    fn extract_arm_string_literals(line: &str) -> Vec<String> {
        let trimmed = line.trim();
        let mut rest = trimmed.strip_prefix('|').map_or(trimmed, str::trim_start);
        if !rest.starts_with('"') {
            return Vec::new();
        }
        let mut lits = Vec::new();
        loop {
            let Some(end) = rest[1..].find('"') else {
                return Vec::new();
            };
            lits.push(rest[1..=end].to_string());
            rest = rest[end + 2..].trim_start();
            if let Some(after_pipe) = rest.strip_prefix('|') {
                rest = after_pipe.trim_start();
                if rest.is_empty() {
                    break; // arm continues on the next line
                }
                if !rest.starts_with('"') {
                    return Vec::new();
                }
                continue;
            }
            break;
        }
        if rest.is_empty() || rest.starts_with("=>") || rest.starts_with("if ") {
            lits
        } else {
            Vec::new()
        }
    }

    /// Extract the right-hand literals of `== "…"` comparisons (e.g.
    /// `sym.name() == "const-array"`, `parts[0] == "map"`).
    fn extract_eq_string_literals(line: &str) -> Vec<String> {
        let mut lits = Vec::new();
        let mut rest = line;
        while let Some(pos) = rest.find("== \"") {
            let after = &rest[pos + 4..];
            let Some(end) = after.find('"') else { break };
            lits.push(after[..end].to_string());
            rest = &after[end + 1..];
        }
        lits
    }

    /// Filter: operator names are short single tokens; format/error strings
    /// contain whitespace, braces, parens, colons or quotes and are dropped.
    fn looks_like_op_name(name: &str) -> bool {
        !name.is_empty()
            && name.len() <= 40
            && !name
                .chars()
                .any(|c| c.is_whitespace() || "{}():'\\\"".contains(c))
    }

    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let app_dir = manifest.join("src/elaborate/app");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&app_dir)
        .expect("read src/elaborate/app")
        .map(|entry| entry.expect("dir entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "rs"))
        .collect();
    files.push(manifest.join("src/elaborate/indexed.rs"));
    files.push(manifest.join("src/elaborate/qualified.rs"));
    files.push(manifest.join("src/elaborate/term.rs"));
    files.sort();

    let mut extracted = std::collections::BTreeSet::new();
    for file in &files {
        let source = std::fs::read_to_string(file)
            .unwrap_or_else(|e| panic!("read {}: {e}", file.display()));
        for line in source.lines() {
            for lit in extract_arm_string_literals(line)
                .into_iter()
                .chain(extract_eq_string_literals(line))
            {
                if looks_like_op_name(&lit) {
                    extracted.insert(lit);
                }
            }
        }
    }

    // Extraction sanity: it must SEE the known vocabulary (guards against the
    // extractor itself rotting into a vacuous pass).
    assert!(
        extracted.len() >= 150,
        "extraction looks broken: only {} names extracted",
        extracted.len()
    );
    for must_see in [
        "select",
        "store",
        "bvadd",
        "fp.isNaN",
        "fp.isZero",
        "multiset.union",
        "set.subset",
        "map.dom",
        "const-array",
        "seq.len",
        "str.len",
        "map",
        // qualified.rs vocabulary (the recheck-found blind spot)
        "set.empty",
        "multiset.empty",
        "map.empty",
        "const",
        // term.rs rounding modes and indexed.rs FP special literals
        "roundNearestTiesToEven",
        "NaN",
    ] {
        assert!(
            extracted.contains(must_see),
            "extraction failed to find known op `{must_see}` — extractor broken?"
        );
    }

    let unclassified: Vec<&String> = extracted
        .iter()
        .filter(|name| !is_reserved_op_name(name) && !is_excluded_declarable_op_name(name))
        .collect();
    assert!(
        unclassified.is_empty(),
        "elaborator-matched op names in NEITHER RESERVED_OP_NAMES nor \
         EXCLUDED_DECLARABLE_OP_NAMES (classify each: reserve it, or add it to \
         the excluded table with a documented reason): {unclassified:?}"
    );

    // And the tables must stay disjoint.
    for &(op, _) in EXCLUDED_DECLARABLE_OP_NAMES {
        assert!(
            !is_reserved_op_name(op),
            "`{op}` appears in BOTH the reserved and excluded tables"
        );
    }
}

#[test]
fn test_normal_symbol_accepted() {
    // Symbols not starting with __ay_ should be accepted
    let input = r#"
            (declare-const _ay_almost Int)
            (declare-fun normal_func (Int) Bool)
            (declare-datatype MyList ((nil) (cons (head Int) (tail MyList))))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    // All should succeed
    assert!(ctx.symbols.contains_key("_ay_almost"));
    assert!(ctx.symbols.contains_key("normal_func"));
    assert!(ctx.symbols.contains_key("nil"));
    assert!(ctx.symbols.contains_key("cons"));
}

#[test]
fn test_is_reserved_symbol() {
    assert!(is_reserved_symbol("__ay_test"));
    assert!(is_reserved_symbol("__ay_dt_depth_List"));
    assert!(is_reserved_symbol("__ay_"));
    assert!(!is_reserved_symbol("_ay_test"));
    assert!(!is_reserved_symbol("__z3_test"));
    assert!(!is_reserved_symbol("normal"));
}

/// Regression test for #2992: undeclared functions in application position
/// must produce an error, not silently create an App with default Sort::Bool.
#[test]
fn test_undeclared_function_application_rejected() {
    let input = r#"
            (declare-const s Int)
            (assert (= (__field_value s) 42))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    let mut found_error = false;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            assert!(
                matches!(e, ElaborateError::UndefinedSymbol(ref name) if name == "__field_value"),
                "Expected UndefinedSymbol for __field_value, got: {e:?}"
            );
            found_error = true;
        }
    }
    assert!(
        found_error,
        "Expected UndefinedSymbol error for undeclared function application"
    );
}

/// Declared functions in application position should still work.
#[test]
fn test_declared_function_application_accepted() {
    let input = r#"
            (declare-fun __field_value (Int) Int)
            (declare-const s Int)
            (assert (= (__field_value s) 42))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

/// #8621: define-fun definitions inside a pushed scope must be removed on pop.
#[test]
fn test_define_fun_removed_on_pop() {
    let input = r#"
            (declare-const a Int)
            (push 1)
            (define-fun f ((x Int)) Int (+ x 1))
            (assert (= (f a) (+ a 1)))
            (pop 1)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    // After pop, fun_defs should not contain "f"
    assert!(
        !ctx.fun_defs.contains_key("f"),
        "fun_defs should not contain 'f' after pop"
    );
    // Symbol table entry for "f" should also be removed on pop
    assert!(
        !ctx.symbols.contains_key("f"),
        "symbols should not contain 'f' after pop"
    );
    // a should still be present since it was declared before push
    assert!(ctx.symbols.contains_key("a"));
    assert_eq!(ctx.assertions.len(), 0);
}

/// #8621: define-fun-rec definitions inside a pushed scope must be removed on pop.
#[test]
fn test_define_fun_rec_removed_on_pop() {
    let input = r#"
            (declare-const a Int)
            (push 1)
            (define-fun-rec g ((x Int)) Int (ite (= x 0) 0 (+ 1 (g (- x 1)))))
            (pop 1)
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert!(
        !ctx.fun_defs.contains_key("g"),
        "fun_defs should not contain 'g' after pop"
    );
    // Symbol table entry for "g" should also be removed on pop
    assert!(
        !ctx.symbols.contains_key("g"),
        "symbols should not contain 'g' after pop"
    );
    assert!(ctx.symbols.contains_key("a"));
}

/// #8621: global define-fun (no push) should persist.
#[test]
fn test_define_fun_persists_without_scope() {
    let input = r#"
            (define-fun double ((x Int)) Int (+ x x))
            (declare-const a Int)
            (assert (= (double a) (+ a a)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    // Without push/pop, the definition should remain
    assert!(
        ctx.fun_defs.contains_key("double"),
        "fun_defs should contain 'double' at global scope"
    );
    assert_eq!(ctx.assertions.len(), 1);
}

/// #8622: define-fun-rec with unbounded recursion must error, not stack overflow.
#[test]
fn test_define_fun_rec_depth_limit() {
    // Define a recursive function that always recurses (no base case reachable
    // during elaboration expansion)
    let input = r#"
            (define-fun-rec diverge ((x Int)) Int (diverge x))
            (declare-const a Int)
            (assert (= (diverge a) 0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    let mut found_depth_error = false;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            assert!(
                matches!(e, ElaborateError::RecursionDepthExceeded(_)),
                "Expected RecursionDepthExceeded error, got: {e:?}"
            );
            found_depth_error = true;
            break;
        }
    }
    assert!(
        found_depth_error,
        "Expected RecursionDepthExceeded error for unbounded recursive function"
    );
}

/// Unknown indexed identifiers must also be rejected, not silently accepted.
#[test]
fn test_unknown_indexed_identifier_rejected() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (assert (= ((_ unknown_bv_op 4) x) x))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    let mut found_error = false;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            assert!(
                format!("{e:?}").contains("unknown indexed identifier"),
                "Expected 'unknown indexed identifier' error, got: {e:?}"
            );
            found_error = true;
        }
    }
    assert!(found_error, "Expected error for unknown indexed identifier");
}

#[test]
fn stringified_declarations_do_not_authorize_generic_indexed_identifiers() {
    for input in [
        "(declare-fun |(_ shadow 1)| (Int) Bool) (assert ((_ shadow 1) true))",
        "(declare-fun |(_ shadow 1)| (Int) Bool) \
         (declare-fun |(_ shadow 1)| (Bool) Bool) \
         (assert ((_ shadow 1) 0))",
    ] {
        let commands = parse(input).unwrap();
        let mut ctx = Context::new();
        assert!(
            commands
                .iter()
                .try_for_each(|command| ctx.process_command(command).map(|_| ()))
                .is_err(),
            "a quoted stringified declaration must not authorize indexed syntax: {input}"
        );
    }
}

#[test]
fn definitional_forall_adoption_rolls_back_on_later_assert_failure() {
    let commands = parse(
        "(declare-fun f (Int) Int) \
         (assert (forall ((x Int)) (= (f x) (+ x 1))))",
    )
    .expect("parse");
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).expect("declaration");

    ctx.fail_next_assert_after_macro_adoption();
    let error = ctx
        .process_command(&commands[1])
        .expect_err("injected error");
    assert!(matches!(error, ElaborateError::Unsupported(_)));
    assert!(ctx.adopted_macro_interp("f").is_none());
    assert!(ctx.assertions.is_empty());

    // A second attempt can adopt the same definition. This proves both the
    // model interpretation and the expansion entry were removed on rollback.
    ctx.process_command(&commands[1])
        .expect("adoption succeeds after rollback");
    assert!(ctx.adopted_macro_interp("f").is_some());
    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn rejected_to_real_declaration_does_not_set_sticky_shadow_state() {
    let mut ctx = Context::new();
    let bad = parse("(declare-fun to_real ((_ BitVec 0)) Real)").expect("parse");
    assert!(ctx.process_command(&bad[0]).is_err());
    assert!(!ctx.terms.to_real_is_shadowed());

    let valid = parse("(declare-fun to_real (Int) Real)").expect("parse");
    ctx.process_command(&valid[0]).expect("valid declaration");
    assert!(ctx.terms.to_real_is_shadowed());
}

#[test]
fn define_funs_rec_late_sort_error_is_atomic() {
    let commands = parse(
        "(define-funs-rec \
           ((f ((x Int)) Int) (g ((y (_ BitVec 0))) Int)) \
           (x y))",
    )
    .expect("parse");
    let mut ctx = Context::new();
    assert!(ctx.process_command(&commands[0]).is_err());
    assert!(!ctx.symbols.contains_key("f"));
    assert!(!ctx.symbols.contains_key("g"));

    let declaration = parse("(declare-fun f (Int) Int)").expect("parse");
    ctx.process_command(&declaration[0])
        .expect("failed recursive group left no binding");
}

#[test]
fn define_funs_rec_body_error_restores_scope_tracking() {
    let mut ctx = Context::new();
    ctx.process_command(&Command::Push(1)).expect("push");
    let commands = parse(
        "(define-funs-rec \
           ((f ((x Int)) Int) (g ((y Int)) Bool)) \
           (x y))",
    )
    .expect("parse");
    assert!(ctx.process_command(&commands[0]).is_err());
    assert!(!ctx.symbols.contains_key("f"));
    assert!(!ctx.symbols.contains_key("g"));
    assert!(!ctx.scopes.last().expect("scope").symbols.contains_key("f"));
    assert!(!ctx.scopes.last().expect("scope").symbols.contains_key("g"));

    let declaration = parse("(declare-const f Int)").expect("parse");
    ctx.process_command(&declaration[0])
        .expect("name is reusable after rollback");
    ctx.process_command(&Command::Pop(1)).expect("pop");
    assert!(!ctx.symbols.contains_key("f"));
}

#[test]
fn define_funs_rec_duplicate_names_fail_before_mutation() {
    let commands = parse(
        "(define-funs-rec \
           ((f ((x Int)) Int) (f ((y Int)) Int)) \
           (x y))",
    )
    .expect("parse");
    let mut ctx = Context::new();
    assert!(ctx.process_command(&commands[0]).is_err());
    assert!(!ctx.symbols.contains_key("f"));
}

#[test]
fn define_fun_rec_body_error_restores_scope_tracking() {
    let mut ctx = Context::new();
    ctx.process_command(&Command::Push(1)).expect("push");
    let commands = parse("(define-fun-rec f ((x Int)) Bool x)").expect("parse");
    assert!(ctx.process_command(&commands[0]).is_err());
    assert!(!ctx.symbols.contains_key("f"));
    assert!(!ctx.scopes.last().expect("scope").symbols.contains_key("f"));

    let declaration = parse("(declare-const f Int)").expect("parse");
    ctx.process_command(&declaration[0])
        .expect("name is reusable after rollback");
    ctx.process_command(&Command::Pop(1)).expect("pop");
    assert!(!ctx.symbols.contains_key("f"));
}

#[test]
fn indexed_identifiers_do_not_alias_quoted_symbols() {
    for input in [
        // The quoted let-bound name is #x01; the structured literal is #x00.
        "(assert (let ((|(_ bv0 8)| #x01)) (distinct |(_ bv0 8)| (_ bv0 8))))",
        // AY lowers both character literal spellings to their integer code point.
        "(assert (let ((|(_ Char 65)| 66)) (distinct |(_ Char 65)| (_ Char 65))))",
        "(assert (let ((|(_ char #x41)| 66)) (distinct |(_ char #x41)| (_ char #x41))))",
        // Positive and negative zero are distinct FloatingPoint bit patterns.
        "(assert (let ((|(_ +zero 8 24)| (_ -zero 8 24))) \
             (distinct |(_ +zero 8 24)| (_ +zero 8 24))))",
        // A quoted array constant is independent of the indexed as-array value.
        "(declare-fun f (Int) Int) \
         (declare-const |(_ as-array f)| (Array Int Int)) \
         (assert (distinct |(_ as-array f)| (_ as-array f)))",
        // A quoted function name is independent of the structured DT tester.
        "(declare-datatype D ((C) (E))) \
         (declare-fun |(_ is C)| (D) Bool) \
         (declare-const x D) \
         (assert (distinct (|(_ is C)| x) ((_ is C) x)))",
    ] {
        let commands = parse(input).expect("indexed/quoted regression parses");
        let mut ctx = Context::new();
        for command in &commands {
            ctx.process_command(command)
                .expect("indexed and quoted identifiers elaborate independently");
        }
        assert_eq!(ctx.assertions.len(), 1, "{input}");
        assert_ne!(ctx.assertions[0], ctx.terms.false_term(), "{input}");
    }
}

#[test]
fn unknown_indexed_identifier_does_not_resolve_as_quoted_symbol() {
    let commands = parse(
        "(declare-const |(_ mystery 1)| Int) \
         (assert (= |(_ mystery 1)| (_ mystery 1)))",
    )
    .expect("syntax parses");
    let mut ctx = Context::new();
    ctx.process_command(&commands[0])
        .expect("quoted declaration is valid");
    assert!(
        ctx.process_command(&commands[1]).is_err(),
        "the structured unknown identifier must fail closed"
    );
}

#[test]
fn qualified_indexed_identifier_does_not_alias_same_spelled_symbol() {
    let quoted = parse(
        "(declare-const |(_ mystery 1)| Int) \
         (assert (= (as |(_ mystery 1)| Int) 0))",
    )
    .expect("qualified quoted-symbol syntax parses");
    let mut ctx = Context::new();
    for command in &quoted {
        ctx.process_command(command)
            .expect("qualified quoted symbol resolves to its declaration");
    }

    let indexed = parse(
        "(declare-const |(_ mystery 1)| Int) \
         (assert (= (as (_ mystery 1) Int) 0))",
    )
    .expect("qualified indexed syntax parses");
    let mut ctx = Context::new();
    ctx.process_command(&indexed[0])
        .expect("quoted declaration is valid");
    assert!(
        ctx.process_command(&indexed[1]).is_err(),
        "unsupported qualified indexed identifier must fail closed"
    );
}

#[test]
fn character_literal_range_is_enforced() {
    let valid = parse(
        "(assert (= (_ Char 0) 0)) \
         (assert (= (_ Char 196607) 196607)) \
         (assert (= (_ char #x2ffff) 196607))",
    )
    .expect("boundary literals parse");
    let mut ctx = Context::new();
    for command in &valid {
        ctx.process_command(command)
            .expect("boundary character literal is valid");
    }

    for input in [
        "(assert (= (_ Char -1) 0))",
        "(assert (= (_ Char 196608) 0))",
        "(assert (= (_ char #x30000) 0))",
    ] {
        let commands = parse(input).expect("out-of-range syntax parses");
        let mut ctx = Context::new();
        assert!(
            ctx.process_command(&commands[0]).is_err(),
            "out-of-range Char literal elaborated: {input}"
        );
    }
}

#[test]
fn reset_assertions_clears_named_formula_provenance() {
    let commands = parse(
        "(declare-const p Bool) \
         (push 1) \
         (assert (! p :named stale)) \
         (reset-assertions)",
    )
    .expect("reset-assertions fixture parses");
    let mut ctx = Context::new();
    for command in &commands {
        ctx.process_command(command)
            .expect("reset-assertions fixture elaborates");
    }

    assert!(ctx.assertions.is_empty());
    assert!(ctx.assertions_parsed().is_empty());
    assert_eq!(ctx.scope_depth(), 0);
    assert!(
        ctx.named_terms_iter().next().is_none(),
        "labels owned by removed assertions must not survive reset-assertions"
    );
}

/// `let` binds in PARALLEL (SMT-LIB 2.6 §3.6.1): a binding's value is
/// elaborated in the environment as it stood BEFORE its own level, so siblings
/// are not in scope for one another. `let*` must be written as nested `let`s.
///
/// Binding sequentially was a wrong-verdict defect in the CORE language,
/// theory-independent and able to flip a verdict in either direction. Against
/// z3 5.0.0: `(let ((a 0)) (let ((a 1) (b a)) (= b 0)))` is a tautology (`b` is
/// the outer `a`) but ay answered `unsat`; `(let ((a false)) (let ((a true)
/// (b a)) b))` is unsatisfiable but ay answered `sat`.
///
/// These tests compare interned `TermId`s inside ONE context: the term store
/// hash-conses, so two assertions share an id exactly when they elaborate to
/// the same term.
fn elaborated_assertions(input: &str) -> Vec<TermId> {
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    ctx.assertions.clone()
}

#[test]
fn test_let_bindings_are_parallel_not_sequential() {
    // The swap idiom: under parallel binding this is `(= y x)`. Bound
    // sequentially the second binding would see the new `x` and it would
    // collapse to `(= y y)`, i.e. `true`.
    let ids = elaborated_assertions(
        r"
            (declare-const x Int)
            (declare-const y Int)
            (assert (let ((x y) (y x)) (= x y)))
            (assert (= y x))
        ",
    );
    assert_eq!(ids.len(), 2);
    assert_eq!(
        ids[0], ids[1],
        "let must bind in parallel: (let ((x y) (y x)) (= x y)) is (= y x)"
    );
}

#[test]
fn test_let_sibling_sees_outer_binding_not_its_sibling() {
    // `b` must resolve to the OUTER `a`, so the body is `(= a 1)`.
    let ids = elaborated_assertions(
        r"
            (declare-const a Int)
            (assert (let ((a 1) (b a)) (= b a)))
            (assert (= a 1))
        ",
    );
    assert_eq!(ids.len(), 2);
    assert_eq!(
        ids[0], ids[1],
        "a sibling binding resolves outward, never to its sibling"
    );
}

#[test]
fn test_nested_let_levels_are_not_collapsed() {
    // Exercises the chain-flatten path specifically. Level boundaries are
    // semantically load-bearing: the inner `b` is the OUTER let's `a` (0), so
    // the whole assertion is a tautology. Collapsing the two levels into one
    // ordered list — which the flatten optimization used to do — makes `b`
    // pick up the inner `a` (1) and turns this into a false assertion.
    let ids = elaborated_assertions(
        r"
            (assert (let ((a 0)) (let ((a 1) (b a)) (= b 0))))
            (assert true)
        ",
    );
    assert_eq!(ids.len(), 2);
    assert_eq!(ids[0], ids[1], "nested let levels must not be collapsed");
}

#[test]
fn test_let_sibling_reference_to_unbound_name_is_rejected() {
    // Direct evidence of the scope leak: with nothing named `a` in scope, the
    // sibling reference must be an error. It was silently accepted while the
    // environment was extended before siblings were elaborated.
    let commands = parse(
        r"
            (declare-const q Bool)
            (assert (let ((a q) (b a)) b))
        ",
    )
    .unwrap();
    let mut ctx = Context::new();
    let mut err = None;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            err = Some(e);
            break;
        }
    }
    assert!(
        err.is_some(),
        "a sibling reference to an otherwise-unbound name must be rejected"
    );
}

#[test]
fn test_let_dead_binding_elimination_survives_parallel_fix() {
    // Dead-binding elimination (#arr_lia561) must still hold: a binding the
    // body never mentions is not elaborated. Kept alongside parallel binding,
    // with liveness computed per level by the free-variable rule.
    let ids = elaborated_assertions(
        r"
            (declare-const p Bool)
            (assert (let ((dead (and p (not p))) (livevar p)) livevar))
            (assert p)
        ",
    );
    assert_eq!(ids.len(), 2);
    assert_eq!(
        ids[0], ids[1],
        "live binding resolves to p; dead one dropped"
    );
}

// ---------------------------------------------------------------------------
// `define-fun` macro expansion is CAPTURE-AVOIDING (SMT-LIB 2.6 §4.2.2).
//
// A definition's body resolves its symbols against the signature AT DEFINITION
// TIME — its own parameters plus the globals — so no binder at the USE SITE
// (quantifier variable, `let` binding, `match` pattern variable) may capture a
// global the body names. `(define-fun f () Int x)` is by definition equivalent
// to `(declare-fun f () Int)` + `(assert (= f x))`, and §3.6.1 makes a
// quantifier's `x` a fresh, unrelated variable.
//
// Expanding the body in the use-site environment was a wrong-verdict defect in
// BOTH directions. Against z3 5.0.0, with `(declare-const x Int)` and
// `(define-fun f () Int x)`:
//   (assert (forall ((x Int)) (= f 11)))                    truth sat,   ay unsat
//   (assert (= x 11)) (assert (exists ((x Int)) (not (= f 11))))
//                                                           truth unsat, ay sat
// AY also disagreed with ITSELF: the standard's own expansion of the first
// script answered `sat`.
//
// These tests compare interned `TermId`s inside ONE context: the store
// hash-conses, so two assertions share an id exactly when they elaborate to the
// same term. Each pairs the macro form with the term it MUST denote, so they
// pin the semantics rather than a verdict string.

#[test]
fn test_define_fun_body_not_captured_by_let_binder() {
    // `f` is the GLOBAL `x`, so the assertion is `(and (> 5 0) (= x 11))`.
    // Captured by the `let`, `f` would become `5` and the assertion `false`.
    let ids = elaborated_assertions(
        r"
            (declare-const x Int)
            (define-fun f () Int x)
            (assert (let ((x 5)) (and (> x 0) (= f 11))))
            (assert (and (> 5 0) (= x 11)))
        ",
    );
    assert_eq!(ids.len(), 2);
    assert_eq!(
        ids[0], ids[1],
        "a define-fun body resolves against the definition-time signature, \
         never against an enclosing let binder"
    );
}

#[test]
fn test_define_fun_body_not_captured_by_quantifier_binder() {
    // The macro form and the CAPTURED reading must not coincide: `f` is the
    // global `x`, the quantifier's `x` is a fresh unrelated variable (§3.6.1).
    let ids = elaborated_assertions(
        r"
            (declare-const x Int)
            (define-fun f () Int x)
            (assert (forall ((x Int)) (= f 11)))
            (assert (forall ((x Int)) (= x 11)))
        ",
    );
    assert_eq!(ids.len(), 2);
    assert_ne!(
        ids[0], ids[1],
        "the body's `x` is the global constant, not the quantifier's binder"
    );
}

#[test]
fn test_define_fun_body_under_quantifier_is_the_global_term() {
    // The positive half, checked structurally: the quantifier's BODY must be
    // exactly the term `(= x 11)` denotes over the global `x`. (Comparing two
    // whole `forall`s would not work — each elaboration mints a fresh binder
    // name, so two α-equivalent quantifiers have different ids.)
    let commands = parse(
        r"
            (declare-const x Int)
            (define-fun f () Int x)
            (assert (forall ((q Int)) (= f 11)))
            (assert (= x 11))
        ",
    )
    .unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }
    assert_eq!(ctx.assertions.len(), 2);
    let TermData::Forall(_, body, _) = ctx.terms.get(ctx.assertions[0]).clone() else {
        panic!("expected a forall assertion");
    };
    assert_eq!(
        body, ctx.assertions[1],
        "under a binder that does not shadow it, the macro body is still the \
         global `x` — the very term `(= x 11)` denotes"
    );
}

#[test]
fn test_define_fun_with_parameters_body_not_captured() {
    // n-ary macro: the parameter `y` is bound to the argument, but the body's
    // free `x` is still the global one.
    let ids = elaborated_assertions(
        r"
            (declare-const x Int)
            (define-fun g ((y Int)) Int (+ y x))
            (assert (let ((x 5)) (and (> x 0) (= (g 0) 11))))
            (assert (and (> 5 0) (= x 11)))
        ",
    );
    assert_eq!(ids.len(), 2);
    assert_eq!(
        ids[0], ids[1],
        "an n-ary macro binds only its parameters; its free symbols stay global"
    );
}

#[test]
fn test_chained_define_fun_body_not_captured() {
    // A definition that uses another definition expands through the same path.
    let ids = elaborated_assertions(
        r"
            (declare-const x Int)
            (define-fun f () Int x)
            (define-fun h () Int (+ f 0))
            (assert (let ((x 5)) (and (> x 0) (= h 11))))
            (assert (and (> 5 0) (= x 11)))
        ",
    );
    assert_eq!(ids.len(), 2);
    assert_eq!(ids[0], ids[1], "chained definitions stay capture-avoiding");
}

#[test]
fn test_define_fun_rec_body_not_captured() {
    let ids = elaborated_assertions(
        r"
            (declare-const x Int)
            (define-fun-rec r ((n Int)) Int (ite (= n 0) x (r (- n 1))))
            (assert (let ((x 5)) (and (> x 0) (= (r 2) 11))))
            (assert (and (> 5 0) (= x 11)))
        ",
    );
    assert_eq!(ids.len(), 2);
    assert_eq!(
        ids[0], ids[1],
        "define-fun-rec expansion is capture-avoiding"
    );
}

#[test]
fn test_define_funs_rec_body_not_captured() {
    // The mutually-recursive form expands through the same path. Confirmed at
    // the CLI too: with `(define-funs-rec ((p …) (q …)) …)` whose bodies name a
    // global `x`, `(assert (forall ((x Int)) (= (p 2) 11)))` answered `unsat`
    // where z3 answers `sat`.
    let ids = elaborated_assertions(
        r"
            (declare-const x Int)
            (define-funs-rec ((p ((n Int)) Int) (q ((n Int)) Int))
              ((ite (= n 0) x (q (- n 1)))
               (ite (= n 0) x (p (- n 1)))))
            (assert (let ((x 5)) (and (> x 0) (= (p 2) 11))))
            (assert (and (> 5 0) (= x 11)))
        ",
    );
    assert_eq!(ids.len(), 2);
    assert_eq!(
        ids[0], ids[1],
        "define-funs-rec expansion is capture-avoiding"
    );
}

#[test]
fn test_define_fun_body_not_captured_by_match_pattern_variable() {
    // A `match` pattern variable is a binder too (§3.6.5) and must not capture
    // the body's global.
    let ids = elaborated_assertions(
        r"
            (declare-const x Int)
            (define-fun f () Int x)
            (declare-datatypes ((Box 0)) (((mk (val Int)))))
            (declare-const b Box)
            (assert (match b (((mk x) (= f 11)))))
            (assert (= x 11))
        ",
    );
    assert_eq!(ids.len(), 2);
    assert_eq!(
        ids[0], ids[1],
        "a match pattern variable must not capture a macro body's global"
    );
}

#[test]
fn test_define_fun_parameter_still_binds_in_its_body() {
    // The other direction: capture-avoidance must not break ordinary parameter
    // binding. `(sq 7)` is `(* 7 7)`.
    let ids = elaborated_assertions(
        r"
            (define-fun sq ((n Int)) Int (* n n))
            (declare-const z Int)
            (assert (= z (sq 7)))
            (assert (= z (* 7 7)))
        ",
    );
    assert_eq!(ids.len(), 2);
    assert_eq!(
        ids[0], ids[1],
        "macro parameters must still bind in the body"
    );
}

// ---------------------------------------------------------------------------
// An UNRESOLVED sort name is an error, and a sort does not outlive its scope.
//
// SMT-LIB 2.6: every sort symbol must already be in the signature, and an
// assertion level owns the declarations made in it, so `(pop n)` removes them —
// `:global-declarations` opts out and defaults to false. AY used to turn any
// unresolved simple sort name into a fresh `Uninterpreted` sort, which accepted
// every mistyped sort name and re-invented a popped sort's NAME with its
// interpretation (and its finite domain) lost.

fn first_elaboration_error(input: &str) -> Option<ElaborateError> {
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            return Some(e);
        }
    }
    None
}

#[test]
fn test_unknown_sort_name_is_rejected() {
    let err = first_elaboration_error("(declare-fun t () Nonexistent)");
    assert!(
        matches!(err, Some(ElaborateError::UnknownSort(ref s)) if s == "Nonexistent"),
        "a sort name that is not in the signature must be rejected, got: {err:?}"
    );
}

#[test]
fn test_declare_sort_does_not_outlive_its_pop() {
    let err = first_elaboration_error(
        r"
            (push 1)
            (declare-sort S 0)
            (pop 1)
            (declare-fun t () S)
        ",
    );
    assert!(
        matches!(err, Some(ElaborateError::UnknownSort(ref s)) if s == "S"),
        "a sort declared inside a push must not survive the pop, got: {err:?}"
    );
}

#[test]
fn test_define_sort_does_not_outlive_its_pop() {
    let err = first_elaboration_error(
        r"
            (push 1)
            (define-sort MyInt () Int)
            (pop 1)
            (declare-fun t () MyInt)
        ",
    );
    assert!(
        matches!(err, Some(ElaborateError::UnknownSort(ref s)) if s == "MyInt"),
        "a sort synonym defined inside a push must not survive the pop, got: {err:?}"
    );
}

#[test]
fn test_datatype_sort_does_not_outlive_its_pop() {
    // The worst half of the leak: the popped datatype's NAME used to survive as
    // an uninterpreted sort, so its finite domain was silently lost.
    let err = first_elaboration_error(
        r"
            (push 1)
            (declare-datatypes ((D 0)) (((a) (b))))
            (pop 1)
            (declare-fun t () D)
        ",
    );
    assert!(
        matches!(err, Some(ElaborateError::UnknownSort(ref s)) if s == "D"),
        "a popped datatype's sort name must not survive as an uninterpreted sort, got: {err:?}"
    );
}

#[test]
fn test_sort_survives_pop_under_global_declarations() {
    // `:global-declarations true` is the documented opt-out and must still work.
    let err = first_elaboration_error(
        r"
            (set-option :global-declarations true)
            (push 1)
            (declare-sort S 0)
            (pop 1)
            (declare-fun t () S)
        ",
    );
    assert!(
        err.is_none(),
        ":global-declarations true must keep the sort declared, got: {err:?}"
    );
}

#[test]
fn test_declared_sort_in_scope_still_resolves() {
    // Guard against over-rejection: an in-scope `declare-sort` still works, and
    // so does the builtin `RoundingMode`, which is never `declare-sort`ed.
    let err = first_elaboration_error(
        r"
            (declare-sort S 0)
            (declare-fun t () S)
            (declare-fun rm () RoundingMode)
            (assert (= rm RNE))
        ",
    );
    assert!(err.is_none(), "in-scope sorts must still resolve: {err:?}");
}

#[test]
fn test_recursive_datatype_sort_is_in_scope_inside_its_own_declaration() {
    // A datatype is in scope inside its own declaration, so the carrier sort
    // must be registered before its field sorts are elaborated.
    let err = first_elaboration_error("(declare-datatype Lst ((nil) (cons (hd Int) (tl Lst))))");
    assert!(
        err.is_none(),
        "a recursive datatype must still elaborate: {err:?}"
    );
}

/// `is_single_shot_query` is the SCOPING precondition diagnostic consumers use
/// before treating `assertions_parsed()` as "the assertion set of the check-sat
/// I am accompanying". It must go false on the first `push`, on the first `pop`,
/// on `check-sat-assuming`, and from the SECOND `check-sat` onwards — including
/// after a matched push/pop pair has restored the scope depth to zero, which is
/// exactly the case a `scopes.is_empty()` test would miss.
#[test]
fn single_shot_query_tracks_scope_and_check_sat_commands() {
    let mut ctx = Context::new();
    assert!(ctx.is_single_shot_query());
    ctx.process_command(&Command::CheckSat).expect("check-sat");
    assert!(
        ctx.is_single_shot_query(),
        "the first check-sat is single-shot"
    );
    ctx.process_command(&Command::CheckSat).expect("check-sat");
    assert!(!ctx.is_single_shot_query(), "a second check-sat is not");

    // A matched push/pop pair leaves scope DEPTH at zero but the query is no
    // longer single-shot: an assertion made inside the scope is gone from
    // `assertions_parsed()` and a consumer must not assume it never existed.
    let mut ctx = Context::new();
    ctx.process_command(&Command::Push(1)).expect("push");
    assert!(!ctx.is_single_shot_query());
    ctx.process_command(&Command::Pop(1)).expect("pop");
    assert_eq!(ctx.scope_depth(), 0);
    assert!(!ctx.is_single_shot_query());

    // `check-sat-assuming` hides its assumptions from the surface export.
    let mut ctx = Context::new();
    ctx.process_command(&Command::CheckSatAssuming(Vec::new()))
        .expect("check-sat-assuming");
    assert!(!ctx.is_single_shot_query());
}
