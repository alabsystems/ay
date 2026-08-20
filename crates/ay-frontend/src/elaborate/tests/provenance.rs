// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::Command;

fn elaborate(script: &str) -> Context {
    let commands = parse(script).expect("parse provenance fixture");
    let mut context = Context::new();
    for command in &commands {
        context
            .process_command(command)
            .expect("elaborate provenance fixture");
    }
    context
}

fn unary_request(name: &str, sort: Sort) -> ProjectionBindingRequest {
    ProjectionBindingRequest {
        symbol: Symbol::named(name),
        parameter_sorts: vec![sort.clone()],
        result_sort: sort,
    }
}

fn unary_bv_context() -> Context {
    elaborate(
        r#"
        (declare-fun f ((_ BitVec 1)) (_ BitVec 1))
        (assert (forall ((x (_ BitVec 1))) (not (= (f x) x))))
        "#,
    )
}

fn reachable_named_application(context: &Context, root: TermId, name: &str) -> bool {
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        match context.terms.get(term) {
            TermData::App(symbol, arguments) => {
                if symbol.name() == name {
                    return true;
                }
                stack.extend(arguments.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                stack.extend([*condition, *then_term, *else_term]);
            }
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, value)| *value));
                stack.push(*body);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                stack.push(*body);
                stack.extend(triggers.iter().flatten().copied());
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            _ => {}
        }
    }
    false
}

#[test]
fn ordinary_free_function_binding_is_positive_and_snapshot_bound() {
    let context = unary_bv_context();
    let request = unary_request("f", Sort::bitvec(1));
    let checked = context
        .check_projection_bindings(&context.assertions, &[request])
        .expect("ordinary free function must bind");

    assert_eq!(checked.roots(), context.assertions);
    assert_eq!(checked.bindings().len(), 1);
    assert_eq!(checked.bindings()[0].symbol(), &Symbol::named("f"));
    assert_eq!(
        context.effective_declaration_kind(checked.bindings()[0].declaration_id()),
        Some(DeclarationKind::Uninterpreted)
    );
    assert!(context.projection_bindings_still_current(&checked, &context.assertions));
    assert!(!context.projection_bindings_still_current(&checked, &[]));
}

#[test]
fn standalone_projection_declaration_is_typed_and_epoch_bound() {
    let mut context = unary_bv_context();
    let request = unary_request("f", Sort::bitvec(1));
    let checked = context
        .check_projection_declaration(&request)
        .expect("ordinary free declaration must bind without root authority");

    assert_eq!(checked.symbol(), &Symbol::named("f"));
    assert_eq!(checked.parameter_sorts(), &[Sort::bitvec(1)]);
    assert_eq!(checked.result_sort(), &Sort::bitvec(1));
    assert!(context.projection_binding_still_current(&checked));

    context
        .process_command(&Command::Push(1))
        .expect("scope mutation");
    assert!(
        !context.projection_binding_still_current(&checked),
        "source/scope epoch changes must retire standalone evidence"
    );
}

#[test]
fn builtin_colliding_private_declaration_is_positive_and_epoch_bound() {
    let mut context = elaborate(
        r#"
        (declare-fun rem (Int Int) Int)
        (assert (= (rem 1 2) 0))
        "#,
    );
    let info = context.symbol_info("rem").expect("rem declaration");
    assert!(info.is_direct_source_declaration());
    let identity = info
        .internal_name
        .clone()
        .expect("builtin-colliding declaration must have a private core identity");
    assert_ne!(identity, "rem");
    assert!(reachable_named_application(
        &context,
        context.assertions[0],
        &identity
    ));

    let request = ProjectionBindingRequest {
        symbol: Symbol::named(&identity),
        parameter_sorts: vec![Sort::Int, Sort::Int],
        result_sort: Sort::Int,
    };
    let checked = context
        .check_projection_bindings(&context.assertions, &[request])
        .expect("an exact private identity owned by a direct declaration must bind");
    assert_eq!(checked.bindings()[0].symbol(), &Symbol::named(&identity));
    assert!(context.projection_bindings_still_current(&checked, &context.assertions));

    context
        .process_command(&Command::Push(1))
        .expect("scope mutation");
    assert!(
        !context.projection_bindings_still_current(&checked, &context.assertions),
        "source/scope epoch changes must retire private-identity evidence"
    );
}

#[test]
fn canonical_application_bypasses_same_spelled_private_declaration() {
    let mut context = elaborate(
        r#"
        (declare-fun = (Int Int) Bool)
        (assert (= 0 1))
        "#,
    );
    let private_identity = context
        .symbol_info("=")
        .and_then(|info| info.internal_name.clone())
        .expect("builtin-colliding declaration has a private identity");
    assert!(matches!(
        context.terms.get(context.assertions[0]),
        TermData::App(Symbol::Named(name), _) if name == &private_identity
    ));

    let zero = context.terms.mk_int(0.into());
    let one = context.terms.mk_int(1.into());
    let canonical = context
        .elaborate_canonical_theory_application("=", &[zero, one])
        .expect("canonical equality");
    assert!(
        context.terms.is_false(canonical),
        "the core identity must retain builtin equality semantics"
    );
    assert!(context
        .elaborate_canonical_theory_application(&private_identity, &[zero, one])
        .is_err());
}

#[test]
fn map_target_definitions_have_private_identity_and_expand_by_surface_name() {
    let cases: &[(&str, &[&str])] = &[
        (
            r#"
                (define-fun div ((x Int) (y Int)) Int x)
                (assert (= (div 7 3) 7))
            "#,
            &["div"],
        ),
        (
            r#"
                (define-fun-rec mod ((x Int)) Int
                    (ite (= x 0) 5 (mod 0)))
                (assert (= (mod 2) 5))
            "#,
            &["mod"],
        ),
        (
            r#"
                (define-funs-rec
                    ((abs ((x Int)) Int) (min ((x Int)) Int))
                    ((ite (= x 0) 11 (min 0))
                     (ite (= x 0) 11 (abs 0))))
                (assert (= (abs 2) 11))
                (assert (= (min 2) 11))
            "#,
            &["abs", "min"],
        ),
    ];

    for &(script, names) in cases {
        let context = elaborate(script);
        assert!(
            context
                .assertions
                .iter()
                .all(|&assertion| assertion == context.terms.true_term()),
            "uses of {names:?} must still expand through their surface-keyed definitions"
        );

        for &name in names {
            let info = context.symbol_info(name).expect("defined symbol metadata");
            let identity = info
                .internal_name
                .as_deref()
                .expect("a map-target definition must have a private core identity");
            assert_ne!(identity, name);
            assert_eq!(info.declaration_kind(), DeclarationKind::Defined);
            assert_eq!(
                context.effective_declaration_kind(info.declaration_id()),
                Some(DeclarationKind::Defined)
            );
            assert_eq!(context.dt_surface_name(identity), Some(name));
            assert!(context.symbol_info_by_identity(identity).is_some());
            assert!(
                context.symbol_info_by_identity(name).is_none(),
                "canonical theory identity `{name}` must have no non-theory owner"
            );
        }
    }
}

#[test]
fn native_private_alias_is_not_a_direct_source_declaration() {
    let mut context = Context::new();
    let identity = "native_private_projection_target";
    context
        .register_native_function_alias(
            "surface_alias".to_string(),
            identity.to_string(),
            vec![Sort::Int],
            Sort::Int,
        )
        .expect("register native alias");
    let alias = context.symbol_info("surface_alias").expect("alias binding");
    assert!(!alias.is_direct_source_declaration());

    let request = ProjectionBindingRequest {
        symbol: Symbol::named(identity),
        parameter_sorts: vec![Sort::Int],
        result_sort: Sort::Int,
    };
    assert_eq!(
        context.check_projection_declaration(&request).unwrap_err(),
        ProjectionBindingRejection::NonOrdinaryBinding {
            symbol: Symbol::named(identity),
        }
    );
}

#[test]
fn native_alias_requires_an_exact_live_target_for_canonical_theory_identity() {
    let mut context = Context::new();
    for (surface, identity, domain, range) in [
        (
            "forged_and",
            "and",
            vec![Sort::Bool, Sort::Bool],
            Sort::Bool,
        ),
        ("forged_div", "div", vec![Sort::Int, Sort::Int], Sort::Int),
    ] {
        let result = if identity == "div" {
            context.register_native_global_function_alias(
                surface.to_string(),
                identity.to_string(),
                domain,
                range,
            )
        } else {
            context.register_native_function_alias(
                surface.to_string(),
                identity.to_string(),
                domain,
                range,
            )
        };
        assert!(matches!(result, Err(ElaborateError::Unsupported(_))));
        assert!(
            context.symbol_info(surface).is_none(),
            "a rejected canonical alias must not mutate the symbol table"
        );
    }

    assert!(context
        .register_native_function_alias(
            "ordinary_alias".to_string(),
            "adapter.private.identity".to_string(),
            vec![Sort::Int],
            Sort::Int,
        )
        .expect("an absent private compatibility identity remains admissible"));

    let mut theory = elaborate("(declare-fun set.subset ((Array Int Bool) (Array Int Bool)) Bool)");
    let target = theory
        .symbol_info("set.subset")
        .expect("declaration-activated theory target")
        .clone();
    let set_sort = Sort::array(Sort::Int, Sort::Bool);
    assert!(theory
        .register_native_function_alias(
            "subset_alias".to_string(),
            "set.subset".to_string(),
            vec![set_sort.clone(), set_sort],
            Sort::Bool,
        )
        .expect("an exact live theory target remains aliasable"));
    let alias = theory
        .symbol_info("subset_alias")
        .expect("registered theory alias");
    assert_eq!(alias.declaration_id(), target.declaration_id());
    assert_eq!(alias.declaration_kind(), DeclarationKind::Theory);
}

#[test]
fn standalone_projection_declaration_rejects_interpreted_conversion() {
    let context = elaborate(
        r#"
        (set-logic LIRA)
        (declare-const x Int)
        (assert (= (to_real x) 0.0))
        "#,
    );
    let request = ProjectionBindingRequest {
        symbol: Symbol::named("to_real"),
        parameter_sorts: vec![Sort::Int],
        result_sort: Sort::Real,
    };

    assert!(
        context.check_projection_declaration(&request).is_err(),
        "an interpreted conversion must never produce free-UF binding evidence"
    );
}

#[test]
fn cancellation_stops_request_validation_and_reachable_freezing() {
    let context = unary_bv_context();
    let request = unary_request("f", Sort::bitvec(1));
    assert_eq!(
        context
            .check_projection_bindings_with_stop(
                &context.assertions,
                std::slice::from_ref(&request),
                || true,
            )
            .unwrap_err(),
        ProjectionBindingRejection::Stopped
    );

    let mut polls = 0;
    assert_eq!(
        context
            .check_projection_bindings_with_stop(
                &context.assertions,
                std::slice::from_ref(&request),
                || {
                    polls += 1;
                    polls >= 3
                },
            )
            .unwrap_err(),
        ProjectionBindingRejection::Stopped
    );
    assert_eq!(polls, 3);
}

#[test]
fn push_pop_invalidates_snapshot_but_restores_exact_outer_declaration() {
    let mut context = unary_bv_context();
    let request = unary_request("f", Sort::bitvec(1));
    let outer_id = context
        .symbol_info("f")
        .expect("outer declaration")
        .declaration_id()
        .clone();
    let checked = context
        .check_projection_bindings(&context.assertions, std::slice::from_ref(&request))
        .expect("outer binding");

    context
        .process_command(&Command::Push(1))
        .expect("push scope");
    assert!(!context.projection_bindings_still_current(&checked, &context.assertions));
    let scoped_declaration = parse("(declare-fun f (Bool) Bool)").expect("parse scoped overload");
    context
        .process_command(&scoped_declaration[0])
        .expect("scoped overload");
    context
        .process_command(&Command::Pop(1))
        .expect("pop scope");

    assert_eq!(
        context
            .symbol_info("f")
            .expect("restored outer declaration")
            .declaration_id(),
        &outer_id
    );
    assert!(!context.projection_bindings_still_current(&checked, &context.assertions));
    let refreshed = context
        .check_projection_bindings(&context.assertions, &[request])
        .expect("fresh evidence after pop");
    assert!(context.projection_bindings_still_current(&refreshed, &context.assertions));
}

#[test]
fn identical_redeclaration_after_pop_gets_a_fresh_declaration_id() {
    let commands = parse(
        r#"
        (push 1)
        (declare-fun f ((_ BitVec 1)) (_ BitVec 1))
        "#,
    )
    .expect("parse scoped declaration");
    let mut context = Context::new();
    for command in &commands {
        context.process_command(command).expect("declare in scope");
    }
    let scoped_id = context
        .symbol_info("f")
        .expect("scoped declaration")
        .declaration_id()
        .clone();
    context
        .process_command(&Command::Pop(1))
        .expect("pop declaration");
    context
        .process_command(
            &parse("(declare-fun f ((_ BitVec 1)) (_ BitVec 1))").expect("parse redeclaration")[0],
        )
        .expect("redeclare after pop");
    let redeclared_id = context
        .symbol_info("f")
        .expect("redeclared function")
        .declaration_id();

    assert_ne!(&scoped_id, redeclared_id);
}

#[test]
fn cloned_context_preserves_declarations_but_not_source_authority() {
    let context = unary_bv_context();
    let request = unary_request("f", Sort::bitvec(1));
    let checked = context
        .check_projection_bindings(&context.assertions, &[request])
        .expect("source binding");
    let clone = context.clone();

    assert_eq!(
        context
            .symbol_info("f")
            .expect("source declaration")
            .declaration_id(),
        clone
            .symbol_info("f")
            .expect("cloned declaration")
            .declaration_id()
    );
    assert_ne!(context.source_context_stamp(), clone.source_context_stamp());
    assert!(!clone.projection_bindings_still_current(&checked, &clone.assertions));
}

#[test]
fn reset_mints_a_new_context_identity_and_retires_old_evidence() {
    let mut context = unary_bv_context();
    let checked = context
        .check_projection_bindings(&context.assertions, &[unary_request("f", Sort::bitvec(1))])
        .expect("source binding");
    let old_roots = context.assertions.clone();

    context
        .process_command(&Command::Reset)
        .expect("reset context");

    assert!(!context.projection_bindings_still_current(&checked, &old_roots));
}

#[test]
fn source_revision_rollover_rotates_context_identity() {
    let mut context = unary_bv_context();
    let before = context.source_context_stamp();
    context.source_revision = u64::MAX;
    let exhausted = context.source_context_stamp();

    context.advance_source_revision();

    let rotated = context.source_context_stamp();
    assert_ne!(exhausted, rotated);
    assert_ne!(before, rotated);
    context.advance_source_revision();
    assert_ne!(exhausted, context.source_context_stamp());
}

#[test]
fn declare_sort_parameter_retires_projection_evidence() {
    let mut context = unary_bv_context();
    let roots = context.assertions.clone();
    let checked = context
        .check_projection_bindings(&roots, &[unary_request("f", Sort::bitvec(1))])
        .expect("binding before source-environment mutation");
    let old_stamp = context.source_context_stamp();

    context
        .process_command(&Command::DeclareSortParameter("T".to_string()))
        .expect("declare sort parameter");

    assert_ne!(context.source_context_stamp(), old_stamp);
    assert!(!context.projection_bindings_still_current(&checked, &roots));
}

#[test]
fn reset_assertions_retires_evidence_and_unadopts_definitions() {
    let mut context = unary_bv_context();
    let old_roots = context.assertions.clone();
    let checked = context
        .check_projection_bindings(&old_roots, &[unary_request("f", Sort::bitvec(1))])
        .expect("binding before reset-assertions");
    let old_stamp = context.source_context_stamp();
    context
        .process_command(&Command::ResetAssertions)
        .expect("reset assertions");
    let rebuilt_assertion = parse("(assert (forall ((x (_ BitVec 1))) (not (= (f x) x))))")
        .expect("parse rebuilt assertion");
    context
        .process_command(&rebuilt_assertion[0])
        .expect("rebuild identical assertion");

    // Re-elaborating a quantifier intentionally creates fresh binder identities,
    // so root TermIds need not repeat. The source epoch itself must still retire
    // the old binding evidence independently of that fresh term graph.
    assert_ne!(context.source_context_stamp(), old_stamp);
    assert!(!context.projection_bindings_still_current(&checked, &context.assertions));

    let mut adopted = elaborate(
        r#"
        (declare-fun g ((_ BitVec 1)) (_ BitVec 1))
        (assert (forall ((x (_ BitVec 1))) (= (g x) x)))
        "#,
    );
    let adopted_id = adopted
        .symbol_info("g")
        .expect("adopted declaration")
        .declaration_id()
        .clone();
    let adopted_stamp = adopted.source_context_stamp();
    assert_eq!(
        adopted.effective_declaration_kind(&adopted_id),
        Some(DeclarationKind::AdoptedDefinition)
    );

    adopted
        .process_command(&Command::ResetAssertions)
        .expect("unadopt definition");

    assert_ne!(adopted.source_context_stamp(), adopted_stamp);
    assert_eq!(
        adopted.effective_declaration_kind(&adopted_id),
        Some(DeclarationKind::Uninterpreted)
    );
    assert!(adopted.adopted_macro_interp("g").is_none());
}

#[test]
fn scoped_definition_is_not_adopted_or_leaked_after_pop() {
    let context = elaborate(
        r#"
        (declare-fun f ((_ BitVec 1)) (_ BitVec 1))
        (push 1)
        (assert (forall ((x (_ BitVec 1))) (= (f x) x)))
        (pop 1)
        (assert (not (= (f #b0) #b0)))
        "#,
    );
    let &[assertion] = context.assertions.as_slice() else {
        panic!("only the post-pop assertion must remain")
    };

    // The live formula is satisfiable with f(#b0) = #b1. Adopting the scoped
    // definition and leaking it across `pop` would rewrite the application to
    // #b0 and fold this assertion to false, creating a wrong-UNSAT reduction.
    assert!(context.adopted_macro_interp("f").is_none());
    assert_ne!(assertion, context.terms.false_term());
    assert!(
        reachable_named_application(&context, assertion, "f"),
        "the post-pop application must once again denote the free UF"
    );
}

#[test]
fn defined_and_adopted_functions_are_never_free_bindings() {
    let defined = elaborate("(define-fun f ((x (_ BitVec 1))) (_ BitVec 1) x)");
    let request = unary_request("f", Sort::bitvec(1));
    assert_eq!(
        defined
            .check_projection_bindings(&[], std::slice::from_ref(&request))
            .unwrap_err(),
        ProjectionBindingRejection::NonFreeDeclaration {
            symbol: Symbol::named("f"),
            kind: DeclarationKind::Defined,
        }
    );

    let mut adopted = elaborate("(declare-fun f ((_ BitVec 1)) (_ BitVec 1))");
    let body = adopted.terms.mk_fresh_var("adopted_body", Sort::bitvec(1));
    assert!(adopted.try_register_native_adopted_macro_interp(
        "f",
        &[("x".to_string(), Sort::bitvec(1))],
        body,
        false,
    ));
    let id = adopted
        .symbol_info("f")
        .expect("adopted declaration")
        .declaration_id();
    assert_eq!(
        adopted.effective_declaration_kind(id),
        Some(DeclarationKind::AdoptedDefinition)
    );
    assert_eq!(
        adopted
            .check_projection_bindings(&[], &[request])
            .unwrap_err(),
        ProjectionBindingRejection::NonFreeDeclaration {
            symbol: Symbol::named("f"),
            kind: DeclarationKind::AdoptedDefinition,
        }
    );
}

#[test]
fn standalone_declaration_binding_accepts_an_ordinary_nullary_constant() {
    let context = elaborate("(declare-const c Int)");
    let request = ProjectionBindingRequest {
        symbol: Symbol::named("c"),
        parameter_sorts: Vec::new(),
        result_sort: Sort::Int,
    };
    let checked = context
        .check_projection_declaration(&request)
        .expect("an ordinary nullary declaration has exact source identity");

    assert_eq!(checked.symbol(), &Symbol::named("c"));
    assert!(checked.parameter_sorts().is_empty());
    assert_eq!(checked.result_sort(), &Sort::Int);
    assert!(context.projection_binding_still_current(&checked));
}

#[test]
fn nullary_declaration_binding_rejects_pop_and_identical_redeclaration() {
    let mut context = Context::new();
    context
        .process_command(&Command::Push(1))
        .expect("push declaration scope");
    context
        .process_command(&parse("(declare-const c Int)").expect("parse declaration")[0])
        .expect("declare scoped constant");
    let request = ProjectionBindingRequest {
        symbol: Symbol::named("c"),
        parameter_sorts: Vec::new(),
        result_sort: Sort::Int,
    };
    let checked = context
        .check_projection_declaration(&request)
        .expect("bind scoped constant");

    context
        .process_command(&Command::Pop(1))
        .expect("pop scoped constant");
    context
        .process_command(&parse("(declare-const c Int)").expect("parse redeclaration")[0])
        .expect("redeclare identical constant");

    assert!(
        !context.projection_binding_still_current(&checked),
        "textual name/signature equality cannot replace declaration identity"
    );
}

#[test]
fn theory_declarations_cannot_be_adopted_as_free_definitions() {
    let mut context =
        elaborate("(declare-fun set.subset ((Array Int Bool) (Array Int Bool)) Bool)");
    let theory_id = context
        .symbol_info("set.subset")
        .expect("theory declaration")
        .declaration_id()
        .clone();
    assert_eq!(
        context.effective_declaration_kind(&theory_id),
        Some(DeclarationKind::Theory)
    );
    let body = context.terms.false_term();
    assert!(
        !context.try_register_native_adopted_macro_interp(
            "set.subset",
            &[
                ("a".to_string(), Sort::array(Sort::Int, Sort::Bool)),
                ("b".to_string(), Sort::array(Sort::Int, Sort::Bool)),
            ],
            body,
            false,
        ),
        "the native adoption entrypoint must enforce the same declaration kind"
    );

    let assertion = parse(
        r#"
        (assert
          (forall ((a (Array Int Bool)) (b (Array Int Bool)))
            (= (set.subset a b) false)))
        "#,
    )
    .expect("parse theory-definition attack");
    context
        .process_command(&assertion[0])
        .expect("elaborate theory-definition attack");

    assert!(
        context.adopted_macro_interp("set.subset").is_none(),
        "a fixed-semantics theory predicate is never a free definitional macro"
    );
    assert_eq!(
        context.effective_declaration_kind(&theory_id),
        Some(DeclarationKind::Theory)
    );
    assert!(matches!(
        context.assertions.as_slice(),
        [root] if matches!(context.terms.get(*root), TermData::Forall(_, _, _))
    ));
}

#[test]
fn internal_theory_datatype_and_overloaded_bindings_fail_closed() {
    let mut internal = Context::new();
    internal.symbols.insert(
        "__ay_binding_internal".to_string(),
        SymbolInfo::fresh(
            None,
            Sort::Bool,
            vec![Sort::Bool],
            PublicSort::Core(Sort::Bool),
            vec![PublicSort::Core(Sort::Bool)],
            None,
            DeclarationKind::SolverInternal,
        ),
    );
    internal.advance_source_revision();
    assert_eq!(
        internal
            .check_projection_bindings(&[], &[unary_request("__ay_binding_internal", Sort::Bool)],)
            .unwrap_err(),
        ProjectionBindingRejection::NonFreeDeclaration {
            symbol: Symbol::named("__ay_binding_internal"),
            kind: DeclarationKind::SolverInternal,
        }
    );

    let theory = elaborate("(declare-fun set.subset ((Array Int Bool) (Array Int Bool)) Bool)");
    let theory_request = ProjectionBindingRequest {
        symbol: Symbol::named("set.subset"),
        parameter_sorts: vec![
            Sort::array(Sort::Int, Sort::Bool),
            Sort::array(Sort::Int, Sort::Bool),
        ],
        result_sort: Sort::Bool,
    };
    assert!(matches!(
        theory.check_projection_bindings(&[], &[theory_request]),
        Err(ProjectionBindingRejection::NonFreeDeclaration {
            kind: DeclarationKind::Theory,
            ..
        })
    ));

    let datatype = elaborate("(declare-datatype D ((C (field Bool))))");
    assert!(matches!(
        datatype.check_projection_bindings(
            &[],
            &[ProjectionBindingRequest {
                symbol: Symbol::named("C"),
                parameter_sorts: vec![Sort::Bool],
                result_sort: Sort::Uninterpreted("D".to_string()),
            }],
        ),
        Err(ProjectionBindingRejection::NonFreeDeclaration {
            kind: DeclarationKind::DatatypeConstructor,
            ..
        })
    ));

    let nullary_datatype = elaborate("(declare-datatype Nat ((zero) (succ (pred Nat))))");
    assert!(matches!(
        nullary_datatype.check_projection_bindings(
            &[],
            &[ProjectionBindingRequest {
                symbol: Symbol::named("zero"),
                parameter_sorts: Vec::new(),
                result_sort: Sort::Uninterpreted("Nat".to_string()),
            }],
        ),
        Err(ProjectionBindingRejection::NonFreeDeclaration {
            kind: DeclarationKind::DatatypeConstructor,
            ..
        })
    ));
    for (symbol, kind) in [
        ("field", DeclarationKind::DatatypeSelector),
        ("is-C", DeclarationKind::DatatypeTester),
    ] {
        assert!(matches!(
            datatype.check_projection_bindings(
                &[],
                &[ProjectionBindingRequest {
                    symbol: Symbol::named(symbol),
                    parameter_sorts: vec![Sort::Uninterpreted("D".to_string())],
                    result_sort: Sort::Bool,
                }],
            ),
            Err(ProjectionBindingRejection::NonFreeDeclaration {
                kind: found,
                ..
            }) if found == kind
        ));
    }

    let overloaded = elaborate(
        r#"
        (declare-fun f ((_ BitVec 1)) (_ BitVec 1))
        (declare-fun f (Bool) Bool)
        "#,
    );
    assert_eq!(
        overloaded
            .check_projection_bindings(&[], &[unary_request("f", Sort::bitvec(1))])
            .unwrap_err(),
        ProjectionBindingRejection::NonOrdinaryBinding {
            symbol: Symbol::named("f"),
        }
    );
}

#[test]
fn selected_signature_and_closed_function_set_are_rechecked() {
    let context = elaborate(
        r#"
        (declare-fun f ((_ BitVec 1)) (_ BitVec 1))
        (declare-fun g ((_ BitVec 1)) (_ BitVec 1))
        (assert (forall ((x (_ BitVec 1))) (= (f x) (g x))))
        "#,
    );
    assert!(matches!(
        context.check_projection_bindings(
            &context.assertions,
            &[unary_request("f", Sort::bitvec(1))],
        ),
        Err(ProjectionBindingRejection::UnselectedDeclarationOccurrence { .. })
    ));
    assert_eq!(
        context
            .check_projection_bindings(&context.assertions, &[unary_request("f", Sort::bitvec(2))],)
            .unwrap_err(),
        ProjectionBindingRejection::SignatureMismatch {
            symbol: Symbol::named("f"),
        }
    );
}

#[test]
fn native_alias_preserves_target_identity_and_kind_but_is_not_ordinary() {
    let mut context = elaborate("(declare-fun target ((_ BitVec 1)) (_ BitVec 1))");
    let target_id = context
        .symbol_info("target")
        .expect("target declaration")
        .declaration_id()
        .clone();
    assert!(context
        .register_native_function_alias(
            "alias".to_string(),
            "target".to_string(),
            vec![Sort::bitvec(1)],
            Sort::bitvec(1),
        )
        .expect("register native alias"));

    let alias = context.symbol_info("alias").expect("alias binding");
    assert_eq!(alias.declaration_id(), &target_id);
    assert_eq!(alias.declaration_kind(), DeclarationKind::Uninterpreted);
    assert_eq!(alias.internal_name.as_deref(), Some("target"));

    let x = context.terms.mk_fresh_var("x", Sort::bitvec(1));
    let application = context
        .terms
        .mk_app(Symbol::named("target"), [x], Sort::bitvec(1));
    assert!(matches!(
        context.check_projection_bindings(
            &[application],
            &[unary_request("target", Sort::bitvec(1))],
        ),
        Err(ProjectionBindingRejection::AmbiguousDeclaration { .. }
            | ProjectionBindingRejection::NonOrdinaryBinding { .. })
    ));
}

#[test]
fn frozen_reachable_terms_detect_suffix_rollback() {
    let mut context = elaborate("(declare-fun f ((_ BitVec 1)) (_ BitVec 1))");
    let checkpoint = context.terms.rollback_checkpoint();
    let argument = context.terms.mk_fresh_var("rollback_arg", Sort::bitvec(1));
    let root = context
        .terms
        .mk_app(Symbol::named("f"), [argument], Sort::bitvec(1));
    let checked = context
        .check_projection_bindings(&[root], &[unary_request("f", Sort::bitvec(1))])
        .expect("binding before speculative rollback");

    // Deliberately model a stale consumer retaining the evidence after the
    // speculative owner violated the rollback retention contract.  The frozen
    // snapshot must still fail closed rather than accepting a reused TermId.
    context.terms.rollback_to(checkpoint);

    assert!(!context.projection_bindings_still_current(&checked, &[root]));
}

/// An internal sub-solve that borrows the logic slot and puts it back must
/// leave the source-context stamp EQUAL to the one captured before it.
///
/// Regression for the `fp.to_real` two-phase lane
/// (`Executor::solve_rewritten_mixed_subproblem`), which inferred a logic for
/// its FP-free subproblem and restored the caller's on exit. With two plain
/// `set_logic` calls the revision advanced twice, so the stamp never returned
/// and `Executor::authenticate_unsat_query_scope` discarded a correct UNSAT as
/// "the public UNSAT source context is no longer current".
#[test]
fn internal_logic_borrow_restores_the_source_context_stamp() {
    let mut context = elaborate("(set-logic QF_UFLRA)\n(declare-fun f (Real) Real)");
    let bound = context.source_context_stamp();

    let borrow = context.begin_internal_logic_borrow("QF_LRA".to_string());
    assert!(
        context.source_context_stamp() != bound,
        "the borrow must be observable WHILE it is held; otherwise this test \
         would pass on a `set_logic` that silently did nothing"
    );
    context.end_internal_logic_borrow(borrow);

    assert!(
        context.source_context_stamp() == bound,
        "an exactly-restoring internal borrow changes nothing observable, so \
         the stamp the mandatory UNSAT gate compares must come back"
    );
    assert_eq!(context.logic(), Some("QF_UFLRA"));
}

/// FAIL-CLOSED HALF, and the reason the rollback is safe: a declaration made
/// INSIDE the borrow is a genuine source-context change, so the stamp must NOT
/// be rolled back over it.
#[test]
fn internal_logic_borrow_does_not_roll_back_over_a_real_source_change() {
    let mut context = elaborate("(set-logic QF_UFLRA)\n(declare-fun f (Real) Real)");
    let bound = context.source_context_stamp();

    let borrow = context.begin_internal_logic_borrow("QF_LRA".to_string());
    context
        .process_command(&parse("(declare-fun g (Real) Real)").expect("parse")[0])
        .expect("declare inside the borrow");
    context.end_internal_logic_borrow(borrow);

    assert!(
        context.source_context_stamp() != bound,
        "a declaration inside the borrow really did change the source scope; \
         rolling the revision back over it would let a stale query certify"
    );
    assert_eq!(context.logic(), Some("QF_UFLRA"));
}
