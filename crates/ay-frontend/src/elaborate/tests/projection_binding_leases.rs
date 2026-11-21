// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn constant_context(logic: &str) -> Context {
    let mut context = Context::new();
    run(
        &mut context,
        &format!("(set-logic {logic})(declare-const p Int)"),
    );
    context
}

fn constant_binding(context: &Context, name: &str) -> CheckedProjectionBinding {
    context
        .check_projection_declaration(&ProjectionBindingRequest {
            symbol: Symbol::named(name),
            parameter_sorts: vec![],
            result_sort: Sort::Int,
        })
        .unwrap()
}

#[test]
fn projection_binding_lease_foreign_logic_token_cannot_resurrect_same_sort_source() {
    let mut original = constant_context("ALL");
    let mut target = constant_context("QF_LIA");
    let replacement = target.terms.mk_int(17.into());
    let checked = constant_binding(&target, "p");
    let prefix = target.terms.snapshot_stamp();
    let geometry = target
        .admit_projection_lookup_work_with_progress(1, &mut |_, _| true)
        .unwrap();
    let token = original.begin_internal_logic_borrow("AUFLIA".into());
    target.register_native_global_symbol("p".into(), replacement, Sort::Int);
    assert_eq!(
        original.source_revision, target.source_revision,
        "the old numeric-only check must actually collide"
    );
    assert!(geometry.matches_storage(&target));
    assert!(prefix.is_append_only_prefix_of(&target.terms));
    let before = target.source_context_stamp();
    let logic = target.logic().map(str::to_owned);
    target.end_internal_logic_borrow(token);
    assert_eq!(
        before,
        target.source_context_stamp(),
        "a foreign token changes no revision"
    );
    assert_eq!(
        logic.as_deref(),
        target.logic(),
        "a foreign token changes no typing logic"
    );
    retired(&target, &checked);
}

#[test]
fn projection_binding_lease_same_context_untouched_logic_borrow_preserves_currency() {
    let mut context = constant_context("ALL");
    let checked = constant_binding(&context, "p");
    let before = context.source_context_stamp();
    let token = context.begin_internal_logic_borrow("QF_LIA".into());
    assert!(!context.projection_binding_lease_still_current(&checked));
    context.end_internal_logic_borrow(token);
    assert_eq!(before, context.source_context_stamp());
    assert_eq!(context.logic(), Some("ALL"));
    assert!(context.projection_binding_lease_still_current(&checked));
    assert!(context.projection_binding_still_current(&checked));
}

#[test]
fn projection_binding_lease_clone_and_reset_numeric_collisions_refuse_old_logic_token() {
    let mut original = constant_context("ALL");
    let mut clone = original.clone();
    let token = original.begin_internal_logic_borrow("QF_LIA".into());
    let replacement = clone.terms.mk_int(17.into());
    let checked = constant_binding(&clone, "p");
    clone.register_native_global_symbol("p".into(), replacement, Sort::Int);
    assert_eq!(original.source_revision, clone.source_revision);
    let before = clone.source_context_stamp();
    clone.end_internal_logic_borrow(token);
    assert_eq!(before, clone.source_context_stamp());
    retired(&clone, &checked);

    let mut context = constant_context("ALL");
    let token = context.begin_internal_logic_borrow("QF_LIA".into());
    let collision = context.source_revision;
    context.process_command(&crate::Command::Reset).unwrap();
    run(&mut context, "(set-logic ALL)(declare-const p Int)");
    let replacement = context.terms.mk_int(17.into());
    let checked = constant_binding(&context, "p");
    context.register_native_global_symbol("p".into(), replacement, Sort::Int);
    assert_eq!(context.source_revision, collision);
    let before = context.source_context_stamp();
    context.end_internal_logic_borrow(token);
    assert_eq!(before, context.source_context_stamp());
    retired(&context, &checked);
}

#[test]
fn projection_binding_lease_revision_rollover_numeric_collision_refuses_old_logic_token() {
    let mut context = constant_context("ALL");
    let replacement = context.terms.mk_int(17.into());
    let token = context.begin_internal_logic_borrow("QF_LIA".into());
    let collision = context.source_revision;
    let old_identity = context.source_context_stamp();
    // Exercise the actual checked overflow branch without 2^64 declarations.
    // The following real namespace write rotates the private context identity.
    context.source_revision = u64::MAX;
    context.register_native_global_symbol("p".into(), replacement, Sort::Int);
    assert!(!old_identity.is_same_context(&context.source_context_stamp()));
    assert_eq!(context.source_revision, 0);
    context.set_logic("ALL".into());
    run(&mut context, "(declare-const q Int)");
    let checked = constant_binding(&context, "q");
    context.register_native_global_symbol("q".into(), replacement, Sort::Int);
    assert_eq!(context.source_revision, collision);
    let before = context.source_context_stamp();
    context.end_internal_logic_borrow(token);
    assert_eq!(before, context.source_context_stamp());
    retired(&context, &checked);
}

fn run(context: &mut Context, text: &str) {
    for command in parse(text).unwrap() {
        context.process_command(&command).unwrap();
    }
}

fn fixture(extra: &str) -> Context {
    let mut context = Context::new();
    run(&mut context, "(set-logic ALL)(declare-fun f (Int) Int)");
    run(&mut context, extra);
    context
}

fn binding(context: &Context) -> CheckedProjectionBinding {
    context
        .check_projection_declaration(&ProjectionBindingRequest {
            symbol: Symbol::named("f"),
            parameter_sorts: vec![Sort::Int],
            result_sort: Sort::Int,
        })
        .unwrap()
}

fn retired(context: &Context, checked: &CheckedProjectionBinding) {
    assert!(!context.projection_binding_lease_still_current(checked));
    assert!(!context.projection_binding_still_current(checked));
}

#[test]
fn projection_binding_lease_immutable_append_and_foreign_context() {
    let mut context = fixture("");
    let checked = binding(&context);
    for _ in 0..4 {
        assert!(context.projection_binding_still_current(&checked));
        assert!(context.projection_binding_lease_still_current(&checked));
    }
    // This lease covers the namespace only. Its model consumer separately
    // authenticates the append-only arena prefix and exact query roots.
    context.terms.mk_int(123.into());
    assert!(context.projection_binding_lease_still_current(&checked));
    assert!(context.projection_binding_still_current(&checked));
    retired(&context.clone(), &checked);
    retired(&Context::new(), &checked);
}

#[test]
fn projection_binding_lease_scope_and_identical_redeclaration_never_restore_currency() {
    let mut context = fixture("");
    run(&mut context, "(push 1)(declare-fun inner (Int) Int)");
    let checked = binding(&context);
    run(&mut context, "(pop 1)");
    retired(&context, &checked);
    let current = binding(&context);
    run(&mut context, "(push 1)(pop 1)");
    retired(&context, &current);
}

#[test]
fn projection_binding_lease_disappeared_and_recreated_source_never_adopts_receipt() {
    let mut context = fixture("");
    let checked = binding(&context);
    context.remove_symbols(&["f".into()]);
    assert!(!context.has_symbol_binding("f"));
    retired(&context, &checked);
    run(&mut context, "(declare-fun f (Int) Int)");
    assert!(context.has_symbol_binding("f"));
    retired(&context, &checked);
}

#[test]
fn projection_binding_lease_native_alias_and_same_sort_replacement_retire() {
    let mut context = fixture("");
    let checked = binding(&context);
    context
        .register_native_function_alias("alias".into(), "f".into(), vec![Sort::Int], Sort::Int)
        .unwrap();
    retired(&context, &checked);

    let mut context = fixture("");
    let checked = binding(&context);
    let value = context.terms.mk_var("replacement", Sort::Int);
    context.register_native_global_symbol("f".into(), value, Sort::Int);
    retired(&context, &checked);
    assert!(
        context
            .check_projection_declaration(&ProjectionBindingRequest {
                symbol: Symbol::named("f"),
                parameter_sorts: vec![],
                result_sort: Sort::Int,
            })
            .is_err(),
        "caller-supplied replacement is not direct source authority"
    );
}

#[test]
fn projection_binding_lease_adoption_and_rollback_cannot_resurrect_receipt() {
    let mut context = fixture("");
    let checked = binding(&context);
    let parameter = context.terms.mk_var("x", Sort::Int);
    assert!(context.try_register_native_adopted_macro_interp(
        "f",
        &[("x".into(), Sort::Int)],
        parameter,
        false,
    ));
    retired(&context, &checked);
    context.rollback_adopted_macro("f");
    retired(&context, &checked);
    let current = binding(&context);
    assert!(context.projection_binding_lease_still_current(&current));
}

#[test]
fn projection_binding_lease_unmaterialized_polymorphic_family_retires() {
    let mut context = fixture("");
    for index in 0..13 {
        run(&mut context, &format!("(declare-sort-parameter T{index})"));
    }
    let checked = binding(&context);
    let parameters = (0..13)
        .map(|index| format!("T{index}"))
        .collect::<Vec<_>>()
        .join(" ");
    run(
        &mut context,
        &format!("(declare-fun poly ({parameters}) T0)"),
    );
    assert_eq!(context.polymorphic_declarations.len(), 1);
    assert!(!context.has_symbol_binding("poly"), "Cartesian family exceeds materialization, so no concrete symbol performed the invalidation");
    retired(&context, &checked);
}

#[test]
fn projection_binding_lease_internal_map_write_survives_logic_borrow_restoration() {
    let mut context = fixture("(declare-const m (Array Int Int))");
    let checked = binding(&context);
    let borrow = context.begin_internal_logic_borrow("AUFLIA".into());
    run(&mut context, "(assert (map.contains_key m 3))");
    assert!(context
        .symbols
        .keys()
        .any(|name| name.starts_with("__ay_map_dom!")));
    context.end_internal_logic_borrow(borrow);
    retired(&context, &checked);
}

#[test]
fn projection_binding_lease_failed_recursive_placeholder_retires_before_restore() {
    for source in [
        "(define-fun-rec broken ((x Int)) Bool x)",
        "(define-funs-rec ((broken ((x Int)) Bool)) (x))",
    ] {
        let mut context = fixture("");
        let checked = binding(&context);
        let commands = parse(source).unwrap();
        assert!(context.process_command(&commands[0]).is_err());
        assert!(
            !context.has_symbol_binding("broken"),
            "temporary signature restored on failure"
        );
        retired(&context, &checked);
    }
}

#[test]
fn projection_binding_lease_eager_private_field_is_retired_before_unwind() {
    let mut context =
        fixture("(declare-datatype Box ((box (slot Int))))(declare-const v!slot Int)");
    let checked = context
        .check_projection_declaration(&ProjectionBindingRequest {
            symbol: Symbol::named("v!slot"),
            parameter_sorts: vec![],
            result_sort: Sort::Int,
        })
        .unwrap();
    let sort = context.resolve_native_sort_name("Box").unwrap();
    let declared = context.symbols.get("v!slot").unwrap().term;
    let previous_internal = context.internal_symbols.clone();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        // An eager private field is inserted before the outer declaration
        // finishes. Its insertion must retire the previous namespace lease.
        context.mk_declared_const_term("v", &sort, None);
        panic!("abort outer declaration after field registration");
    }));
    assert!(result.is_err());
    assert!(!context.internal_symbols.contains("v!slot"));
    assert_eq!(context.symbols.get("v!slot").unwrap().term, declared);
    assert!(context
        .internal_symbols
        .difference(&previous_internal)
        .any(|name| context.is_dt_field_identity(name)));
    retired(&context, &checked);
}
