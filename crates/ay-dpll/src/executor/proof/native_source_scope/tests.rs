// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_frontend::command::Term as Parsed;

fn marker() -> Parsed {
    Parsed::Symbol(crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER.to_owned())
}

fn fixture() -> Executor {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let root = exec.ctx.terms.mk_fresh_var("native_input", Sort::Bool);
    exec.ctx.add_native_assertion_with_parsed(root, marker());
    begin(&mut exec);
    exec
}

fn begin(exec: &mut Executor) {
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
}

fn capture(exec: &Executor) -> NativeProofSourceScope {
    let permit = exec.detached_authored_plain_hard_permit_for_test().unwrap();
    NativeProofSourceScope::capture(exec, &permit).expect("exact native plain input must capture")
}

#[test]
fn source_capture_survives_append_only_proof_terms_without_refreshing_input_hash() {
    let mut exec = fixture();
    let scope = capture(&exec);
    let digest = scope.full_typed_query_sha256();
    let _derived = exec.ctx.terms.mk_fresh_var("proof_auxiliary", Sort::Int);
    assert!(scope.is_current_after_proof_growth(&exec));
    assert_eq!(scope.full_typed_query_sha256(), digest);
    assert_eq!(scope.roots(), exec.ctx.assertions);
    assert_eq!(scope.root_entries().len(), scope.roots().len());
}

#[test]
fn later_identical_query_and_sibling_context_reject_old_scope() {
    let mut exec = fixture();
    let scope = capture(&exec);
    let mut sibling = Executor::new();
    sibling.ctx = exec.ctx.clone();
    begin(&mut sibling);
    assert!(!scope.is_current_after_proof_growth(&sibling));
    begin(&mut exec);
    assert_eq!(scope.roots(), exec.ctx.assertions);
    assert!(!scope.is_current_after_proof_growth(&exec));
    assert!(capture(&exec).is_current_after_proof_growth(&exec));
}

#[test]
fn scope_rejects_source_scope_and_declaration_changes() {
    for script in ["(push 1)(pop 1)", "(declare-const later Int)"] {
        let mut exec = fixture();
        let scope = capture(&exec);
        exec.execute_all(&ay_frontend::parse(script).unwrap())
            .unwrap();
        assert!(!scope.is_current_after_proof_growth(&exec), "{script}");
    }
}

#[test]
fn source_entry_slot_reuse_cannot_inherit_capture() {
    let mut exec = Executor::new();
    let checkpoint = exec.ctx.terms.rollback_checkpoint();
    let old = exec
        .ctx
        .terms
        .mk_fresh_var("reused_native_input", Sort::Bool);
    exec.ctx.add_native_assertion_with_parsed(old, marker());
    begin(&mut exec);
    let scope = capture(&exec);
    exec.ctx.terms.rollback_to(checkpoint);
    let replacement = exec
        .ctx
        .terms
        .mk_fresh_var("reused_native_input", Sort::Bool);
    assert_eq!(old, replacement);
    assert!(!scope.is_current_after_proof_growth(&exec));
}

#[test]
fn checker_metadata_change_retires_scope_without_reusing_root_entries() {
    let mut exec = fixture();
    let scope = capture(&exec);
    let entries = scope.root_entries().to_vec();
    exec.ctx.terms.mark_to_real_shadowed();
    assert_eq!(entries, scope.root_entries());
    assert_ne!(
        scope.checker_metadata_generation(),
        exec.ctx.terms.checker_visible_metadata_generation()
    );
    assert!(!scope.is_current_after_proof_growth(&exec));
}

#[test]
fn original_free_variable_set_respects_quantifier_and_simultaneous_let_scopes() {
    for use_let in [false, true] {
        let mut exec = Executor::new();
        let shadow = exec.ctx.terms.mk_var("lexical_shadow", Sort::Int);
        let outside = exec.ctx.terms.mk_var("lexical_outside", Sort::Int);
        let body = exec.ctx.terms.mk_eq(shadow, outside);
        let root = if use_let {
            exec.ctx
                .terms
                .mk_let(vec![("lexical_shadow".to_owned(), shadow)], body)
        } else {
            exec.ctx.terms.mk_forall_with_triggers(
                vec![("lexical_shadow".to_owned(), Sort::Int)],
                body,
                vec![vec![shadow, outside]],
            )
        };
        exec.ctx.add_native_assertion_with_parsed(root, marker());
        begin(&mut exec);
        let scope = capture(&exec);
        let free: Vec<_> = scope
            .free_variables()
            .iter()
            .map(|variable| variable.term)
            .collect();
        assert!(free.contains(&outside));
        assert_eq!(
            free.contains(&shadow),
            use_let,
            "let RHS remains in its outer scope"
        );
        for variable in scope.free_variables() {
            assert_eq!(
                exec.ctx.terms.entry_stamp(variable.term),
                Some(variable.entry)
            );
            assert_eq!(exec.ctx.terms.sort(variable.term), &variable.sort);
        }
    }
}

#[test]
fn free_variable_identities_are_not_merged_by_name_or_sort() {
    let mut exec = Executor::new();
    let a = exec
        .ctx
        .terms
        .mk_fresh_named_var("shared_spelling", Sort::Bool);
    let b = exec
        .ctx
        .terms
        .mk_fresh_named_var("shared_spelling", Sort::Bool);
    exec.ctx.add_native_assertion_with_parsed(a, marker());
    exec.ctx.add_native_assertion_with_parsed(b, marker());
    begin(&mut exec);
    let scope = capture(&exec);
    assert_eq!(
        scope
            .free_variables()
            .iter()
            .map(|variable| variable.term)
            .collect::<Vec<_>>(),
        vec![a, b]
    );
}

#[test]
fn text_mixed_assumptions_definitions_and_datatypes_decline() {
    let mut malformed = Executor::new();
    let integer_root = malformed.ctx.terms.mk_int(0.into());
    malformed
        .ctx
        .add_native_assertion_with_parsed(integer_root, marker());
    begin(&mut malformed);
    let permit = malformed
        .detached_authored_plain_hard_permit_for_test()
        .unwrap();
    assert!(NativeProofSourceScope::capture(&malformed, &permit).is_none());

    let mut text = Executor::new();
    text.execute_all(&ay_frontend::parse("(assert true)").unwrap())
        .unwrap();
    begin(&mut text);
    let permit = text.detached_authored_plain_hard_permit_for_test().unwrap();
    assert!(NativeProofSourceScope::capture(&text, &permit).is_none());

    let mut mixed = fixture();
    let root = mixed.ctx.terms.true_term();
    mixed.ctx.add_assertion_with_parsed(root, marker());
    begin(&mut mixed);
    let permit = mixed
        .detached_authored_plain_hard_permit_for_test()
        .unwrap();
    assert!(NativeProofSourceScope::capture(&mixed, &permit).is_none());

    let mut assumed = fixture();
    assumed.begin_public_solve(false);
    assumed.bind_unsat_query_assumptions(&assumed.ctx.assertions.clone());
    let permit = assumed
        .detached_authored_plain_hard_permit_for_test()
        .unwrap();
    assert!(NativeProofSourceScope::capture(&assumed, &permit).is_none());

    for setup in ["(define-fun hidden () Int 1)"] {
        let mut exec = fixture();
        exec.execute_all(&ay_frontend::parse(setup).unwrap())
            .unwrap();
        begin(&mut exec);
        let permit = exec.detached_authored_plain_hard_permit_for_test().unwrap();
        assert!(
            NativeProofSourceScope::capture(&exec, &permit).is_none(),
            "{setup}"
        );
    }
}

#[test]
fn source_capture_retains_typed_datatype_member_ownership_and_retires_on_redeclaration() {
    let mut exec = fixture();
    exec.execute_all(&ay_frontend::parse("(push 1)(declare-datatype Hidden ((hidden)))").unwrap())
        .unwrap();
    begin(&mut exec);
    let scope = capture(&exec);
    assert_eq!(scope.datatypes.declarations().len(), 1);
    assert_eq!(scope.datatypes.signatures().len(), 2);
    assert!(scope.is_current_after_proof_growth(&exec));
    let old = scope.datatypes.signatures()[0].identity.clone();
    exec.execute_all(&ay_frontend::parse("(pop 1)(declare-datatype Hidden ((hidden)))").unwrap())
        .unwrap();
    begin(&mut exec);
    assert!(!scope.is_current_after_proof_growth(&exec));
    let current = capture(&exec);
    assert_eq!(
        current.datatypes.declarations().len(),
        2,
        "retained old definitions remain distinct from new visible names"
    );
    assert!(current
        .datatypes
        .signatures()
        .iter()
        .any(|signature| signature.identity == old));
    assert_ne!(
        scope.declaration_context_sha256(),
        current.declaration_context_sha256()
    );
}

#[test]
fn source_capture_refuses_unowned_nominal_sorts() {
    let mut exec = Executor::new();
    let x = exec
        .ctx
        .terms
        .mk_fresh_var("unowned", Sort::Uninterpreted("missing_carrier".into()));
    let y = exec
        .ctx
        .terms
        .mk_fresh_var("another", Sort::Uninterpreted("missing_carrier".into()));
    let root = exec.ctx.terms.mk_eq(x, y);
    exec.ctx.add_native_assertion_with_parsed(root, marker());
    begin(&mut exec);
    let permit = exec.detached_authored_plain_hard_permit_for_test().unwrap();
    assert!(NativeProofSourceScope::capture(&exec, &permit).is_none());

    let mut exec = Executor::new();
    let body = exec.ctx.terms.mk_fresh_var("body", Sort::Bool);
    let root = exec.ctx.terms.mk_forall(
        vec![(
            "unused".into(),
            Sort::Uninterpreted("missing_unused_carrier".into()),
        )],
        body,
    );
    exec.ctx.add_native_assertion_with_parsed(root, marker());
    begin(&mut exec);
    let permit = exec.detached_authored_plain_hard_permit_for_test().unwrap();
    assert!(
        NativeProofSourceScope::capture(&exec, &permit).is_none(),
        "an unused binder type is still declaration-owned source"
    );
}

#[test]
fn native_diagnostic_scope_refuses_unowned_application_and_wrong_declared_signature() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("argument", Sort::Int);
    let unknown = exec
        .ctx
        .terms
        .mk_app(Symbol::named("missing_function"), [x], Sort::Bool);
    exec.ctx.add_native_assertion_with_parsed(unknown, marker());
    begin(&mut exec);
    let scope = capture(&exec);
    assert_eq!(
        scope.diagnostic_applications_are_declared_with_progress(&exec, &mut |_, _| true),
        Some(false)
    );

    let mut exec = Executor::new();
    exec.execute_all(&ay_frontend::parse("(declare-fun owned_function (Int) Bool)").unwrap())
        .unwrap();
    let x = exec.ctx.terms.mk_fresh_var("argument", Sort::Real);
    let wrong = exec
        .ctx
        .terms
        .mk_app(Symbol::named("owned_function"), [x], Sort::Bool);
    exec.ctx.add_native_assertion_with_parsed(wrong, marker());
    begin(&mut exec);
    let scope = capture(&exec);
    assert_eq!(
        scope.diagnostic_applications_are_declared_with_progress(&exec, &mut |_, _| true),
        Some(false)
    );
}

#[test]
fn native_diagnostic_scope_refuses_untransported_interpretation_switches() {
    for mark in [
        ay_core::TermStore::mark_to_real_shadowed as fn(&mut ay_core::TermStore),
        ay_core::TermStore::mark_is_int_shadowed,
    ] {
        let mut exec = fixture();
        mark(&mut exec.ctx.terms);
        begin(&mut exec);
        let scope = capture(&exec);
        assert!(scope.is_current_after_proof_growth(&exec));
        assert_eq!(
            scope.diagnostic_applications_are_declared_with_progress(&exec, &mut |_, _| true),
            Some(false),
            "v3 cannot discard a native interpretation switch and claim exact-source replay"
        );
    }
}

#[test]
fn full_digest_preserves_root_order_and_duplicate_occurrences() {
    let order_digest = |reverse| {
        let mut exec = Executor::new();
        let a = exec.ctx.terms.mk_fresh_var("order_a", Sort::Bool);
        let b = exec.ctx.terms.mk_fresh_var("order_b", Sort::Bool);
        let roots = if reverse { [b, a] } else { [a, b] };
        for root in roots {
            exec.ctx.add_native_assertion_with_parsed(root, marker());
        }
        begin(&mut exec);
        capture(&exec)
    };
    let forward = order_digest(false);
    let reverse = order_digest(true);
    assert_eq!(
        forward.declaration_context_sha256(),
        reverse.declaration_context_sha256()
    );
    assert_ne!(
        forward.full_typed_query_sha256(),
        reverse.full_typed_query_sha256()
    );
    let mut exec = fixture();
    let first = capture(&exec);
    let a = exec.ctx.assertions[0];
    let b = exec
        .ctx
        .terms
        .mk_fresh_var("other_native_input", Sort::Bool);
    exec.ctx.add_native_assertion_with_parsed(b, marker());
    begin(&mut exec);
    let ordered = capture(&exec);
    assert_ne!(
        first.full_typed_query_sha256(),
        ordered.full_typed_query_sha256()
    );
    exec.ctx.add_native_assertion_with_parsed(a, marker());
    begin(&mut exec);
    let duplicate = capture(&exec);
    assert_eq!(duplicate.roots(), &[a, b, a]);
    assert_ne!(
        ordered.full_typed_query_sha256(),
        duplicate.full_typed_query_sha256()
    );
    assert_eq!(
        ordered.declaration_context_sha256(),
        duplicate.declaration_context_sha256()
    );
}

#[test]
fn full_digest_keeps_unused_quantifier_trigger_metadata() {
    let digest = |extra_trigger| {
        let mut exec = Executor::new();
        let q = exec.ctx.terms.mk_var("bound_input", Sort::Int);
        let zero = exec.ctx.terms.mk_int(0.into());
        let body = exec.ctx.terms.mk_le(zero, q);
        let trigger = if extra_trigger {
            vec![q, zero]
        } else {
            vec![q]
        };
        let root = exec.ctx.terms.mk_forall_with_triggers(
            vec![("bound_input".to_owned(), Sort::Int)],
            body,
            vec![trigger],
        );
        exec.ctx.add_native_assertion_with_parsed(root, marker());
        begin(&mut exec);
        capture(&exec).full_typed_query_sha256()
    };
    assert_ne!(digest(false), digest(true));
}

#[test]
fn capture_refusal_is_terminal_at_every_cooperative_checkpoint() {
    let exec = fixture();
    let permit = exec.detached_authored_plain_hard_permit_for_test().unwrap();
    let mut offers = 0;
    assert!(
        NativeProofSourceScope::capture_with_progress(&exec, &permit, &mut |_, _| {
            offers += 1;
            true
        })
        .is_some()
    );
    for stop_at in 1..=offers {
        let mut seen = 0;
        let result = NativeProofSourceScope::capture_with_progress(&exec, &permit, &mut |_, _| {
            seen += 1;
            seen < stop_at
        });
        assert!(result.is_none(), "checkpoint {stop_at}");
        assert_eq!(seen, stop_at, "no callback after the first refusal");
    }
}
