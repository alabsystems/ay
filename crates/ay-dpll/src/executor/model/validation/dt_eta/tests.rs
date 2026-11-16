// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Real frontend declaration identities; no solver or model is constructed.

use super::*;

fn declared(tester: &str) -> (Executor, TermId) {
    let mut executor = Executor::new();
    let text = format!("(set-logic ALL)
        (declare-datatypes ((D 0)) (((C (p Bool) (q Bool) (data (Array (_ BitVec 64) (_ BitVec 8)))) N)))
        (declare-const y D)
        (declare-fun user-tester (D) Bool)
        (assert (= ({tester} y) (= y (C (p y) (q y) (data y)))))");
    let commands = ay_frontend::parse(&text).expect("the declaration-only fixture must parse");
    assert_eq!(
        executor
            .execute_all(&commands)
            .expect("the fixture must elaborate"),
        [] as [String; 0]
    );
    let term = *executor
        .ctx
        .assertions
        .last()
        .expect("the actual eta assertion must be retained");
    (executor, term)
}

#[test]
fn actual_live_registry_proves_array_field_eta_but_not_a_same_typed_uf_tester() {
    let (executor, term) = declared("is-C");
    assert!(is_eta(&executor, term, 4000));
    assert!(is_eta(&executor, term, 32));
    assert!(is_eta(&executor, term, 1));
    assert!(!is_eta(&executor, term, 0));
    let (executor, term) = declared("user-tester");
    assert!(!is_eta(&executor, term, 4000));
}

#[test]
fn inactive_datatype_members_cannot_be_reused_as_current_eta_authority() {
    let mut executor = Executor::new();
    executor
        .execute_all(&ay_frontend::parse("(set-logic ALL)(push 1)").unwrap())
        .unwrap();
    let text = "(declare-datatypes ((D 0)) (((C (p Bool)) N)))
        (declare-const y D)(assert (= (is-C y) (= y (C (p y)))))";
    executor
        .execute_all(&ay_frontend::parse(text).unwrap())
        .unwrap();
    let term = *executor.ctx.assertions.last().unwrap();
    assert!(is_eta(&executor, term, 4000));
    executor
        .execute_all(&ay_frontend::parse("(pop 1)").unwrap())
        .unwrap();
    assert!(!is_eta(&executor, term, 4000));
}

#[test]
fn equality_requires_its_canonical_owner_but_allows_a_private_surface_shadow() {
    let (mut executor, term) = declared("is-C");
    assert!(is_eta(&executor, term, 4000));
    let forged = executor.ctx.terms.mk_fresh_named_var("=", Sort::Bool);
    executor
        .ctx
        .register_symbol("=".to_string(), forged, Sort::Bool);
    let owner = executor
        .ctx
        .symbol_info("=")
        .expect("actual forged declaration");
    assert_eq!(owner.declaration_kind(), DeclarationKind::Uninterpreted);
    assert_eq!(executor.ctx.symbol_identity_name("=", owner), "=");
    assert!(!executor.ctx.canonical_operator_binding_is_unambiguous("="));
    assert!(!is_eta(&executor, term, 4000));

    let (mut executor, term) = declared("is-C");
    let _ = executor
        .ctx
        .register_native_global_constant("=".to_string(), Sort::Bool);
    let owner = executor
        .ctx
        .symbol_info("=")
        .expect("real private native declaration");
    assert_ne!(executor.ctx.symbol_identity_name("=", owner), "=");
    assert!(executor.ctx.canonical_operator_binding_is_unambiguous("="));
    assert!(is_eta(&executor, term, 4000));
}
