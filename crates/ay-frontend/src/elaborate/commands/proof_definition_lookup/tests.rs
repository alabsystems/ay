// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::Sort;

fn process(context: &mut Context, text: &str) {
    for command in crate::parse(text).unwrap() {
        context.process_command(&command).unwrap();
    }
}

#[test]
fn source_macro_lookup_borrows_the_unfolded_body_without_mutating_context() {
    let mut context = Context::new();
    process(
        &mut context,
        "(declare-const x (_ BitVec 8))(define-fun alias () (_ BitVec 8) (bvadd x #x00))",
    );
    let stamp = context.source_context_stamp();
    let size = context.terms.len();
    let body = context
        .source_nullary_definition_for_proof("alias")
        .unwrap();
    assert!(std::ptr::eq(body, &raw const context.fun_defs["alias"].2));
    assert!(matches!(body, ParsedTerm::App(op, args) if op == "bvadd" && args.len() == 2));
    assert!(context.source_nullary_definition_for_proof("x").is_none());
    assert!(context
        .source_nullary_definition_for_proof("missing")
        .is_none());
    assert_eq!(context.source_context_stamp(), stamp);
    assert_eq!(context.terms.len(), size);
}

#[test]
fn recursive_applied_and_adopted_definitions_are_not_plain_macro_authority() {
    let mut context = Context::new();
    process(&mut context, "(define-fun-rec recursive () (_ BitVec 8) #x00)(define-fun applied ((x (_ BitVec 8))) (_ BitVec 8) x)(declare-fun adopted ((_ BitVec 8)) (_ BitVec 8))(assert (forall ((x (_ BitVec 8))) (= (adopted x) (bvadd x #x01))))");
    assert!(context.adopted_macro_interp("adopted").is_some());
    for name in ["recursive", "applied", "adopted"] {
        assert!(context.source_nullary_definition_for_proof(name).is_none());
    }
}

#[test]
fn native_and_forged_definition_slots_do_not_gain_source_ownership() {
    let mut context = Context::new();
    process(
        &mut context,
        "(declare-const ordinary (_ BitVec 8))(define-fun original () (_ BitVec 8) #x01)",
    );
    let body = context.fun_defs["original"].clone();
    context.fun_defs.insert("ordinary".into(), body.clone());
    let _ = context.register_native_global_constant("native".into(), Sort::bitvec(8));
    context.fun_defs.insert("native".into(), body);
    for name in ["ordinary", "native"] {
        assert!(context.source_nullary_definition_for_proof(name).is_none());
    }
}

#[test]
fn popped_definition_cannot_authorize_a_new_declaration() {
    let mut context = Context::new();
    process(
        &mut context,
        "(push 1)(define-fun alias () (_ BitVec 8) #x01)",
    );
    assert!(context
        .source_nullary_definition_for_proof("alias")
        .is_some());
    process(&mut context, "(pop 1)(declare-const alias (_ BitVec 8))");
    assert!(context
        .source_nullary_definition_for_proof("alias")
        .is_none());
}

/// A `:named` label binds a nullary definition later assertions can use, but
/// a proof checker expands the label instead of holding `(= a BODY)` as a
/// premise, so the label is no `define-fun` authority.
#[test]
fn named_label_is_a_usable_definition_without_define_fun_authority() {
    let mut context = Context::new();
    process(
        &mut context,
        "(declare-const x Int)(define-fun m () Bool (< x 3))\
         (assert (! (> x 5) :named a))(assert (not a))",
    );
    assert!(context.fun_defs.contains_key("a"));
    assert_eq!(context.assertions.len(), 2);
    assert!(context.source_nullary_definition_for_proof("a").is_none());
    assert!(context.source_nullary_definition_for_proof("m").is_some());
}

#[test]
fn define_fun_reusing_a_popped_label_name_has_authority() {
    let mut context = Context::new();
    process(
        &mut context,
        "(declare-const x Int)(push 1)(assert (! (> x 5) :named a))",
    );
    assert!(context.source_nullary_definition_for_proof("a").is_none());
    process(&mut context, "(pop 1)(define-fun a () Bool (< x 3))");
    assert!(context.source_nullary_definition_for_proof("a").is_some());
}
