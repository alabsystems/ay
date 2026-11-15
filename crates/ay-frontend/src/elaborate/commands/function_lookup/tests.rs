// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
#![allow(clippy::unwrap_used)]

use super::*;
use crate::parse;
use ay_core::TermId;

fn process(context: &mut Context, text: &str) {
    for command in parse(text).unwrap() {
        context.process_command(&command).unwrap();
    }
}

fn context(text: &str) -> Context {
    let mut context = Context::new();
    process(&mut context, text);
    context
}

#[test]
fn unique_source_function_lookup_borrows_exact_names_and_signature() {
    let context = context(
        "(declare-fun |f with space| (Bool (_ BitVec 72)) (_ BitVec 136))
        (declare-fun zero () (_ BitVec 128))",
    );
    let size = context.terms.len();
    for name in ["f with space", "zero"] {
        let (arguments, result) = context.source_function_for_model(name).unwrap();
        let info = context.symbol_info(name).unwrap();
        assert!(std::ptr::eq(arguments, info.arg_sorts.as_slice()));
        assert!(std::ptr::eq(result, &info.sort));
    }
    let (args, result) = context.source_function_for_model("f with space").unwrap();
    assert_eq!(args, [Sort::Bool, Sort::bitvec(72)]);
    assert_eq!(result, &Sort::bitvec(136));
    assert!(context
        .source_function_for_model("|f with space|")
        .is_none());
    assert!(context.source_function_for_model("(zero)").is_none());
    assert!(context.source_function_for_model("missing").is_none());
    assert_eq!(context.terms.len(), size);
}

#[test]
fn original_adopted_declaration_is_retained_but_real_definitions_are_not() {
    let context = context(
        "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((x (_ BitVec 8))) (= (f x) (bvadd x #x01))))
        (define-fun defined ((x (_ BitVec 8))) (_ BitVec 8) (bvadd x #x01))",
    );
    assert!(context.is_defined_fun("f"));
    assert!(context.adopted_macro_interp("f").is_some());
    let (args, result) = context.source_function_for_model("f").unwrap();
    assert_eq!(args, [Sort::bitvec(8)]);
    assert_eq!(result, &Sort::bitvec(8));
    assert!(context.source_function_for_model("defined").is_none());
}

#[test]
fn overloads_native_aliases_and_datatype_operations_do_not_acquire_uf_ownership() {
    for text in [
        "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))(declare-fun f (Bool) (_ BitVec 8))",
        "(declare-fun f (Bool) (_ BitVec 8))(declare-fun f ((_ BitVec 8)) (_ BitVec 8))",
        "(declare-fun f () (_ BitVec 8))(declare-fun f (Bool) (_ BitVec 8))",
    ] {
        assert!(context(text).source_function_for_model("f").is_none());
    }
    let mut context = context(
        "(declare-datatype R ((mkR (field (_ BitVec 8)))))
        (declare-const x (_ BitVec 8))",
    );
    let term = context.source_constant_for_value("x").unwrap().0;
    context.register_symbol("alias".into(), term, Sort::bitvec(8));
    context.register_native_global_constant("native".into(), Sort::bitvec(8));
    for name in ["alias", "native", "mkR", "field", "is-mkR"] {
        assert!(context.source_function_for_model(name).is_none(), "{name}");
    }
    assert!(context.source_function_for_model("x").is_some());
}

#[test]
fn pop_redeclare_resolves_only_the_new_complete_signature() {
    let mut context = context("(push 1)(declare-fun f ((_ BitVec 8)) (_ BitVec 8))");
    let old_id = context.symbol_info("f").unwrap().declaration_id().clone();
    process(&mut context, "(pop 1)");
    assert!(context.source_function_for_model("f").is_none());
    process(&mut context, "(declare-fun f (Bool) (_ BitVec 136))");
    let (args, result) = context.source_function_for_model("f").unwrap();
    assert_eq!(args, [Sort::Bool]);
    assert_eq!(result, &Sort::bitvec(136));
    assert_ne!(&old_id, context.symbol_info("f").unwrap().declaration_id());
}

#[test]
fn stale_adopted_identity_and_missing_value_slots_refuse() {
    let mut context = context(
        "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun other ((_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((x (_ BitVec 8))) (= (f x) #x07)))
        (declare-fun zero () (_ BitVec 8))",
    );
    let original = context
        .adopted_macro_declaration_ids
        .get("f")
        .unwrap()
        .clone();
    let foreign = context
        .symbol_info("other")
        .unwrap()
        .declaration_id()
        .clone();
    context
        .adopted_macro_declaration_ids
        .insert("f".into(), foreign);
    assert!(context.source_function_for_model("f").is_none());
    context
        .adopted_macro_declaration_ids
        .insert("f".into(), original);
    assert!(context.source_function_for_model("f").is_some());
    context.adopted_macro_interps.get_mut("f").unwrap().1 = TermId(u32::MAX);
    assert!(context.source_function_for_model("f").is_none());
    context.symbols.get_mut("zero").unwrap().term = Some(TermId(u32::MAX));
    assert!(context.source_function_for_model("zero").is_none());
}
