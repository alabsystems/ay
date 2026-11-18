// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::unwrap_used)]

use super::*;
use crate::parse;
use ay_core::TermData;

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
fn source_constant_lookup_is_borrowed_and_does_not_redeclare() {
    let context = context(
        "(declare-const |x with space| Int)
         (declare-fun flag () Bool)
         (declare-const |(+ x 1)| Int)",
    );
    let size = context.terms.len();
    for (name, sort) in [
        ("x with space", Sort::Int),
        ("flag", Sort::Bool),
        ("(+ x 1)", Sort::Int),
    ] {
        let (term, declared) = context.source_constant_for_value(name).unwrap();
        let info = context.symbol_info(name).unwrap();
        assert_eq!(Some(term), info.term);
        assert!(std::ptr::eq(declared, &raw const info.sort));
        assert_eq!(declared, &sort);
        assert_eq!(context.terms.sort(term), declared);
    }
    assert!(context
        .source_constant_for_value("|x with space|")
        .is_none());
    assert!(context.source_constant_for_value("missing").is_none());
    assert_eq!(context.terms.len(), size);
}

#[test]
fn eager_records_and_unit_constants_keep_the_actual_declaration_term() {
    let context = context(
        "(declare-datatype Row ((row (cells (Array (_ BitVec 2) Bool)))))
         (declare-datatype Outer ((outer (child Row))))
         (declare-datatype Unit ((unit)))
         (declare-const v Outer)(declare-const u Unit)",
    );
    let (record, sort) = context.source_constant_for_value("v").unwrap();
    assert!(matches!(context.terms.get(record), TermData::App(_, _)));
    assert_eq!(context.terms.sort(record), sort);
    assert_eq!(Some(record), context.symbol_info("v").unwrap().term);
    let (unit, _) = context.source_constant_for_value("u").unwrap();
    assert_eq!(Some(unit), context.symbol_info("unit").unwrap().term);
    let field_identities: Vec<String> = context
        .symbol_iter()
        .map(|(name, _)| name.clone())
        .filter(|name| context.is_dt_field_identity(name))
        .collect();
    assert_eq!(field_identities.len(), 2, "{field_identities:?}");
    let internal_names = ["outer", "row", "unit"]
        .into_iter()
        .chain(field_identities.iter().map(String::as_str));
    for internal in internal_names {
        assert!(
            context.source_constant_for_value(internal).is_none(),
            "{internal}"
        );
    }
}

#[test]
fn overloads_are_resolved_by_unique_nullary_signature_not_last_registration() {
    for declarations in [
        "(declare-const x Int)(declare-const x Bool)",
        "(declare-const x Bool)(declare-const x Int)",
    ] {
        let context = context(declarations);
        assert!(context.symbol_info("x").is_some());
        assert!(context.source_constant_for_value("x").is_none());
    }
    for declarations in [
        "(declare-const x Int)(declare-fun x (Int) Bool)",
        "(declare-fun x (Int) Bool)(declare-const x Int)",
    ] {
        let context = context(declarations);
        let (term, sort) = context.source_constant_for_value("x").unwrap();
        assert_eq!(sort, &Sort::Int);
        assert_eq!(context.terms.sort(term), sort);
    }
}

#[test]
fn definitions_native_registrations_and_aliases_are_not_source_constants() {
    let mut context = context(
        "(declare-const x Int)(declare-fun f (Int) Int)
         (define-fun fixed () Int 7)",
    );
    let term = context.source_constant_for_value("x").unwrap().0;
    context.register_symbol("alias".into(), term, Sort::Int);
    let _ = context.register_native_global_constant("native".into(), Sort::Int);
    for name in ["f", "fixed", "alias", "native"] {
        assert!(context.source_constant_for_value(name).is_none(), "{name}");
    }
    assert_eq!(context.source_constant_for_value("x").unwrap().0, term);
}

#[test]
fn popped_names_resolve_only_the_new_live_declaration() {
    let mut context = context("(push 1)(declare-const x Int)");
    let old = context.source_constant_for_value("x").unwrap().0;
    process(&mut context, "(pop 1)");
    assert!(context.source_constant_for_value("x").is_none());
    process(&mut context, "(declare-const x Bool)");
    let (new, sort) = context.source_constant_for_value("x").unwrap();
    assert_ne!(old, new);
    assert_eq!(sort, &Sort::Bool);
    assert_eq!(context.terms.sort(old), &Sort::Int);
}

#[test]
fn malformed_live_slot_and_oversized_overload_family_refuse_without_indexing() {
    let mut context = context("(declare-const x Int)");
    let original = context.symbols.get("x").unwrap().clone();
    context.symbols.get_mut("x").unwrap().term = Some(TermId(u32::MAX));
    assert!(context.source_constant_for_value("x").is_none());
    context.symbols.insert("x".into(), original.clone());
    context
        .overloaded_symbols
        .insert("x".into(), vec![original.clone(); 4097]);
    assert!(context.source_constant_for_value("x").is_none());
    context
        .overloaded_symbols
        .insert("x".into(), vec![original.clone(), original]);
    assert!(context.source_constant_for_value("x").is_none());
}
