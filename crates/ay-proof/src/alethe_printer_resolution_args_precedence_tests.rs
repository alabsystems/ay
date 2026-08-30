// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certified-rendering precedence barriers for derived literals.

use super::AlethePrinter;
use ay_core::kani_compat::DetHashMap;
use ay_core::{Sort, Symbol, TermId, TermStore};

fn equality_and_negation(terms: &mut TermStore) -> (TermId, TermId) {
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let equality = terms.mk_app(Symbol::named("="), vec![x, y], Sort::Bool);
    (equality, terms.mk_not_raw(equality))
}

#[test]
fn a_direct_outer_let_bridge_precedes_inner_negation_synthesis() {
    let mut terms = TermStore::new();
    let (equality, disequality) = equality_and_negation(&mut terms);
    let printer = AlethePrinter::new(&terms);
    printer
        .let_bridge_renderings
        .borrow_mut()
        .insert(equality, "(= x y)".to_string());
    printer
        .let_bridge_renderings
        .borrow_mut()
        .insert(disequality, "(not (= y x))".to_string());

    let mut output = String::new();
    printer.write_derived_literal_into(&mut output, disequality);
    assert_eq!(output, "(not (= y x))");
}

#[test]
fn an_outer_skolem_rendering_precedes_inner_negation_synthesis() {
    let mut terms = TermStore::new();
    let (equality, disequality) = equality_and_negation(&mut terms);
    let printer = AlethePrinter::new(&terms);
    printer
        .let_bridge_renderings
        .borrow_mut()
        .insert(equality, "(= x y)".to_string());
    printer
        .skolem_overrides
        .borrow_mut()
        .insert(disequality, "(not (= sx y))".to_string());

    let mut output = String::new();
    printer.write_derived_literal_into(&mut output, disequality);
    assert_eq!(output, "(not (= sx y))");
}

#[test]
fn a_raw_outer_source_override_does_not_supersede_the_certified_inner_bridge() {
    let mut terms = TermStore::new();
    let (equality, disequality) = equality_and_negation(&mut terms);
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(disequality, "(not (let ((?v_0 x)) (= ?v_0 y)))".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    printer
        .let_bridge_renderings
        .borrow_mut()
        .insert(equality, "(= x y)".to_string());

    let mut output = String::new();
    printer.write_derived_literal_into(&mut output, disequality);
    assert_eq!(output, "(not (= x y))");
}
