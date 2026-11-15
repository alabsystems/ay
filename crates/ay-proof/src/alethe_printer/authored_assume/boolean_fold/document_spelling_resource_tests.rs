// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{Symbol, TermStore};

#[test]
fn a_wide_root_refuses_before_any_child_copy_or_debit() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let root = terms.mk_app(
        Symbol::named("and"),
        vec![p; MAX_DOCUMENT_SPELLING_NODES + 1],
        Sort::Bool,
    );
    let printer = AlethePrinter::new(&terms);
    let mut walk = SpellingWalk::new(&printer, MAX_DOCUMENT_SPELLING_NODES);
    assert!(!walk.push_children(root));
    assert!(walk.stack.is_empty());
    assert_eq!(walk.edges, 0);
    assert_eq!(printer.work_used(), 0);
}

#[test]
fn repeated_shared_edges_cannot_escape_the_queue_cap() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let repeated = terms.mk_app(Symbol::named("and"), vec![p; 20], Sort::Bool);
    let printer = AlethePrinter::new(&terms);
    let mut walk = SpellingWalk::new(&printer, 32);
    assert!(walk.push_children(repeated));
    walk.stack.clear();
    assert!(!walk.push_children(repeated));
    assert!(walk.stack.is_empty());
    assert_eq!(walk.edges, 20);
}

#[test]
fn work_refusal_precedes_queue_reservation() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let root = terms.mk_app(Symbol::named("and"), [p, p], Sort::Bool);
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(0));
    let mut walk = SpellingWalk::new(&printer, 32);
    assert!(!walk.push_children(root));
    assert!(walk.stack.is_empty());
    assert_eq!(walk.stack.capacity(), 0);
}

#[test]
fn canonical_allocation_is_refused_before_rendering() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let mut overrides = HashMap::default();
    overrides.insert(p, "(or p false)".to_string());
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, Some(&overrides), Some(1));
    let mut walk = SpellingWalk::new(&printer, 32);
    assert_eq!(
        printer.override_respells(&overrides, p, false, &mut walk),
        None
    );
    assert!(printer.work_budget_exhausted());
}
