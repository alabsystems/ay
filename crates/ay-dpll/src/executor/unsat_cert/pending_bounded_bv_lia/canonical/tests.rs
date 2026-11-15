// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver-free parity with the former full-arena snapshot comparison.

use super::term_entries_match;
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;

struct Fixture {
    terms: TermStore,
    root: TermId,
    unused_array: TermId,
    unused_payload: TermId,
}

fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let seven = terms.mk_int(BigInt::from(7));
    let sum = terms.mk_app(Symbol::named("+"), [x, seven], Sort::Int);
    let root = terms.mk_app(Symbol::named("="), [sum, seven], Sort::Bool);
    terms.mk_bitvec((BigInt::from(1) << 128usize) + BigInt::from(3), 129);
    let unused_array = terms.mk_var(
        "unused_array",
        Sort::array(Sort::bitvec(8), Sort::bitvec(129)),
    );
    let unused_payload = terms.mk_var("a".repeat(64 * 1024), Sort::Int);
    Fixture {
        terms,
        root,
        unused_array,
        unused_payload,
    }
}

fn parity(terms: &TermStore, entries: &[(TermData, Sort)], expected: bool) {
    // Keep the old operation only as an independent test oracle.
    let legacy = entries == terms.entries_snapshot().as_slice();
    assert_eq!(legacy, expected);
    assert_eq!(term_entries_match(terms, entries), legacy);
}

#[test]
fn borrowed_comparison_preserves_snapshot_length_order_and_content_identity() {
    let empty = TermStore::from_entries(Vec::new(), None, None, 0);
    parity(&empty, &[], true);
    let Fixture { mut terms, .. } = fixture();
    let entries = terms.entries_snapshot();
    parity(&terms, &entries, true);
    parity(&terms, &[], false);
    parity(&terms, &entries[..entries.len() - 1], false);
    let mut extended = entries.clone();
    extended.push(entries[0].clone());
    parity(&terms, &extended, false);
    let mut reordered = entries.clone();
    assert_ne!(reordered[0], reordered[1]);
    reordered.swap(0, 1);
    parity(&terms, &reordered, false);

    // Fresh checker-only entry stamps do not change positional wire content.
    let rebuilt = TermStore::from_entries(
        entries.clone(),
        Some(terms.true_term()),
        Some(terms.false_term()),
        terms.var_counter(),
    );
    parity(&rebuilt, &entries, true);
    terms.mk_var("later_unused_append", Sort::Bool);
    parity(&terms, &entries, false);
    parity(&terms, &terms.entries_snapshot(), true);
}

#[test]
fn changing_data_or_sort_at_every_position_rejects_the_snapshot() {
    let fixture = fixture();
    let entries = fixture.terms.entries_snapshot();
    for index in 0..entries.len() {
        let mut changed_data = entries.clone();
        changed_data[index].0 = TermData::Var(format!("changed_slot_{index}"), u32::MAX);
        assert_ne!(changed_data[index].0, entries[index].0);
        parity(&fixture.terms, &changed_data, false);

        let mut changed_sort = entries.clone();
        changed_sort[index].1 = if entries[index].1 == Sort::Bool {
            Sort::Int
        } else {
            Sort::Bool
        };
        parity(&fixture.terms, &changed_sort, false);
    }
    parity(&fixture.terms, &entries, true);
}

#[test]
fn unused_large_payload_is_compared_completely_by_content() {
    let fixture = fixture();
    assert!(fixture.root.index() < fixture.unused_payload.index());
    let TermData::App(_, root_args) = fixture.terms.get(fixture.root) else {
        panic!("authored equality root");
    };
    assert!(root_args.iter().all(|id| id.index() < fixture.root.index()));
    let entries = fixture.terms.entries_snapshot();
    let index = fixture.unused_payload.index();
    let TermData::Var(source_name, _) = fixture.terms.get(fixture.unused_payload) else {
        panic!("unused variable with owned payload");
    };
    let TermData::Var(copied_name, _) = &entries[index].0 else {
        panic!("snapshot must preserve the payload kind");
    };
    assert_eq!(source_name.len(), 64 * 1024);
    assert_ne!(source_name.as_ptr(), copied_name.as_ptr());
    parity(&fixture.terms, &entries, true);
    for offset in [0, source_name.len() / 2, source_name.len() - 1] {
        let mut changed = entries.clone();
        let TermData::Var(name, _) = &mut changed[index].0 else {
            panic!("snapshot variable");
        };
        name.replace_range(offset..offset + 1, "b");
        assert_eq!(name.len(), source_name.len());
        parity(&fixture.terms, &changed, false);
    }
    let mut changed = entries.clone();
    let TermData::Var(_, id) = &mut changed[index].0 else {
        panic!("snapshot variable");
    };
    *id = id.checked_add(1).unwrap();
    parity(&fixture.terms, &changed, false);
}

#[test]
fn same_array_sort_kind_still_requires_exact_nested_index_and_element_sorts() {
    let fixture = fixture();
    assert!(fixture.root.index() < fixture.unused_array.index());
    let entries = fixture.terms.entries_snapshot();
    for sort in [
        Sort::array(Sort::bitvec(9), Sort::bitvec(129)),
        Sort::array(Sort::bitvec(8), Sort::bitvec(128)),
        Sort::array(Sort::bitvec(129), Sort::bitvec(8)),
    ] {
        let mut changed = entries.clone();
        changed[fixture.unused_array.index()].1 = sort;
        parity(&fixture.terms, &changed, false);
    }
    parity(&fixture.terms, &entries, true);
}
