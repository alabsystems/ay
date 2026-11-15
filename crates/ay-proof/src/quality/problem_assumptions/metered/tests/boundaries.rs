// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn cyclic_authored_conjunctions_terminate_and_keep_exact_duplicate_closure() {
    let mut fixture = Fixture::new();
    let mut entries = fixture.terms.entries_snapshot();
    let first = TermId(entries.len() as u32);
    let second = TermId(first.0 + 1);
    entries.push((
        TermData::App(Symbol::named("and"), vec![second, second, fixture.ite]),
        Sort::Bool,
    ));
    entries.push((
        TermData::App(Symbol::named("and"), vec![first, first]),
        Sort::Bool,
    ));
    fixture.replace_entries(entries);
    fixture.roots = vec![first, second, first];
    fixture.proof.add_assume(second, None);
    // This private closure is cycle-safe, not a whole-snapshot validator.
    // Independent snapshot preflight still rejects forward/cyclic edges.
    fixture
        .compare()
        .expect("each reachable conjunction visited once");
}

#[test]
fn dangling_problem_roots_conjuncts_and_assumptions_are_checked_before_get() {
    for location in 0..3 {
        let mut fixture = Fixture::new();
        match location {
            0 => fixture.roots.push(TermId::SENTINEL),
            1 => {
                let mut entries = fixture.terms.entries_snapshot();
                let root = TermId(entries.len() as u32);
                entries.push((
                    TermData::App(Symbol::named("and"), vec![TermId::SENTINEL]),
                    Sort::Bool,
                ));
                fixture.replace_entries(entries);
                fixture.roots.push(root);
            }
            _ => {
                fixture.proof.add_assume(TermId::SENTINEL, None);
            }
        }
        assert!(matches!(
            fixture.run(&mut |_, _| true),
            Err(ProofCheckError::MalformedProofBundle { .. })
        ));
    }
}

#[test]
fn malformed_handle_diagnostics_are_precharged() {
    let fixture = Fixture::new();
    let mut allocations = 0usize;
    assert_resource(term(&fixture.terms, TermId::SENTINEL, &mut |_, bytes| {
        allocations += usize::from(bytes != 0);
        bytes == 0
    }));
    assert_eq!(allocations, 1);
}

#[test]
fn empty_inputs_and_nonboolean_authored_leaves_preserve_legacy_scope() {
    let mut fixture = Fixture::new();
    fixture.proof = Proof::new();
    fixture.roots.clear();
    fixture.compare().expect("empty assumption fragment");
    let integer = fixture.terms.mk_var("authored_integer", Sort::Int);
    fixture.roots.push(integer);
    fixture.proof.add_assume(integer, None);
    // Sort/proof validity belongs to the strict checker. Authorization alone
    // must not silently acquire a new typing policy.
    fixture
        .compare()
        .expect("exact authored leaf is authorized, not proved Boolean");
}
