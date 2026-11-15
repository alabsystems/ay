// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

fn app(terms: &mut TermStore, head: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(head), args, sort)
}

pub(crate) fn theorem(terms: &mut TermStore, x: TermId, d: TermId, width: u32) -> TermId {
    let zero = terms.mk_bitvec(0.into(), width);
    let guard = app(terms, "=", &[d, zero], Sort::Bool);
    let rem = app(terms, "bvurem", &[x, d], Sort::bitvec(width));
    let bound = app(terms, "bvult", &[rem, d], Sort::Bool);
    app(terms, "or", &[guard, bound], Sort::Bool)
}

fn fixture(width: u32) -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("dividend", Sort::bitvec(width));
    let d = terms.mk_var("divisor", Sort::bitvec(width));
    let root = theorem(&mut terms, x, d, width);
    (terms, root)
}

fn accepts(terms: &TermStore, clause: &[TermId]) -> bool {
    validate(terms, ProofId(1), clause, &mut |_, _| true).is_ok()
}

#[test]
fn native_bound_accepts_one_odd_and_machine_widths() {
    for width in [1, 3, 5, 31, 32, 63, 64, 127, 128] {
        let (terms, root) = fixture(width);
        let shape = validate(&terms, ProofId(1), &[root], &mut |_, _| true).unwrap();
        assert_eq!(shape.width, width);
        assert_eq!(shape.theorem, root);
        assert_eq!(terms.sort(shape.dividend), &Sort::bitvec(width));
    }
}

#[test]
fn native_bound_handles_typed_compounds_and_the_zero_divisor_case() {
    for width in [1, 3, 32, 64, 128] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(width));
        let x = app(&mut terms, "bvneg", &[x], Sort::bitvec(width));
        for value in [0, 1] {
            let d = terms.mk_bitvec(value.into(), width);
            let root = theorem(&mut terms, x, d, width);
            assert!(accepts(&terms, &[root]));
        }
    }
}

#[test]
fn native_bound_rejects_unsupported_widths_and_invalid_handles() {
    for width in [0, 129, 256] {
        let (terms, root) = fixture(width);
        assert!(!accepts(&terms, &[root]));
    }
    let (terms, root) = fixture(32);
    assert!(!accepts(&terms, &[]));
    assert!(!accepts(&terms, &[root, root]));
    assert!(!accepts(&terms, &[TermId(u32::MAX)]));
}

#[test]
fn native_bound_requires_the_exact_guard_operator_and_repeated_divisor() {
    for mutation in 0..5 {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(32));
        let d = terms.mk_var("d", Sort::bitvec(32));
        let other = terms.mk_var("other", Sort::bitvec(32));
        let constant = terms.mk_bitvec(if mutation == 0 { 1.into() } else { 0.into() }, 32);
        let guard = app(
            &mut terms,
            if mutation == 1 { "distinct" } else { "=" },
            &[d, constant],
            Sort::Bool,
        );
        let rem = app(
            &mut terms,
            if mutation == 2 { "bvudiv" } else { "bvurem" },
            &[x, d],
            Sort::bitvec(32),
        );
        let bound = app(
            &mut terms,
            if mutation == 3 { "bvule" } else { "bvult" },
            &[rem, if mutation == 4 { other } else { d }],
            Sort::Bool,
        );
        let root = app(&mut terms, "or", &[guard, bound], Sort::Bool);
        assert!(!accepts(&terms, &[root]), "mutation {mutation}");
    }
}

#[test]
fn native_bound_does_not_accept_its_negation_or_an_unguarded_range() {
    let (mut terms, root) = fixture(4);
    let negative = terms.mk_not_raw(root);
    let bound = named(&terms, root, "or").unwrap()[1];
    assert!(!accepts(&terms, &[negative]));
    assert!(!accepts(&terms, &[bound]));
    // Independent small-domain semantics, including zero and maximum d.
    for width in 1..=4 {
        for x in 0..(1_u32 << width) {
            for d in 0..(1_u32 << width) {
                let r = x.checked_rem(d).unwrap_or(x);
                assert!(d == 0 || r < d);
                if d == 0 {
                    assert!(!(r < d));
                }
            }
        }
    }
}

#[test]
fn malformed_dead_arms_and_result_sorts_are_not_theorems() {
    for bad_kind in 0..4 {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(32));
        let d = terms.mk_var("d", Sort::bitvec(32));
        let narrow = terms.mk_var("narrow", Sort::bitvec(8));
        let bad = match bad_kind {
            0 => app(&mut terms, "bvadd", &[x, narrow], Sort::bitvec(32)),
            1 => app(&mut terms, "bvurem", &[x, d], Sort::Bool),
            2 => app(&mut terms, "uninterpreted", &[x], Sort::bitvec(32)),
            _ => terms.mk_app(
                Symbol::indexed("extract", vec![32, 1]),
                [x],
                Sort::bitvec(32),
            ),
        };
        let yes = terms.mk_bool(true);
        let input = terms.mk_ite_raw(yes, x, x);
        let root = theorem(&mut terms, input, d, 32);
        // Ordinary constructors correctly reject mismatched ITE branch
        // sorts. Exercise the hostile checker snapshot, not that assertion.
        let mut entries = terms.entries_snapshot();
        entries[input.index()].0 = TermData::Ite(yes, x, bad);
        let snapshot = TermStore::from_entries(entries, None, None, terms.var_counter());
        assert!(!accepts(&snapshot, &[root]), "dead arm {bad_kind}");
    }
}

#[test]
fn counted_native_bound_has_exact_and_one_short_cumulative_admission() {
    let (terms, root) = fixture(128);
    let (mut work, mut bytes) = (0, 0);
    validate(&terms, ProofId(1), &[root], &mut |w, b| {
        work += w;
        bytes += b;
        true
    })
    .unwrap();
    assert!(work > 0 && bytes > 0);
    for (work_limit, byte_limit, expected) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
        (0, 0, false),
    ] {
        let (mut used_work, mut used_bytes) = (0, 0);
        let result = validate(&terms, ProofId(1), &[root], &mut |w, b| {
            used_work += w;
            used_bytes += b;
            used_work <= work_limit && used_bytes <= byte_limit
        });
        assert_eq!(result.is_ok(), expected);
        if !expected {
            assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        }
    }
}

#[test]
fn every_native_admission_including_cleanup_can_refuse() {
    let (terms, root) = fixture(3);
    let calls = Cell::new(0);
    validate(&terms, ProofId(1), &[root], &mut |_, _| {
        calls.set(calls.get() + 1);
        true
    })
    .unwrap();
    for stop in 1..=calls.get() {
        let seen = Cell::new(0);
        let result = validate(&terms, ProofId(1), &[root], &mut |_, _| {
            seen.set(seen.get() + 1);
            seen.get() != stop
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(seen.get(), stop);
    }
}

#[test]
fn registered_function_identities_never_gain_builtin_theorem_authority() {
    for head in ["bvurem", "bvult", "or", "="] {
        let (mut terms, root) = fixture(32);
        assert!(accepts(&terms, &[root]));
        terms.register_declared_function(head);
        assert!(!accepts(&terms, &[root]), "registered {head}");
    }
    let mut terms = TermStore::new();
    let word = terms.mk_var("x", Sort::bitvec(32));
    let x = terms.mk_app(
        Symbol::indexed("extract", vec![7, 0]),
        [word],
        Sort::bitvec(8),
    );
    let d = terms.mk_var("d", Sort::bitvec(8));
    let root = theorem(&mut terms, x, d, 8);
    assert!(accepts(&terms, &[root]));
    terms.register_declared_function("extract");
    assert!(!accepts(&terms, &[root]));
}
