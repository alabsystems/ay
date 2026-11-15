// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

struct Fixture {
    terms: TermStore,
    guard: TermId,
    property: TermId,
    root: TermId,
    clause: TermId,
}

fn app(terms: &mut TermStore, op: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(op), args, sort)
}

fn fixture(width: u32, length: u32, last_offset: u32, malformed: bool) -> Fixture {
    let mut terms = TermStore::new();
    let word = Sort::bitvec(width);
    let array = Sort::array(word.clone(), Sort::bitvec(8));
    let sp = terms.mk_var("stack", word.clone());
    let observe = terms.mk_var("observe", word.clone());
    let size = terms.mk_bitvec(length.into(), width);
    let start = app(&mut terms, "bvsub", &[sp, size], word.clone());
    let guard = app(&mut terms, "bvuge", &[sp, size], Sort::Bool);
    let below = app(&mut terms, "bvult", &[observe, start], Sort::Bool);
    let above = app(&mut terms, "bvuge", &[observe, sp], Sort::Bool);
    let outside = app(&mut terms, "or", &[below, above], Sort::Bool);
    let not_outside = terms.mk_not_raw(outside);
    let base = terms.mk_var("memory", array.clone());
    let value = terms.mk_var("value", Sort::bitvec(8));
    let mut memory = base;
    if malformed {
        let bad = app(&mut terms, "bvadd", &[value], Sort::bitvec(8));
        memory = app(&mut terms, "store", &[memory, start, bad], array.clone());
    }
    for offset in 0..length {
        let actual = if offset.checked_add(1) == Some(length) {
            last_offset
        } else {
            offset
        };
        let offset = terms.mk_bitvec(actual.into(), width);
        let index = app(&mut terms, "bvadd", &[start, offset], word.clone());
        memory = app(&mut terms, "store", &[memory, index, value], array.clone());
    }
    let after = app(&mut terms, "select", &[memory, observe], Sort::bitvec(8));
    let before = app(&mut terms, "select", &[base, observe], Sort::bitvec(8));
    let equal = app(&mut terms, "=", &[after, before], Sort::Bool);
    let property = app(&mut terms, "or", &[not_outside, equal], Sort::Bool);
    let negative = terms.mk_not_raw(property);
    let root = app(&mut terms, "and", &[guard, negative], Sort::Bool);
    let clause = terms.mk_not_raw(root);
    Fixture {
        terms,
        guard,
        property,
        root,
        clause,
    }
}

#[test]
fn every_frame_write_uses_the_checked_free_offset_lemma() {
    for width in [9, 64, 128] {
        for length in [2, 48] {
            let f = fixture(width, length, length - 1, false);
            let shape = Shape::recognize(&f.terms, &[f.clause]).expect("source shape");
            assert_eq!(shape.root, f.root);
            assert_eq!(shape.property, f.property);
            assert_eq!(shape.length, u128::from(length));
            super::super::validate(&f.terms, &[f.clause], &mut || Ok(()))
                .unwrap_or_else(|error| panic!("width={width} length={length}: {error}"));
        }
    }
}

#[test]
fn outside_property_cannot_hide_a_false_sibling_property() {
    let mut f = fixture(9, 2, 1, false);
    let other = f.terms.mk_var("independent_property", Sort::Bool);
    let both = app(&mut f.terms, "and", &[f.property, other], Sort::Bool);
    let not_both = f.terms.mk_not_raw(both);
    let root = app(&mut f.terms, "and", &[f.guard, not_both], Sort::Bool);
    let clause = f.terms.mk_not_raw(root);
    assert!(Shape::recognize(&f.terms, &[clause]).is_some());
    assert!(super::super::validate(&f.terms, &[clause], &mut || Ok(())).is_err());
}

#[test]
fn guards_under_disjunction_are_not_positive_facts() {
    let mut f = fixture(9, 2, 1, false);
    let not_property = f.terms.mk_not_raw(f.property);
    let root = app(&mut f.terms, "or", &[f.guard, not_property], Sort::Bool);
    let clause = f.terms.mk_not_raw(root);
    assert!(Shape::recognize(&f.terms, &[clause]).is_none());
    assert!(super::super::validate(&f.terms, &[clause], &mut || Ok(())).is_err());
}

#[test]
fn outside_writes_and_overwritten_malformed_values_are_refused() {
    for (last, malformed) in [(2, false), (1, true)] {
        let f = fixture(9, 2, last, malformed);
        if !malformed {
            assert!(Shape::recognize(&f.terms, &[f.clause]).is_none());
        }
        assert!(super::super::validate(&f.terms, &[f.clause], &mut || Ok(())).is_err());
    }
}

mod common;
