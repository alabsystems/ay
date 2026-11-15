// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn extend(terms: &mut TermStore, arg: TermId, added: u32, width: u32) -> TermId {
    terms.mk_app(
        Symbol::indexed("sign_extend", vec![added]),
        [arg],
        Sort::bitvec(width),
    )
}

#[test]
fn cancelled_planning_stops_before_a_slice_is_returned() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(128));
    let extended = extend(&mut terms, a, 1, 129);
    let mut calls = 0;
    let result = planning::plan(&terms, extended, extended, Partition::Fields, &mut || {
        calls += 1;
        Err("caller cancelled".into())
    });
    assert!(matches!(result, Err(planning::Error::Resource(_))));
    assert_eq!(calls, 1);
}

#[test]
fn malformed_wide_sorts_and_extensions_are_refused() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(128));
    let b = terms.mk_var("b", Sort::bitvec(64));
    let good = extend(&mut terms, a, 1, 129);
    let wrong_extension = extend(&mut terms, a, 2, 129);
    let wrong_concat = terms.mk_app(Symbol::named("concat"), [a, b], Sort::bitvec(129));
    let wrong_add = terms.mk_app(Symbol::named("bvadd"), [good, a], Sort::bitvec(129));
    for bad in [wrong_extension, wrong_concat, wrong_add] {
        assert!(matches!(
            plan(&terms, good, bad),
            Err(planning::Error::Unsupported(_))
        ));
    }
}

#[test]
fn virtual_shared_arithmetic_expansion_is_bounded_before_lowering() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(128));
    let mut term = extend(&mut terms, a, 1, 129);
    // Small source DAG, exponentially large boxed producer view. The existing
    // construction-node bound must refuse it during planning, not allocate it.
    for _ in 0..20 {
        term = terms.mk_app(Symbol::named("bvadd"), [term, term], Sort::bitvec(129));
    }
    assert!(matches!(
        plan(&terms, term, term),
        Err(planning::Error::Resource(_))
    ));
}

#[test]
fn the_legacy_maximum_width_concat_plan_remains_supported() {
    let mut terms = TermStore::new();
    let bit = terms.mk_var("bit", Sort::bitvec(1));
    let mut term = bit;
    for width in 2..=MAX_WIDE_WIDTH {
        term = terms.mk_app(Symbol::named("concat"), [bit, term], Sort::bitvec(width));
    }
    let slices = plan(&terms, term, term).expect("legacy concat width remains supported");
    assert_eq!(slices.len(), (MAX_WIDE_WIDTH / SLICE) as usize);
}

#[test]
fn reflexive_slices_still_validate_unsupported_narrow_operands() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(128));
    let unsupported = terms.mk_app(
        Symbol::named("unsupported_function"),
        [a],
        Sort::bitvec(128),
    );
    let pad = terms.mk_var("pad", Sort::bitvec(64));
    let joined = terms.mk_app(
        Symbol::named("concat"),
        [unsupported, pad],
        Sort::bitvec(192),
    );
    let equality = terms.mk_app(Symbol::named("="), [joined, joined], Sort::Bool);
    let root = terms.mk_not_raw(equality);
    let result = authenticate_bool_bv_unsat_query(&terms, &[root], None);
    assert!(result
        .expect_err("reflexivity must not skip source validation")
        .is_unsupported_fragment());
}
