// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Declared datatype carriers: the rung keeps a sort unchanged only when no
//! array is reachable from it, and a `declare-datatype` carrier reaches the
//! store as a bare `Sort::Uninterpreted` identity whose fields only the
//! store's registered field table knows. The builder and the checker both
//! resolve carriers through that table
//! (`StaticFeatures::sort_reaches_array`, the walk the quarantine arms by;
//! #nested-array-quarantine-datatype-fields). A carrier that reaches an array
//! is renamed as a whole, with its constructors and selectors
//! (#nested-array-checked-rung); any other container of an array still
//! declines. Measured by making the classification carrier-blind again: both
//! tests below go red.

use super::super::build::{classify_sort, SortClass};
use super::*;

/// The congruence refutation beside two reads of an array of a DECLARED record
/// carrier, `Row`, whose one field has sort `field`. The carrier sits inside an
/// array because the frontend flattens a lone record constant into one
/// constant per field, which would leave no `Row` term to classify.
fn congruence_beside_rows(field: &str) -> String {
    format!(
        "(declare-datatype Row ((mk_row (cells {field}))))\
         (declare-const m (Array Int Row))\
         {CONGRUENCE_UNSAT}\
         (assert (not (= (select m 0) (select m 1))))"
    )
}

/// The sort of the `Row` reads in [`congruence_beside_rows`]: the one nominal
/// sort reachable from its roots, which is how a declared carrier is stored.
fn carrier_sort(terms: &TermStore, roots: &[TermId]) -> Sort {
    let mut seen = ay_core::kani_compat::DetHashSet::<TermId>::default();
    let mut stack = roots.to_vec();
    while let Some(node) = stack.pop() {
        if !seen.insert(node) {
            continue;
        }
        if let sort @ Sort::Uninterpreted(_) = terms.sort(node) {
            return sort.clone();
        }
        match terms.get(node) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            _ => {}
        }
    }
    panic!("the roots mention a declared carrier");
}

/// A `declare-datatype` carrier reaches the store as a bare
/// `Sort::Uninterpreted` identity, so only the store's registered field sorts
/// say it holds an array. The rung keeps a sort unchanged only when no array is
/// reachable from it, through that table too: a kept `Row` with an array field
/// would leave an array inside the "array-free" abstraction
/// (#nested-array-quarantine-datatype-fields).
///
/// #nested-array-checked-rung RE-PIN (was
/// `a_declared_carrier_with_an_array_field_declines_to_build`): such a `Row`
/// is now RENAMED, never kept, so the abstraction builds, holds no array and
/// is refuted. The carrier-blind counterfactual still goes red here: `Row`
/// would classify `Plain`, be kept, and fail the array-freedom check.
#[test]
fn a_declared_carrier_with_an_array_field_is_renamed_as_a_whole() {
    let (mut exec, roots) = load(&congruence_beside_rows("(Array Int Int)"));
    let row = carrier_sort(&exec.ctx.terms, &roots);
    assert_eq!(classify_sort(&exec.ctx.terms, &row), SortClass::Carrier);
    let abstraction = ArrayUfAbstraction::build(&mut exec.ctx.terms, &roots)
        .expect("an array-carrying declared carrier is renamed");
    assert!(abstraction.witness.sorts.contains_key(&row));
    assert!(is_pure_renaming(&exec.ctx.terms, &roots, &abstraction));
    assert!(exec.nested_array_uf_abstraction_unsat(&roots));

    // The same carrier over a scalar field is kept, and the rung refutes the
    // congruence core beside it.
    let (mut exec, roots) = load(&congruence_beside_rows("Int"));
    let row = carrier_sort(&exec.ctx.terms, &roots);
    assert_eq!(classify_sort(&exec.ctx.terms, &row), SortClass::Plain);
    let abstraction = ArrayUfAbstraction::build(&mut exec.ctx.terms, &roots)
        .expect("a carrier of scalars builds");
    assert!(!abstraction.witness.sorts.contains_key(&row));
    assert!(is_pure_renaming(&exec.ctx.terms, &roots, &abstraction));
    assert!(exec.nested_array_uf_abstraction_unsat(&roots));
}

/// Only a DECLARED carrier has a renaming for its operations. An array inside
/// any other container (here a `Seq`) still declines.
#[test]
fn an_array_inside_a_sequence_still_declines() {
    let (mut exec, roots) = load(&format!(
        "(declare-const s (Seq (Array Int Int))){CONGRUENCE_UNSAT}\
         (assert (= (seq.unit (select u 0)) s))"
    ));
    let seq = Sort::Seq(Box::new(Sort::array(Sort::Int, Sort::Int)));
    assert_eq!(classify_sort(&exec.ctx.terms, &seq), SortClass::Unsupported);
    assert!(ArrayUfAbstraction::build(&mut exec.ctx.terms, &roots).is_none());
}

/// The checker resolves carriers itself rather than trusting the builder: an
/// abstraction built while `Row` read as plain is refused once the store
/// records an array field for it.
#[test]
fn the_checker_refuses_a_kept_carrier_that_reaches_an_array() {
    let (mut exec, roots) = load(&congruence_beside_rows("Int"));
    let abstraction = ArrayUfAbstraction::build(&mut exec.ctx.terms, &roots)
        .expect("a carrier of scalars builds");
    assert!(
        is_pure_renaming(&exec.ctx.terms, &roots, &abstraction),
        "positive control"
    );
    let Sort::Uninterpreted(carrier) = carrier_sort(&exec.ctx.terms, &roots) else {
        unreachable!("carrier_sort returns a nominal sort");
    };
    exec.ctx
        .terms
        .register_datatype_field_sorts(&carrier, &[Sort::array(Sort::Int, Sort::Int)]);
    assert!(!is_pure_renaming(&exec.ctx.terms, &roots, &abstraction));
}

/// Only a renamed carrier's constructors and selectors get fresh functions. A
/// tester over it has no renaming (keeping it at the fresh sort would change
/// its signature), so a problem that tests a renamed carrier declines to
/// build and the rung declines.
#[test]
fn a_tester_over_a_renamed_carrier_declines() {
    let (mut exec, roots) = load(
        "(declare-datatype E ((A (fa (Array Int Int))) (B (fb Int))))\
         (declare-const t (Array Int E))\
         (assert ((_ is A) (select t 0)))(assert ((_ is B) (select t 0)))",
    );
    assert!(ArrayUfAbstraction::build(&mut exec.ctx.terms, &roots).is_none());
    assert!(!exec.nested_array_uf_abstraction_unsat(&roots));
}
