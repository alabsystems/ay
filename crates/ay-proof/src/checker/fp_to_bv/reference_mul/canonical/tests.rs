// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Constant, Sort, Symbol, TermData};
use ay_sat::Literal;
use std::cell::Cell;
use std::ops::ControlFlow;
use std::time::Duration;

mod binding;
mod gates;
mod ownership;
mod word_oracle;

fn limits() -> ResolutionProofLimits {
    let mut limits = ResolutionProofLimits {
        deadline: Some(Instant::now() + Duration::from_secs(30)),
        max_num_vars: 100_000,
        max_input_clauses: 500_000,
        max_input_literals: 2_000_000,
        max_conflicts: Some(50_000),
        max_decisions: Some(100_000),
        ..ResolutionProofLimits::default()
    };
    limits.validation.max_work = 2_000_000;
    limits
}

fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

fn raw(terms: &mut TermStore, word: TermId, eb: u32, p: u32) -> TermId {
    terms.mk_app(
        Symbol::indexed("to_fp", vec![eb, p]),
        [word],
        Sort::FloatingPoint(eb, p),
    )
}

fn literal(terms: &mut TermStore, number: u64, width: u32) -> TermId {
    terms.mk_bitvec(number.into(), width)
}

fn opposite_equal(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    let equal = app(terms, "=", &[a, b], Sort::Bool);
    // Build actual unsimplified source, not the core Boolean folder's shortcut.
    app(terms, "not", &[equal], Sort::Bool)
}

fn mul_identity(terms: &mut TermStore) -> TermId {
    let bv = terms.mk_var("raw_source_x", Sort::bitvec(4));
    let x = raw(terms, bv, 2, 2);
    let one = literal(terms, 2, 4);
    let one = raw(terms, one, 2, 2);
    let rm = terms.mk_var("actual_smt_rm", Sort::Uninterpreted("RoundingMode".into()));
    let product = app(terms, "fp.mul", &[rm, x, one], Sort::FloatingPoint(2, 2));
    opposite_equal(terms, product, x)
}

#[test]
fn fp_namespace_canonical_source_does_not_lower_registered_builtins() {
    for name in ["fp.mul", "to_fp", "not", "="] {
        let mut terms = TermStore::new();
        let root = mul_identity(&mut terms);
        let mut live = || ControlFlow::Continue(());
        let mut work = WorkBudget::new(50_000_000, &mut live);
        capture(&terms, &[root], &limits(), &mut work).unwrap();
        terms.register_declared_function(name);
        let mut work = WorkBudget::new(50_000_000, &mut live);
        assert!(
            capture(&terms, &[root], &limits(), &mut work).is_err(),
            "{name}"
        );
    }
}

#[test]
fn raw_interchange_full_symbolic_mul_source_refutation_replays() {
    let mut terms = TermStore::new();
    let root = mul_identity(&mut terms);
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(50_000_000, &mut live);
    let mut proof = capture(&terms, &[root], &limits(), &mut work).expect("actual symbolic source");
    proof.replay().expect("source rederived and RUP replayed");
}

#[test]
fn nested_add_sub_source_uses_same_original_bv_occurrences() {
    let mut terms = TermStore::new();
    let word = terms.mk_var("x", Sort::bitvec(4));
    let x = raw(&mut terms, word, 2, 2);
    let rm = app(
        &mut terms,
        "RNE",
        &[],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let add = app(&mut terms, "fp.add", &[rm, x, x], Sort::FloatingPoint(2, 2));
    let sub = app(
        &mut terms,
        "fp.sub",
        &[rm, add, add],
        Sort::FloatingPoint(2, 2),
    );
    let root = opposite_equal(&mut terms, sub, sub);
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(50_000_000, &mut live);
    capture(&terms, &[root], &limits(), &mut work).expect("whole nested source");
}

#[test]
fn composite_bv_interchange_is_derived_not_fresh_arbitrary_field_inputs() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(2));
    let b = terms.mk_var("b", Sort::bitvec(2));
    let joined = app(&mut terms, "concat", &[a, b], Sort::bitvec(4));
    let x = raw(&mut terms, joined, 2, 2);
    let root = opposite_equal(&mut terms, x, x);
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(10_000_000, &mut live);
    let mut proof =
        capture(&terms, &[root], &limits(), &mut work).expect("actual concat/extract source");
    proof.replay().expect("same composite source");
}

#[test]
fn all_nan_representatives_are_one_logical_value_but_ieee_eq_is_false() {
    let mut terms = TermStore::new();
    let a = literal(&mut terms, 7, 4);
    let b = literal(&mut terms, 15, 4);
    let a = raw(&mut terms, a, 2, 2);
    let b = raw(&mut terms, b, 2, 2);
    let structural_false = opposite_equal(&mut terms, a, b);
    let ieee_true = app(&mut terms, "fp.eq", &[a, b], Sort::Bool);
    for root in [structural_false, ieee_true] {
        let mut live = || ControlFlow::Continue(());
        let mut work = WorkBudget::new(10_000_000, &mut live);
        capture(&terms, &[root], &limits(), &mut work).expect("SMT NaN quotient/IEEE exclusion");
    }
}

#[test]
fn signed_zero_structural_inequality_remains_satisfiable_no_refutation() {
    let mut terms = TermStore::new();
    let a = literal(&mut terms, 0, 4);
    let b = literal(&mut terms, 8, 4);
    let a = raw(&mut terms, a, 2, 2);
    let b = raw(&mut terms, b, 2, 2);
    let root = opposite_equal(&mut terms, a, b);
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(10_000_000, &mut live);
    assert!(matches!(
        capture(&terms, &[root], &limits(), &mut work),
        Err(Error::Search(ay_sat::ResolutionProofError::Satisfiable))
    ));
}

#[test]
fn ieee_zero_equality_and_order_do_not_invent_structural_zero_equality() {
    let mut terms = TermStore::new();
    let a = literal(&mut terms, 0, 4);
    let b = literal(&mut terms, 8, 4);
    let a = raw(&mut terms, a, 2, 2);
    let b = raw(&mut terms, b, 2, 2);
    let equal = app(&mut terms, "fp.eq", &[a, b], Sort::Bool);
    let not_equal = app(&mut terms, "not", &[equal], Sort::Bool);
    let less = app(&mut terms, "fp.lt", &[a, b], Sort::Bool);
    for root in [not_equal, less] {
        let mut live = || ControlFlow::Continue(());
        let mut work = WorkBudget::new(10_000_000, &mut live);
        capture(&terms, &[root], &limits(), &mut work).expect("both IEEE zeros unordered/equal");
    }
}
