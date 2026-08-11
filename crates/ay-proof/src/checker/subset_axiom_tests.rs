// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Schema tests for `SubsetReflexive` and `SubsetElementInstance`.
//!
//! A lemma kind is a licence to believe a clause with no derivation behind it,
//! so the REJECTIONS matter more than the acceptances: each near-miss below is
//! a clause that is falsifiable, and admitting any one of them would let a
//! refutation be assembled out of nothing.

use ay_core::{ArraySort, ProofId, Sort, Symbol, TermId, TermStore};

use super::{validate_subset_element_instance, validate_subset_reflexive};

const STEP: ProofId = ProofId(0);

fn set_sort() -> Sort {
    Sort::Array(Box::new(ArraySort {
        index_sort: Sort::Int,
        element_sort: Sort::Bool,
    }))
}

fn multiset_sort() -> Sort {
    Sort::Array(Box::new(ArraySort {
        index_sort: Sort::Int,
        element_sort: Sort::Int,
    }))
}

fn set_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, set_sort())
}

fn multiset_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, multiset_sort())
}

fn subset(terms: &mut TermStore, op: &str, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named(op), [left, right], Sort::Bool)
}

fn select(terms: &mut TermStore, array: TermId, index: TermId, sort: Sort) -> TermId {
    terms.mk_app(Symbol::named("select"), [array, index], sort)
}

// ---------------------------------------------------------------------------
// SubsetReflexive
// ---------------------------------------------------------------------------

#[test]
fn accepts_reflexivity_for_every_collection_predicate() {
    for op in ["set.subset", "map.subset", "multiset.subset"] {
        let mut terms = TermStore::new();
        let s = set_var(&mut terms, "s");
        let clause = vec![subset(&mut terms, op, s, s)];
        assert!(
            validate_subset_reflexive(&terms, STEP, &clause).is_ok(),
            "{op} must accept `(X.subset s s)`"
        );
    }
}

/// THE load-bearing rejection. `(subset s t)` for distinct `s` and `t` is an
/// arbitrary subset claim, not a tautology: it is false whenever `s` has a
/// member `t` lacks.
#[test]
fn rejects_a_subset_claim_between_different_collections() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let t = set_var(&mut terms, "t");
    let clause = vec![subset(&mut terms, "set.subset", s, t)];
    assert!(validate_subset_reflexive(&terms, STEP, &clause).is_err());
}

/// The NEGATED reflexive atom is the exact opposite claim and is
/// unsatisfiable, so it must never be handed out as a lemma.
#[test]
fn rejects_the_negated_reflexive_atom() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let atom = subset(&mut terms, "set.subset", s, s);
    let clause = vec![terms.mk_not(atom)];
    assert!(validate_subset_reflexive(&terms, STEP, &clause).is_err());
}

/// An unrelated predicate that merely happens to be applied to one term twice
/// carries no reflexivity guarantee.
#[test]
fn rejects_an_unrelated_binary_predicate() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let clause = vec![subset(&mut terms, "my.subset", s, s)];
    assert!(validate_subset_reflexive(&terms, STEP, &clause).is_err());
}

/// The native collection signature is re-derived here, not taken from the
/// frontend: a two-argument `set.subset` over NON-array operands is the shape
/// a forged declaration would have to take, and it is rejected.
#[test]
fn rejects_a_non_array_operand_signature() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let clause = vec![subset(&mut terms, "set.subset", i, i)];
    assert!(validate_subset_reflexive(&terms, STEP, &clause).is_err());
}

#[test]
fn rejects_a_multi_literal_clause() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let t = set_var(&mut terms, "t");
    let first = subset(&mut terms, "set.subset", s, s);
    let second = subset(&mut terms, "set.subset", t, t);
    assert!(validate_subset_reflexive(&terms, STEP, &[first, second]).is_err());
}

// ---------------------------------------------------------------------------
// SubsetElementInstance — set membership carrier
// ---------------------------------------------------------------------------

/// `(cl (not (set.subset A B)) (not (select A E)) (select B E))`.
fn set_instance(terms: &mut TermStore, sub: TermId, sup: TermId, index: i64) -> Vec<TermId> {
    let atom = subset(terms, "set.subset", sub, sup);
    let e = terms.mk_int(index.into());
    let in_sub = select(terms, sub, e, Sort::Bool);
    let in_sup = select(terms, sup, e, Sort::Bool);
    let not_atom = terms.mk_not(atom);
    let not_in_sub = terms.mk_not(in_sub);
    vec![not_atom, not_in_sub, in_sup]
}

#[test]
fn accepts_the_set_membership_instantiation() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let t = set_var(&mut terms, "t");
    let clause = set_instance(&mut terms, s, t, 7);
    assert!(validate_subset_element_instance(&terms, STEP, &clause).is_ok());
}

/// Literal order is free — the SAT trace may permute a clause — but the
/// literal SET is exact.
#[test]
fn accepts_the_set_instantiation_in_any_literal_order() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let t = set_var(&mut terms, "t");
    let mut clause = set_instance(&mut terms, s, t, 7);
    clause.reverse();
    assert!(validate_subset_element_instance(&terms, STEP, &clause).is_ok());
}

/// THE load-bearing rejection for this schema. Reading the SUPERSET in the
/// antecedent and the SUBSET in the consequent is the CONVERSE implication
/// (`A ⊆ B → (e ∈ B → e ∈ A)`), which is false.
#[test]
fn rejects_the_converse_membership_implication() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let t = set_var(&mut terms, "t");
    let atom = subset(&mut terms, "set.subset", s, t);
    let e = terms.mk_int(7.into());
    let in_sub = select(&mut terms, s, e, Sort::Bool);
    let in_sup = select(&mut terms, t, e, Sort::Bool);
    let not_atom = terms.mk_not(atom);
    let not_in_sup = terms.mk_not(in_sup);
    let clause = vec![not_atom, not_in_sup, in_sub];
    assert!(validate_subset_element_instance(&terms, STEP, &clause).is_err());
}

/// Reading a THIRD collection in the consequent would licence
/// `A ⊆ B ⇒ e ∈ C` for an unrelated `C`. The operand identity is the whole
/// content of the axiom.
#[test]
fn rejects_a_consequent_over_an_unrelated_collection() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let t = set_var(&mut terms, "t");
    let u = set_var(&mut terms, "u");
    let atom = subset(&mut terms, "set.subset", s, t);
    let e = terms.mk_int(7.into());
    let in_sub = select(&mut terms, s, e, Sort::Bool);
    let in_other = select(&mut terms, u, e, Sort::Bool);
    let not_atom = terms.mk_not(atom);
    let not_in_sub = terms.mk_not(in_sub);
    let clause = vec![not_atom, not_in_sub, in_other];
    assert!(validate_subset_element_instance(&terms, STEP, &clause).is_err());
}

/// Two DIFFERENT element terms break the instantiation: `e ∈ A → f ∈ B` is
/// not entailed by `A ⊆ B`.
#[test]
fn rejects_two_different_element_terms() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let t = set_var(&mut terms, "t");
    let atom = subset(&mut terms, "set.subset", s, t);
    let e = terms.mk_int(7.into());
    let f = terms.mk_int(8.into());
    let in_sub = select(&mut terms, s, e, Sort::Bool);
    let in_sup = select(&mut terms, t, f, Sort::Bool);
    let not_atom = terms.mk_not(atom);
    let not_in_sub = terms.mk_not(in_sub);
    let clause = vec![not_atom, not_in_sub, in_sup];
    assert!(validate_subset_element_instance(&terms, STEP, &clause).is_err());
}

/// The POSITIVE subset atom turns the clause into `A ⊆ B ∨ ...`, which claims
/// something quite different and is not valid.
#[test]
fn rejects_a_positive_subset_atom() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let t = set_var(&mut terms, "t");
    let atom = subset(&mut terms, "set.subset", s, t);
    let e = terms.mk_int(7.into());
    let in_sub = select(&mut terms, s, e, Sort::Bool);
    let in_sup = select(&mut terms, t, e, Sort::Bool);
    let not_in_sub = terms.mk_not(in_sub);
    let clause = vec![atom, not_in_sub, in_sup];
    assert!(validate_subset_element_instance(&terms, STEP, &clause).is_err());
}

/// `map.subset`'s element-wise definition is a CONJUNCTION over the `map.dom`
/// projection, not this single membership implication, so the map predicate
/// must fail closed here.
#[test]
fn rejects_map_subset_in_the_membership_schema() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let t = set_var(&mut terms, "t");
    let atom = subset(&mut terms, "map.subset", s, t);
    let e = terms.mk_int(7.into());
    let in_sub = select(&mut terms, s, e, Sort::Bool);
    let in_sup = select(&mut terms, t, e, Sort::Bool);
    let not_atom = terms.mk_not(atom);
    let not_in_sub = terms.mk_not(in_sub);
    let clause = vec![not_atom, not_in_sub, in_sup];
    assert!(validate_subset_element_instance(&terms, STEP, &clause).is_err());
}

// ---------------------------------------------------------------------------
// SubsetElementInstance — multiset count carrier
// ---------------------------------------------------------------------------

/// `(cl (not (multiset.subset A B)) (<= (select A E) (select B E)))`.
fn multiset_instance(terms: &mut TermStore, sub: TermId, sup: TermId) -> Vec<TermId> {
    let atom = subset(terms, "multiset.subset", sub, sup);
    let e = terms.mk_int(9.into());
    let count_sub = select(terms, sub, e, Sort::Int);
    let count_sup = select(terms, sup, e, Sort::Int);
    let bound = terms.mk_le(count_sub, count_sup);
    let not_atom = terms.mk_not(atom);
    vec![not_atom, bound]
}

#[test]
fn accepts_the_multiset_count_instantiation() {
    let mut terms = TermStore::new();
    let m = multiset_var(&mut terms, "m");
    let n = multiset_var(&mut terms, "n");
    let clause = multiset_instance(&mut terms, m, n);
    assert!(validate_subset_element_instance(&terms, STEP, &clause).is_ok());
}

/// The same clause spelled as a unit `(cl (or ..))`, which is how the emitter
/// hands it over. Same literal multiset, same verdict.
#[test]
fn accepts_the_multiset_instantiation_wrapped_in_an_or() {
    let mut terms = TermStore::new();
    let m = multiset_var(&mut terms, "m");
    let n = multiset_var(&mut terms, "n");
    let literals = multiset_instance(&mut terms, m, n);
    let wrapped = terms.mk_or(literals);
    assert!(validate_subset_element_instance(&terms, STEP, &[wrapped]).is_ok());
}

/// THE load-bearing rejection for this schema. `count(B,E) <= count(A,E)` is
/// the CONVERSE bound and is false: `{a} ⊆ {a,a}` has `1 <= 2`, not `2 <= 1`.
/// The orientation is fixed, never searched.
#[test]
fn rejects_the_reversed_count_bound() {
    let mut terms = TermStore::new();
    let m = multiset_var(&mut terms, "m");
    let n = multiset_var(&mut terms, "n");
    let atom = subset(&mut terms, "multiset.subset", m, n);
    let e = terms.mk_int(9.into());
    let count_sub = select(&mut terms, m, e, Sort::Int);
    let count_sup = select(&mut terms, n, e, Sort::Int);
    let reversed = terms.mk_le(count_sup, count_sub);
    let not_atom = terms.mk_not(atom);
    assert!(validate_subset_element_instance(&terms, STEP, &[not_atom, reversed]).is_err());
}

/// A count bound over a THIRD multiset is not entailed by `A ⊆ B`.
#[test]
fn rejects_a_count_bound_over_an_unrelated_multiset() {
    let mut terms = TermStore::new();
    let m = multiset_var(&mut terms, "m");
    let n = multiset_var(&mut terms, "n");
    let other = multiset_var(&mut terms, "other");
    let atom = subset(&mut terms, "multiset.subset", m, n);
    let e = terms.mk_int(9.into());
    let count_sub = select(&mut terms, m, e, Sort::Int);
    let count_other = select(&mut terms, other, e, Sort::Int);
    let bound = terms.mk_le(count_sub, count_other);
    let not_atom = terms.mk_not(atom);
    assert!(validate_subset_element_instance(&terms, STEP, &[not_atom, bound]).is_err());
}

/// A STRICT bound is a different (and false) claim: `A ⊆ B` permits equal
/// counts.
#[test]
fn rejects_a_strict_count_bound() {
    let mut terms = TermStore::new();
    let m = multiset_var(&mut terms, "m");
    let n = multiset_var(&mut terms, "n");
    let atom = subset(&mut terms, "multiset.subset", m, n);
    let e = terms.mk_int(9.into());
    let count_sub = select(&mut terms, m, e, Sort::Int);
    let count_sup = select(&mut terms, n, e, Sort::Int);
    let strict = terms.mk_lt(count_sub, count_sup);
    let not_atom = terms.mk_not(atom);
    assert!(validate_subset_element_instance(&terms, STEP, &[not_atom, strict]).is_err());
}
