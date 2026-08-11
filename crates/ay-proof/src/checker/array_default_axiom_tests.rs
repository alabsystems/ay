// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict forgery tests for the folded array-default/const-array congruence.

use crate::checker::*;
use ay_core::{
    ArraySort, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind,
};

fn array_sort(index: Sort, element: Sort) -> Sort {
    Sort::Array(Box::new(ArraySort::new(index, element)))
}

fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

fn raw_store(
    terms: &mut TermStore,
    array: TermId,
    index: TermId,
    value: TermId,
    result_sort: Sort,
) -> TermId {
    terms.mk_app(
        Symbol::named("store"),
        vec![array, index, value],
        result_sort,
    )
}

fn validate_strict(terms: &TermStore, clause: Vec<TermId>) -> Result<(), ProofCheckError> {
    let step = ProofStep::TheoryLemma {
        theory: "arrays".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::ArrayDefaultConst,
        lia: None,
    };
    let mut derived = Vec::new();
    validate_step(terms, &mut derived, ProofId(0), &step, true, None)
}

struct Fixture {
    terms: TermStore,
    array: TermId,
    other_array: TermId,
    fill: TermId,
    other_fill: TermId,
    constant: TermId,
    default: TermId,
}

impl Fixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let sort = array_sort(Sort::Int, Sort::Int);
        let array = terms.mk_var("a", sort.clone());
        let other_array = terms.mk_var("b", sort);
        let fill = terms.mk_int(0.into());
        let other_fill = terms.mk_int(1.into());
        let constant = terms.mk_const_array(Sort::Int, fill);
        let default = terms.mk_array_default(array);
        Self {
            terms,
            array,
            other_array,
            fill,
            other_fill,
            constant,
            default,
        }
    }

    fn exact_clause(&mut self) -> Vec<TermId> {
        let array_eq = eq(&mut self.terms, self.array, self.constant);
        let premise = self.terms.mk_not_raw(array_eq);
        let conclusion = eq(&mut self.terms, self.default, self.fill);
        vec![premise, conclusion]
    }
}

#[test]
fn accepts_exact_default_const_congruence_and_recognizes_it() {
    let mut fixture = Fixture::new();
    let clause = fixture.exact_clause();
    assert_eq!(
        recognize_array_theory_lemma(&fixture.terms, &clause),
        Some(TheoryLemmaKind::ArrayDefaultConst)
    );
    validate_strict(&fixture.terms, clause).expect("exact folded congruence must certify");
}

#[test]
fn accepts_packed_or_and_both_equality_orientations() {
    let mut fixture = Fixture::new();
    let array_eq = eq(&mut fixture.terms, fixture.constant, fixture.array);
    let premise = fixture.terms.mk_not_raw(array_eq);
    let conclusion = eq(&mut fixture.terms, fixture.fill, fixture.default);
    let packed = fixture
        .terms
        .mk_app(Symbol::named("or"), vec![conclusion, premise], Sort::Bool);
    validate_strict(&fixture.terms, vec![packed])
        .expect("packing and harmless orientations must preserve the exact clause");
}

#[test]
fn rejects_packed_or_with_non_bool_child_even_when_shape_matches() {
    // `TermStore` deliberately permits raw applications. A hostile proof
    // bundle can therefore annotate an equality with a non-Bool result sort
    // and hide it beneath a Bool-annotated `or`. Strict checking must validate
    // every flattened child, not merely the aggregate's outer sort.
    let mut fixture = Fixture::new();
    let array_eq = eq(&mut fixture.terms, fixture.array, fixture.constant);
    let premise = fixture.terms.mk_not_raw(array_eq);
    let malformed_conclusion = fixture.terms.mk_app(
        Symbol::named("="),
        vec![fixture.default, fixture.fill],
        Sort::Int,
    );
    let packed = fixture.terms.mk_app(
        Symbol::named("or"),
        vec![premise, malformed_conclusion],
        Sort::Bool,
    );

    assert_eq!(
        recognize_array_theory_lemma(&fixture.terms, &[packed]),
        None,
        "classification must not promote a packed clause with a non-Bool child"
    );
    validate_strict(&fixture.terms, vec![packed])
        .expect_err("strict replay must reject a packed clause with a non-Bool child");
}

#[test]
fn accepts_well_sorted_reordered_store_chains_with_the_same_const_root() {
    let mut fixture = Fixture::new();
    let sort = fixture.terms.sort(fixture.array).clone();
    let i0 = fixture.terms.mk_int(0.into());
    let i1 = fixture.terms.mk_int(1.into());
    let v0 = fixture.terms.mk_int(30.into());
    let v1 = fixture.terms.mk_int(40.into());

    for writes in [[(i0, v0), (i1, v1)], [(i1, v1), (i0, v0)]] {
        let mut chain = fixture.constant;
        for (index, value) in writes {
            chain = raw_store(&mut fixture.terms, chain, index, value, sort.clone());
        }
        let array_eq = eq(&mut fixture.terms, fixture.array, chain);
        let premise = fixture.terms.mk_not_raw(array_eq);
        let conclusion = eq(&mut fixture.terms, fixture.default, fixture.fill);
        validate_strict(&fixture.terms, vec![premise, conclusion])
            .expect("finite well-sorted writes do not change a constant array's default");
    }
}

#[test]
fn accepts_default_const_under_exact_equal_matched_stores() {
    let mut fixture = Fixture::new();
    let sort = fixture.terms.sort(fixture.array).clone();
    let index = fixture.terms.mk_int(7.into());
    let value = fixture.terms.mk_int(30.into());
    let stored_array = raw_store(
        &mut fixture.terms,
        fixture.array,
        index,
        value,
        sort.clone(),
    );
    let stored_constant = raw_store(&mut fixture.terms, fixture.constant, index, value, sort);
    let premise_eq = eq(&mut fixture.terms, stored_array, stored_constant);
    let premise = fixture.terms.mk_not_raw(premise_eq);
    let conclusion = eq(&mut fixture.terms, fixture.fill, fixture.default);
    let clause = vec![conclusion, premise];

    assert_eq!(
        recognize_array_theory_lemma(&fixture.terms, &clause),
        Some(TheoryLemmaKind::ArrayDefaultConst)
    );
    validate_strict(&fixture.terms, clause.clone())
        .expect("equal matched stores preserve the const base's default");

    let packed = fixture
        .terms
        .mk_app(Symbol::named("or"), clause.clone(), Sort::Bool);
    validate_strict(&fixture.terms, vec![packed])
        .expect("the packed AY clause must preserve the exact schema");

    let mut proof = Proof::new();
    let lemma =
        proof.add_theory_lemma_with_kind("arrays", clause, TheoryLemmaKind::ArrayDefaultConst);
    let guard = proof.add_assume(premise_eq, None);
    let unit_conclusion = proof.add_resolution(vec![conclusion], premise_eq, lemma, guard);
    let not_conclusion = fixture.terms.mk_not(conclusion);
    let contrary = proof.add_assume(not_conclusion, None);
    proof.add_resolution(vec![], conclusion, unit_conclusion, contrary);
    crate::check_proof_strict(&proof, &fixture.terms)
        .expect("matched-store default lemma must survive strict whole-proof replay");
}

#[test]
fn accepts_matched_outer_store_over_a_folded_const_base() {
    let mut fixture = Fixture::new();
    let sort = fixture.terms.sort(fixture.array).clone();
    let inner_index = fixture.terms.mk_int(0.into());
    let outer_index = fixture.terms.mk_int(7.into());
    let value = fixture.terms.mk_int(30.into());
    let folded_constant_base = raw_store(
        &mut fixture.terms,
        fixture.constant,
        inner_index,
        value,
        sort.clone(),
    );
    let stored_array = raw_store(
        &mut fixture.terms,
        fixture.array,
        outer_index,
        value,
        sort.clone(),
    );
    let stored_folded_constant = raw_store(
        &mut fixture.terms,
        folded_constant_base,
        outer_index,
        value,
        sort,
    );
    let premise_eq = eq(&mut fixture.terms, stored_array, stored_folded_constant);
    let premise = fixture.terms.mk_not_raw(premise_eq);
    let conclusion = eq(&mut fixture.terms, fixture.fill, fixture.default);
    validate_strict(&fixture.terms, vec![conclusion, premise])
        .expect("a bounded folded const base has the same preserved default");
}

#[test]
fn rejects_matched_store_default_near_misses() {
    let mut fixture = Fixture::new();
    let sort = fixture.terms.sort(fixture.array).clone();
    let index = fixture.terms.mk_int(7.into());
    let wrong_index = fixture.terms.mk_int(8.into());
    let value = fixture.terms.mk_int(30.into());
    let wrong_value = fixture.terms.mk_int(31.into());
    let stored_array = raw_store(
        &mut fixture.terms,
        fixture.array,
        index,
        value,
        sort.clone(),
    );
    let stored_constant = raw_store(
        &mut fixture.terms,
        fixture.constant,
        index,
        value,
        sort.clone(),
    );
    let premise_eq = eq(&mut fixture.terms, stored_array, stored_constant);
    let premise = fixture.terms.mk_not_raw(premise_eq);
    let exact = eq(&mut fixture.terms, fixture.default, fixture.fill);

    let stored_other = raw_store(
        &mut fixture.terms,
        fixture.other_array,
        index,
        value,
        sort.clone(),
    );
    let wrong_base_eq = eq(&mut fixture.terms, stored_other, stored_constant);
    let wrong_base = fixture.terms.mk_not_raw(wrong_base_eq);
    let stored_constant_wrong_index = raw_store(
        &mut fixture.terms,
        fixture.constant,
        wrong_index,
        value,
        sort.clone(),
    );
    let wrong_index_eq = eq(
        &mut fixture.terms,
        stored_array,
        stored_constant_wrong_index,
    );
    let wrong_index_premise = fixture.terms.mk_not_raw(wrong_index_eq);
    let stored_constant_wrong_value = raw_store(
        &mut fixture.terms,
        fixture.constant,
        index,
        wrong_value,
        sort.clone(),
    );
    let wrong_value_eq = eq(
        &mut fixture.terms,
        stored_array,
        stored_constant_wrong_value,
    );
    let wrong_value_premise = fixture.terms.mk_not_raw(wrong_value_eq);
    let wrong_fill_conclusion = eq(&mut fixture.terms, fixture.default, fixture.other_fill);
    let inner = raw_store(
        &mut fixture.terms,
        fixture.array,
        wrong_index,
        wrong_value,
        sort.clone(),
    );
    let depth_two = raw_store(&mut fixture.terms, inner, index, value, sort.clone());
    let depth_eq = eq(&mut fixture.terms, depth_two, stored_constant);
    let depth_premise = fixture.terms.mk_not_raw(depth_eq);
    let bool_index = fixture.terms.mk_bool(true);
    let ill_sorted = raw_store(
        &mut fixture.terms,
        fixture.constant,
        bool_index,
        value,
        sort,
    );
    let ill_sorted_eq = eq(&mut fixture.terms, stored_array, ill_sorted);
    let ill_sorted_premise = fixture.terms.mk_not_raw(ill_sorted_eq);
    let negated_conclusion = fixture.terms.mk_not(exact);
    let extra = fixture.terms.mk_var("extra_matched_store", Sort::Bool);

    for (label, clause) in [
        ("wrong base/conclusion splice", vec![wrong_base, exact]),
        ("different index", vec![wrong_index_premise, exact]),
        ("different value", vec![wrong_value_premise, exact]),
        ("wrong fill", vec![premise, wrong_fill_conclusion]),
        ("depth-two store", vec![depth_premise, exact]),
        ("ill-sorted raw store", vec![ill_sorted_premise, exact]),
        ("positive premise", vec![premise_eq, exact]),
        ("negative conclusion", vec![premise, negated_conclusion]),
        ("extra literal", vec![premise, exact, extra]),
    ] {
        validate_strict(&fixture.terms, clause).expect_err(label);
    }
}

#[test]
fn rejects_default_of_a_different_array() {
    let mut fixture = Fixture::new();
    let array_eq = eq(&mut fixture.terms, fixture.array, fixture.constant);
    let premise = fixture.terms.mk_not_raw(array_eq);
    let other_default = fixture.terms.mk_array_default(fixture.other_array);
    let conclusion = eq(&mut fixture.terms, other_default, fixture.fill);
    validate_strict(&fixture.terms, vec![premise, conclusion])
        .expect_err("the conclusion must use the premise's exact array term");
}

#[test]
fn rejects_mismatched_const_fill() {
    let mut fixture = Fixture::new();
    let array_eq = eq(&mut fixture.terms, fixture.array, fixture.constant);
    let premise = fixture.terms.mk_not_raw(array_eq);
    let conclusion = eq(&mut fixture.terms, fixture.default, fixture.other_fill);
    validate_strict(&fixture.terms, vec![premise, conclusion])
        .expect_err("the conclusion must use the const-array's exact fill");
}

#[test]
fn rejects_extra_literal_and_missing_negated_premise() {
    let mut fixture = Fixture::new();
    let mut clause = fixture.exact_clause();
    let extra = fixture.terms.mk_var("extra", Sort::Bool);
    clause.push(extra);
    validate_strict(&fixture.terms, clause)
        .expect_err("the certificate schema is exact and rejects weakening literals");

    let conclusion = eq(&mut fixture.terms, fixture.default, fixture.fill);
    validate_strict(&fixture.terms, vec![conclusion])
        .expect_err("a default equality alone needs the matching array-equality premise");
}

#[test]
fn rejects_non_const_array_premise() {
    let mut fixture = Fixture::new();
    let array_eq = eq(&mut fixture.terms, fixture.array, fixture.other_array);
    let premise = fixture.terms.mk_not_raw(array_eq);
    let conclusion = eq(&mut fixture.terms, fixture.default, fixture.fill);
    validate_strict(&fixture.terms, vec![premise, conclusion])
        .expect_err("one premise side must be the exact const-array application");
}

#[test]
fn rejects_ill_sorted_const_fill_and_default_result() {
    let mut fixture = Fixture::new();
    let bool_fill = fixture.terms.mk_bool(true);
    let malformed_const = fixture.terms.mk_app(
        Symbol::named("const-array"),
        vec![bool_fill],
        array_sort(Sort::Int, Sort::Int),
    );
    let array_eq = eq(&mut fixture.terms, fixture.array, malformed_const);
    let premise = fixture.terms.mk_not_raw(array_eq);
    let malformed_default =
        fixture
            .terms
            .mk_app(Symbol::named("default"), vec![fixture.array], Sort::Bool);
    let conclusion = eq(&mut fixture.terms, malformed_default, bool_fill);
    validate_strict(&fixture.terms, vec![premise, conclusion])
        .expect_err("application result annotations cannot override exact array element sorts");
}

#[test]
fn rejects_wrong_store_index_value_and_result_sorts() {
    let mut fixture = Fixture::new();
    let expected_sort = fixture.terms.sort(fixture.array).clone();
    let bool_term = fixture.terms.mk_bool(true);
    let int_term = fixture.terms.mk_int(9.into());

    let wrong_index = raw_store(
        &mut fixture.terms,
        fixture.constant,
        bool_term,
        int_term,
        expected_sort.clone(),
    );
    let wrong_value = raw_store(
        &mut fixture.terms,
        fixture.constant,
        int_term,
        bool_term,
        expected_sort.clone(),
    );
    let wrong_result = raw_store(
        &mut fixture.terms,
        fixture.constant,
        int_term,
        int_term,
        array_sort(Sort::Bool, Sort::Int),
    );

    for forged in [wrong_index, wrong_value, wrong_result] {
        let array_eq = eq(&mut fixture.terms, fixture.array, forged);
        let premise = fixture.terms.mk_not_raw(array_eq);
        let conclusion = eq(&mut fixture.terms, fixture.default, fixture.fill);
        validate_strict(&fixture.terms, vec![premise, conclusion])
            .expect_err("every store signature and the unchanged array sort are load-bearing");
    }
}

#[test]
fn rejects_store_chain_over_the_explicit_depth_budget() {
    let mut fixture = Fixture::new();
    let sort = fixture.terms.sort(fixture.array).clone();
    let index = fixture.terms.mk_int(5.into());
    let value = fixture.terms.mk_int(7.into());
    let mut chain = fixture.constant;
    for _ in 0..=1_024 {
        chain = raw_store(&mut fixture.terms, chain, index, value, sort.clone());
    }
    let array_eq = eq(&mut fixture.terms, fixture.array, chain);
    let premise = fixture.terms.mk_not_raw(array_eq);
    let conclusion = eq(&mut fixture.terms, fixture.default, fixture.fill);
    validate_strict(&fixture.terms, vec![premise, conclusion])
        .expect_err("an untrusted proof cannot force unbounded store-chain traversal");
}

#[test]
fn rejects_matched_outer_store_over_folded_base_depth_budget() {
    let mut fixture = Fixture::new();
    let sort = fixture.terms.sort(fixture.array).clone();
    let inner_index = fixture.terms.mk_int(5.into());
    let outer_index = fixture.terms.mk_int(6.into());
    let value = fixture.terms.mk_int(7.into());
    let mut folded_base = fixture.constant;
    for _ in 0..=1_024 {
        folded_base = raw_store(
            &mut fixture.terms,
            folded_base,
            inner_index,
            value,
            sort.clone(),
        );
    }
    let stored_array = raw_store(
        &mut fixture.terms,
        fixture.array,
        outer_index,
        value,
        sort.clone(),
    );
    let stored_folded = raw_store(&mut fixture.terms, folded_base, outer_index, value, sort);
    let premise_eq = eq(&mut fixture.terms, stored_array, stored_folded);
    let premise = fixture.terms.mk_not_raw(premise_eq);
    let conclusion = eq(&mut fixture.terms, fixture.default, fixture.fill);
    validate_strict(&fixture.terms, vec![premise, conclusion])
        .expect_err("matched-store validation must retain the folded-base depth cap");
}

// ---------------------------------------------------------------------------
// Carrier-sensitivity regressions.
//
// `default(store(a,i,v)) = default(a)` is NOT universally valid: a store can
// change the element the default is read from whenever a finite chain can reach
// the whole index carrier. Before the `sort_provably_infinite` gate, the folded
// matcher peeled up to 1024 stores with no carrier check at all, so every case
// below was ACCEPTED. Each is refuted by Z3 5.0.0 with its builtin `default`;
// the oracle query is quoted per test.
//
// These are checker-boundary tests: no AY producer emits `ArrayDefaultConst`
// today, so they guard against a forged or imported proof rather than a wrong
// answer from AY's own search.
// ---------------------------------------------------------------------------

/// Bool index carrier, ONE store. Accepted before the gate.
///
/// ```text
/// (= a (store ((as const (Array Bool Int)) 0) true 7))
/// (not (= (default a) 0))                                => sat   INVALID
/// ```
#[test]
fn rejects_folded_default_over_a_finite_bool_carrier() {
    let mut terms = TermStore::new();
    let sort = array_sort(Sort::Bool, Sort::Int);
    let array = terms.mk_var("a", sort.clone());
    let fill = terms.mk_int(0.into());
    let stored = terms.mk_int(7.into());
    let index = terms.mk_var("i", Sort::Bool);
    let constant = terms.mk_const_array(Sort::Bool, fill);
    let chain = raw_store(&mut terms, constant, index, stored, sort);
    let array_eq = eq(&mut terms, array, chain);
    let premise = terms.mk_not_raw(array_eq);
    let default = terms.mk_array_default(array);
    let conclusion = eq(&mut terms, default, fill);
    validate_strict(&terms, vec![premise, conclusion]).expect_err(
        "a store over a FINITE carrier can change the default; peeling to the \
         const root is unsound and must be refused",
    );
}

/// A chain that COVERS a Bool carrier: the array provably *is* `const 7`, so its
/// default is 7, not the root's 0.
///
/// ```text
/// A = (store (store ((as const (Array Bool Int)) 0) false 7) true 7)
/// (= (default A) 0) => unsat        (= (default A) 7) => sat
/// ```
#[test]
fn rejects_folded_default_when_the_chain_covers_the_carrier() {
    let mut terms = TermStore::new();
    let sort = array_sort(Sort::Bool, Sort::Int);
    let array = terms.mk_var("a", sort.clone());
    let fill = terms.mk_int(0.into());
    let stored = terms.mk_int(7.into());
    let f = terms.mk_bool(false);
    let t = terms.mk_bool(true);
    let constant = terms.mk_const_array(Sort::Bool, fill);
    let inner = raw_store(&mut terms, constant, f, stored, sort.clone());
    let chain = raw_store(&mut terms, inner, t, stored, sort);
    let array_eq = eq(&mut terms, array, chain);
    let premise = terms.mk_not_raw(array_eq);
    let default = terms.mk_array_default(array);
    let conclusion = eq(&mut terms, default, fill);
    validate_strict(&terms, vec![premise, conclusion])
        .expect_err("the covering chain IS const 7, so the root fill 0 is the wrong default");
}

/// A BitVec carrier is finite too, however wide. The 2^14 figure in the solver
/// is a Z3 *performance* heuristic, not a validity threshold, so width must not
/// be used to admit peeling.
#[test]
fn rejects_folded_default_over_a_bitvec_carrier() {
    let mut terms = TermStore::new();
    let bv = Sort::BitVec(ay_core::BitVecSort::new(8));
    let sort = array_sort(bv.clone(), Sort::Int);
    let array = terms.mk_var("a", sort.clone());
    let fill = terms.mk_int(0.into());
    let stored = terms.mk_int(7.into());
    let index = terms.mk_var("i", bv.clone());
    let constant = terms.mk_const_array(bv, fill);
    let chain = raw_store(&mut terms, constant, index, stored, sort);
    let array_eq = eq(&mut terms, array, chain);
    let premise = terms.mk_not_raw(array_eq);
    let default = terms.mk_array_default(array);
    let conclusion = eq(&mut terms, default, fill);
    validate_strict(&terms, vec![premise, conclusion])
        .expect_err("BitVec is finite at every width; peeling must be refused");
}

/// An uninterpreted index sort must be refused, and that is SOUNDNESS, not
/// caution: `validate_array_default_const` is dispatched without a datatype
/// registry, so a finite enum arrives indistinguishable from a genuine
/// uninterpreted sort. Z3 refutes the fold for a 3-element enum.
#[test]
fn rejects_folded_default_over_an_uninterpreted_carrier() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let sort = array_sort(u.clone(), Sort::Int);
    let array = terms.mk_var("a", sort.clone());
    let fill = terms.mk_int(0.into());
    let stored = terms.mk_int(7.into());
    let index = terms.mk_var("i", u.clone());
    let constant = terms.mk_const_array(u, fill);
    let chain = raw_store(&mut terms, constant, index, stored, sort);
    let array_eq = eq(&mut terms, array, chain);
    let premise = terms.mk_not_raw(array_eq);
    let default = terms.mk_array_default(array);
    let conclusion = eq(&mut terms, default, fill);
    validate_strict(&terms, vec![premise, conclusion])
        .expect_err("cardinality is unrecoverable here, so the carrier gate must fail closed");
}

/// `(Array Int E)` with `|E| = 1` has exactly ONE inhabitant, so an index sort
/// being an array of an infinite index does NOT make it infinite. Guards the
/// `|Array I E| = |E|^|I|` reasoning in `sort_provably_infinite`.
#[test]
fn rejects_folded_default_when_the_index_is_itself_a_finite_array() {
    let mut terms = TermStore::new();
    let idx = array_sort(Sort::Int, Sort::Bool);
    let sort = array_sort(idx.clone(), Sort::Int);
    let array = terms.mk_var("a", sort.clone());
    let fill = terms.mk_int(0.into());
    let stored = terms.mk_int(7.into());
    let index = terms.mk_var("i", idx.clone());
    let constant = terms.mk_const_array(idx, fill);
    let chain = raw_store(&mut terms, constant, index, stored, sort);
    let array_eq = eq(&mut terms, array, chain);
    let premise = terms.mk_not_raw(array_eq);
    let default = terms.mk_array_default(array);
    let conclusion = eq(&mut terms, default, fill);
    validate_strict(&terms, vec![premise, conclusion])
        .expect_err("an array index sort is only infinite when its ELEMENT sort is");
}

/// The deliberate positive control: an INFINITE carrier must still be accepted,
/// so the gate does not silently cost capability.
///
/// ```text
/// A = (store (store ((as const (Array Int Int)) 3) 0 5) 7 9)
/// (not (= (default A) 3))                                => unsat  VALID
/// ```
#[test]
fn still_accepts_folded_default_over_an_infinite_carrier() {
    let mut terms = TermStore::new();
    let sort = array_sort(Sort::Int, Sort::Int);
    let array = terms.mk_var("a", sort.clone());
    let fill = terms.mk_int(3.into());
    let i0 = terms.mk_int(0.into());
    let v0 = terms.mk_int(5.into());
    let i1 = terms.mk_int(7.into());
    let v1 = terms.mk_int(9.into());
    let constant = terms.mk_const_array(Sort::Int, fill);
    let inner = raw_store(&mut terms, constant, i0, v0, sort.clone());
    let chain = raw_store(&mut terms, inner, i1, v1, sort);
    let array_eq = eq(&mut terms, array, chain);
    let premise = terms.mk_not_raw(array_eq);
    let default = terms.mk_array_default(array);
    let conclusion = eq(&mut terms, default, fill);
    validate_strict(&terms, vec![premise, conclusion])
        .expect("no finite chain reaches an infinite carrier, so the fold is valid here");
}
