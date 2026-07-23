// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict-mode tests for the Skolemized array-extensionality schema
//! `ArrayExtensionality` and its `array_ext_diff_intro` provenance.
//!
//! This schema is the one array axiom that is NOT a tautology:
//! `(= a b) ∨ ¬(= (select a k) (select b k))` is false for a general index `k`
//! and sound only for a FRESH witness minted for exactly `(a, b)`. Every
//! positive test below is therefore paired with a negative test that breaks
//! exactly one provenance condition and asserts the checker REJECTS — a wrong
//! UNSAT here is total failure.

use crate::checker::*;
use ay_core::{
    AletheRule, ArraySort, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore,
    TheoryLemmaKind,
};

/// `(Array Int Int)`.
fn array_sort() -> Sort {
    Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)))
}

fn select_with_sort(
    terms: &mut TermStore,
    array: TermId,
    index: TermId,
    result_sort: Sort,
) -> TermId {
    terms.mk_app(Symbol::named("select"), vec![array, index], result_sort)
}

fn select(terms: &mut TermStore, array: TermId, index: TermId) -> TermId {
    select_with_sort(terms, array, index, Sort::Int)
}

fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

/// The extensionality clause `(or (= a b) (not (= (select a k) (select b k))))`
/// as the single-literal `or` shape the solver actually emits.
fn ext_clause(terms: &mut TermStore, a: TermId, b: TermId, k: TermId) -> TermId {
    let eq_ab = eq(terms, a, b);
    let sel_a = select(terms, a, k);
    let sel_b = select(terms, b, k);
    let sel_eq = eq(terms, sel_a, sel_b);
    let not_sel_eq = terms.mk_not(sel_eq);
    terms.mk_or(vec![eq_ab, not_sel_eq])
}

/// A one-level extensionality clause whose two witness reads have already
/// been folded to `folded_a` and `folded_b`.
fn folded_ext_clause(
    terms: &mut TermStore,
    a: TermId,
    b: TermId,
    folded_a: TermId,
    folded_b: TermId,
) -> TermId {
    let eq_ab = eq(terms, a, b);
    let folded_eq = eq(terms, folded_a, folded_b);
    let not_folded_eq = terms.mk_not(folded_eq);
    terms.mk_or(vec![eq_ab, not_folded_eq])
}

fn raw_store(terms: &mut TermStore, base: TermId, index: TermId, value: TermId) -> TermId {
    let sort = terms.sort(base).clone();
    terms.mk_app(Symbol::named("store"), vec![base, index, value], sort)
}

fn symbolic_store_fold(
    terms: &mut TermStore,
    base: TermId,
    store_index: TermId,
    value: TermId,
    witness: TermId,
) -> TermId {
    let condition = eq(terms, witness, store_index);
    let base_read = select(terms, base, witness);
    terms.mk_ite_raw(condition, value, base_read)
}

fn intro_step(witness: TermId, a: TermId, b: TermId) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::ArrayExtDiffIntro,
        clause: Vec::new(),
        premises: Vec::new(),
        args: vec![witness, a, b],
    }
}

fn ext_lemma_step(clause: TermId) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "arrays".to_string(),
        clause: vec![clause],
        farkas: None,
        kind: TheoryLemmaKind::ArrayExtensionality,
        lia: None,
    }
}

/// Two arrays `a`, `b`, a fresh witness `k`, and one problem assertion
/// `(not (= a b))` that mentions NEITHER `k` nor anything else.
struct Fixture {
    terms: TermStore,
    a: TermId,
    b: TermId,
    k: TermId,
    problem: Vec<TermId>,
}

impl Fixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", array_sort());
        let b = terms.mk_var("b", array_sort());
        let k = terms.mk_var("__ext_diff_1_2", Sort::Int);
        let eq_ab = eq(&mut terms, a, b);
        let problem = vec![terms.mk_not(eq_ab)];
        Self {
            terms,
            a,
            b,
            k,
            problem,
        }
    }
}

/// Two nested arrays and the exact two-level chain
/// `a[k0][k1] != b[k0][k1]` used by the deep extensionality emitter.
struct DeepFixture {
    terms: TermStore,
    a: TermId,
    b: TermId,
    k0: TermId,
    k1: TermId,
    a1: TermId,
    b1: TermId,
    clause: TermId,
    problem: Vec<TermId>,
}

impl DeepFixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let inner_sort = array_sort();
        let outer_sort = Sort::array(Sort::Int, inner_sort.clone());
        let a = terms.mk_var("deep_a", outer_sort.clone());
        let b = terms.mk_var("deep_b", outer_sort);
        let k0 = terms.mk_var("__ext_diff_outer", Sort::Int);
        let k1 = terms.mk_var("__ext_diff_inner", Sort::Int);
        let a1 = select_with_sort(&mut terms, a, k0, inner_sort.clone());
        let b1 = select_with_sort(&mut terms, b, k0, inner_sort);
        let a2 = select(&mut terms, a1, k1);
        let b2 = select(&mut terms, b1, k1);
        let eq_ab = eq(&mut terms, a, b);
        let problem = vec![terms.mk_not(eq_ab)];
        let final_eq = eq(&mut terms, a2, b2);
        let not_final_eq = terms.mk_not(final_eq);
        let clause = terms.mk_or(vec![eq_ab, not_final_eq]);
        Self {
            terms,
            a,
            b,
            k0,
            k1,
            a1,
            b1,
            clause,
            problem,
        }
    }
}

/// Run the whole-proof extensionality provenance validation — the exact check
/// the `--self-check` gate applies — over `steps`.
fn check_provenance(
    terms: &TermStore,
    steps: Vec<ProofStep>,
    problem: &[TermId],
) -> Result<(), ProofCheckError> {
    let proof = Proof::from_steps(steps);
    crate::validate_array_extensionality_provenance(&proof, terms, problem)
}

// ============================================================================
// POSITIVE: a correctly introduced, fresh, once-bound witness certifies.
// ============================================================================

#[test]
fn accepts_extensionality_with_a_matching_fresh_introduction() {
    let mut f = Fixture::new();
    let clause = ext_clause(&mut f.terms, f.a, f.b, f.k);
    check_provenance(
        &f.terms,
        vec![intro_step(f.k, f.a, f.b), ext_lemma_step(clause)],
        &f.problem,
    )
    .expect("a fresh, once-bound witness introduced for this exact pair must certify");
}

#[test]
fn accepts_when_the_introduction_lists_the_pair_in_the_other_order() {
    // The witness differentiates an UNORDERED pair; `diff(a,b)` and
    // `diff(b,a)` name the same obligation.
    let mut f = Fixture::new();
    let clause = ext_clause(&mut f.terms, f.a, f.b, f.k);
    check_provenance(
        &f.terms,
        vec![intro_step(f.k, f.b, f.a), ext_lemma_step(clause)],
        &f.problem,
    )
    .expect("pair order must not matter");
}

#[test]
fn accepts_two_witnesses_for_two_different_pairs() {
    let mut f = Fixture::new();
    let c = f.terms.mk_var("c", array_sort());
    let k2 = f.terms.mk_var("__ext_diff_1_3", Sort::Int);
    let clause_ab = ext_clause(&mut f.terms, f.a, f.b, f.k);
    let clause_ac = ext_clause(&mut f.terms, f.a, c, k2);
    check_provenance(
        &f.terms,
        vec![
            intro_step(f.k, f.a, f.b),
            intro_step(k2, f.a, c),
            ext_lemma_step(clause_ab),
            ext_lemma_step(clause_ac),
        ],
        &f.problem,
    )
    .expect("distinct witnesses for distinct pairs are independent and must certify");
}

#[test]
fn recognizer_and_validator_agree_on_the_exact_schema() {
    // The emitter labels a clause `ArrayExtensionality` using exactly this
    // matcher, so recognizer and checker cannot drift.
    let mut f = Fixture::new();
    let clause = ext_clause(&mut f.terms, f.a, f.b, f.k);
    let parts = recognize_array_extensionality(&f.terms, &[clause])
        .expect("the exact schema must be recognized");
    assert_eq!(parts, (f.a, f.b, f.k));
    assert_eq!(
        recognize_array_extensionality_chain(&f.terms, &[clause]),
        Some(vec![parts]),
        "the additive chain API must include the historical one-level case"
    );
}

// ============================================================================
// POSITIVE: proof-shape-preserving folded witness reads.
// ============================================================================

#[test]
fn recognizes_and_certifies_const_array_folded_extensionality() {
    let mut terms = TermStore::new();
    let fill_a = terms.mk_var("const_fill_a", Sort::Int);
    let fill_b = terms.mk_var("const_fill_b", Sort::Int);
    let a = terms.mk_const_array(Sort::Int, fill_a);
    let b = terms.mk_const_array(Sort::Int, fill_b);
    let k = terms.mk_var("__folded_const_diff", Sort::Int);
    let clause = folded_ext_clause(&mut terms, a, b, fill_a, fill_b);

    assert!(recognize_folded_array_extensionality(
        &terms,
        &[clause],
        a,
        b,
        k
    ));
    check_provenance(
        &terms,
        vec![intro_step(k, a, b), ext_lemma_step(clause)],
        &[],
    )
    .expect("const-array fills must certify against the matching fresh pair binding");
}

#[test]
fn recognizes_and_certifies_store_folded_extensionality() {
    let mut terms = TermStore::new();
    let base_a = terms.mk_var("store_base_a", array_sort());
    let base_b = terms.mk_var("store_base_b", array_sort());
    let store_index = terms.mk_var("store_index", Sort::Int);
    let value_a = terms.mk_var("store_value_a", Sort::Int);
    let value_b = terms.mk_var("store_value_b", Sort::Int);
    let k = terms.mk_var("__folded_store_diff", Sort::Int);
    let a = raw_store(&mut terms, base_a, store_index, value_a);
    let b = raw_store(&mut terms, base_b, store_index, value_b);
    let folded_a = symbolic_store_fold(&mut terms, base_a, store_index, value_a, k);
    let folded_b = symbolic_store_fold(&mut terms, base_b, store_index, value_b, k);
    let clause = folded_ext_clause(&mut terms, a, b, folded_a, folded_b);

    assert!(recognize_folded_array_extensionality(
        &terms,
        &[clause],
        a,
        b,
        k
    ));
    check_provenance(
        &terms,
        vec![intro_step(k, a, b), ext_lemma_step(clause)],
        &[],
    )
    .expect("the exact symbolic McCarthy store fold must certify");
}

#[test]
fn recognizes_constant_row1_and_row2_store_folds() {
    let mut terms = TermStore::new();
    let base_a = terms.mk_var("constant_store_base_a", array_sort());
    let base_b = terms.mk_var("constant_store_base_b", array_sort());
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let one = terms.mk_int(num_bigint::BigInt::from(1));
    let value_a = terms.mk_var("constant_store_value_a", Sort::Int);
    let value_b = terms.mk_var("constant_store_value_b", Sort::Int);

    // ROW1: the witness is syntactically the store index.
    let row1_a = raw_store(&mut terms, base_a, zero, value_a);
    let row1_b = raw_store(&mut terms, base_b, zero, value_b);
    let row1_clause = folded_ext_clause(&mut terms, row1_a, row1_b, value_a, value_b);
    assert!(recognize_folded_array_extensionality(
        &terms,
        &[row1_clause],
        row1_a,
        row1_b,
        zero
    ));

    // ROW2: two distinct constant indices read through to the base arrays.
    let row2_a = raw_store(&mut terms, base_a, zero, value_a);
    let row2_b = raw_store(&mut terms, base_b, zero, value_b);
    let row2_read_a = select(&mut terms, base_a, one);
    let row2_read_b = select(&mut terms, base_b, one);
    let row2_clause = folded_ext_clause(&mut terms, row2_a, row2_b, row2_read_a, row2_read_b);
    assert!(recognize_folded_array_extensionality(
        &terms,
        &[row2_clause],
        row2_a,
        row2_b,
        one
    ));
}

#[test]
fn recognizes_and_certifies_array_ite_folded_extensionality() {
    let mut terms = TermStore::new();
    let guard = terms.mk_var("array_ite_guard", Sort::Bool);
    let a_then_fill = terms.mk_var("a_then_fill", Sort::Int);
    let a_else_fill = terms.mk_var("a_else_fill", Sort::Int);
    let b_then_fill = terms.mk_var("b_then_fill", Sort::Int);
    let b_else_fill = terms.mk_var("b_else_fill", Sort::Int);
    let a_then = terms.mk_const_array(Sort::Int, a_then_fill);
    let a_else = terms.mk_const_array(Sort::Int, a_else_fill);
    let b_then = terms.mk_const_array(Sort::Int, b_then_fill);
    let b_else = terms.mk_const_array(Sort::Int, b_else_fill);
    let a = terms.mk_ite_raw(guard, a_then, a_else);
    let b = terms.mk_ite_raw(guard, b_then, b_else);
    let folded_a = terms.mk_ite_raw(guard, a_then_fill, a_else_fill);
    let folded_b = terms.mk_ite_raw(guard, b_then_fill, b_else_fill);
    let k = terms.mk_var("__folded_ite_diff", Sort::Int);
    let clause = folded_ext_clause(&mut terms, a, b, folded_a, folded_b);

    assert!(recognize_folded_array_extensionality(
        &terms,
        &[clause],
        a,
        b,
        k
    ));
    check_provenance(
        &terms,
        vec![intro_step(k, a, b), ext_lemma_step(clause)],
        &[],
    )
    .expect("array-ITE distribution with the exact raw guard must certify");
}

#[test]
fn folded_array_ite_shared_dag_is_memoized() {
    // Each raw ITE retains two references to the SAME child. A recursive tree
    // walk takes 2^40 calls; the checker must visit the shared product DAG once
    // per level and remain comfortably inside its hard work ceiling.
    let mut terms = TermStore::new();
    let fill_a = terms.mk_var("shared_dag_fill_a", Sort::Int);
    let fill_b = terms.mk_var("shared_dag_fill_b", Sort::Int);
    let mut a = terms.mk_const_array(Sort::Int, fill_a);
    let mut b = terms.mk_const_array(Sort::Int, fill_b);
    let mut folded_a = fill_a;
    let mut folded_b = fill_b;
    for level in 0..40 {
        let guard = terms.mk_var(format!("shared_dag_guard_{level}"), Sort::Bool);
        a = terms.mk_ite_raw(guard, a, a);
        b = terms.mk_ite_raw(guard, b, b);
        folded_a = terms.mk_ite_raw(guard, folded_a, folded_a);
        folded_b = terms.mk_ite_raw(guard, folded_b, folded_b);
    }
    let k = terms.mk_var("__shared_dag_diff", Sort::Int);
    let clause = folded_ext_clause(&mut terms, a, b, folded_a, folded_b);

    assert!(recognize_folded_array_extensionality(
        &terms,
        &[clause],
        a,
        b,
        k
    ));
    check_provenance(
        &terms,
        vec![intro_step(k, a, b), ext_lemma_step(clause)],
        &[],
    )
    .expect("shared raw-ITE DAGs must certify without exponential checker work");
}

#[test]
fn folded_registry_matching_has_one_aggregate_work_budget() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("budget_a", array_sort());
    let b = terms.mk_var("budget_b", array_sort());
    let c = terms.mk_var("budget_c", array_sort());
    let d = terms.mk_var("budget_d", array_sort());
    let k1 = terms.mk_var("__budget_diff_1", Sort::Int);
    let k2 = terms.mk_var("__budget_diff_2", Sort::Int);
    let proof = Proof::from_steps(vec![intro_step(k1, a, b), intro_step(k2, c, d)]);
    let registry = ExtDiffRegistry::collect(&proof, &terms, &[])
        .expect("two independent fresh bindings form a valid registry");
    registry.set_folded_work_budget_for_test(1);
    let unrelated_clause = [terms.true_term()];

    let err = array_axiom::validate_folded_registry_match_with_budget(
        &terms,
        ProofId(7),
        &unrelated_clause,
        &registry,
    )
    .expect_err("one shared unit cannot scan two registry bindings");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("shared whole-proof work budget")),
        "expected aggregate folded-registry budget exhaustion, got {err:?}"
    );

    let one_binding_proof = Proof::from_steps(vec![intro_step(k1, a, b)]);
    let one_binding_registry = ExtDiffRegistry::collect(&one_binding_proof, &terms, &[])
        .expect("one fresh binding forms a valid registry");
    one_binding_registry.set_folded_work_budget_for_test(1);
    assert!(!array_axiom::validate_folded_registry_match_with_budget(
        &terms,
        ProofId(8),
        &unrelated_clause,
        &one_binding_registry,
    )
    .expect("the first lemma fits the shared proof budget"));
    array_axiom::validate_folded_registry_match_with_budget(
        &terms,
        ProofId(9),
        &unrelated_clause,
        &one_binding_registry,
    )
    .expect_err("a second lemma must not receive a fresh per-step budget");
}

// ============================================================================
// NEGATIVE: every folded component and the registry binding are authoritative.
// ============================================================================

#[test]
fn rejects_forged_const_array_fill() {
    let mut terms = TermStore::new();
    let fill_a = terms.mk_var("genuine_fill_a", Sort::Int);
    let fill_b = terms.mk_var("genuine_fill_b", Sort::Int);
    let forged_fill = terms.mk_var("forged_fill", Sort::Int);
    let a = terms.mk_const_array(Sort::Int, fill_a);
    let b = terms.mk_const_array(Sort::Int, fill_b);
    let k = terms.mk_var("__forged_fill_diff", Sort::Int);
    let clause = folded_ext_clause(&mut terms, a, b, forged_fill, fill_b);

    assert!(!recognize_folded_array_extensionality(
        &terms,
        &[clause],
        a,
        b,
        k
    ));
    check_provenance(
        &terms,
        vec![intro_step(k, a, b), ext_lemma_step(clause)],
        &[],
    )
    .expect_err("a claimed const-array fold must use the array's exact fill term");
}

#[test]
fn rejects_forged_array_ite_guard() {
    let mut terms = TermStore::new();
    let guard = terms.mk_var("genuine_array_guard", Sort::Bool);
    let forged_guard = terms.mk_var("forged_array_guard", Sort::Bool);
    let a_then_fill = terms.mk_var("guard_a_then", Sort::Int);
    let a_else_fill = terms.mk_var("guard_a_else", Sort::Int);
    let b_then_fill = terms.mk_var("guard_b_then", Sort::Int);
    let b_else_fill = terms.mk_var("guard_b_else", Sort::Int);
    let a_then = terms.mk_const_array(Sort::Int, a_then_fill);
    let a_else = terms.mk_const_array(Sort::Int, a_else_fill);
    let b_then = terms.mk_const_array(Sort::Int, b_then_fill);
    let b_else = terms.mk_const_array(Sort::Int, b_else_fill);
    let a = terms.mk_ite_raw(guard, a_then, a_else);
    let b = terms.mk_ite_raw(guard, b_then, b_else);
    let forged_a = terms.mk_ite_raw(forged_guard, a_then_fill, a_else_fill);
    let folded_b = terms.mk_ite_raw(guard, b_then_fill, b_else_fill);
    let k = terms.mk_var("__forged_guard_diff", Sort::Int);
    let clause = folded_ext_clause(&mut terms, a, b, forged_a, folded_b);

    assert!(!recognize_folded_array_extensionality(
        &terms,
        &[clause],
        a,
        b,
        k
    ));
    check_provenance(
        &terms,
        vec![intro_step(k, a, b), ext_lemma_step(clause)],
        &[],
    )
    .expect_err("array-ITE folding must preserve the root ITE's exact guard");
}

#[test]
fn rejects_folded_clause_introduced_for_another_pair() {
    let mut terms = TermStore::new();
    let fill_a = terms.mk_var("pair_fill_a", Sort::Int);
    let fill_b = terms.mk_var("pair_fill_b", Sort::Int);
    let fill_c = terms.mk_var("pair_fill_c", Sort::Int);
    let a = terms.mk_const_array(Sort::Int, fill_a);
    let b = terms.mk_const_array(Sort::Int, fill_b);
    let c = terms.mk_const_array(Sort::Int, fill_c);
    let k = terms.mk_var("__wrong_pair_folded_diff", Sort::Int);
    let clause = folded_ext_clause(&mut terms, a, b, fill_a, fill_b);

    assert!(recognize_folded_array_extensionality(
        &terms,
        &[clause],
        a,
        b,
        k
    ));
    check_provenance(
        &terms,
        vec![intro_step(k, a, c), ext_lemma_step(clause)],
        &[],
    )
    .expect_err("shape for one pair must not borrow another pair's introduction");
}

#[test]
fn rejects_store_fold_using_an_unintroduced_witness() {
    let mut terms = TermStore::new();
    let base_a = terms.mk_var("witness_base_a", array_sort());
    let base_b = terms.mk_var("witness_base_b", array_sort());
    let store_index = terms.mk_var("witness_store_index", Sort::Int);
    let value_a = terms.mk_var("witness_value_a", Sort::Int);
    let value_b = terms.mk_var("witness_value_b", Sort::Int);
    let clause_witness = terms.mk_var("__clause_folded_diff", Sort::Int);
    let introduced_witness = terms.mk_var("__other_folded_diff", Sort::Int);
    let a = raw_store(&mut terms, base_a, store_index, value_a);
    let b = raw_store(&mut terms, base_b, store_index, value_b);
    let folded_a = symbolic_store_fold(&mut terms, base_a, store_index, value_a, clause_witness);
    let folded_b = symbolic_store_fold(&mut terms, base_b, store_index, value_b, clause_witness);
    let clause = folded_ext_clause(&mut terms, a, b, folded_a, folded_b);

    assert!(recognize_folded_array_extensionality(
        &terms,
        &[clause],
        a,
        b,
        clause_witness
    ));
    assert!(!recognize_folded_array_extensionality(
        &terms,
        &[clause],
        a,
        b,
        introduced_witness
    ));
    check_provenance(
        &terms,
        vec![intro_step(introduced_witness, a, b), ext_lemma_step(clause)],
        &[],
    )
    .expect_err("only the witness carried by the checked pair binding has authority");
}

#[test]
fn rejects_folded_extensionality_sort_forgeries() {
    let mut terms = TermStore::new();
    let fill_a = terms.mk_var("sort_fill_a", Sort::Int);
    let fill_b = terms.mk_var("sort_fill_b", Sort::Int);
    let wrong_sort_fill = terms.mk_var("wrong_sort_fill", Sort::Bool);
    let a = terms.mk_const_array(Sort::Int, fill_a);
    let b = terms.mk_const_array(Sort::Int, fill_b);
    let k = terms.mk_var("__sort_folded_diff", Sort::Int);
    let bool_k = terms.mk_var("__bool_folded_diff", Sort::Bool);
    let wrong_result_clause = folded_ext_clause(&mut terms, a, b, wrong_sort_fill, fill_b);
    let genuine_clause = folded_ext_clause(&mut terms, a, b, fill_a, fill_b);

    assert!(!recognize_folded_array_extensionality(
        &terms,
        &[wrong_result_clause],
        a,
        b,
        k
    ));
    assert!(!recognize_folded_array_extensionality(
        &terms,
        &[genuine_clause],
        a,
        b,
        bool_k
    ));
    check_provenance(
        &terms,
        vec![intro_step(bool_k, a, b), ext_lemma_step(genuine_clause)],
        &[],
    )
    .expect_err("an introduced witness must have the array index sort");
}

#[test]
fn rejects_indexed_homonyms_of_array_builtins() {
    let mut terms = TermStore::new();
    let fill_a = terms.mk_var("indexed_fill_a", Sort::Int);
    let fill_b = terms.mk_var("indexed_fill_b", Sort::Int);
    let const_a = terms.mk_const_array(Sort::Int, fill_a);
    let const_b = terms.mk_const_array(Sort::Int, fill_b);
    let k = terms.mk_var("__indexed_builtin_diff", Sort::Int);
    let genuine_fold_eq = eq(&mut terms, fill_a, fill_b);
    let not_genuine_fold_eq = terms.mk_not(genuine_fold_eq);

    // An indexed symbol with the text `=` is not the builtin equality.
    let indexed_root_eq = terms.mk_app(
        Symbol::indexed("=", vec![0]),
        vec![const_a, const_b],
        Sort::Bool,
    );
    let indexed_eq_clause = terms.mk_or(vec![indexed_root_eq, not_genuine_fold_eq]);
    assert!(!recognize_folded_array_extensionality(
        &terms,
        &[indexed_eq_clause],
        const_a,
        const_b,
        k
    ));

    // Nor may an indexed `or` smuggle its arguments into clause flattening.
    let genuine_root_eq = eq(&mut terms, const_a, const_b);
    let indexed_or_clause = terms.mk_app(
        Symbol::indexed("or", vec![0]),
        vec![genuine_root_eq, not_genuine_fold_eq],
        Sort::Bool,
    );
    assert!(!recognize_folded_array_extensionality(
        &terms,
        &[indexed_or_clause],
        const_a,
        const_b,
        k
    ));

    // Indexed `store` is an uninterpreted application, not a McCarthy store.
    let base_a = terms.mk_var("indexed_store_base_a", array_sort());
    let base_b = terms.mk_var("indexed_store_base_b", array_sort());
    let store_index = terms.mk_var("indexed_store_index", Sort::Int);
    let value_a = terms.mk_var("indexed_store_value_a", Sort::Int);
    let value_b = terms.mk_var("indexed_store_value_b", Sort::Int);
    let indexed_store_a = terms.mk_app(
        Symbol::indexed("store", vec![0]),
        vec![base_a, store_index, value_a],
        array_sort(),
    );
    let indexed_store_b = terms.mk_app(
        Symbol::indexed("store", vec![0]),
        vec![base_b, store_index, value_b],
        array_sort(),
    );
    let claimed_store_fold_a = symbolic_store_fold(&mut terms, base_a, store_index, value_a, k);
    let claimed_store_fold_b = symbolic_store_fold(&mut terms, base_b, store_index, value_b, k);
    let indexed_store_clause = folded_ext_clause(
        &mut terms,
        indexed_store_a,
        indexed_store_b,
        claimed_store_fold_a,
        claimed_store_fold_b,
    );
    assert!(!recognize_folded_array_extensionality(
        &terms,
        &[indexed_store_clause],
        indexed_store_a,
        indexed_store_b,
        k
    ));

    // The raw-select fallback and the historical raw-chain recognizer must
    // likewise require the exact Named builtin.
    let raw_a = terms.mk_var("indexed_select_a", array_sort());
    let raw_b = terms.mk_var("indexed_select_b", array_sort());
    let indexed_select_a = terms.mk_app(
        Symbol::indexed("select", vec![0]),
        vec![raw_a, k],
        Sort::Int,
    );
    let indexed_select_b = terms.mk_app(
        Symbol::indexed("select", vec![0]),
        vec![raw_b, k],
        Sort::Int,
    );
    let indexed_select_clause =
        folded_ext_clause(&mut terms, raw_a, raw_b, indexed_select_a, indexed_select_b);
    assert!(!recognize_folded_array_extensionality(
        &terms,
        &[indexed_select_clause],
        raw_a,
        raw_b,
        k
    ));
    assert_eq!(
        recognize_array_extensionality(&terms, &[indexed_select_clause]),
        None
    );
    check_provenance(
        &terms,
        vec![
            intro_step(k, raw_a, raw_b),
            ext_lemma_step(indexed_select_clause),
        ],
        &[],
    )
    .expect_err("indexed homonyms must never cross the strict proof boundary");
}

#[test]
fn recognizes_and_certifies_a_two_level_extensionality_chain() {
    let f = DeepFixture::new();
    let expected = vec![(f.a, f.b, f.k0), (f.a1, f.b1, f.k1)];
    assert_eq!(
        recognize_array_extensionality_chain(&f.terms, &[f.clause]),
        Some(expected),
        "the chain recognizer must return every binding in outer-to-inner order"
    );
    assert_eq!(
        recognize_array_extensionality(&f.terms, &[f.clause]),
        None,
        "the legacy recognizer must preserve its exact one-level contract"
    );

    check_provenance(
        &f.terms,
        vec![
            intro_step(f.k0, f.a, f.b),
            intro_step(f.k1, f.a1, f.b1),
            ext_lemma_step(f.clause),
        ],
        &f.problem,
    )
    .expect("every link has a fresh matching introduction and must certify");
}

#[test]
fn certifies_a_deep_chain_with_an_array_valued_terminal_pair() {
    // The generator's defensive depth cap may stop before reaching a scalar.
    // Extensionality still makes the selected terminal ARRAYS unequal, so the
    // proof schema must not require a non-array final sort.
    let mut terms = TermStore::new();
    let terminal_sort = array_sort();
    let middle_sort = Sort::array(Sort::Int, terminal_sort.clone());
    let outer_sort = Sort::array(Sort::Int, middle_sort.clone());
    let a = terms.mk_var("capped_a", outer_sort.clone());
    let b = terms.mk_var("capped_b", outer_sort);
    let k0 = terms.mk_var("__ext_diff_capped_outer", Sort::Int);
    let k1 = terms.mk_var("__ext_diff_capped_inner", Sort::Int);
    let a1 = select_with_sort(&mut terms, a, k0, middle_sort.clone());
    let b1 = select_with_sort(&mut terms, b, k0, middle_sort);
    let a2 = select_with_sort(&mut terms, a1, k1, terminal_sort.clone());
    let b2 = select_with_sort(&mut terms, b1, k1, terminal_sort);
    let eq_ab = eq(&mut terms, a, b);
    let final_eq = eq(&mut terms, a2, b2);
    let not_final_eq = terms.mk_not(final_eq);
    let clause = terms.mk_or(vec![eq_ab, not_final_eq]);

    assert_eq!(
        recognize_array_extensionality_chain(&terms, &[clause]),
        Some(vec![(a, b, k0), (a1, b1, k1)])
    );
    check_provenance(
        &terms,
        vec![
            intro_step(k0, a, b),
            intro_step(k1, a1, b1),
            ext_lemma_step(clause),
        ],
        &[],
    )
    .expect("a well-proven array-valued terminal disequality must certify");
}

#[test]
fn deep_recognizer_normalizes_one_global_reversed_orientation() {
    let mut f = DeepFixture::new();
    let a2 = select(&mut f.terms, f.a1, f.k1);
    let b2 = select(&mut f.terms, f.b1, f.k1);
    let eq_ab = eq(&mut f.terms, f.a, f.b);
    let reversed_final_eq = eq(&mut f.terms, b2, a2);
    let not_reversed_final_eq = f.terms.mk_not(reversed_final_eq);
    let clause = f.terms.mk_or(vec![eq_ab, not_reversed_final_eq]);

    assert_eq!(
        recognize_array_extensionality_chain(&f.terms, &[clause]),
        Some(vec![(f.a, f.b, f.k0), (f.a1, f.b1, f.k1)]),
        "swapping the two complete spines must not swap individual levels"
    );
}

#[test]
fn deep_recognizer_stops_at_roots_that_are_themselves_selects() {
    // Peeling to the ultimate non-select bases would overshoot `a` and `b` and
    // reject this valid chain. Exact root TermIds are the stopping condition.
    let mut terms = TermStore::new();
    let leaf_array_sort = array_sort();
    let root_sort = Sort::array(Sort::Int, leaf_array_sort.clone());
    let base_sort = Sort::array(Sort::Int, root_sort.clone());
    let base_a = terms.mk_var("base_a", base_sort.clone());
    let base_b = terms.mk_var("base_b", base_sort);
    let root_index = terms.mk_var("root_index", Sort::Int);
    let a = select_with_sort(&mut terms, base_a, root_index, root_sort.clone());
    let b = select_with_sort(&mut terms, base_b, root_index, root_sort);
    let k0 = terms.mk_var("__ext_diff_selected_outer", Sort::Int);
    let k1 = terms.mk_var("__ext_diff_selected_inner", Sort::Int);
    let a1 = select_with_sort(&mut terms, a, k0, leaf_array_sort.clone());
    let b1 = select_with_sort(&mut terms, b, k0, leaf_array_sort);
    let a2 = select(&mut terms, a1, k1);
    let b2 = select(&mut terms, b1, k1);
    let eq_ab = eq(&mut terms, a, b);
    let final_eq = eq(&mut terms, a2, b2);
    let not_final_eq = terms.mk_not(final_eq);
    let clause = terms.mk_or(vec![eq_ab, not_final_eq]);

    assert_eq!(
        recognize_array_extensionality_chain(&terms, &[clause]),
        Some(vec![(a, b, k0), (a1, b1, k1)])
    );
}

#[test]
fn rejects_a_deep_chain_with_no_inner_introduction() {
    let f = DeepFixture::new();
    let err = check_provenance(
        &f.terms,
        vec![intro_step(f.k0, f.a, f.b), ext_lemma_step(f.clause)],
        &f.problem,
    )
    .expect_err("certifying only the outer link must not certify the deep clause");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("__ext_diff_inner")
                && reason.contains("no `array_ext_diff_intro`")),
        "expected a missing inner-introduction rejection, got {err:?}"
    );
}

#[test]
fn rejects_a_deep_chain_with_an_inner_introduction_for_another_pair() {
    let mut f = DeepFixture::new();
    let c = f.terms.mk_var("deep_c", array_sort());
    let err = check_provenance(
        &f.terms,
        vec![
            intro_step(f.k0, f.a, f.b),
            intro_step(f.k1, f.a1, c),
            ext_lemma_step(f.clause),
        ],
        &f.problem,
    )
    .expect_err("every deep witness must be introduced for its exact intermediate pair");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("__ext_diff_inner")
                && reason.contains("DIFFERENT array pair")),
        "expected a wrong inner-pair rejection, got {err:?}"
    );
}

#[test]
fn rejects_deep_select_spines_with_a_mismatched_index() {
    let mut f = DeepFixture::new();
    let other_index = f.terms.mk_var("other_index", Sort::Int);
    let a2 = select(&mut f.terms, f.a1, f.k1);
    let b2 = select(&mut f.terms, f.b1, other_index);
    let eq_ab = eq(&mut f.terms, f.a, f.b);
    let final_eq = eq(&mut f.terms, a2, b2);
    let not_final_eq = f.terms.mk_not(final_eq);
    let clause = f.terms.mk_or(vec![eq_ab, not_final_eq]);

    assert_eq!(
        recognize_array_extensionality_chain(&f.terms, &[clause]),
        None,
        "both spines must use the same witness at every level"
    );
}

#[test]
fn rejects_deep_select_spines_with_unequal_depths() {
    let mut f = DeepFixture::new();
    let a2 = select(&mut f.terms, f.a1, f.k1);
    let eq_ab = eq(&mut f.terms, f.a, f.b);
    let uneven_final_eq = eq(&mut f.terms, a2, f.b1);
    let not_uneven_final_eq = f.terms.mk_not(uneven_final_eq);
    let clause = f.terms.mk_or(vec![eq_ab, not_uneven_final_eq]);

    assert_eq!(
        recognize_array_extensionality_chain(&f.terms, &[clause]),
        None,
        "the two select spines must reach the roots in lockstep"
    );
}

#[test]
fn rejects_a_compound_witness_at_an_inner_chain_level() {
    let mut f = DeepFixture::new();
    let one = f.terms.mk_int(num_bigint::BigInt::from(1));
    let compound = f
        .terms
        .mk_app(Symbol::named("+"), vec![f.k1, one], Sort::Int);
    let a2 = select(&mut f.terms, f.a1, compound);
    let b2 = select(&mut f.terms, f.b1, compound);
    let eq_ab = eq(&mut f.terms, f.a, f.b);
    let final_eq = eq(&mut f.terms, a2, b2);
    let not_final_eq = f.terms.mk_not(final_eq);
    let clause = f.terms.mk_or(vec![eq_ab, not_final_eq]);

    assert!(
        recognize_array_extensionality_chain(&f.terms, &[clause]).is_some(),
        "shape recognition deliberately leaves provenance to strict validation"
    );
    let err = check_provenance(
        &f.terms,
        vec![intro_step(f.k0, f.a, f.b), ext_lemma_step(clause)],
        &f.problem,
    )
    .expect_err("every chain witness must be an introduced atomic symbol");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("atomic symbol")),
        "expected an atomic-witness rejection, got {err:?}"
    );
}

// ============================================================================
// NEGATIVE 1: no introduction at all.
// ============================================================================

#[test]
fn rejects_extensionality_whose_witness_has_no_introduction() {
    let mut f = Fixture::new();
    let clause = ext_clause(&mut f.terms, f.a, f.b, f.k);
    let err = check_provenance(&f.terms, vec![ext_lemma_step(clause)], &f.problem)
        .expect_err("an unintroduced diff witness must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("no `array_ext_diff_intro`")),
        "expected a missing-introduction rejection, got {err:?}"
    );
}

#[test]
fn rejects_extensionality_when_no_problem_context_is_available() {
    // `check_proof_strict` has no problem assertion set, so it cannot verify
    // freshness and must keep failing closed even with a perfect introduction.
    let mut f = Fixture::new();
    let clause = ext_clause(&mut f.terms, f.a, f.b, f.k);
    let mut derived = Vec::new();
    let err = validate_step(
        &f.terms,
        &mut derived,
        ProofId(0),
        &ext_lemma_step(clause),
        true,
        None,
    )
    .expect_err("with no registry the lemma must fail closed");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("no checked provenance")),
        "expected a fail-closed no-provenance rejection, got {err:?}"
    );
}

// ============================================================================
// NEGATIVE 2: the introduction is for a DIFFERENT array pair.
// ============================================================================

#[test]
fn rejects_extensionality_using_a_witness_introduced_for_another_pair() {
    let mut f = Fixture::new();
    let c = f.terms.mk_var("c", array_sort());
    let clause_ab = ext_clause(&mut f.terms, f.a, f.b, f.k);
    let err = check_provenance(
        &f.terms,
        // `k` was minted to differentiate (a, c) — using it for (a, b) claims
        // one index witnesses two independent array disequalities.
        vec![intro_step(f.k, f.a, c), ext_lemma_step(clause_ab)],
        &f.problem,
    )
    .expect_err("a witness introduced for another pair must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("DIFFERENT array pair")),
        "expected a wrong-pair rejection, got {err:?}"
    );
}

// ============================================================================
// NEGATIVE 3 (soundness crux): the witness is NOT fresh.
// ============================================================================

#[test]
fn rejects_extensionality_whose_witness_also_occurs_in_the_problem() {
    // The user's own problem constrains `__ext_diff_1_2`. The extensionality
    // clause over it is then NOT a conservative extension: it asserts that a
    // problem-constrained index is the difference witness.
    let mut f = Fixture::new();
    let zero = f.terms.mk_int(num_bigint::BigInt::from(0));
    let pinned = eq(&mut f.terms, f.k, zero);
    f.problem.push(pinned);
    let clause = ext_clause(&mut f.terms, f.a, f.b, f.k);
    let err = check_provenance(
        &f.terms,
        vec![intro_step(f.k, f.a, f.b), ext_lemma_step(clause)],
        &f.problem,
    )
    .expect_err("a witness the problem also constrains is not fresh and must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("NOT fresh")),
        "expected a freshness rejection, got {err:?}"
    );
}

#[test]
fn rejects_when_the_witness_occurs_only_deep_inside_a_problem_assertion() {
    // Freshness must be a DEEP scan, not a top-level one.
    let mut f = Fixture::new();
    let sel = select(&mut f.terms, f.a, f.k);
    let zero = f.terms.mk_int(num_bigint::BigInt::from(0));
    let buried = eq(&mut f.terms, sel, zero);
    f.problem.push(f.terms.mk_not(buried));
    let clause = ext_clause(&mut f.terms, f.a, f.b, f.k);
    let err = check_provenance(
        &f.terms,
        vec![intro_step(f.k, f.a, f.b), ext_lemma_step(clause)],
        &f.problem,
    )
    .expect_err("a witness buried in a problem assertion is not fresh");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("NOT fresh")),
        "expected a freshness rejection, got {err:?}"
    );
}

#[test]
fn rejects_when_the_witness_occurs_in_a_proof_assume() {
    // Even if the caller's problem list somehow misses it, an `assume` leaf
    // mentioning the witness means the proof itself constrains it.
    let mut f = Fixture::new();
    let zero = f.terms.mk_int(num_bigint::BigInt::from(0));
    let pinned = eq(&mut f.terms, f.k, zero);
    let clause = ext_clause(&mut f.terms, f.a, f.b, f.k);
    let err = check_provenance(
        &f.terms,
        vec![
            ProofStep::Assume(pinned),
            intro_step(f.k, f.a, f.b),
            ext_lemma_step(clause),
        ],
        &f.problem,
    )
    .expect_err("a witness constrained by an assume is not fresh");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("NOT fresh")),
        "expected a freshness rejection, got {err:?}"
    );
}

#[test]
fn rejects_when_the_witness_occurs_inside_the_array_pair() {
    // `k = diff(store(a, k, v), b)` is a circular Skolem definition.
    let mut f = Fixture::new();
    let v = f.terms.mk_var("v", Sort::Int);
    let sort = array_sort();
    let stored = f
        .terms
        .mk_app(Symbol::named("store"), vec![f.a, f.k, v], sort);
    let clause = ext_clause(&mut f.terms, stored, f.b, f.k);
    let err = check_provenance(
        &f.terms,
        vec![intro_step(f.k, stored, f.b), ext_lemma_step(clause)],
        &f.problem,
    )
    .expect_err("a self-referential witness must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("circular")),
        "expected a circularity rejection, got {err:?}"
    );
}

#[test]
fn accepts_an_acyclic_witness_dependency() {
    // Nested-array proof construction can legitimately choose an inner
    // witness from arrays that mention an already chosen outer witness. The
    // dependency graph must permit that topological order while rejecting
    // cycles.
    let mut terms = TermStore::new();
    let sort = array_sort();
    let j = terms.mk_var("__ext_diff_outer", Sort::Int);
    let k = terms.mk_var("__ext_diff_inner", Sort::Int);
    let c = terms.mk_var("c", sort.clone());
    let d = terms.mk_var("d", sort.clone());
    let a = terms.mk_app(Symbol::named("array_at_left"), vec![j], sort.clone());
    let b = terms.mk_app(Symbol::named("array_at_right"), vec![j], sort);
    let clause_j = ext_clause(&mut terms, c, d, j);
    let clause_k = ext_clause(&mut terms, a, b, k);

    check_provenance(
        &terms,
        vec![
            intro_step(j, c, d),
            intro_step(k, a, b),
            ext_lemma_step(clause_j),
            ext_lemma_step(clause_k),
        ],
        &[],
    )
    .expect("an acyclic dependency admits a topological witness interpretation");
}

#[test]
fn rejects_a_two_witness_dependency_cycle() {
    // A direct `k`-inside-its-own-pair check is insufficient. These two fresh
    // introductions are mutually circular even though neither is directly
    // self-referential:
    //
    //   A = const(false), B(j) = store(A, not j, true)  => k = not j
    //   C = const(false), D(k) = store(C, k, true)      => j = k
    //
    // Thus the two individually plausible extensionality clauses are jointly
    // UNSAT over Bool indices while the empty original problem is SAT. A sound
    // conservative-extension checker must reject the dependency cycle.
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::Bool, Sort::Bool);
    let k = terms.mk_var("__ext_diff_k", Sort::Bool);
    let j = terms.mk_var("__ext_diff_j", Sort::Bool);
    let false_term = terms.false_term();
    let true_term = terms.true_term();
    let a = terms.mk_app(
        Symbol::named("const-array"),
        vec![false_term],
        array_sort.clone(),
    );
    let not_j = terms.mk_not(j);
    let b = terms.mk_app(
        Symbol::named("store"),
        vec![a, not_j, true_term],
        array_sort.clone(),
    );
    let c = a;
    let d = terms.mk_app(Symbol::named("store"), vec![c, k, true_term], array_sort);

    let eq_ab = eq(&mut terms, a, b);
    let sel_a_k = terms.mk_app(Symbol::named("select"), vec![a, k], Sort::Bool);
    let sel_b_k = terms.mk_app(Symbol::named("select"), vec![b, k], Sort::Bool);
    let sel_eq_k = eq(&mut terms, sel_a_k, sel_b_k);
    let not_sel_eq_k = terms.mk_not(sel_eq_k);
    let clause_k = terms.mk_or(vec![eq_ab, not_sel_eq_k]);

    let eq_cd = eq(&mut terms, c, d);
    let sel_c_j = terms.mk_app(Symbol::named("select"), vec![c, j], Sort::Bool);
    let sel_d_j = terms.mk_app(Symbol::named("select"), vec![d, j], Sort::Bool);
    let sel_eq_j = eq(&mut terms, sel_c_j, sel_d_j);
    let not_sel_eq_j = terms.mk_not(sel_eq_j);
    let clause_j = terms.mk_or(vec![eq_cd, not_sel_eq_j]);

    let err = check_provenance(
        &terms,
        vec![
            intro_step(k, a, b),
            intro_step(j, c, d),
            ext_lemma_step(clause_k),
            ext_lemma_step(clause_j),
        ],
        &[],
    )
    .expect_err("mutually circular witnesses must not form a conservative extension");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("dependency cycle")
                && reason.contains("__ext_diff_k")
                && reason.contains("__ext_diff_j")),
        "expected a two-witness dependency-cycle rejection, got {err:?}"
    );
}

// ============================================================================
// NEGATIVE 4: the same symbol bound twice, to different pairs.
// ============================================================================

#[test]
fn rejects_two_introductions_binding_one_witness_to_different_pairs() {
    let mut f = Fixture::new();
    let c = f.terms.mk_var("c", array_sort());
    let clause = ext_clause(&mut f.terms, f.a, f.b, f.k);
    let err = check_provenance(
        &f.terms,
        vec![
            intro_step(f.k, f.a, f.b),
            intro_step(f.k, f.a, c),
            ext_lemma_step(clause),
        ],
        &f.problem,
    )
    .expect_err("one witness must not acquire two array-pair definitions");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("introduced more than once")),
        "expected a bound-twice rejection, got {err:?}"
    );
}

#[test]
fn rejects_a_repeated_introduction_even_for_the_same_pair() {
    // Bound-ONCE is enforced literally: a duplicate binding is a malformed
    // proof, and accepting duplicates would need the checker to reason about
    // when two bindings "agree" — exactly the kind of leniency this schema
    // cannot afford.
    let mut f = Fixture::new();
    let clause = ext_clause(&mut f.terms, f.a, f.b, f.k);
    let err = check_provenance(
        &f.terms,
        vec![
            intro_step(f.k, f.a, f.b),
            intro_step(f.k, f.a, f.b),
            ext_lemma_step(clause),
        ],
        &f.problem,
    )
    .expect_err("a duplicate introduction must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("introduced more than once")),
        "expected a bound-twice rejection, got {err:?}"
    );
}

#[test]
fn rejects_two_extensionality_lemmas_sharing_one_witness_across_pairs() {
    // The dangerous shape the bound-once rule exists to stop: a single index
    // asserted to witness BOTH `a != b` and `a != c`. With one introduction the
    // second lemma cannot match its pair.
    let mut f = Fixture::new();
    let c = f.terms.mk_var("c", array_sort());
    let clause_ab = ext_clause(&mut f.terms, f.a, f.b, f.k);
    let clause_ac = ext_clause(&mut f.terms, f.a, c, f.k);
    let err = check_provenance(
        &f.terms,
        vec![
            intro_step(f.k, f.a, f.b),
            ext_lemma_step(clause_ab),
            ext_lemma_step(clause_ac),
        ],
        &f.problem,
    )
    .expect_err("one witness must not certify two different array pairs");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("DIFFERENT array pair")),
        "expected a wrong-pair rejection, got {err:?}"
    );
}

// ============================================================================
// NEGATIVE 5: flipped polarity.
// ============================================================================

#[test]
fn rejects_the_flipped_polarity_clause() {
    // `¬(= a b) ∨ (= (select a k) (select b k))` is the CONVERSE and is false;
    // it must not ride in on the extensionality kind.
    let mut f = Fixture::new();
    let eq_ab = eq(&mut f.terms, f.a, f.b);
    let not_eq_ab = f.terms.mk_not(eq_ab);
    let sel_a = select(&mut f.terms, f.a, f.k);
    let sel_b = select(&mut f.terms, f.b, f.k);
    let sel_eq = eq(&mut f.terms, sel_a, sel_b);
    let flipped = f.terms.mk_or(vec![not_eq_ab, sel_eq]);

    assert_eq!(
        recognize_array_extensionality(&f.terms, &[flipped]),
        None,
        "the flipped-polarity clause must not be recognized as extensionality"
    );
    let err = check_provenance(
        &f.terms,
        vec![intro_step(f.k, f.a, f.b), ext_lemma_step(flipped)],
        &f.problem,
    )
    .expect_err("the flipped-polarity clause must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("does not match")),
        "expected a schema rejection, got {err:?}"
    );
}

#[test]
fn rejects_a_clause_with_both_literals_positive() {
    let mut f = Fixture::new();
    let eq_ab = eq(&mut f.terms, f.a, f.b);
    let sel_a = select(&mut f.terms, f.a, f.k);
    let sel_b = select(&mut f.terms, f.b, f.k);
    let sel_eq = eq(&mut f.terms, sel_a, sel_b);
    let both_positive = f.terms.mk_or(vec![eq_ab, sel_eq]);
    let err = check_provenance(
        &f.terms,
        vec![intro_step(f.k, f.a, f.b), ext_lemma_step(both_positive)],
        &f.problem,
    )
    .expect_err("both-positive is not the extensionality schema");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("does not match")),
        "expected a schema rejection, got {err:?}"
    );
}

// ============================================================================
// NEGATIVE 6: malformed introductions.
// ============================================================================

#[test]
fn rejects_an_introduction_that_concludes_a_clause() {
    // A definition that also concludes something could be resolved against.
    let mut f = Fixture::new();
    let p = f.terms.mk_var("p", Sort::Bool);
    let bogus = ProofStep::Step {
        rule: AletheRule::ArrayExtDiffIntro,
        clause: vec![p],
        premises: Vec::new(),
        args: vec![f.k, f.a, f.b],
    };
    let err = check_provenance(&f.terms, vec![bogus], &f.problem)
        .expect_err("an introduction with a conclusion must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("must conclude no clause")),
        "expected a clause-free rejection, got {err:?}"
    );
}

#[test]
fn rejects_an_introduction_over_a_compound_witness() {
    let mut f = Fixture::new();
    let i = f.terms.mk_var("i", Sort::Int);
    let compound = f.terms.mk_app(Symbol::named("+"), vec![i, i], Sort::Int);
    let err = check_provenance(&f.terms, vec![intro_step(compound, f.a, f.b)], &f.problem)
        .expect_err("a compound witness is not a Skolem constant");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("atomic symbol")),
        "expected an atomic-witness rejection, got {err:?}"
    );
}

#[test]
fn rejects_an_introduction_whose_witness_is_at_the_wrong_sort() {
    let mut f = Fixture::new();
    let wrong = f.terms.mk_var("__ext_diff_bool", Sort::Bool);
    let err = check_provenance(&f.terms, vec![intro_step(wrong, f.a, f.b)], &f.problem)
        .expect_err("the witness must live at the array's index sort");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("index sort")),
        "expected an index-sort rejection, got {err:?}"
    );
}

#[test]
fn rejects_an_introduction_over_non_array_terms() {
    let mut f = Fixture::new();
    let i = f.terms.mk_var("i", Sort::Int);
    let j = f.terms.mk_var("j", Sort::Int);
    let err = check_provenance(&f.terms, vec![intro_step(f.k, i, j)], &f.problem)
        .expect_err("only array pairs have a difference witness");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("array-sorted")),
        "expected an array-sort rejection, got {err:?}"
    );
}

#[test]
fn rejects_an_introduction_for_an_identical_pair() {
    let f = Fixture::new();
    let err = check_provenance(&f.terms, vec![intro_step(f.k, f.a, f.a)], &f.problem)
        .expect_err("`a` never differs from itself");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("distinct array terms")),
        "expected a distinctness rejection, got {err:?}"
    );
}

#[test]
fn rejects_an_introduction_with_the_wrong_argument_count() {
    let f = Fixture::new();
    for args in [vec![f.k], vec![f.k, f.a], vec![f.k, f.a, f.b, f.b]] {
        let bogus = ProofStep::Step {
            rule: AletheRule::ArrayExtDiffIntro,
            clause: Vec::new(),
            premises: Vec::new(),
            args,
        };
        let err = check_provenance(&f.terms, vec![bogus], &f.problem)
            .expect_err("an introduction must carry exactly (witness, array, array)");
        assert!(
            matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
                if reason.contains("exactly three arguments")),
            "expected an arity rejection, got {err:?}"
        );
    }
}

#[test]
fn rejects_an_introduction_with_premises() {
    let mut f = Fixture::new();
    let p = f.terms.mk_var("p", Sort::Bool);
    let bogus = ProofStep::Step {
        rule: AletheRule::ArrayExtDiffIntro,
        clause: Vec::new(),
        premises: vec![ProofId(0)],
        args: vec![f.k, f.a, f.b],
    };
    let err = check_provenance(&f.terms, vec![ProofStep::Assume(p), bogus], &f.problem)
        .expect_err("a definition derives nothing and must have no premises");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { ref reason, .. }
            if reason.contains("must not have premises")),
        "expected a premise rejection, got {err:?}"
    );
}

// ============================================================================
// STRUCTURAL: the clause-free introduction can never masquerade as a proof.
// ============================================================================

#[test]
fn an_introduction_produces_no_clause_and_derives_no_empty_clause() {
    let mut f = Fixture::new();
    let mut derived: Vec<Option<Vec<TermId>>> = Vec::new();
    validate_step(
        &f.terms,
        &mut derived,
        ProofId(0),
        &intro_step(f.k, f.a, f.b),
        true,
        None,
    )
    .expect("a well-formed introduction validates structurally");
    assert_eq!(
        derived,
        vec![None],
        "the introduction must contribute NO clause to the derivation table"
    );

    // A proof consisting only of introductions derives nothing: the terminal
    // empty-clause requirement must not be satisfiable by an introduction's
    // empty `clause` field.
    let proof = Proof::from_steps(vec![intro_step(f.k, f.a, f.b)]);
    let report = crate::terminal_trust_report(&proof);
    assert_eq!(
        report.empty_clause_steps, 0,
        "a clause-free introduction is not a derivation of (cl)"
    );
    assert!(
        !report.is_trust_free(),
        "a proof with no empty clause is never trust-free"
    );
    let clause = ext_clause(&mut f.terms, f.a, f.b, f.k);
    let err = check_proof(
        &Proof::from_steps(vec![intro_step(f.k, f.a, f.b), ext_lemma_step(clause)]),
        &f.terms,
    )
    .expect_err("a proof that never derives (cl) must be rejected");
    assert!(
        matches!(err, ProofCheckError::FinalClauseNotEmpty { .. }),
        "expected a terminal-clause rejection, got {err:?}"
    );
}
