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

fn select(terms: &mut TermStore, array: TermId, index: TermId) -> TermId {
    terms.mk_app(Symbol::named("select"), vec![array, index], Sort::Int)
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
            if reason.contains("does not match the exact")),
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
            if reason.contains("does not match the exact")),
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
