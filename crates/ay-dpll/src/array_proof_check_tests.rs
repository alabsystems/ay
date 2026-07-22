// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the semantic array proof checker.
//!
//! Coverage:
//! - Positive: canonical RoW1 / RoW2 / congruence array tautology clauses
//!   (built as real `Proof` / `TermStore` objects) all validate via solver
//!   discharge.
//! - Negative: hand-corrupted clauses (wrong index, wrong value, dropped
//!   `i != j` guard) are rejected with a precise reason.
//! - Unsupported: a clause containing an out-of-fragment node returns
//!   `Unchecked` (fail-closed), never `Valid`.
//! - Regression: a guard-less ROW2 unit is rejected, while the live prover
//!   repairs its contextual eager lemma into the guarded theorem before proof
//!   publication.

use super::*;
use ay_core::{ArraySort, Proof, ProofStep, Symbol, TermStore, TheoryLemmaKind};

/// Helper: build a `(Array Int Int)` sort.
fn int_array_sort() -> Sort {
    Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)))
}

/// Helper: wrap a clause as an `ArraySelectStore { index_eq }` theory lemma and
/// run it through the array checker, returning the single step's verdict.
fn check_select_store_clause(
    terms: &TermStore,
    clause: Vec<TermId>,
    index_eq: bool,
) -> ArrayStepVerdict {
    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "arrays".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::ArraySelectStore { index_eq },
        lia: None,
    });
    let report = check_array_proof(&proof, terms);
    assert_eq!(report.steps.len(), 1, "expected exactly one array step");
    report.steps[0].verdict.clone()
}

fn check_extensionality_clause(terms: &TermStore, clause: Vec<TermId>) -> ArrayStepVerdict {
    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "arrays".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::ArrayExtensionality,
        lia: None,
    });
    let report = check_array_proof(&proof, terms);
    assert_eq!(report.steps.len(), 1);
    report.steps[0].verdict.clone()
}

// ---------------------------------------------------------------------------
// Positive cases: genuine array-theory tautologies validate.
// ---------------------------------------------------------------------------

/// RoW1: `(= (select (store a i v) i) v)` is an array tautology -> Valid.
#[test]
fn row1_same_index_validates() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", int_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let store = terms.mk_store(a, i, v);
    let select = terms.mk_select(store, i);
    let eq = terms.mk_eq(select, v);

    let verdict = check_select_store_clause(&terms, vec![eq], true);
    assert_eq!(verdict, ArrayStepVerdict::Valid, "RoW1 must validate");
}

/// RoW2 (clausal CNF form): `(or (= i j) (= (select (store a i v) j) (select a j)))`
/// is an array tautology (it is the CNF of `i != j => ...`) -> Valid.
#[test]
fn row2_clausal_with_guard_validates() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", int_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let store = terms.mk_store(a, i, v);
    let select_store = terms.mk_select(store, j);
    let select_base = terms.mk_select(a, j);
    let idx_eq = terms.mk_eq(i, j);
    let row2_eq = terms.mk_eq(select_store, select_base);
    let clause = terms.mk_or(vec![idx_eq, row2_eq]);

    let verdict = check_select_store_clause(&terms, vec![clause], false);
    assert_eq!(
        verdict,
        ArrayStepVerdict::Valid,
        "guarded clausal RoW2 must validate"
    );
}

/// RoW2 (implication form): `(=> (not (= i j)) (= (select (store a i v) j) (select a j)))`
/// is an array tautology -> Valid. Exercises the `=>`/`not` translation path.
#[test]
fn row2_implication_form_validates() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", int_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let store = terms.mk_store(a, i, v);
    let select_store = terms.mk_select(store, j);
    let select_base = terms.mk_select(a, j);
    let idx_eq = terms.mk_eq(i, j);
    let idx_neq = terms.mk_not(idx_eq);
    let row2_eq = terms.mk_eq(select_store, select_base);
    let implies = terms.mk_app(Symbol::named("=>"), [idx_neq, row2_eq], Sort::Bool);

    let verdict = check_select_store_clause(&terms, vec![implies], false);
    assert_eq!(verdict, ArrayStepVerdict::Valid);
}

/// A congruence clause mislabelled as `read_over_write_neg`:
/// `(or (= (select a k) (select b k)) (not (= a b)))` is genuinely entailed
/// (EUF congruence) so the semantic checker validates it regardless of the
/// wrong label.
#[test]
fn mislabelled_congruence_clause_validates() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", int_array_sort());
    let b = terms.mk_var("b", int_array_sort());
    let k = terms.mk_var("k", Sort::Int);
    let sel_a = terms.mk_select(a, k);
    let sel_b = terms.mk_select(b, k);
    let sel_eq = terms.mk_eq(sel_a, sel_b);
    let ab = terms.mk_eq(a, b);
    let not_ab = terms.mk_not(ab);
    let clause = terms.mk_or(vec![sel_eq, not_ab]);

    let verdict = check_select_store_clause(&terms, vec![clause], false);
    assert_eq!(
        verdict,
        ArrayStepVerdict::Valid,
        "congruence clause is entailed and must validate despite the array label"
    );
}

/// RoW1 with a multi-write store: `(= (select (store (store a i v1) i v2) i) v2)`
/// is an array tautology (latest write wins) -> Valid.
#[test]
fn row1_nested_store_validates() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", int_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let v1 = terms.mk_var("v1", Sort::Int);
    let v2 = terms.mk_var("v2", Sort::Int);
    let s1 = terms.mk_store(a, i, v1);
    let s2 = terms.mk_store(s1, i, v2);
    let sel = terms.mk_select(s2, i);
    let eq = terms.mk_eq(sel, v2);

    let verdict = check_select_store_clause(&terms, vec![eq], true);
    assert_eq!(verdict, ArrayStepVerdict::Valid);
}

// ---------------------------------------------------------------------------
// Negative cases: corrupted clauses are rejected with a precise reason.
// ---------------------------------------------------------------------------

/// RoW1 corrupted value: `(= (select (store a i v) i) w)` with `w != v` is NOT
/// entailed -> Invalid.
#[test]
fn row1_wrong_value_rejected() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", int_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int); // a different value variable
    let store = terms.mk_store(a, i, v);
    let select = terms.mk_select(store, i);
    let eq = terms.mk_eq(select, w);

    let verdict = check_select_store_clause(&terms, vec![eq], true);
    assert!(
        verdict.is_invalid(),
        "RoW1 with wrong value must be rejected, got {verdict:?}"
    );
    if let ArrayStepVerdict::Invalid { reason } = &verdict {
        assert!(
            reason.contains("not an array-theory tautology"),
            "reason: {reason}"
        );
    }
}

/// RoW1 corrupted index: `(= (select (store a i v) k) v)` with read index `k`
/// different from write index `i` is NOT entailed -> Invalid.
#[test]
fn row1_wrong_index_rejected() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", int_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let k = terms.mk_var("k", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let store = terms.mk_store(a, i, v);
    let select = terms.mk_select(store, k);
    let eq = terms.mk_eq(select, v);

    let verdict = check_select_store_clause(&terms, vec![eq], true);
    assert!(
        verdict.is_invalid(),
        "RoW1 with wrong read index must be rejected, got {verdict:?}"
    );
}

/// RoW2 with the `i != j` guard dropped, over an *Int* index: the bare unit
/// clause `(= (select (store a i v) j) (select a j))` is NOT entailed. The
/// soundness-critical property is that the checker never reports `Valid`. (Over
/// infinite Int indices `ay` returns `Unknown` for `¬clause` rather than
/// eagerly producing the `i = j` falsifying model, so this lands in `Unchecked`
/// — still fail-closed, never `Valid`.)
#[test]
fn row2_dropped_guard_int_is_never_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", int_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let store = terms.mk_store(a, i, v);
    let select_store = terms.mk_select(store, j);
    let select_base = terms.mk_select(a, j);
    let row2_eq = terms.mk_eq(select_store, select_base);

    let verdict = check_select_store_clause(&terms, vec![row2_eq], false);
    assert!(
        !verdict.is_valid(),
        "guard-less RoW2 unit clause must never be Valid, got {verdict:?}"
    );
}

/// Same guard-less RoW2 over a *finite* BitVec index, where `QF_ABV` is
/// decidable: `¬clause` is decided `SAT` (the `i = j` falsification), so the
/// checker reports `Invalid` with a precise reason. This is the crisp negative
/// for the dropped-guard corruption.
#[test]
fn row2_dropped_guard_bitvec_rejected() {
    let mut terms = TermStore::new();
    let bv = Sort::bitvec(4);
    let arr = Sort::array(bv.clone(), bv.clone());
    let a = terms.mk_var("a", arr);
    let i = terms.mk_var("i", bv.clone());
    let j = terms.mk_var("j", bv.clone());
    let v = terms.mk_var("v", bv);
    let store = terms.mk_store(a, i, v);
    let select_store = terms.mk_select(store, j);
    let select_base = terms.mk_select(a, j);
    let row2_eq = terms.mk_eq(select_store, select_base);

    let verdict = check_select_store_clause(&terms, vec![row2_eq], false);
    assert!(
        verdict.is_invalid(),
        "guard-less RoW2 over a finite (BitVec) index must be Invalid, got {verdict:?}"
    );
    if let ArrayStepVerdict::Invalid { reason } = &verdict {
        assert!(
            reason.contains("not an array-theory tautology"),
            "reason: {reason}"
        );
    }
}

/// RoW2 with the guard polarity flipped (`(or (not (= i j)) ...)` instead of
/// `(or (= i j) ...)`): not entailed -> Invalid.
#[test]
fn row2_flipped_guard_rejected() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", int_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let store = terms.mk_store(a, i, v);
    let select_store = terms.mk_select(store, j);
    let select_base = terms.mk_select(a, j);
    let idx_eq = terms.mk_eq(i, j);
    let idx_neq = terms.mk_not(idx_eq);
    let row2_eq = terms.mk_eq(select_store, select_base);
    let clause = terms.mk_or(vec![idx_neq, row2_eq]);

    let verdict = check_select_store_clause(&terms, vec![clause], false);
    assert!(
        verdict.is_invalid(),
        "flipped-guard RoW2 must be rejected, got {verdict:?}"
    );
}

/// Bare array extensionality without the diff/Skolem witness:
/// `(or (= a b) (not (= (select a k) (select b k))))` for an arbitrary `k` is
/// NOT entailed (it needs `k = diff(a,b)`), so it is rejected -> Invalid.
#[test]
fn extensionality_arbitrary_witness_rejected() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", int_array_sort());
    let b = terms.mk_var("b", int_array_sort());
    let k = terms.mk_var("k", Sort::Int);
    let array_eq = terms.mk_eq(a, b);
    let sel_a = terms.mk_select(a, k);
    let sel_b = terms.mk_select(b, k);
    let sel_eq = terms.mk_eq(sel_a, sel_b);
    let not_sel_eq = terms.mk_not(sel_eq);
    let clause = terms.mk_or(vec![array_eq, not_sel_eq]);

    let verdict = check_extensionality_clause(&terms, vec![clause]);
    assert!(
        verdict.is_invalid(),
        "extensionality with arbitrary witness must be rejected (no diff witness), got {verdict:?}"
    );
}

// ---------------------------------------------------------------------------
// Unsupported / fail-closed cases.
// ---------------------------------------------------------------------------

/// A clause whose literal uses an arithmetic operator (`<`) is outside the
/// modelled fragment -> Unchecked (never Valid).
#[test]
fn arithmetic_literal_is_unchecked_not_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", int_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let store = terms.mk_store(a, i, v);
    let select = terms.mk_select(store, i);
    // (< (select (store a i v) i) v) — Boolean but uses `<` over Int.
    let lt = terms.mk_app(Symbol::named("<"), [select, v], Sort::Bool);

    let verdict = check_select_store_clause(&terms, vec![lt], true);
    assert!(
        verdict.is_unchecked(),
        "arithmetic operator must be Unchecked, got {verdict:?}"
    );
    assert!(!verdict.is_valid(), "must never be Valid");
}

/// An empty clause is ill-formed for an array lemma -> Unchecked.
#[test]
fn empty_clause_is_unchecked() {
    let terms = TermStore::new();
    let verdict = check_select_store_clause(&terms, vec![], true);
    assert!(
        verdict.is_unchecked(),
        "empty clause must be Unchecked, got {verdict:?}"
    );
}

/// A non-Bool clause literal (an Int term used as a literal) -> Unchecked.
#[test]
fn non_bool_literal_is_unchecked() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    // `i` itself (Int-sorted) is not a propositional literal.
    let verdict = check_select_store_clause(&terms, vec![i], true);
    assert!(
        verdict.is_unchecked(),
        "non-Bool literal must be Unchecked, got {verdict:?}"
    );
}

// ---------------------------------------------------------------------------
// Skipping / aggregation.
// ---------------------------------------------------------------------------

/// Non-array steps are not reported (the checker makes no claim about them).
#[test]
fn non_array_steps_are_skipped() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(p));
    proof.add_step(ProofStep::TheoryLemma {
        theory: "EUF".to_string(),
        clause: vec![p],
        farkas: None,
        kind: TheoryLemmaKind::EufTransitive,
        lia: None,
    });
    let report = check_array_proof(&proof, &terms);
    assert!(report.steps.is_empty(), "no array steps -> empty report");
    assert!(report.all_array_steps_valid(), "vacuously sound for arrays");
}

/// Aggregate counts across a mixed proof: one valid, one invalid, one unchecked.
#[test]
fn aggregate_counts() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", int_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let store = terms.mk_store(a, i, v);

    // Valid RoW1.
    let sel_i = terms.mk_select(store, i);
    let valid = terms.mk_eq(sel_i, v);

    // Invalid RoW1 (wrong value).
    let invalid = terms.mk_eq(sel_i, w);

    // Unchecked (arithmetic).
    let unchecked = terms.mk_app(Symbol::named("<"), [sel_i, v], Sort::Bool);

    let mut proof = Proof::new();
    for clause in [valid, invalid, unchecked] {
        proof.add_step(ProofStep::TheoryLemma {
            theory: "arrays".to_string(),
            clause: vec![clause],
            farkas: None,
            kind: TheoryLemmaKind::ArraySelectStore { index_eq: true },
            lia: None,
        });
    }

    let report = check_array_proof(&proof, &terms);
    assert_eq!(report.steps.len(), 3);
    assert_eq!(report.valid_count(), 1, "{report:?}");
    assert_eq!(report.invalid_count(), 1, "{report:?}");
    assert_eq!(report.unchecked_count(), 1, "{report:?}");
    assert!(!report.all_array_steps_valid());
    assert!(report.first_invalid().is_some());
}

// ---------------------------------------------------------------------------
// End-to-end against the live prover (documents the soundness finding).
// ---------------------------------------------------------------------------

/// The live prover, asked to refute `i != j` and
/// `select(store(a,i,v),j) != select(a,j)`, emits an `ArraySelectStore`
/// theory lemma whose conclusion is the *guard-less* unit clause
/// `(= (select (store a i v) j) (select a j))`. That clause is not an array
/// tautology on its own, so the semantic checker rejects it. This test pins
/// the finding: the prover's emitted RoW2 step is not independently sound.
#[test]
fn live_prover_row2_clause_shape_is_rejected() {
    // Rebuild the exact clause the prover emits (verified empirically during
    // scouting) in a fresh store and confirm the checker rejects it.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", int_array_sort());
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let store = terms.mk_store(a, i, v);
    let select_store = terms.mk_select(store, j);
    let select_base = terms.mk_select(a, j);
    let prover_clause = terms.mk_eq(select_store, select_base);

    let verdict = check_select_store_clause(&terms, vec![prover_clause], false);
    assert!(
        !verdict.is_valid(),
        "the prover's guard-less RoW2 conclusion must NOT be validated by the \
         semantic checker (soundness finding); it is either Invalid or \
         Unchecked, got {verdict:?}"
    );
}

/// Fully end-to-end: drive the real `ay` solver on a small UNSAT ROW2 array
/// query, take the *actual* `Proof` and its backing `TermStore`, and run the
/// semantic checker over them.  The eager lane initially learns the contextual
/// unit equality, but proof finalization must publish the self-contained
/// `(i = j) OR ROW2` theorem and use both input assumptions to close the proof.
#[test]
fn end_to_end_live_prover_row2_lemma_is_guarded_and_validated() {
    use crate::api::{Logic, Solver};

    let mut solver = Solver::new(Logic::QfAx);
    solver.set_produce_proofs(true);
    let arr = int_array_sort();
    let a = solver.declare_const("a", arr);
    let i = solver.declare_const("i", Sort::Int);
    let j = solver.declare_const("j", Sort::Int);
    let v = solver.declare_const("v", Sort::Int);
    // i != j  AND  select(store(a,i,v), j) != select(a, j)  -> UNSAT (RoW2).
    let ij = solver.eq(i, j);
    let nij = solver.not(ij);
    solver.assert_term(nij);
    let st = solver.store(a, i, v);
    let sel1 = solver.select(st, j);
    let sel2 = solver.select(a, j);
    let e = solver.eq(sel1, sel2);
    let ne = solver.not(e);
    solver.assert_term(ne);
    assert!(solver.check_sat().is_unsat(), "RoW2 query must be UNSAT");

    let proof = solver
        .last_proof()
        .expect("proof must be present after UNSAT");
    let store = solver.proof_term_store();
    let report = check_array_proof(proof, store);

    // The prover publishes exactly one guarded array theory lemma.
    assert_eq!(
        report.steps.len(),
        1,
        "expected one array lemma step in the live proof, got {report:?}"
    );
    assert!(
        report.all_array_steps_valid(),
        "the live proof's repaired guarded ROW2 theorem must validate: {report:?}"
    );
    assert_eq!(report.valid_count(), 1);
    assert_eq!(report.invalid_count(), 0);
    assert!(proof
        .steps
        .iter()
        .all(|step| !matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust())));
}

// ---------------------------------------------------------------------------
// Regression: the int↔bv bridge builtins must not ICE the array checker.
//
// A mixed Int/BV clause of the shape num-integer/memchr's bounded-arithmetic
// VCs produce — `(= (bv2nat (bvand (_ int2bv 8) i) ((_ int2bv 8) j))) k)` —
// used to CRASH the array checker: `translate_app` strips an indexed symbol's
// indices via `Symbol::name()` and routed `int2bv`/`bv2nat` into
// `translate_uninterpreted`, which called `Solver::declare_fun("int2bv", ..)`.
// Since a reserved builtin name is rejected by ay-frontend's reserved-symbol
// gate, the panicking `declare_fun` wrapper turned that into an ICE.
//
// The QF_AX array checker cannot faithfully model the BV<->LIA bridge, so the
// only sound answer is to decline: `Unchecked`, never a panic and never Valid.
// (The overall proof is instead certified by the whole-problem Executor
// re-solve; see `discharge_trust_clause`'s fallback.)
// ---------------------------------------------------------------------------

/// `int2bv` (an indexed builtin) inside an array-lemma clause must be declined
/// gracefully as `Unchecked` — never an ICE, never `Valid`.
#[test]
fn int2bv_bridge_op_is_unchecked_not_ice() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    // (_ int2bv 8) i  and  (_ int2bv 8) j  — symbolic Int args, so these stay as
    // real `Symbol::indexed("int2bv", [8])` applications (no constant folding).
    let bi = terms.mk_int2bv(8, i);
    let bj = terms.mk_int2bv(8, j);
    let band = terms.mk_bvand(vec![bi, bj]);
    let nat = terms.mk_bv2nat(band); // bv2nat(...) -> Int
    let k = terms.mk_int(7.into());
    let eq = terms.mk_eq(nat, k); // Bool literal

    // Must not panic (the pre-fix ICE) and must fail closed.
    let verdict = check_select_store_clause(&terms, vec![eq], true);
    assert!(
        verdict.is_unchecked(),
        "int2bv/bv2nat bridge clause must be Unchecked (fail-closed), got {verdict:?}"
    );
    assert!(
        !verdict.is_valid(),
        "a reserved bridge op must never be Valid"
    );
}

/// `bv2nat` (a reserved *named* builtin) alone must also be declined gracefully
/// rather than declared as an uninterpreted function (which would ICE).
#[test]
fn bv2nat_named_bridge_op_is_unchecked_not_ice() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let nat = terms.mk_bv2nat(x); // bv2nat(x) -> Int (Symbol::named("bv2nat"))
    let k = terms.mk_int(3.into());
    let eq = terms.mk_eq(nat, k);

    let verdict = check_select_store_clause(&terms, vec![eq], true);
    assert!(
        verdict.is_unchecked(),
        "bv2nat named bridge op must be Unchecked (fail-closed), got {verdict:?}"
    );
    assert!(
        !verdict.is_valid(),
        "a reserved bridge op must never be Valid"
    );
}
