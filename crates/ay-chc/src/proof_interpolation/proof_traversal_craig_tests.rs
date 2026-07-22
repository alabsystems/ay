// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Full Craig property verification tests for McMillan/Pudlak proof traversal.
//!
//! These tests construct synthetic proof trees and verify all 3 Craig
//! interpolation conditions via SMT:
//! 1. A ⊨ I (A implies I)
//! 2. I ∧ B is UNSAT (I blocks B)
//! 3. I mentions only shared variables
//!
//! Part of #4175 acceptance criteria.

use super::*;

fn hash_set<T: std::hash::Hash + Eq + Clone>(items: &[T]) -> FxHashSet<T> {
    items.iter().cloned().collect()
}

fn le_expr(var_name: &str, value: i64) -> ChcExpr {
    ChcExpr::Op(
        ChcOp::Le,
        vec![
            Arc::new(ChcExpr::Var(ChcVar {
                name: var_name.to_string(),
                sort: ChcSort::Int,
            })),
            Arc::new(ChcExpr::int(value)),
        ],
    )
}

fn ge_expr(var_name: &str, value: i64) -> ChcExpr {
    ChcExpr::Op(
        ChcOp::Le,
        vec![
            Arc::new(ChcExpr::int(value)),
            Arc::new(ChcExpr::Var(ChcVar {
                name: var_name.to_string(),
                sort: ChcSort::Int,
            })),
        ],
    )
}

fn assert_variable_locality(interpolant: &ChcExpr, shared_vars: &FxHashSet<String>, label: &str) {
    assert!(
        vars_all_shared(interpolant, shared_vars),
        "{label}: interpolant {interpolant} mentions non-shared vars (shared={shared_vars:?})"
    );
}

/// Full Craig property verification on a B-local resolution proof.
///
/// A: x ≤ 3 (via shared atom a asserted by A), B: x ≥ 5
/// Proof: Assume(a), Assume(b), Resolution(pivot=b, B-local)
/// Verify: A ⊨ I, I ∧ B UNSAT, I uses only shared vars.
#[test]
fn test_traverse_craig_verification_b_local_resolution() {
    let mut terms = TermStore::new();
    let a_atom = terms.mk_var("a", ay_core::Sort::Bool);
    let b_atom = terms.mk_var("b", ay_core::Sort::Bool);

    let a_expr = le_expr("x", 3);
    let b_expr = ge_expr("x", 5);

    let a_lits: FxHashSet<SignedLit> = hash_set(&[(a_atom, true)]);
    let a_atoms: FxHashSet<TermId> = hash_set(&[a_atom]);
    let b_atoms: FxHashSet<TermId> = hash_set(&[a_atom, b_atom]);
    let shared_vars: FxHashSet<String> = hash_set(&["x".to_string()]);

    let mut atom_to_expr = FxHashMap::default();
    atom_to_expr.insert(a_atom, a_expr.clone());
    atom_to_expr.insert(b_atom, b_expr.clone());

    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(a_atom));
    proof.add_step(ProofStep::Assume(b_atom));
    proof.add_resolution(vec![], b_atom, ProofId(0), ProofId(1));

    let interp = traverse_proof(
        &proof,
        &terms,
        &a_lits,
        &a_atoms,
        &b_atoms,
        &atom_to_expr,
        &shared_vars,
        TraversalAlgorithm::McMillan,
    )
    .expect("should produce interpolant");

    assert_variable_locality(&interp, &shared_vars, "craig_b_local");

    let mut smt = SmtContext::new();
    assert!(
        verify_craig_properties(
            &interp,
            &a_expr,
            &b_expr,
            &shared_vars,
            &mut smt,
            "craig_b_local"
        ),
        "Craig properties must hold for B-local resolution interpolant: {interp}"
    );
}

/// KEYSTONE labeling-consistency test (#rank-4 increment 1).
///
/// Hand-computed shared-pivot refutation where OR-vs-AND give different
/// answers and only the consistent McMillan labeling (shared pivot → AND)
/// yields a verified interpolant:
///
///   A = {s},  B = {¬s},  s ↦ (x ≤ 5),  shared = {x}
///   Proof: Assume(s) [A], Assume(¬s) [B], Resolution(pivot=s, shared)
///
///   McMillan leaves: I₀ = (x ≤ 5), I₁ = true.
///   Consistent (AND): I = (x ≤ 5) ∧ true = (x ≤ 5)
///     → A ⊨ I and I ∧ B UNSAT: verified.
///   Inconsistent (the old OR rule): I = (x ≤ 5) ∨ true = true
///     → true ∧ B is SAT: NOT an interpolant.
#[test]
fn test_craig_shared_pivot_mcmillan_and_vs_or() {
    let mut terms = TermStore::new();
    let s_atom = terms.mk_var("s", ay_core::Sort::Bool);
    let not_s = terms.mk_not(s_atom);
    let s_expr = le_expr("x", 5);

    let a_expr = s_expr.clone();
    let b_expr = ChcExpr::not(s_expr.clone());

    let a_lits: FxHashSet<SignedLit> = hash_set(&[(s_atom, true)]);
    let a_atoms: FxHashSet<TermId> = hash_set(&[s_atom]);
    let b_atoms: FxHashSet<TermId> = hash_set(&[s_atom]);
    let shared_vars: FxHashSet<String> = hash_set(&["x".to_string()]);

    let mut atom_to_expr = FxHashMap::default();
    atom_to_expr.insert(s_atom, s_expr.clone());

    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(s_atom));
    proof.add_step(ProofStep::Assume(not_s));
    proof.add_resolution(vec![], s_atom, ProofId(0), ProofId(1));

    let interp = traverse_proof(
        &proof,
        &terms,
        &a_lits,
        &a_atoms,
        &b_atoms,
        &atom_to_expr,
        &shared_vars,
        TraversalAlgorithm::McMillan,
    )
    .expect("McMillan should produce interpolant");

    let mut smt = SmtContext::new();
    assert!(
        verify_craig_properties(
            &interp,
            &a_expr,
            &b_expr,
            &shared_vars,
            &mut smt,
            "mcmillan_consistent_and",
        ),
        "consistent McMillan (shared pivot → AND) must verify, got {interp}"
    );

    // Hand-computed result of the OLD inconsistent labeling (McMillan leaves
    // I₀ = (x ≤ 5), I₁ = true, but shared pivot → OR): I = true. This is NOT
    // a Craig interpolant for (A, B): I ∧ B is satisfiable.
    let inconsistent = ChcExpr::or(s_expr.clone(), ChcExpr::Bool(true)).simplify_constants();
    assert!(
        !verify_craig_properties(
            &inconsistent,
            &a_expr,
            &b_expr,
            &shared_vars,
            &mut smt,
            "mcmillan_inconsistent_or",
        ),
        "the old OR-labeled McMillan result ({inconsistent}) must NOT verify"
    );
}

/// Dual keystone test: McMillan' (shared pivot → OR) on the same refutation.
///
///   McMillan' leaves: I₀ = false, I₁ = ¬(¬s) ↦ ¬¬(x ≤ 5).
///   Consistent (OR): I = false ∨ ¬¬(x ≤ 5) ≡ (x ≤ 5): verified.
///   Inconsistent (the old AND rule): I = false ∧ ... = false
///     → A ⊨ false fails: NOT an interpolant.
#[test]
fn test_craig_shared_pivot_mcmillan_prime_or_vs_and() {
    let mut terms = TermStore::new();
    let s_atom = terms.mk_var("s", ay_core::Sort::Bool);
    let not_s = terms.mk_not(s_atom);
    let s_expr = le_expr("x", 5);

    let a_expr = s_expr.clone();
    let b_expr = ChcExpr::not(s_expr.clone());

    let a_lits: FxHashSet<SignedLit> = hash_set(&[(s_atom, true)]);
    let a_atoms: FxHashSet<TermId> = hash_set(&[s_atom]);
    let b_atoms: FxHashSet<TermId> = hash_set(&[s_atom]);
    let shared_vars: FxHashSet<String> = hash_set(&["x".to_string()]);

    let mut atom_to_expr = FxHashMap::default();
    atom_to_expr.insert(s_atom, s_expr.clone());

    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(s_atom));
    proof.add_step(ProofStep::Assume(not_s));
    proof.add_resolution(vec![], s_atom, ProofId(0), ProofId(1));

    let mut smt = SmtContext::new();

    let interp = traverse_proof(
        &proof,
        &terms,
        &a_lits,
        &a_atoms,
        &b_atoms,
        &atom_to_expr,
        &shared_vars,
        TraversalAlgorithm::McMillanPrime,
    )
    .expect("McMillan' should produce interpolant");
    assert!(
        verify_craig_properties(
            &interp,
            &a_expr,
            &b_expr,
            &shared_vars,
            &mut smt,
            "mcmillan_prime_consistent_or",
        ),
        "consistent McMillan' (shared pivot → OR) must verify, got {interp}"
    );

    // Hand-computed result of the OLD inconsistent labeling (McMillan' B-leaf
    // conjunction with shared pivot → AND): I = false ∧ ¬¬(x ≤ 5) = false.
    // A ⊨ false fails.
    let inconsistent = ChcExpr::Bool(false);
    assert!(
        !verify_craig_properties(
            &inconsistent,
            &a_expr,
            &b_expr,
            &shared_vars,
            &mut smt,
            "mcmillan_prime_inconsistent_and",
        ),
        "the old AND-labeled McMillan' result (false) must NOT verify"
    );

    // Pudlak on the same proof: (false ∨ s) ∧ (true ∨ ¬s) ≡ (x ≤ 5): verified.
    let pudlak = traverse_proof(
        &proof,
        &terms,
        &a_lits,
        &a_atoms,
        &b_atoms,
        &atom_to_expr,
        &shared_vars,
        TraversalAlgorithm::Pudlak,
    )
    .expect("Pudlak should produce interpolant");
    assert!(
        verify_craig_properties(
            &pudlak,
            &a_expr,
            &b_expr,
            &shared_vars,
            &mut smt,
            "pudlak_shared_pivot",
        ),
        "Pudlak shared-pivot interpolant must verify, got {pudlak}"
    );
}

/// Full Craig verification on TheoryLemma + Resolution.
///
/// Step 0: TheoryLemma({¬(x ≤ 3), ¬(x ≥ 5)}, Farkas[1,1])
/// Step 1: Assume(x ≥ 10) — B assertion
/// Step 2: Resolution(pivot=b2, B-local)
#[test]
fn test_traverse_craig_verification_theory_lemma_plus_resolution() {
    use num_bigint::BigInt;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", ay_core::Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let a_le = terms.mk_le(x, three);
    let b_ge = terms.mk_le(five, x);
    let not_a_le = terms.mk_not(a_le);
    let not_b_ge = terms.mk_not(b_ge);
    let b2_atom = terms.mk_le(ten, x);

    let a_lits: FxHashSet<SignedLit> = hash_set(&[(a_le, true)]);
    let a_atoms: FxHashSet<TermId> = hash_set(&[a_le]);
    let b_atoms: FxHashSet<TermId> = hash_set(&[b_ge, b2_atom]);
    let shared_vars: FxHashSet<String> = hash_set(&["x".to_string()]);

    let mut atom_to_expr = FxHashMap::default();
    atom_to_expr.insert(a_le, le_expr("x", 3));
    atom_to_expr.insert(b_ge, ge_expr("x", 5));
    atom_to_expr.insert(b2_atom, ge_expr("x", 10));

    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: vec![not_a_le, not_b_ge],
        farkas: Some(FarkasAnnotation::from_ints(&[1, 1])),
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });
    proof.add_step(ProofStep::Assume(b2_atom));
    proof.add_resolution(vec![], b2_atom, ProofId(0), ProofId(1));

    let interp = traverse_proof(
        &proof,
        &terms,
        &a_lits,
        &a_atoms,
        &b_atoms,
        &atom_to_expr,
        &shared_vars,
        TraversalAlgorithm::McMillan,
    )
    .expect("should produce interpolant from theory lemma + resolution");

    assert_variable_locality(&interp, &shared_vars, "theory_lemma_resolution");

    let a_conj = le_expr("x", 3);
    let b_conj = ChcExpr::and(ge_expr("x", 5), ge_expr("x", 10));
    let mut smt = SmtContext::new();
    assert!(
        verify_craig_properties(
            &interp,
            &a_conj,
            &b_conj,
            &shared_vars,
            &mut smt,
            "theory_lemma_resolution"
        ),
        "Craig properties must hold for theory lemma + resolution: {interp}"
    );
}

/// Craig verification on a 3-deep resolution chain with mixed pivot types.
///
/// A = (x ≤ 3) ∧ (y ≤ 2), B = (x ≥ 10), shared = {x}, y is A-local.
#[test]
fn test_traverse_craig_verification_3_deep_mixed_pivots() {
    let mut terms = TermStore::new();
    let a1 = terms.mk_var("a1", ay_core::Sort::Bool);
    let a2 = terms.mk_var("a2", ay_core::Sort::Bool);
    let b1 = terms.mk_var("b1", ay_core::Sort::Bool);

    let a1_expr = le_expr("x", 3);
    let a2_expr = le_expr("y", 2);
    let b1_expr = ge_expr("x", 10);

    // a1 is a shared atom asserted by A; a2 is A-only (y is A-local).
    let a_lits: FxHashSet<SignedLit> = hash_set(&[(a1, true), (a2, true)]);
    let a_atoms: FxHashSet<TermId> = hash_set(&[a1, a2]);
    let b_atoms: FxHashSet<TermId> = hash_set(&[a1, b1]);
    let shared_vars: FxHashSet<String> = hash_set(&["x".to_string()]);

    let mut atom_to_expr = FxHashMap::default();
    atom_to_expr.insert(a1, a1_expr.clone());
    atom_to_expr.insert(a2, a2_expr.clone());
    atom_to_expr.insert(b1, b1_expr.clone());

    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(a1));
    proof.add_step(ProofStep::Assume(a2));
    proof.add_resolution(vec![], a2, ProofId(0), ProofId(1)); // A-local
    proof.add_step(ProofStep::Assume(b1));
    proof.add_resolution(vec![], b1, ProofId(2), ProofId(3)); // B-local

    let interp = traverse_proof(
        &proof,
        &terms,
        &a_lits,
        &a_atoms,
        &b_atoms,
        &atom_to_expr,
        &shared_vars,
        TraversalAlgorithm::McMillan,
    )
    .expect("should produce interpolant for 3-deep mixed proof");

    assert_variable_locality(&interp, &shared_vars, "craig_3_deep");

    let var_names: Vec<String> = interp.vars().into_iter().map(|v| v.name).collect();
    assert!(
        !var_names.contains(&"y".to_string()),
        "A-local var 'y' must not appear in interpolant"
    );

    let mut smt = SmtContext::new();
    assert!(
        verify_craig_properties(
            &interp,
            &ChcExpr::and(a1_expr, a2_expr),
            &b1_expr,
            &shared_vars,
            &mut smt,
            "craig_3_deep",
        ),
        "Craig properties must hold for 3-deep mixed proof: {interp}"
    );
}
