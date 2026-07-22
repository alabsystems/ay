// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Multi-step synthetic proof tree tests for McMillan/Pudlak traversal.
//!
//! These tests exercise `traverse_proof` end-to-end with multi-step proofs
//! and verify Craig variable locality (condition 3) on all outputs.
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

fn int_var(name: &str) -> ChcExpr {
    ChcExpr::Var(ChcVar {
        name: name.to_string(),
        sort: ChcSort::Int,
    })
}

fn assert_variable_locality(interpolant: &ChcExpr, shared_vars: &FxHashSet<String>, label: &str) {
    assert!(
        vars_all_shared(interpolant, shared_vars),
        "{label}: interpolant {interpolant} mentions non-shared vars (shared={shared_vars:?})"
    );
}

/// A+B assumptions resolved via B-local pivot → I₀ ∧ I₁.
/// Step 0: Assume(a) — shared atom asserted by A → I₀ = (x ≤ 3) (McMillan)
/// Step 1: Assume(b) — B-side → I₁ = true
/// Step 2: Resolution(pivot=b) — B-local → (x ≤ 3) ∧ true = x ≤ 3
#[test]
fn test_traverse_a_b_resolution_b_local_pivot() {
    let mut terms = TermStore::new();
    let a_atom = terms.mk_var("a", ay_core::Sort::Bool);
    let b_atom = terms.mk_var("b", ay_core::Sort::Bool);
    let a_expr = le_expr("x", 3);

    // `a` is a shared atom (occurs in both partitions) asserted by A; under
    // McMillan it is b-labeled and contributes the literal at the A-leaf.
    let a_lits: FxHashSet<SignedLit> = hash_set(&[(a_atom, true)]);
    let a_atoms: FxHashSet<TermId> = hash_set(&[a_atom]);
    let b_atoms: FxHashSet<TermId> = hash_set(&[a_atom, b_atom]);
    let shared_vars: FxHashSet<String> = hash_set(&["x".to_string()]);

    let mut atom_to_expr = FxHashMap::default();
    atom_to_expr.insert(a_atom, a_expr.clone());

    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(a_atom));
    proof.add_step(ProofStep::Assume(b_atom));
    proof.add_resolution(vec![], b_atom, ProofId(0), ProofId(1));

    let result = traverse_proof(
        &proof,
        &terms,
        &a_lits,
        &a_atoms,
        &b_atoms,
        &atom_to_expr,
        &shared_vars,
        TraversalAlgorithm::McMillan,
    );
    let interp = result.expect("should produce interpolant");
    assert_variable_locality(&interp, &shared_vars, "a_b_b_local");
    assert_eq!(interp, a_expr);
}

/// Pure B-resolution chain → true.
/// Step 0: Assume(b1) — B → true, Step 1: Assume(b2) — B → true
/// Step 2: Resolution(pivot=b1) — B-local → true ∧ true = true
#[test]
fn test_traverse_pure_b_resolution_chain() {
    let mut terms = TermStore::new();
    let b1 = terms.mk_var("b1", ay_core::Sort::Bool);
    let b2 = terms.mk_var("b2", ay_core::Sort::Bool);

    let b_atoms: FxHashSet<TermId> = hash_set(&[b1, b2]);
    let shared_vars: FxHashSet<String> = hash_set(&["x".to_string()]);

    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(b1));
    proof.add_step(ProofStep::Assume(b2));
    proof.add_resolution(vec![], b1, ProofId(0), ProofId(1));

    let result = traverse_proof(
        &proof,
        &terms,
        &FxHashSet::default(),
        &FxHashSet::default(),
        &b_atoms,
        &FxHashMap::default(),
        &shared_vars,
        TraversalAlgorithm::McMillan,
    );
    let interp = result.expect("should produce interpolant");
    assert_variable_locality(&interp, &shared_vars, "pure_b");
    assert_eq!(interp, ChcExpr::Bool(true));
}

/// Nested 4-step proof: A-local then B-local pivots.
/// Step 0: Assume(a1) — shared atom asserted by A → (x ≤ 3)
/// Step 1: Assume(a2) — A-only atom (a-labeled) → false
/// Step 2: Resolution(pivot=a2) — A-local → (x ≤ 3) ∨ false = x ≤ 3
/// Step 3: Assume(b1) — B → true
/// Step 4: Resolution(pivot=b1) — B-local → (x ≤ 3) ∧ true = x ≤ 3
#[test]
fn test_traverse_nested_resolution_four_steps() {
    let mut terms = TermStore::new();
    let a1 = terms.mk_var("a1", ay_core::Sort::Bool);
    let a2 = terms.mk_var("a2", ay_core::Sort::Bool);
    let b1 = terms.mk_var("b1", ay_core::Sort::Bool);
    let a1_expr = le_expr("x", 3);

    let a_lits: FxHashSet<SignedLit> = hash_set(&[(a1, true)]);
    let a_atoms: FxHashSet<TermId> = hash_set(&[a1, a2]);
    let b_atoms: FxHashSet<TermId> = hash_set(&[a1, b1]);
    let shared_vars: FxHashSet<String> = hash_set(&["x".to_string()]);

    let mut atom_to_expr = FxHashMap::default();
    atom_to_expr.insert(a1, a1_expr.clone());
    atom_to_expr.insert(a2, ge_expr("x", 1));

    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(a1));
    proof.add_step(ProofStep::Assume(a2));
    proof.add_resolution(vec![], a2, ProofId(0), ProofId(1));
    proof.add_step(ProofStep::Assume(b1));
    proof.add_resolution(vec![], b1, ProofId(2), ProofId(3));

    let result = traverse_proof(
        &proof,
        &terms,
        &a_lits,
        &a_atoms,
        &b_atoms,
        &atom_to_expr,
        &shared_vars,
        TraversalAlgorithm::McMillan,
    );
    let interp = result.expect("should produce interpolant for nested proof");
    assert_variable_locality(&interp, &shared_vars, "nested_four");
    assert_eq!(interp, a1_expr);
}

/// Shared pivot on a real refutation: A = {s}, B = {¬s} with s ↦ (x ≤ 5).
/// Step 0: Assume(s)  — shared atom asserted by A
/// Step 1: Assume(¬s) — shared atom asserted by B
/// Step 2: Resolution(pivot=s) — shared pivot
///
/// All three (now internally consistent) systems derive I = (x ≤ 5):
/// - McMillan:  I₀ = (x ≤ 5), I₁ = true,  shared → AND → x ≤ 5
/// - McMillan': I₀ = false,   I₁ = ¬¬(x ≤ 5), shared → OR → x ≤ 5
/// - Pudlak:    I₀ = false,   I₁ = true,  shared → (false ∨ p) ∧ (true ∨ ¬p) = x ≤ 5
#[test]
fn test_traverse_shared_pivot_all_algorithms() {
    let mut terms = TermStore::new();
    let s_atom = terms.mk_var("s", ay_core::Sort::Bool);
    let not_s = terms.mk_not(s_atom);
    let s_expr = le_expr("x", 5);

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

    for algorithm in [
        TraversalAlgorithm::McMillan,
        TraversalAlgorithm::McMillanPrime,
        TraversalAlgorithm::Pudlak,
    ] {
        let interp = traverse_proof(
            &proof,
            &terms,
            &a_lits,
            &a_atoms,
            &b_atoms,
            &atom_to_expr,
            &shared_vars,
            algorithm,
        )
        .unwrap_or_else(|| panic!("{algorithm:?} should produce an interpolant"));
        assert_variable_locality(&interp, &shared_vars, &format!("{algorithm:?}"));
        // All systems reduce to (x ≤ 5) after constant folding (McMillan'
        // produces ¬¬(x ≤ 5), which is semantically equal; accept both).
        let double_neg = ChcExpr::not(ChcExpr::not(s_expr.clone()));
        assert!(
            interp == s_expr || interp == double_neg,
            "{algorithm:?}: expected (x ≤ 5) (mod double negation), got {interp}"
        );
    }
}

/// 5-step mixed proof: A-local pivot then B-local pivot.
/// A-local OR absorbs to true; B-local AND preserves true.
#[test]
fn test_traverse_five_step_mixed_pivots() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", ay_core::Sort::Bool);
    let b1 = terms.mk_var("b1", ay_core::Sort::Bool);
    let b2 = terms.mk_var("b2", ay_core::Sort::Bool);

    let a_atoms: FxHashSet<TermId> = hash_set(&[a]);
    let b_atoms: FxHashSet<TermId> = hash_set(&[b1, b2]);
    let shared_vars: FxHashSet<String> = hash_set(&["x".to_string()]);

    let mut atom_to_expr = FxHashMap::default();
    atom_to_expr.insert(a, le_expr("x", 3));

    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(a));
    proof.add_step(ProofStep::Assume(b1));
    proof.add_resolution(vec![], a, ProofId(0), ProofId(1)); // A-local → OR → true
    proof.add_step(ProofStep::Assume(b2));
    proof.add_resolution(vec![], b2, ProofId(2), ProofId(3)); // B-local → AND

    let result = traverse_proof(
        &proof,
        &terms,
        &FxHashSet::default(),
        &a_atoms,
        &b_atoms,
        &atom_to_expr,
        &shared_vars,
        TraversalAlgorithm::McMillan,
    );
    let interp = result.expect("should produce interpolant");
    assert_variable_locality(&interp, &shared_vars, "five_step");
    assert_eq!(interp, ChcExpr::Bool(true));
}

/// Variable locality with multi-variable expression (x + y ≤ 10).
#[test]
fn test_traverse_variable_locality_nontrivial() {
    let mut terms = TermStore::new();
    let a1 = terms.mk_var("a1", ay_core::Sort::Bool);
    let b1 = terms.mk_var("b1", ay_core::Sort::Bool);

    let a1_expr = ChcExpr::Op(
        ChcOp::Le,
        vec![
            Arc::new(ChcExpr::Op(
                ChcOp::Add,
                vec![Arc::new(int_var("x")), Arc::new(int_var("y"))],
            )),
            Arc::new(ChcExpr::Int(10)),
        ],
    );

    // a1 is a shared atom asserted by A (b-labeled under McMillan).
    let a_lits: FxHashSet<SignedLit> = hash_set(&[(a1, true)]);
    let a_atoms: FxHashSet<TermId> = hash_set(&[a1]);
    let b_atoms: FxHashSet<TermId> = hash_set(&[a1, b1]);
    let shared_vars: FxHashSet<String> = hash_set(&["x".to_string(), "y".to_string()]);

    let mut atom_to_expr = FxHashMap::default();
    atom_to_expr.insert(a1, a1_expr.clone());

    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(a1));
    proof.add_step(ProofStep::Assume(b1));
    proof.add_resolution(vec![], b1, ProofId(0), ProofId(1));

    let result = traverse_proof(
        &proof,
        &terms,
        &a_lits,
        &a_atoms,
        &b_atoms,
        &atom_to_expr,
        &shared_vars,
        TraversalAlgorithm::McMillan,
    );
    let interp = result.expect("should produce interpolant");
    assert_variable_locality(&interp, &shared_vars, "locality_nontrivial");
    assert_eq!(interp, a1_expr);

    let vars: Vec<String> = interp.vars().into_iter().map(|v| v.name).collect();
    assert!(vars.contains(&"x".to_string()));
    assert!(vars.contains(&"y".to_string()));
    assert!(vars.iter().all(|v| shared_vars.contains(v)));
}

/// A-local variables are excluded from the interpolant.
/// Step 0: Assume(a1) — A-only atom (A-local var w) → false
/// Step 1: Assume(a2) — shared atom asserted by A → (x ≤ 7)
/// Step 2: Resolution(pivot=a1) — A-local → false ∨ (x ≤ 7) = x ≤ 7
/// Step 3: Assume(b1) — B → true
/// Step 4: Resolution(pivot=b1) — B-local → (x ≤ 7) ∧ true = x ≤ 7
#[test]
fn test_traverse_a_local_vars_excluded() {
    let mut terms = TermStore::new();
    let a1 = terms.mk_var("a1", ay_core::Sort::Bool);
    let a2 = terms.mk_var("a2", ay_core::Sort::Bool);
    let b1 = terms.mk_var("b1", ay_core::Sort::Bool);
    let a2_expr = le_expr("x", 7);

    let a_lits: FxHashSet<SignedLit> = hash_set(&[(a1, true), (a2, true)]);
    let a_atoms: FxHashSet<TermId> = hash_set(&[a1, a2]);
    let b_atoms: FxHashSet<TermId> = hash_set(&[a2, b1]);
    let shared_vars: FxHashSet<String> = hash_set(&["x".to_string()]);

    let mut atom_to_expr = FxHashMap::default();
    atom_to_expr.insert(a1, int_var("w")); // A-local var
    atom_to_expr.insert(a2, a2_expr.clone());

    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(a1));
    proof.add_step(ProofStep::Assume(a2));
    proof.add_resolution(vec![], a1, ProofId(0), ProofId(1));
    proof.add_step(ProofStep::Assume(b1));
    proof.add_resolution(vec![], b1, ProofId(2), ProofId(3));

    let result = traverse_proof(
        &proof,
        &terms,
        &a_lits,
        &a_atoms,
        &b_atoms,
        &atom_to_expr,
        &shared_vars,
        TraversalAlgorithm::McMillan,
    );
    let interp = result.expect("should produce interpolant");
    assert_variable_locality(&interp, &shared_vars, "a_local_excluded");

    let var_names: Vec<String> = interp.vars().into_iter().map(|v| v.name).collect();
    assert!(
        !var_names.contains(&"w".to_string()),
        "A-local var 'w' must not appear"
    );
    assert_eq!(interp, a2_expr);
}
