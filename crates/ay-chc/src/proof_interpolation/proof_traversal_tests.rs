// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for McMillan/Pudlak proof traversal.

use super::*;
use num_bigint::BigInt;

/// Helper: build a FxHashSet from a slice.
fn hash_set<T: std::hash::Hash + Eq + Clone>(items: &[T]) -> FxHashSet<T> {
    items.iter().cloned().collect()
}

/// Build a `ChcExpr` representing `var_name ≤ value`.
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

/// Build a `ChcExpr` representing `value ≤ var_name` (i.e., var_name ≥ value).
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

/// Build a `ChcExpr::Var` with Int sort.
fn int_var(name: &str) -> ChcExpr {
    ChcExpr::Var(ChcVar {
        name: name.to_string(),
        sort: ChcSort::Int,
    })
}

/// Test that an empty proof returns None.
#[test]
fn test_traverse_empty_proof() {
    let proof = Proof::new();
    let terms = TermStore::new();
    let result = traverse_proof(
        &proof,
        &terms,
        &FxHashSet::default(),
        &FxHashSet::default(),
        &FxHashSet::default(),
        &FxHashMap::default(),
        &FxHashSet::default(),
        TraversalAlgorithm::McMillan,
    );
    assert!(result.is_none());
}

/// Test single TheoryLemma proof (current common case).
#[test]
fn test_traverse_single_theory_lemma() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", ay_core::Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let a = terms.mk_le(x, three);
    let five = terms.mk_int(BigInt::from(5));
    let b = terms.mk_le(five, x);
    let not_a = terms.mk_not(a);
    let not_b = terms.mk_not(b);

    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: vec![not_a, not_b],
        farkas: Some(FarkasAnnotation::from_ints(&[1, 1])),
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });

    let a_lits: FxHashSet<SignedLit> = hash_set(&[(a, true)]);
    let a_atoms: FxHashSet<TermId> = hash_set(&[a]);
    let b_atoms: FxHashSet<TermId> = hash_set(&[b]);
    let shared_vars: FxHashSet<String> = hash_set(&["x".to_string()]);

    let mut atom_to_expr = FxHashMap::default();
    atom_to_expr.insert(a, le_expr("x", 3));
    atom_to_expr.insert(b, ge_expr("x", 5));

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
    // A-side has one constraint (x <= 3) with Farkas weight 1.
    // The interpolant must exist and use only the shared variable x.
    let interpolant = result.expect("single A-side Farkas constraint should produce interpolant");
    assert!(
        vars_all_shared(&interpolant, &shared_vars),
        "interpolant {interpolant} must use only shared vars (x)"
    );
}

/// Test that A-local pivot produces OR combination.
#[test]
fn test_resolution_a_local_pivot() {
    let mut terms = TermStore::new();
    let a_local_atom = terms.mk_var("a_local", ay_core::Sort::Bool);
    let a_atoms: FxHashSet<TermId> = hash_set(&[a_local_atom]);
    let result = interpolate_resolution(
        a_local_atom,
        &terms,
        Some(ChcExpr::Bool(false)),
        Some(ChcExpr::Bool(true)),
        &a_atoms,
        &FxHashSet::default(),
        &FxHashMap::default(),
        TraversalAlgorithm::McMillan,
    );
    assert_eq!(result, Some(ChcExpr::Bool(true)));
}

/// Test that B-local pivot produces AND combination.
#[test]
fn test_resolution_b_local_pivot() {
    let mut terms = TermStore::new();
    let b_local_atom = terms.mk_var("b_local", ay_core::Sort::Bool);
    let b_atoms: FxHashSet<TermId> = hash_set(&[b_local_atom]);
    let result = interpolate_resolution(
        b_local_atom,
        &terms,
        Some(ChcExpr::Bool(true)),
        Some(ChcExpr::Bool(false)),
        &FxHashSet::default(),
        &b_atoms,
        &FxHashMap::default(),
        TraversalAlgorithm::McMillan,
    );
    assert_eq!(result, Some(ChcExpr::Bool(false)));
}

/// Helper: shared pivot setup for algorithm comparison tests.
fn shared_pivot_setup() -> (
    TermStore,
    TermId,
    FxHashSet<TermId>,
    FxHashSet<TermId>,
    ChcExpr,
    ChcExpr,
) {
    let mut terms = TermStore::new();
    let shared_atom = terms.mk_var("shared", ay_core::Sort::Bool);
    let a_atoms: FxHashSet<TermId> = hash_set(&[shared_atom]);
    let b_atoms: FxHashSet<TermId> = hash_set(&[shared_atom]);
    let i1 = ChcExpr::Var(ChcVar {
        name: "i1".to_string(),
        sort: ChcSort::Bool,
    });
    let i2 = ChcExpr::Var(ChcVar {
        name: "i2".to_string(),
        sort: ChcSort::Bool,
    });
    (terms, shared_atom, a_atoms, b_atoms, i1, i2)
}

/// McMillan: shared pivot → AND (shared label `b`).
/// McMillanPrime: shared pivot → OR (shared label `a`).
/// (#rank-4 increment 1: the pairing was previously inverted, mixing the
/// two systems and producing non-interpolants.)
#[test]
fn test_resolution_shared_pivot_mcmillan() {
    let (terms, shared_atom, a_atoms, b_atoms, i1, i2) = shared_pivot_setup();
    let mc = interpolate_resolution(
        shared_atom,
        &terms,
        Some(i1.clone()),
        Some(i2.clone()),
        &a_atoms,
        &b_atoms,
        &FxHashMap::default(),
        TraversalAlgorithm::McMillan,
    );
    assert!(matches!(mc, Some(ChcExpr::Op(ChcOp::And, _))));

    let mcp = interpolate_resolution(
        shared_atom,
        &terms,
        Some(i1),
        Some(i2),
        &a_atoms,
        &b_atoms,
        &FxHashMap::default(),
        TraversalAlgorithm::McMillanPrime,
    );
    assert!(matches!(mcp, Some(ChcExpr::Op(ChcOp::Or, _))));
}

/// Pudlak: shared pivot → (I₁ ∨ p) ∧ (I₂ ∨ ¬p). Without an atom_to_expr
/// entry the ab-labeled pivot cannot be expressed, so the traversal fails
/// honestly (no sound constant combination exists).
#[test]
fn test_resolution_shared_pivot_pudlak() {
    let (terms, shared_atom, a_atoms, b_atoms, i1, i2) = shared_pivot_setup();
    let fallback = interpolate_resolution(
        shared_atom,
        &terms,
        Some(i1.clone()),
        Some(i2.clone()),
        &a_atoms,
        &b_atoms,
        &FxHashMap::default(),
        TraversalAlgorithm::Pudlak,
    );
    assert!(fallback.is_none());

    let mut atom_map = FxHashMap::default();
    atom_map.insert(
        shared_atom,
        ChcExpr::Var(ChcVar {
            name: "shared".to_string(),
            sort: ChcSort::Bool,
        }),
    );
    let pudlak = interpolate_resolution(
        shared_atom,
        &terms,
        Some(i1),
        Some(i2),
        &a_atoms,
        &b_atoms,
        &atom_map,
        TraversalAlgorithm::Pudlak,
    );
    assert!(matches!(pudlak, Some(ChcExpr::Op(ChcOp::And, _))));
}

/// Test that None sub-interpolants propagate correctly.
#[test]
fn test_resolution_none_propagation() {
    let mut terms = TermStore::new();
    let atom = terms.mk_var("a", ay_core::Sort::Bool);
    let a_atoms: FxHashSet<TermId> = hash_set(&[atom]);
    let result = interpolate_resolution(
        atom,
        &terms,
        None,
        Some(ChcExpr::Bool(true)),
        &a_atoms,
        &FxHashSet::default(),
        &FxHashMap::default(),
        TraversalAlgorithm::McMillan,
    );
    assert!(result.is_none());
}

/// Test B-assume returns true.
#[test]
fn test_assume_b_side() {
    let mut terms = TermStore::new();
    let b_atom = terms.mk_var("b", ay_core::Sort::Bool);
    let result = interpolate_assume(
        b_atom,
        &terms,
        &FxHashSet::default(),
        &FxHashMap::default(),
        &FxHashSet::default(),
        DependencyMark::B,
        TraversalAlgorithm::McMillan,
    );
    assert_eq!(result, Some(ChcExpr::Bool(true)));
}

/// A-assume with an A-only atom is a-labeled in every system: I = false,
/// even when the atom's expression uses only shared variables.
#[test]
fn test_assume_a_side_a_only_atom_is_false() {
    let mut terms = TermStore::new();
    let a_atom = terms.mk_var("a", ay_core::Sort::Bool);
    let expr = int_var("x");
    let mut atom_to_expr = FxHashMap::default();
    atom_to_expr.insert(a_atom, expr);
    let shared_vars: FxHashSet<String> = hash_set(&["x".to_string()]);
    for algorithm in [
        TraversalAlgorithm::McMillan,
        TraversalAlgorithm::McMillanPrime,
        TraversalAlgorithm::Pudlak,
    ] {
        let result = interpolate_assume(
            a_atom,
            &terms,
            &FxHashSet::default(),
            &atom_to_expr,
            &shared_vars,
            DependencyMark::A,
            algorithm,
        );
        assert_eq!(result, Some(ChcExpr::Bool(false)), "{algorithm:?}");
    }
}

/// Shared (AB) A-asserted assume: McMillan (shared → b) contributes the
/// literal; Pudlak/McMillan' (shared → ab/a) contribute false.
#[test]
fn test_assume_shared_atom_a_asserted() {
    let mut terms = TermStore::new();
    let s_atom = terms.mk_var("s", ay_core::Sort::Bool);
    let expr = int_var("x");
    let mut atom_to_expr = FxHashMap::default();
    atom_to_expr.insert(s_atom, expr.clone());
    let shared_vars: FxHashSet<String> = hash_set(&["x".to_string()]);
    let a_lits: FxHashSet<SignedLit> = hash_set(&[(s_atom, true)]);

    let mc = interpolate_assume(
        s_atom,
        &terms,
        &a_lits,
        &atom_to_expr,
        &shared_vars,
        DependencyMark::AB,
        TraversalAlgorithm::McMillan,
    );
    assert_eq!(mc, Some(expr));

    for algorithm in [
        TraversalAlgorithm::Pudlak,
        TraversalAlgorithm::McMillanPrime,
    ] {
        let result = interpolate_assume(
            s_atom,
            &terms,
            &a_lits,
            &atom_to_expr,
            &shared_vars,
            DependencyMark::AB,
            algorithm,
        );
        assert_eq!(result, Some(ChcExpr::Bool(false)), "{algorithm:?}");
    }
}

/// Shared (AB) B-asserted assume: McMillan' (shared → a) contributes the
/// negated literal; McMillan/Pudlak contribute true.
#[test]
fn test_assume_shared_atom_b_asserted() {
    let mut terms = TermStore::new();
    let s_atom = terms.mk_var("s", ay_core::Sort::Bool);
    let expr = int_var("x");
    let mut atom_to_expr = FxHashMap::default();
    atom_to_expr.insert(s_atom, expr.clone());
    let shared_vars: FxHashSet<String> = hash_set(&["x".to_string()]);
    // a_lits does NOT contain (s, true): the literal is asserted by B.
    let a_lits: FxHashSet<SignedLit> = FxHashSet::default();

    let mcp = interpolate_assume(
        s_atom,
        &terms,
        &a_lits,
        &atom_to_expr,
        &shared_vars,
        DependencyMark::AB,
        TraversalAlgorithm::McMillanPrime,
    );
    assert_eq!(mcp, Some(ChcExpr::not(expr)));

    for algorithm in [TraversalAlgorithm::Pudlak, TraversalAlgorithm::McMillan] {
        let result = interpolate_assume(
            s_atom,
            &terms,
            &a_lits,
            &atom_to_expr,
            &shared_vars,
            DependencyMark::AB,
            algorithm,
        );
        assert_eq!(result, Some(ChcExpr::Bool(true)), "{algorithm:?}");
    }
}

// ---- simplify_partial tests ----

#[test]
fn test_simplify_partial_or_absorbing() {
    let x = ChcExpr::Var(ChcVar {
        name: "x".to_string(),
        sort: ChcSort::Bool,
    });
    let expr = ChcExpr::Op(ChcOp::Or, vec![Arc::new(ChcExpr::Bool(true)), Arc::new(x)]);
    assert_eq!(simplify_partial(expr), ChcExpr::Bool(true));
}

#[test]
fn test_simplify_partial_and_absorbing() {
    let x = ChcExpr::Var(ChcVar {
        name: "x".to_string(),
        sort: ChcSort::Bool,
    });
    let expr = ChcExpr::Op(
        ChcOp::And,
        vec![Arc::new(ChcExpr::Bool(false)), Arc::new(x)],
    );
    assert_eq!(simplify_partial(expr), ChcExpr::Bool(false));
}

#[test]
fn test_simplify_partial_or_identity() {
    let x = ChcExpr::Var(ChcVar {
        name: "x".to_string(),
        sort: ChcSort::Bool,
    });
    let expr = ChcExpr::Op(
        ChcOp::Or,
        vec![Arc::new(ChcExpr::Bool(false)), Arc::new(x.clone())],
    );
    assert_eq!(simplify_partial(expr), x);
}

#[test]
fn test_simplify_partial_and_identity() {
    let x = ChcExpr::Var(ChcVar {
        name: "x".to_string(),
        sort: ChcSort::Bool,
    });
    let expr = ChcExpr::Op(
        ChcOp::And,
        vec![Arc::new(ChcExpr::Bool(true)), Arc::new(x.clone())],
    );
    assert_eq!(simplify_partial(expr), x);
}

#[test]
fn test_simplify_partial_not_constants() {
    assert_eq!(
        simplify_partial(ChcExpr::not(ChcExpr::Bool(true))),
        ChcExpr::Bool(false)
    );
    assert_eq!(
        simplify_partial(ChcExpr::not(ChcExpr::Bool(false))),
        ChcExpr::Bool(true)
    );
}

#[test]
fn test_simplify_partial_passthrough() {
    let x = ChcExpr::Var(ChcVar {
        name: "x".to_string(),
        sort: ChcSort::Bool,
    });
    assert_eq!(simplify_partial(x.clone()), x);
}
