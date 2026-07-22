// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Negative tests for #8820: ensure BV/Array/FP/String theory lemma kinds
//! reject forged clauses in strict mode.
//!
//! Prior to #8820 every BV/Array/FP/String lemma was accepted if the clause
//! was non-empty. An attacker-controlled proof could therefore forge any
//! Boolean clause (including single `false` literals that collapse to the
//! empty clause via resolution) and drive the checker to UNSAT.
//!
//! This module asserts that each theory lemma kind now rejects clauses that
//! the strict checker cannot independently prove.

use crate::checker::*;
use ay_core::{
    BvGateType, CuttingPlaneAnnotation, FarkasAnnotation, FpOp, LiaAnnotation, ProofId, ProofStep,
    Sort, TermId, TermStore, TheoryLemmaKind,
};
use num_bigint::BigInt;

/// Validate a `TheoryLemma` step in strict mode, returning the error (if any).
fn validate_theory_lemma_strict(
    terms: &TermStore,
    clause: Vec<TermId>,
    kind: TheoryLemmaKind,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::TheoryLemma {
        theory: "test".to_string(),
        clause,
        farkas: None,
        kind,
        lia: None,
    };
    let mut derived = Vec::new();
    validate_step(terms, &mut derived, ProofId(0), &step, true, None)
}

// ============================================================================
// BV bit-blast forgeries (#8820)
// ============================================================================

#[test]
fn test_bv_bitblast_rejects_clause_with_no_bv_content() {
    // Forged clause: `(cl p (not q))` where p, q are pure Boolean variables
    // with no BV sub-terms. The previous checker accepted this; the schema
    // check now rejects it.
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_q = terms.mk_not(q);

    let err = validate_theory_lemma_strict(&terms, vec![p, not_q], TheoryLemmaKind::BvBitBlast)
        .expect_err("forged BV bitblast clause with no BV content must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_bv_bitblast_rejects_non_bool_literal() {
    // Forged clause where a literal is not Boolean-sorted. Real bit-blast
    // clauses are always propositional.
    let mut terms = TermStore::new();
    let bv = terms.mk_var("bv", Sort::bitvec(8));

    let err = validate_theory_lemma_strict(&terms, vec![bv], TheoryLemmaKind::BvBitBlast)
        .expect_err("BV-sorted literal in bv_bitblast clause must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_bv_bitblast_rejects_empty_clause() {
    let terms = TermStore::new();
    let err = validate_theory_lemma_strict(&terms, vec![], TheoryLemmaKind::BvBitBlast)
        .expect_err("empty bv_bitblast clause must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_bv_bitblast_rejects_schema_shaped_unproved_equality_clause() {
    // Schema-shaped but not valid: `(= bv 0)` is falsifiable. Strict mode must
    // not accept it just because it mentions BV terms.
    let mut terms = TermStore::new();
    let bv = terms.mk_var("bv", Sort::bitvec(2));
    let zero = terms.mk_bitvec(BigInt::from(0), 2);
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![bv, zero], Sort::Bool);
    let err = validate_theory_lemma_strict(&terms, vec![eq], TheoryLemmaKind::BvBitBlast)
        .expect_err("falsifiable BV equality must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_bv_bitblast_accepts_bounded_semantic_tautology() {
    let mut terms = TermStore::new();
    let bv = terms.mk_var("bv", Sort::bitvec(2));
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![bv, bv], Sort::Bool);
    validate_theory_lemma_strict(&terms, vec![eq], TheoryLemmaKind::BvBitBlast)
        .expect("bounded BV tautology should pass strict semantic checking");
}

#[test]
fn test_bv_bitblast_rejects_too_wide_unchecked_clause() {
    let mut terms = TermStore::new();
    let bv = terms.mk_var("bv", Sort::bitvec(8));
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![bv, bv], Sort::Bool);
    let err = validate_theory_lemma_strict(&terms, vec![eq], TheoryLemmaKind::BvBitBlast)
        .expect_err("too-wide BV lemma must fail closed");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_bv_bitblast_gate_rejects_clause_missing_declared_op() {
    // Declared gate = `bvand`, but the clause only mentions `bvor` — this
    // is a plausible forgery that the schema check catches.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(4));
    let b = terms.mk_var("b", Sort::bitvec(4));
    let bvor = terms.mk_app(ay_core::Symbol::named("bvor"), vec![a, b], Sort::bitvec(4));
    let zero = terms.mk_app(ay_core::Symbol::named("bvconst"), vec![], Sort::bitvec(4));
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![bvor, zero], Sort::Bool);

    let err = validate_theory_lemma_strict(
        &terms,
        vec![eq],
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::And,
            width: 4,
        },
    )
    .expect_err("gate mismatch must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_bv_bitblast_gate_rejects_declared_width_mismatch() {
    // Declared width = 4, but the only matching `bvand` gate is 8-bit.
    // This is schema-shaped but not the annotated bit-blast gate.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let bvand = terms.mk_app(ay_core::Symbol::named("bvand"), vec![a, b], Sort::bitvec(8));
    let zero = terms.mk_app(ay_core::Symbol::named("bvconst"), vec![], Sort::bitvec(8));
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![bvand, zero], Sort::Bool);

    let err = validate_theory_lemma_strict(
        &terms,
        vec![eq],
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::And,
            width: 4,
        },
    )
    .expect_err("annotated gate width mismatch must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_bv_bitblast_gate_accepts_matching_op() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(4));
    let b = terms.mk_var("b", Sort::bitvec(4));
    let bvand = terms.mk_app(ay_core::Symbol::named("bvand"), vec![a, b], Sort::bitvec(4));
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![bvand, bvand], Sort::Bool);
    validate_theory_lemma_strict(
        &terms,
        vec![eq],
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::And,
            width: 4,
        },
    )
    .expect("matching gate op clause should pass");
}

#[test]
fn test_bv_bitblast_gate_rejects_bounded_falsifiable_and_semantics() {
    // Schema-shaped but semantically false for a=3, b=3: bvand(a,b) is not
    // always zero. The bounded gate checker enumerates the 2-bit inputs.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(2));
    let b = terms.mk_var("b", Sort::bitvec(2));
    let bvand = terms.mk_app(ay_core::Symbol::named("bvand"), vec![a, b], Sort::bitvec(2));
    let zero = terms.mk_bitvec(BigInt::from(0), 2);
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![bvand, zero], Sort::Bool);

    let err = validate_theory_lemma_strict(
        &terms,
        vec![eq],
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::And,
            width: 2,
        },
    )
    .expect_err("bounded semantic check must reject falsifiable bvand clause");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_bv_bitblast_gate_accepts_bounded_semantic_tautology() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(2));
    let b = terms.mk_var("b", Sort::bitvec(2));
    let bvand = terms.mk_app(ay_core::Symbol::named("bvand"), vec![a, b], Sort::bitvec(2));
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![bvand, bvand], Sort::Bool);

    validate_theory_lemma_strict(
        &terms,
        vec![eq],
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::And,
            width: 2,
        },
    )
    .expect("bounded semantic tautology should pass");
}

// ============================================================================
// Array axiom forgeries (#8820)
// ============================================================================

#[test]
fn test_array_select_store_pos_rejects_clause_without_select_store() {
    // Forgery: plain Boolean clause with no select/store applications.
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let err = validate_theory_lemma_strict(
        &terms,
        vec![p],
        TheoryLemmaKind::ArraySelectStore { index_eq: true },
    )
    .expect_err("array axiom without select-over-store must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_array_select_store_pos_rejects_unrelated_stored_value() {
    // Plausible but false: the same-index read is equated with `w`, not the
    // stored value `v`.
    let mut terms = TermStore::new();
    let index_sort = Sort::Int;
    let elem_sort = Sort::Int;
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(
        index_sort.clone(),
        elem_sort.clone(),
    )));
    let a = terms.mk_var("a", array_sort);
    let i = terms.mk_var("i", index_sort);
    let v = terms.mk_var("v", elem_sort.clone());
    let w = terms.mk_var("w", elem_sort);
    let store_sort = terms.sort(a).clone();
    let store = terms.mk_app(ay_core::Symbol::named("store"), vec![a, i, v], store_sort);
    let select = terms.mk_app(ay_core::Symbol::named("select"), vec![store, i], Sort::Int);
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![select, w], Sort::Bool);

    let err = validate_theory_lemma_strict(
        &terms,
        vec![eq],
        TheoryLemmaKind::ArraySelectStore { index_eq: true },
    )
    .expect_err("positive select-store axiom must use the stored value");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_array_select_store_pos_rejects_wrong_read_index() {
    // Plausible but false: `(select (store a i v) j) = v` is not the
    // unconditional positive read-over-write axiom when `j` is distinct.
    let mut terms = TermStore::new();
    let index_sort = Sort::Int;
    let elem_sort = Sort::Int;
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(
        index_sort.clone(),
        elem_sort.clone(),
    )));
    let a = terms.mk_var("a", array_sort);
    let i = terms.mk_var("i", index_sort.clone());
    let j = terms.mk_var("j", index_sort);
    let v = terms.mk_var("v", elem_sort);
    let store_sort = terms.sort(a).clone();
    let store = terms.mk_app(ay_core::Symbol::named("store"), vec![a, i, v], store_sort);
    let select = terms.mk_app(ay_core::Symbol::named("select"), vec![store, j], Sort::Int);
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![select, v], Sort::Bool);

    let err = validate_theory_lemma_strict(
        &terms,
        vec![eq],
        TheoryLemmaKind::ArraySelectStore { index_eq: true },
    )
    .expect_err("positive select-store axiom must read at the stored index");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_array_select_store_neg_requires_disequality() {
    // Well-formed select-over-store, but NO disequality literal on indices.
    // Negative case requires one.
    let mut terms = TermStore::new();
    let index_sort = Sort::Int;
    let elem_sort = Sort::Int;
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(
        index_sort.clone(),
        elem_sort.clone(),
    )));
    let a = terms.mk_var("a", array_sort);
    let i = terms.mk_var("i", index_sort);
    let v = terms.mk_var("v", elem_sort);
    let store = terms.mk_app(
        ay_core::Symbol::named("store"),
        vec![a, i, v],
        terms.sort(a).clone(),
    );
    let select = terms.mk_app(ay_core::Symbol::named("select"), vec![store, i], Sort::Int);
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![select, v], Sort::Bool);

    let err = validate_theory_lemma_strict(
        &terms,
        vec![eq],
        TheoryLemmaKind::ArraySelectStore { index_eq: false },
    )
    .expect_err("negative select-store axiom without disequality must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_array_select_store_pos_accepts_well_formed() {
    let mut terms = TermStore::new();
    let index_sort = Sort::Int;
    let elem_sort = Sort::Int;
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(
        index_sort.clone(),
        elem_sort.clone(),
    )));
    let a = terms.mk_var("a", array_sort);
    let i = terms.mk_var("i", index_sort);
    let v = terms.mk_var("v", elem_sort);
    let store_sort = terms.sort(a).clone();
    let store = terms.mk_app(ay_core::Symbol::named("store"), vec![a, i, v], store_sort);
    let select = terms.mk_app(ay_core::Symbol::named("select"), vec![store, i], Sort::Int);
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![select, v], Sort::Bool);
    validate_theory_lemma_strict(
        &terms,
        vec![eq],
        TheoryLemmaKind::ArraySelectStore { index_eq: true },
    )
    .expect("well-formed positive select-store axiom should pass");
}

#[test]
fn test_array_select_store_neg_accepts_nested_store_base() {
    // ROW2 permits any array term as its base, including another store.  The
    // base-side select is therefore also syntactically a select-over-store;
    // strict recognition must still match the outer store decomposition.
    let mut terms = TermStore::new();
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(Sort::Int, Sort::Int)));
    let a = terms.mk_var("a", array_sort);
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let store_sort = terms.sort(a).clone();
    let inner = terms.mk_app(
        ay_core::Symbol::named("store"),
        vec![a, i, v],
        store_sort.clone(),
    );
    let outer = terms.mk_app(
        ay_core::Symbol::named("store"),
        vec![inner, j, x],
        store_sort,
    );
    let select_outer = terms.mk_app(ay_core::Symbol::named("select"), vec![outer, i], Sort::Int);
    let select_inner = terms.mk_app(ay_core::Symbol::named("select"), vec![inner, i], Sort::Int);
    let idx_eq = terms.mk_eq(i, j);
    let row2_eq = terms.mk_eq(select_outer, select_inner);

    validate_theory_lemma_strict(
        &terms,
        vec![idx_eq, row2_eq],
        TheoryLemmaKind::ArraySelectStore { index_eq: false },
    )
    .expect("ROW2 over a nested-store base is an exact strict schema");
}

#[test]
fn test_array_select_store_neg_rejects_weakened_three_literal_attribution() {
    let mut terms = TermStore::new();
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(Sort::Int, Sort::Int)));
    let a = terms.mk_var("a", array_sort.clone());
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let p = terms.mk_var("p", Sort::Int);
    let q = terms.mk_var("q", Sort::Int);
    let store = terms.mk_app(ay_core::Symbol::named("store"), vec![a, i, v], array_sort);
    let select_store = terms.mk_app(ay_core::Symbol::named("select"), vec![store, j], Sort::Int);
    let select_base = terms.mk_app(ay_core::Symbol::named("select"), vec![a, j], Sort::Int);
    let idx_eq = terms.mk_eq(i, j);
    let row2_eq = terms.mk_eq(select_store, select_base);
    let extra_eq = terms.mk_eq(p, q);
    let extra = terms.mk_not(extra_eq);
    let clause = vec![idx_eq, row2_eq, extra];

    validate_theory_lemma_strict(
        &terms,
        clause.clone(),
        TheoryLemmaKind::ArraySelectStore { index_eq: false },
    )
    .expect_err("weakened ROW2 needs an explicit weakening step");
    assert_eq!(recognize_array_select_store(&terms, &clause), None);
}

#[test]
fn test_array_select_store_neg_rejects_malformed_operator_sorts() {
    // `TermStore::mk_app` permits raw applications.  Names and arities alone
    // must not turn non-array or wrong-index applications into array axioms.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let store = terms.mk_app(ay_core::Symbol::named("store"), vec![a, i, v], Sort::Int);
    let select_store = terms.mk_app(ay_core::Symbol::named("select"), vec![store, j], Sort::Int);
    let select_base = terms.mk_app(ay_core::Symbol::named("select"), vec![a, j], Sort::Int);
    let clause = vec![terms.mk_eq(i, j), terms.mk_eq(select_store, select_base)];
    validate_theory_lemma_strict(
        &terms,
        clause.clone(),
        TheoryLemmaKind::ArraySelectStore { index_eq: false },
    )
    .expect_err("non-array store/select applications must be rejected");
    assert_eq!(recognize_array_select_store(&terms, &clause), None);

    let mut terms = TermStore::new();
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(Sort::Int, Sort::Int)));
    let a = terms.mk_var("a", array_sort.clone());
    let i = terms.mk_var("i", Sort::Bool);
    let j = terms.mk_var("j", Sort::Bool);
    let v = terms.mk_var("v", Sort::Int);
    let store = terms.mk_app(ay_core::Symbol::named("store"), vec![a, i, v], array_sort);
    let select_store = terms.mk_app(ay_core::Symbol::named("select"), vec![store, j], Sort::Int);
    let select_base = terms.mk_app(ay_core::Symbol::named("select"), vec![a, j], Sort::Int);
    let clause = vec![terms.mk_eq(i, j), terms.mk_eq(select_store, select_base)];
    validate_theory_lemma_strict(
        &terms,
        clause.clone(),
        TheoryLemmaKind::ArraySelectStore { index_eq: false },
    )
    .expect_err("store/select indices must match the array index sort");
    assert_eq!(recognize_array_select_store(&terms, &clause), None);
}

#[test]
fn test_array_extensionality_rejects_clause_without_array_equality() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let err = validate_theory_lemma_strict(&terms, vec![p], TheoryLemmaKind::ArrayExtensionality)
        .expect_err("extensionality without array equality must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

// ============================================================================
#[test]
fn test_array_select_store_pos_rejects_row2_wrong_polarity() {
    // ROW2 is `(= i j) ∨ (= (select (store a i v) j) (select a j))`.
    // It must not be accepted as the positive ROW1 attribution.
    let mut terms = TermStore::new();
    let index_sort = Sort::Int;
    let elem_sort = Sort::Int;
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(
        index_sort.clone(),
        elem_sort.clone(),
    )));
    let a = terms.mk_var("a", array_sort);
    let i = terms.mk_var("i", index_sort.clone());
    let j = terms.mk_var("j", index_sort);
    let v = terms.mk_var("v", elem_sort);
    let store_sort = terms.sort(a).clone();
    let store = terms.mk_app(ay_core::Symbol::named("store"), vec![a, i, v], store_sort);
    let select_store = terms.mk_app(ay_core::Symbol::named("select"), vec![store, j], Sort::Int);
    let select_base = terms.mk_app(ay_core::Symbol::named("select"), vec![a, j], Sort::Int);
    let idx_eq = terms.mk_app(ay_core::Symbol::named("="), vec![i, j], Sort::Bool);
    let row2_eq = terms.mk_app(
        ay_core::Symbol::named("="),
        vec![select_store, select_base],
        Sort::Bool,
    );
    let row2_clause = terms.mk_or(vec![idx_eq, row2_eq]);

    let err = validate_theory_lemma_strict(
        &terms,
        vec![row2_clause],
        TheoryLemmaKind::ArraySelectStore { index_eq: true },
    )
    .expect_err("ROW2 clause must be rejected under ROW1/positive attribution");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );

    validate_theory_lemma_strict(
        &terms,
        vec![row2_clause],
        TheoryLemmaKind::ArraySelectStore { index_eq: false },
    )
    .expect("same clause should pass under ROW2/negative attribution");
}

#[test]
fn test_array_select_store_neg_rejects_row2_unit_shortcut() {
    // A bare ROW2 equality is only justified by generator context
    // (for example a surrounding asserted index disequality). It is not a
    // context-free ROW2 axiom and must be rejected as a standalone lemma.
    let mut terms = TermStore::new();
    let index_sort = Sort::Int;
    let elem_sort = Sort::Int;
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(
        index_sort.clone(),
        elem_sort.clone(),
    )));
    let a = terms.mk_var("a", array_sort);
    let i = terms.mk_var("i", index_sort.clone());
    let j = terms.mk_var("j", index_sort);
    let v = terms.mk_var("v", elem_sort);
    let store_sort = terms.sort(a).clone();
    let store = terms.mk_app(ay_core::Symbol::named("store"), vec![a, i, v], store_sort);
    let select_store = terms.mk_app(ay_core::Symbol::named("select"), vec![store, j], Sort::Int);
    let select_base = terms.mk_app(ay_core::Symbol::named("select"), vec![a, j], Sort::Int);
    let row2_eq = terms.mk_app(
        ay_core::Symbol::named("="),
        vec![select_store, select_base],
        Sort::Bool,
    );

    let err = validate_theory_lemma_strict(
        &terms,
        vec![row2_eq],
        TheoryLemmaKind::ArraySelectStore { index_eq: false },
    )
    .expect_err("standalone row2_unit_shortcut must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_array_extensionality_rejects_wrong_select_pair() {
    let mut terms = TermStore::new();
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(Sort::Int, Sort::Int)));
    let a = terms.mk_var("a", array_sort.clone());
    let b = terms.mk_var("b", array_sort.clone());
    let c = terms.mk_var("c", array_sort);
    let k = terms.mk_var("k", Sort::Int);
    let eq_ab = terms.mk_app(ay_core::Symbol::named("="), vec![a, b], Sort::Bool);
    let sel_a = terms.mk_app(ay_core::Symbol::named("select"), vec![a, k], Sort::Int);
    let sel_c = terms.mk_app(ay_core::Symbol::named("select"), vec![c, k], Sort::Int);
    let sel_eq = terms.mk_app(ay_core::Symbol::named("="), vec![sel_a, sel_c], Sort::Bool);
    let not_sel_eq = terms.mk_not(sel_eq);
    let forged = terms.mk_or(vec![eq_ab, not_sel_eq]);

    let err =
        validate_theory_lemma_strict(&terms, vec![forged], TheoryLemmaKind::ArrayExtensionality)
            .expect_err("extensionality witness must select from the exact array pair");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_array_extensionality_rejects_unchecked_exact_schema() {
    let mut terms = TermStore::new();
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(Sort::Int, Sort::Int)));
    let a = terms.mk_var("a", array_sort.clone());
    let b = terms.mk_var("b", array_sort);
    let k = terms.mk_var("k", Sort::Int);
    let eq_ab = terms.mk_app(ay_core::Symbol::named("="), vec![a, b], Sort::Bool);
    let sel_a = terms.mk_app(ay_core::Symbol::named("select"), vec![a, k], Sort::Int);
    let sel_b = terms.mk_app(ay_core::Symbol::named("select"), vec![b, k], Sort::Int);
    let sel_eq = terms.mk_app(ay_core::Symbol::named("="), vec![sel_a, sel_b], Sort::Bool);
    let not_sel_eq = terms.mk_not(sel_eq);
    let ext = terms.mk_or(vec![eq_ab, not_sel_eq]);

    let err = validate_theory_lemma_strict(&terms, vec![ext], TheoryLemmaKind::ArrayExtensionality)
        .expect_err("syntactic extensionality witness must fail closed");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

// ============================================================================
// FP→BV forgeries (#8820)
// ============================================================================

#[test]
fn test_fp_to_bv_rejects_clause_without_fp_or_bv() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let err = validate_theory_lemma_strict(
        &terms,
        vec![p, q],
        TheoryLemmaKind::FpToBv {
            operation: FpOp::Add,
        },
    )
    .expect_err("fp_to_bv without FP/BV content must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_fp_to_bv_rejects_non_bool_literal() {
    let mut terms = TermStore::new();
    let bv = terms.mk_var("bv", Sort::bitvec(32));
    let err = validate_theory_lemma_strict(
        &terms,
        vec![bv],
        TheoryLemmaKind::FpToBv {
            operation: FpOp::Add,
        },
    )
    .expect_err("non-Bool fp_to_bv literal must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_fp_to_bv_rejects_declared_operation_mismatch() {
    let mut terms = TermStore::new();
    let f = terms.mk_var("f", Sort::FloatingPoint(11, 53));
    let eq = terms.mk_app(ay_core::Symbol::named("fp.isNaN"), vec![f], Sort::Bool);
    let err = validate_theory_lemma_strict(
        &terms,
        vec![eq],
        TheoryLemmaKind::FpToBv {
            operation: FpOp::Add,
        },
    )
    .expect_err("fp_to_bv Add annotation must not accept fp.isNaN clause");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_fp_to_bv_rejects_clause_with_declared_fp_operation_without_certificate() {
    let mut terms = TermStore::new();
    let rm = terms.mk_var("rm", Sort::Uninterpreted("RoundingMode".to_string()));
    let a = terms.mk_var("a", Sort::FloatingPoint(11, 53));
    let b = terms.mk_var("b", Sort::FloatingPoint(11, 53));
    let add = terms.mk_app(
        ay_core::Symbol::named("fp.add"),
        vec![rm, a, b],
        Sort::FloatingPoint(11, 53),
    );
    let eq = terms.mk_app(ay_core::Symbol::named("fp.isNaN"), vec![add], Sort::Bool);
    let err = validate_theory_lemma_strict(
        &terms,
        vec![eq],
        TheoryLemmaKind::FpToBv {
            operation: FpOp::Add,
        },
    )
    .expect_err("schema-shaped FP lowering without certificate must fail closed");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

// ============================================================================
// String axiom forgeries (#8820)
// ============================================================================

#[test]
fn test_string_length_rejects_clause_without_str_len() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("s", Sort::String);
    let eq_s_s = terms.mk_app(ay_core::Symbol::named("="), vec![s, s], Sort::Bool);
    let err =
        validate_theory_lemma_strict(&terms, vec![eq_s_s], TheoryLemmaKind::StringLengthAxiom)
            .expect_err("string_length clause without str.len must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_string_length_rejects_clause_without_string_content() {
    // Even if `str.len` appears abstractly, a clause with only pure Bool
    // variables has no string sub-term. But since str.len application is
    // part of the schema, we contrive a clause that only has Bool variables.
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let err = validate_theory_lemma_strict(&terms, vec![p], TheoryLemmaKind::StringLengthAxiom)
        .expect_err("string_length with pure Bool clause must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_string_length_rejects_statically_false_constant_length_clause() {
    let mut terms = TermStore::new();
    let s = terms.mk_string("abc".to_string());
    let len_s = terms.mk_app(ay_core::Symbol::named("str.len"), vec![s], Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let false_len = terms.mk_app(ay_core::Symbol::named("="), vec![len_s, two], Sort::Bool);

    let err =
        validate_theory_lemma_strict(&terms, vec![false_len], TheoryLemmaKind::StringLengthAxiom)
            .expect_err("string_length must reject concrete false length clauses");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_string_length_accepts_statically_true_constant_length_clause() {
    let mut terms = TermStore::new();
    let s = terms.mk_string("abc".to_string());
    let len_s = terms.mk_app(ay_core::Symbol::named("str.len"), vec![s], Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let true_len = terms.mk_app(ay_core::Symbol::named("="), vec![len_s, three], Sort::Bool);

    validate_theory_lemma_strict(&terms, vec![true_len], TheoryLemmaKind::StringLengthAxiom)
        .expect("concrete true string length clause should pass");
}

#[test]
fn test_string_length_rejects_symbolic_well_formed_clause() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("s", Sort::String);
    let len_s = terms.mk_app(ay_core::Symbol::named("str.len"), vec![s], Sort::Int);
    let zero = terms.mk_app(ay_core::Symbol::named("int.zero"), vec![], Sort::Int);
    let ge = terms.mk_app(ay_core::Symbol::named(">="), vec![len_s, zero], Sort::Bool);
    let err = validate_theory_lemma_strict(&terms, vec![ge], TheoryLemmaKind::StringLengthAxiom)
        .expect_err("symbolic string length lemma must fail closed");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_string_content_rejects_clause_without_content_op() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("s", Sort::String);
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![s, s], Sort::Bool);
    let err = validate_theory_lemma_strict(&terms, vec![eq], TheoryLemmaKind::StringContentAxiom)
        .expect_err("string_content without content op must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_string_content_rejects_schema_shaped_unchecked_clause() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("s", Sort::String);
    let empty = terms.mk_string(String::new());
    let contains = terms.mk_app(
        ay_core::Symbol::named("str.contains"),
        vec![s, empty],
        Sort::Bool,
    );
    let err =
        validate_theory_lemma_strict(&terms, vec![contains], TheoryLemmaKind::StringContentAxiom)
            .expect_err("string content lemma without semantic checker must fail closed");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_string_normal_form_rejects_pure_boolean_clause() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let err = validate_theory_lemma_strict(&terms, vec![p], TheoryLemmaKind::StringNormalForm)
        .expect_err("string_normal_form with no string content must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_string_normal_form_rejects_schema_shaped_unchecked_clause() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("s", Sort::String);
    let code = terms.mk_app(ay_core::Symbol::named("str.to_code"), vec![s], Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let ge = terms.mk_app(ay_core::Symbol::named(">="), vec![code, zero], Sort::Bool);
    let err = validate_theory_lemma_strict(&terms, vec![ge], TheoryLemmaKind::StringNormalForm)
        .expect_err("string normal-form lemma without semantic checker must fail closed");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

// ============================================================================
// Soundness regression: forged proof cannot derive UNSAT via theory lemma
// ============================================================================

/// A forged proof sequence:
///   (assume p)
///   (theory_lemma BvBitBlast (cl (not p)))    <- forged
///   (resolution () on p from 0,1)             <- empty clause
///
/// Prior to #8820 the theory_lemma step was accepted (clause non-empty), so
/// the resolution produced the empty clause and `check_proof_strict` would
/// conclude UNSAT. This test asserts the checker now rejects step 1.
#[test]
fn test_forged_bv_lemma_cannot_drive_strict_checker_to_unsat() {
    use ay_core::Proof;

    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    proof.add_assume(p, None);
    proof.add_step(ProofStep::TheoryLemma {
        theory: "forged".to_string(),
        clause: vec![not_p],
        farkas: None,
        kind: TheoryLemmaKind::BvBitBlast,
        lia: None,
    });
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: p,
        clause1: ProofId(0),
        clause2: ProofId(1),
    });

    let err = crate::check_proof_strict(&proof, &terms)
        .expect_err("strict checker must reject forged BV lemma");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected forged BV lemma to be rejected, got {err:?}"
    );
}

/// Same forgery pattern but with `ArraySelectStore`.
#[test]
fn test_forged_array_lemma_cannot_drive_strict_checker_to_unsat() {
    use ay_core::Proof;

    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    proof.add_assume(p, None);
    proof.add_step(ProofStep::TheoryLemma {
        theory: "forged".to_string(),
        clause: vec![not_p],
        farkas: None,
        kind: TheoryLemmaKind::ArraySelectStore { index_eq: true },
        lia: None,
    });
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: p,
        clause1: ProofId(0),
        clause2: ProofId(1),
    });

    let err = crate::check_proof_strict(&proof, &terms)
        .expect_err("strict checker must reject forged array lemma");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected forged array lemma to be rejected, got {err:?}"
    );
}

/// Same forgery pattern with `FpToBv`.
#[test]
fn test_forged_fp_lemma_cannot_drive_strict_checker_to_unsat() {
    use ay_core::Proof;

    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    proof.add_assume(p, None);
    proof.add_step(ProofStep::TheoryLemma {
        theory: "forged".to_string(),
        clause: vec![not_p],
        farkas: None,
        kind: TheoryLemmaKind::FpToBv {
            operation: FpOp::Add,
        },
        lia: None,
    });
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: p,
        clause1: ProofId(0),
        clause2: ProofId(1),
    });

    let err = crate::check_proof_strict(&proof, &terms)
        .expect_err("strict checker must reject forged FP lemma");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected forged FP lemma to be rejected, got {err:?}"
    );
}

/// Same forgery pattern with `StringLengthAxiom`.
#[test]
fn test_forged_string_lemma_cannot_drive_strict_checker_to_unsat() {
    use ay_core::Proof;

    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    proof.add_assume(p, None);
    proof.add_step(ProofStep::TheoryLemma {
        theory: "forged".to_string(),
        clause: vec![not_p],
        farkas: None,
        kind: TheoryLemmaKind::StringLengthAxiom,
        lia: None,
    });
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: p,
        clause1: ProofId(0),
        clause2: ProofId(1),
    });

    let err = crate::check_proof_strict(&proof, &terms)
        .expect_err("strict checker must reject forged string lemma");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected forged string lemma to be rejected, got {err:?}"
    );
}

// ============================================================================
// LIA forged theory-lemma (meta-false-PROVE): a forged `LiaGeneric` lemma whose
// `Divisibility`/`CuttingPlane` annotation labels a NON-tautological clause must
// be rejected in strict mode. Before the fail-closed fix, `validate_divisibility`
// accepted any non-empty clause and `validate_cutting_plane` shape-checked only,
// so a forged lemma could be resolved to the empty clause and make
// `check_proof_strict` certify UNSAT on a satisfiable formula -- the worst
// possible bug in a proof checker.
// ============================================================================

#[test]
fn test_forged_lia_divisibility_cannot_drive_strict_checker_to_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let x_le_3 = terms.mk_le(x, three);
    let not_x_le_3 = terms.mk_not(x_le_3); // clause {x > 3} -- NOT a tautology
    let step = ProofStep::TheoryLemma {
        theory: "test".to_string(),
        clause: vec![not_x_le_3],
        farkas: None,
        kind: TheoryLemmaKind::LiaGeneric,
        lia: Some(LiaAnnotation::Divisibility),
    };
    let mut derived = Vec::new();
    let err = validate_step(&terms, &mut derived, ProofId(0), &step, true, None).expect_err(
        "forged LIA Divisibility lemma over a non-tautological clause must be rejected",
    );
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn test_forged_lia_cutting_plane_cannot_drive_strict_checker_to_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let x_le_3 = terms.mk_le(x, three);
    let not_x_le_3 = terms.mk_not(x_le_3); // clause {x > 3} -- NOT a contradiction
    let cp = CuttingPlaneAnnotation {
        farkas: FarkasAnnotation::from_ints(&[1]),
        divisor: 2,
    };
    let step = ProofStep::TheoryLemma {
        theory: "test".to_string(),
        clause: vec![not_x_le_3],
        farkas: None,
        kind: TheoryLemmaKind::LiaGeneric,
        lia: Some(LiaAnnotation::CuttingPlane(cp)),
    };
    let mut derived = Vec::new();
    let err = validate_step(&terms, &mut derived, ProofId(0), &step, true, None).expect_err(
        "forged LIA CuttingPlane lemma over a non-contradictory clause must be rejected",
    );
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

// ============================================================================
// Propositional sibling of the meta-false-PROVE: a forged `and_neg` step.
// `and_neg` is the tautology `(and a b) ∨ ¬a ∨ ¬b`. The old validator only
// COUNTED literals negating some conjunct, so the forged clause
// `[(and a b), ¬a, ¬a]` (duplicate ¬a, missing ¬b) passed even though it is
// falsified at a=true, b=false. The proof below resolves that non-tautological
// clause to the empty clause over the SATISFIABLE formula {a, ¬b}; every other
// step is genuinely sound, so before the fix `check_proof_strict` certified
// UNSAT on a satisfiable formula. The checker must now reject the forged step.
// ============================================================================
#[test]
fn test_forged_and_neg_cannot_drive_strict_checker_to_unsat() {
    use ay_core::{AletheRule, Proof};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let and_ab = terms.mk_and(vec![a, b]);
    let not_a = terms.mk_not(a);
    let not_b = terms.mk_not(b);
    let not_and_ab = terms.mk_not(and_ab);

    let mut proof = Proof::new();
    proof.add_assume(a, None); // 0: {a}
    proof.add_assume(not_b, None); // 1: {¬b}
                                   // 2: forged and_neg  [(and a b), ¬a, ¬a]  -- the ONLY unsound step
    proof.add_rule_step(
        AletheRule::AndNeg,
        vec![and_ab, not_a, not_a],
        vec![],
        vec![and_ab],
    );
    // 3: resolve {a}(0) with (2) on a -> [(and a b)]
    proof.add_resolution(vec![and_ab], a, ProofId(0), ProofId(2));
    // 4: and_pos(1) tautology [¬(and a b), b]
    proof.add_rule_step(
        AletheRule::AndPos(1),
        vec![not_and_ab, b],
        vec![],
        vec![and_ab],
    );
    // 5: resolve (3) with (4) on (and a b) -> [b]
    proof.add_resolution(vec![b], and_ab, ProofId(3), ProofId(4));
    // 6: resolve (5) with {¬b}(1) on b -> []  (empty clause = UNSAT)
    proof.add_resolution(vec![], b, ProofId(5), ProofId(1));

    let err = crate::check_proof_strict(&proof, &terms)
        .expect_err("strict checker must reject the forged and_neg proof");
    assert!(
        matches!(err, ProofCheckError::InvalidBooleanRule { .. }),
        "expected forged and_neg to be rejected, got {err:?}"
    );
}

// ============================================================================
// BV bit-blast SHIFT gate enforcement.
//
// The strict checker validates a bit-blast gate lemma by exhaustively
// enumerating its bounded inputs and evaluating the clause. For that to
// ENFORCE the SMT-LIB shift spec (bvshl/bvlshr/bvashr), the checker's evaluator
// must understand shifts -- including the over-shift saturation case (shift
// amount >= width => 0 for shl/lshr, sign-fill for ashr) where machine/LLVM
// shifts famously diverge from SMT-LIB. Before shift support these lemmas were
// rejected with "cannot evaluate"; the acceptance tests below are RED without
// the evaluator change and GREEN with it.
// ============================================================================

/// `bvshl(a, 1) == a + a` for all 2-bit `a`. Exercises the in-range shift and
/// requires the checker to evaluate `bvshl`.
#[test]
fn test_bv_bitblast_gate_accepts_shl_in_range_doubling() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(2));
    let one = terms.mk_bitvec(BigInt::from(1), 2);
    let shl = terms.mk_app(
        ay_core::Symbol::named("bvshl"),
        vec![a, one],
        Sort::bitvec(2),
    );
    let sum = terms.mk_app(ay_core::Symbol::named("bvadd"), vec![a, a], Sort::bitvec(2));
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![shl, sum], Sort::Bool);
    validate_theory_lemma_strict(
        &terms,
        vec![eq],
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::Shl,
            width: 2,
        },
    )
    .expect("bvshl(a,1) == a+a must be checkable and accepted");
}

/// Over-shift saturation for `bvshl`: `(b < 2) OR (bvshl(a,b) = 0)` is valid for
/// all 2-bit `a,b` ONLY under SMT-LIB semantics (shift >= width yields 0). A
/// machine-style count-mask (b & 1) would falsify it, so the checker accepting
/// this pins the over-shift rule.
#[test]
fn test_bv_bitblast_gate_accepts_shl_overshift_saturation() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(2));
    let b = terms.mk_var("b", Sort::bitvec(2));
    let two = terms.mk_bitvec(BigInt::from(2), 2);
    let zero = terms.mk_bitvec(BigInt::from(0), 2);
    let shl = terms.mk_app(ay_core::Symbol::named("bvshl"), vec![a, b], Sort::bitvec(2));
    let b_lt_w = terms.mk_app(ay_core::Symbol::named("bvult"), vec![b, two], Sort::Bool);
    let shl_zero = terms.mk_app(ay_core::Symbol::named("="), vec![shl, zero], Sort::Bool);
    validate_theory_lemma_strict(
        &terms,
        vec![b_lt_w, shl_zero],
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::Shl,
            width: 2,
        },
    )
    .expect("bvshl over-shift (>= width) must saturate to 0 and be accepted");
}

/// Over-shift saturation for `bvlshr`: `(b < 2) OR (bvlshr(a,b) = 0)`.
#[test]
fn test_bv_bitblast_gate_accepts_lshr_overshift_saturation() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(2));
    let b = terms.mk_var("b", Sort::bitvec(2));
    let two = terms.mk_bitvec(BigInt::from(2), 2);
    let zero = terms.mk_bitvec(BigInt::from(0), 2);
    let lshr = terms.mk_app(
        ay_core::Symbol::named("bvlshr"),
        vec![a, b],
        Sort::bitvec(2),
    );
    let b_lt_w = terms.mk_app(ay_core::Symbol::named("bvult"), vec![b, two], Sort::Bool);
    let lshr_zero = terms.mk_app(ay_core::Symbol::named("="), vec![lshr, zero], Sort::Bool);
    validate_theory_lemma_strict(
        &terms,
        vec![b_lt_w, lshr_zero],
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::Lshr,
            width: 2,
        },
    )
    .expect("bvlshr over-shift (>= width) must saturate to 0 and be accepted");
}

/// Over-shift sign-fill for `bvashr`: for shift >= width the result is all-ones
/// when `a` is negative (sign bit set, i.e. `a >= 2` at width 2) and 0 otherwise.
/// Encoded as `(b < 2) OR (bvashr(a,b) = ite(a < 2, 0, 3))`.
#[test]
fn test_bv_bitblast_gate_accepts_ashr_overshift_sign_fill() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(2));
    let b = terms.mk_var("b", Sort::bitvec(2));
    let two = terms.mk_bitvec(BigInt::from(2), 2);
    let zero = terms.mk_bitvec(BigInt::from(0), 2);
    let three = terms.mk_bitvec(BigInt::from(3), 2);
    let ashr = terms.mk_app(
        ay_core::Symbol::named("bvashr"),
        vec![a, b],
        Sort::bitvec(2),
    );
    let a_nonneg = terms.mk_app(ay_core::Symbol::named("bvult"), vec![a, two], Sort::Bool);
    let sign_fill = terms.mk_ite(a_nonneg, zero, three);
    let b_lt_w = terms.mk_app(ay_core::Symbol::named("bvult"), vec![b, two], Sort::Bool);
    let ashr_eq = terms.mk_app(
        ay_core::Symbol::named("="),
        vec![ashr, sign_fill],
        Sort::Bool,
    );
    validate_theory_lemma_strict(
        &terms,
        vec![b_lt_w, ashr_eq],
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::Ashr,
            width: 2,
        },
    )
    .expect("bvashr over-shift must fill with the sign bit and be accepted");
}

/// Forgery: claims `bvshl` is the identity on over-shift (the "shift does
/// nothing" bug). `(b < 2) OR (bvshl(a,b) = a)` is FALSE for a=1, b=2 (shl=0 !=
/// 1). The strict checker must find the falsifying assignment and reject it.
#[test]
fn test_bv_bitblast_gate_rejects_shl_overshift_identity_forgery() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(2));
    let b = terms.mk_var("b", Sort::bitvec(2));
    let two = terms.mk_bitvec(BigInt::from(2), 2);
    let shl = terms.mk_app(ay_core::Symbol::named("bvshl"), vec![a, b], Sort::bitvec(2));
    let b_lt_w = terms.mk_app(ay_core::Symbol::named("bvult"), vec![b, two], Sort::Bool);
    let shl_is_a = terms.mk_app(ay_core::Symbol::named("="), vec![shl, a], Sort::Bool);
    let err = validate_theory_lemma_strict(
        &terms,
        vec![b_lt_w, shl_is_a],
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::Shl,
            width: 2,
        },
    )
    .expect_err("forged identity-shift over-shift lemma must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

/// Forgery: claims `bvashr` fills over-shift with 0 (logical, not arithmetic).
/// `(b < 2) OR (bvashr(a,b) = 0)` is FALSE for a=3 (negative), b=2 where the
/// correct result is 3 (all ones). The checker must reject it.
#[test]
fn test_bv_bitblast_gate_rejects_ashr_logical_fill_forgery() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(2));
    let b = terms.mk_var("b", Sort::bitvec(2));
    let two = terms.mk_bitvec(BigInt::from(2), 2);
    let zero = terms.mk_bitvec(BigInt::from(0), 2);
    let ashr = terms.mk_app(
        ay_core::Symbol::named("bvashr"),
        vec![a, b],
        Sort::bitvec(2),
    );
    let b_lt_w = terms.mk_app(ay_core::Symbol::named("bvult"), vec![b, two], Sort::Bool);
    let ashr_zero = terms.mk_app(ay_core::Symbol::named("="), vec![ashr, zero], Sort::Bool);
    let err = validate_theory_lemma_strict(
        &terms,
        vec![b_lt_w, ashr_zero],
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::Ashr,
            width: 2,
        },
    )
    .expect_err("forged logical-fill ashr over-shift lemma must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

// ============================================================================
// BV bit-blast: remaining gate-type enforcement (udiv/urem div-by-zero, concat
// bit-order, sign vs zero extend). Each advertised BvGateType is now exhaustively
// evaluable, so the strict checker enforces its SMT-LIB semantics. Uses the
// un-annotated BvBitBlast kind (pure bounded semantic check).
// ============================================================================

/// SMT-LIB makes `bvudiv` total: dividing by zero yields all-ones. The clause
/// `(b != 0) OR (bvudiv(a,b) = 3)` is valid for all 2-bit a,b and must be
/// accepted -- which forces the checker to model div-by-zero correctly.
#[test]
fn test_bv_bitblast_accepts_bvudiv_div_by_zero_all_ones() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(2));
    let b = terms.mk_var("b", Sort::bitvec(2));
    let zero = terms.mk_bitvec(BigInt::from(0), 2);
    let three = terms.mk_bitvec(BigInt::from(3), 2);
    let b_eq_zero = terms.mk_app(ay_core::Symbol::named("="), vec![b, zero], Sort::Bool);
    let b_ne_zero = terms.mk_not(b_eq_zero);
    let udiv = terms.mk_app(
        ay_core::Symbol::named("bvudiv"),
        vec![a, b],
        Sort::bitvec(2),
    );
    let udiv_all_ones = terms.mk_app(ay_core::Symbol::named("="), vec![udiv, three], Sort::Bool);
    validate_theory_lemma_strict(
        &terms,
        vec![b_ne_zero, udiv_all_ones],
        TheoryLemmaKind::BvBitBlast,
    )
    .expect("bvudiv by zero must equal all-ones and be accepted");
}

/// Forgery: claims `bvudiv` by zero is 0. False at b=0 (correct result is 3), so
/// the checker must reject it.
#[test]
fn test_bv_bitblast_rejects_bvudiv_div_by_zero_forgery() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(2));
    let b = terms.mk_var("b", Sort::bitvec(2));
    let zero = terms.mk_bitvec(BigInt::from(0), 2);
    let b_eq_zero = terms.mk_app(ay_core::Symbol::named("="), vec![b, zero], Sort::Bool);
    let b_ne_zero = terms.mk_not(b_eq_zero);
    let udiv = terms.mk_app(
        ay_core::Symbol::named("bvudiv"),
        vec![a, b],
        Sort::bitvec(2),
    );
    let udiv_zero = terms.mk_app(ay_core::Symbol::named("="), vec![udiv, zero], Sort::Bool);
    let err = validate_theory_lemma_strict(
        &terms,
        vec![b_ne_zero, udiv_zero],
        TheoryLemmaKind::BvBitBlast,
    )
    .expect_err("forged bvudiv-by-zero = 0 lemma must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

/// SMT-LIB `bvurem` by zero returns the dividend: `(b != 0) OR (bvurem(a,b) = a)`.
#[test]
fn test_bv_bitblast_accepts_bvurem_rem_by_zero_is_dividend() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(2));
    let b = terms.mk_var("b", Sort::bitvec(2));
    let zero = terms.mk_bitvec(BigInt::from(0), 2);
    let b_eq_zero = terms.mk_app(ay_core::Symbol::named("="), vec![b, zero], Sort::Bool);
    let b_ne_zero = terms.mk_not(b_eq_zero);
    let urem = terms.mk_app(
        ay_core::Symbol::named("bvurem"),
        vec![a, b],
        Sort::bitvec(2),
    );
    let urem_eq_a = terms.mk_app(ay_core::Symbol::named("="), vec![urem, a], Sort::Bool);
    validate_theory_lemma_strict(
        &terms,
        vec![b_ne_zero, urem_eq_a],
        TheoryLemmaKind::BvBitBlast,
    )
    .expect("bvurem by zero must equal the dividend and be accepted");
}

/// `concat` puts the first arg in the high bits: `extract[3:2](concat(a,b)) == a`
/// for 2-bit a,b. Exercises concat bit-order and extract together.
#[test]
fn test_bv_bitblast_accepts_concat_extract_high_roundtrip() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(2));
    let b = terms.mk_var("b", Sort::bitvec(2));
    let cat = terms.mk_app(
        ay_core::Symbol::named("concat"),
        vec![a, b],
        Sort::bitvec(4),
    );
    let hi = terms.mk_app(
        ay_core::Symbol::indexed("extract", vec![3, 2]),
        vec![cat],
        Sort::bitvec(2),
    );
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![hi, a], Sort::Bool);
    validate_theory_lemma_strict(&terms, vec![eq], TheoryLemmaKind::BvBitBlast)
        .expect("extract[3:2](concat(a,b)) == a must be accepted");
}

/// Forgery: claims the LOW half of `concat(a,b)` equals `a` (it is `b`). False
/// when a != b, so the checker must reject -- pinning the concat bit-order.
#[test]
fn test_bv_bitblast_rejects_concat_low_is_high_forgery() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(2));
    let b = terms.mk_var("b", Sort::bitvec(2));
    let cat = terms.mk_app(
        ay_core::Symbol::named("concat"),
        vec![a, b],
        Sort::bitvec(4),
    );
    let lo = terms.mk_app(
        ay_core::Symbol::indexed("extract", vec![1, 0]),
        vec![cat],
        Sort::bitvec(2),
    );
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![lo, a], Sort::Bool);
    let err = validate_theory_lemma_strict(&terms, vec![eq], TheoryLemmaKind::BvBitBlast)
        .expect_err("forged concat low==high lemma must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

/// `sign_extend` replicates the sign bit: the new top bit of `sign_extend(1, a)`
/// equals `a`'s sign bit. `extract[2:2](sign_extend(1,a)) == extract[1:1](a)`.
#[test]
fn test_bv_bitblast_accepts_sign_extend_replicates_sign() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(2));
    let sext = terms.mk_app(
        ay_core::Symbol::indexed("sign_extend", vec![1]),
        vec![a],
        Sort::bitvec(3),
    );
    let new_top = terms.mk_app(
        ay_core::Symbol::indexed("extract", vec![2, 2]),
        vec![sext],
        Sort::bitvec(1),
    );
    let sign = terms.mk_app(
        ay_core::Symbol::indexed("extract", vec![1, 1]),
        vec![a],
        Sort::bitvec(1),
    );
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![new_top, sign], Sort::Bool);
    validate_theory_lemma_strict(&terms, vec![eq], TheoryLemmaKind::BvBitBlast)
        .expect("sign_extend must replicate the sign bit and be accepted");
}

/// Forgery: claims `zero_extend` replicates the sign bit (it fills 0). The new
/// top bit of `zero_extend(1, a)` is 0, not `a`'s sign, so this is false when
/// the sign bit is 1 -- the checker must reject it.
#[test]
fn test_bv_bitblast_rejects_zero_extend_as_sign_forgery() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(2));
    let zext = terms.mk_app(
        ay_core::Symbol::indexed("zero_extend", vec![1]),
        vec![a],
        Sort::bitvec(3),
    );
    let new_top = terms.mk_app(
        ay_core::Symbol::indexed("extract", vec![2, 2]),
        vec![zext],
        Sort::bitvec(1),
    );
    let sign = terms.mk_app(
        ay_core::Symbol::indexed("extract", vec![1, 1]),
        vec![a],
        Sort::bitvec(1),
    );
    let eq = terms.mk_app(ay_core::Symbol::named("="), vec![new_top, sign], Sort::Bool);
    let err = validate_theory_lemma_strict(&terms, vec![eq], TheoryLemmaKind::BvBitBlast)
        .expect_err("forged zero_extend-as-sign lemma must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

// ============================================================================
// SELF-PROVING BV semantics in trust compilation.
//
// For every QF_BV operator, the *trusted bit-blast checker* exhaustively proves
// `(op a b) == <ground-truth ite-table>` over all width-3 inputs by re-deriving
// the op's semantics itself and enumerating every assignment. No external solver
// or oracle is consulted at run time: the trust kernel is the prover. A forged
// table (the wrong op's truth table) is rejected, so acceptance is not vacuous.
// ============================================================================

const SP_W: u32 = 3; // <= MAX_BOUNDED_BV_WIDTH; 2*SP_W = 6 <= MAX_BOUNDED_ASSIGNMENT_BITS

fn sp_mask(w: u32) -> u128 {
    (1u128 << w) - 1
}
fn sp_to_signed(v: u128, w: u32) -> i128 {
    if (v >> (w - 1)) & 1 == 1 {
        v as i128 - (1i128 << w)
    } else {
        v as i128
    }
}
fn sp_from_signed(s: i128, w: u32) -> u128 {
    (s as u128) & sp_mask(w)
}

fn sp_unary(op: &str, a: u128, w: u32) -> u128 {
    let m = sp_mask(w);
    match op {
        "bvnot" => !a & m,
        "bvneg" => a.wrapping_neg() & m,
        _ => unreachable!(),
    }
}
fn sp_binary(op: &str, a: u128, b: u128, w: u32) -> u128 {
    let m = sp_mask(w);
    let sa = sp_to_signed(a, w);
    let sb = sp_to_signed(b, w);
    match op {
        "bvadd" => a.wrapping_add(b) & m,
        "bvsub" => a.wrapping_sub(b) & m,
        "bvmul" => a.wrapping_mul(b) & m,
        "bvand" => a & b,
        "bvor" => a | b,
        "bvxor" => a ^ b,
        "bvnand" => !(a & b) & m,
        "bvnor" => !(a | b) & m,
        "bvxnor" => !(a ^ b) & m,
        "bvshl" => {
            if b >= u128::from(w) {
                0
            } else {
                (a << b) & m
            }
        }
        "bvlshr" => {
            if b >= u128::from(w) {
                0
            } else {
                a >> b
            }
        }
        "bvashr" => {
            if b >= u128::from(w) {
                if (a >> (w - 1)) & 1 == 1 {
                    m
                } else {
                    0
                }
            } else {
                sp_from_signed(sa >> b, w)
            }
        }
        "bvudiv" => a.checked_div(b).unwrap_or(m),
        "bvurem" => {
            if b == 0 {
                a
            } else {
                a % b
            }
        }
        "bvsdiv" => {
            if sb == 0 {
                sp_from_signed(if sa >= 0 { -1 } else { 1 }, w)
            } else {
                sp_from_signed(sa / sb, w)
            }
        }
        "bvsrem" => {
            if sb == 0 {
                a
            } else {
                sp_from_signed(sa % sb, w)
            }
        }
        "bvsmod" => {
            if sb == 0 {
                a
            } else {
                let r = sa % sb;
                let m2 = if r == 0 || (r < 0) == (sb < 0) {
                    r
                } else {
                    r + sb
                };
                sp_from_signed(m2, w)
            }
        }
        "concat" => (a << w) | b,
        _ => unreachable!(),
    }
}
fn sp_cmp(op: &str, a: u128, b: u128, w: u32) -> bool {
    let sa = sp_to_signed(a, w);
    let sb = sp_to_signed(b, w);
    match op {
        "bvult" => a < b,
        "bvule" => a <= b,
        "bvugt" => a > b,
        "bvuge" => a >= b,
        "bvslt" => sa < sb,
        "bvsle" => sa <= sb,
        "bvsgt" => sa > sb,
        "bvsge" => sa >= sb,
        _ => unreachable!(),
    }
}

fn sp_lit(terms: &mut TermStore, v: u128, w: u32) -> TermId {
    terms.mk_bitvec(BigInt::from(v as u64), w)
}
fn sp_eq(terms: &mut TermStore, x: TermId, y: TermId) -> TermId {
    terms.mk_app(ay_core::Symbol::named("="), vec![x, y], Sort::Bool)
}

/// ite-table over `a` (width `in_w`) with `vals[a]` as a width-`leaf_w` literal.
fn sp_unary_table(
    terms: &mut TermStore,
    a: TermId,
    in_w: u32,
    leaf_w: u32,
    vals: &[u128],
) -> TermId {
    let n = 1usize << in_w;
    let mut acc = sp_lit(terms, vals[n - 1], leaf_w);
    for ai in (0..n - 1).rev() {
        let leaf = sp_lit(terms, vals[ai], leaf_w);
        let alit = sp_lit(terms, ai as u128, in_w);
        let cond = sp_eq(terms, a, alit);
        acc = terms.mk_ite(cond, leaf, acc);
    }
    acc
}
fn sp_binary_row(terms: &mut TermStore, b: TermId, in_w: u32, leaf_w: u32, row: &[u128]) -> TermId {
    let n = 1usize << in_w;
    let mut acc = sp_lit(terms, row[n - 1], leaf_w);
    for bi in (0..n - 1).rev() {
        let leaf = sp_lit(terms, row[bi], leaf_w);
        let blit = sp_lit(terms, bi as u128, in_w);
        let cond = sp_eq(terms, b, blit);
        acc = terms.mk_ite(cond, leaf, acc);
    }
    acc
}
fn sp_binary_table(
    terms: &mut TermStore,
    a: TermId,
    b: TermId,
    in_w: u32,
    leaf_w: u32,
    vals: &[Vec<u128>],
) -> TermId {
    let n = 1usize << in_w;
    let mut acc = sp_binary_row(terms, b, in_w, leaf_w, &vals[n - 1]);
    for ai in (0..n - 1).rev() {
        let row = sp_binary_row(terms, b, in_w, leaf_w, &vals[ai]);
        let alit = sp_lit(terms, ai as u128, in_w);
        let cond = sp_eq(terms, a, alit);
        acc = terms.mk_ite(cond, row, acc);
    }
    acc
}
fn sp_bool_row(terms: &mut TermStore, b: TermId, in_w: u32, row: &[bool]) -> TermId {
    let n = 1usize << in_w;
    let mut acc = terms.mk_bool(row[n - 1]);
    for bi in (0..n - 1).rev() {
        let leaf = terms.mk_bool(row[bi]);
        let blit = sp_lit(terms, bi as u128, in_w);
        let cond = sp_eq(terms, b, blit);
        acc = terms.mk_ite(cond, leaf, acc);
    }
    acc
}
fn sp_bool_table(
    terms: &mut TermStore,
    a: TermId,
    b: TermId,
    in_w: u32,
    vals: &[Vec<bool>],
) -> TermId {
    let n = 1usize << in_w;
    let mut acc = sp_bool_row(terms, b, in_w, &vals[n - 1]);
    for ai in (0..n - 1).rev() {
        let row = sp_bool_row(terms, b, in_w, &vals[ai]);
        let alit = sp_lit(terms, ai as u128, in_w);
        let cond = sp_eq(terms, a, alit);
        acc = terms.mk_ite(cond, row, acc);
    }
    acc
}

fn sp_validate(terms: &TermStore, eq: TermId, what: &str) {
    validate_theory_lemma_strict(terms, vec![eq], TheoryLemmaKind::BvBitBlast)
        .unwrap_or_else(|e| panic!("trusted checker must self-prove {what}: {e:?}"));
}

const SP_BINARY: [&str; 17] = [
    "bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor", "bvshl",
    "bvlshr", "bvashr", "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod",
];
const SP_CMP: [&str; 8] = [
    "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
];

/// The trust kernel self-proves every unary, same-width binary, and comparison
/// operator against its full ground-truth table at width 3.
#[test]
fn bv_checker_self_proves_same_width_ops() {
    let w = SP_W;
    let n = 1usize << w;

    for op in ["bvnot", "bvneg"] {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::bitvec(w));
        let lhs = terms.mk_app(ay_core::Symbol::named(op), vec![a], Sort::bitvec(w));
        let vals: Vec<u128> = (0..n).map(|ai| sp_unary(op, ai as u128, w)).collect();
        let table = sp_unary_table(&mut terms, a, w, w, &vals);
        let eq = sp_eq(&mut terms, lhs, table);
        sp_validate(&terms, eq, op);
    }
    for op in SP_BINARY {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::bitvec(w));
        let b = terms.mk_var("b", Sort::bitvec(w));
        let lhs = terms.mk_app(ay_core::Symbol::named(op), vec![a, b], Sort::bitvec(w));
        let vals: Vec<Vec<u128>> = (0..n)
            .map(|ai| {
                (0..n)
                    .map(|bi| sp_binary(op, ai as u128, bi as u128, w))
                    .collect()
            })
            .collect();
        let table = sp_binary_table(&mut terms, a, b, w, w, &vals);
        let eq = sp_eq(&mut terms, lhs, table);
        sp_validate(&terms, eq, op);
    }
    for op in SP_CMP {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::bitvec(w));
        let b = terms.mk_var("b", Sort::bitvec(w));
        let lhs = terms.mk_app(ay_core::Symbol::named(op), vec![a, b], Sort::Bool);
        let vals: Vec<Vec<bool>> = (0..n)
            .map(|ai| {
                (0..n)
                    .map(|bi| sp_cmp(op, ai as u128, bi as u128, w))
                    .collect()
            })
            .collect();
        let table = sp_bool_table(&mut terms, a, b, w, &vals);
        let eq = sp_eq(&mut terms, lhs, table);
        sp_validate(&terms, eq, op);
    }
}

/// The trust kernel self-proves the width-changing / indexed operators
/// (concat, extract, zero/sign extend, repeat, rotate) against ground truth.
///
/// Uses width 2 so every result stays within the checker's `MAX_BOUNDED_BV_WIDTH`
/// (4) — the bound that keeps the validator from re-bit-blasting wide terms.
#[test]
fn bv_checker_self_proves_width_changing_ops() {
    let w = 2u32;
    let n = 1usize << w;

    // concat(a,b): result width 2w (=4), a is the high half.
    {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::bitvec(w));
        let b = terms.mk_var("b", Sort::bitvec(w));
        let lhs = terms.mk_app(
            ay_core::Symbol::named("concat"),
            vec![a, b],
            Sort::bitvec(2 * w),
        );
        let vals: Vec<Vec<u128>> = (0..n)
            .map(|ai| {
                (0..n)
                    .map(|bi| sp_binary("concat", ai as u128, bi as u128, w))
                    .collect()
            })
            .collect();
        let table = sp_binary_table(&mut terms, a, b, w, 2 * w, &vals);
        let eq = sp_eq(&mut terms, lhs, table);
        sp_validate(&terms, eq, "concat");
    }

    // Unary indexed ops: each maps input `a` to a width-`leaf_w` result (all <= 4).
    type UnaryIndexedOp = (&'static str, Vec<u32>, u32, Box<dyn Fn(u128) -> u128>);
    let unary_indexed: [UnaryIndexedOp; 7] = [
        ("zero_extend", vec![2], w + 2, Box::new(move |a| a)),
        (
            "sign_extend",
            vec![2],
            w + 2,
            Box::new(move |a| {
                if (a >> (w - 1)) & 1 == 1 {
                    (a | (sp_mask(w + 2) ^ sp_mask(w))) & sp_mask(w + 2)
                } else {
                    a
                }
            }),
        ),
        (
            "sign_extend",
            vec![1],
            w + 1,
            Box::new(move |a| {
                if (a >> (w - 1)) & 1 == 1 {
                    (a | (sp_mask(w + 1) ^ sp_mask(w))) & sp_mask(w + 1)
                } else {
                    a
                }
            }),
        ),
        ("extract", vec![1, 1], 1, Box::new(move |a| (a >> 1) & 1)),
        ("repeat", vec![2], 2 * w, Box::new(move |a| (a << w) | a)),
        (
            "rotate_left",
            vec![1],
            w,
            Box::new(move |a| ((a << 1) | (a >> (w - 1))) & sp_mask(w)),
        ),
        (
            "rotate_right",
            vec![1],
            w,
            Box::new(move |a| ((a >> 1) | (a << (w - 1))) & sp_mask(w)),
        ),
    ];
    for (name, idx, leaf_w, f) in unary_indexed {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::bitvec(w));
        let lhs = terms.mk_app(
            ay_core::Symbol::indexed(name, idx.clone()),
            vec![a],
            Sort::bitvec(leaf_w),
        );
        let vals: Vec<u128> = (0..n).map(|ai| f(ai as u128)).collect();
        let table = sp_unary_table(&mut terms, a, w, leaf_w, &vals);
        let eq = sp_eq(&mut terms, lhs, table);
        sp_validate(&terms, eq, &format!("{name}{idx:?}"));
    }
}

/// Acceptance is not vacuous: a forged table (a *different* op's truth table) is
/// rejected by the trust kernel.
#[test]
fn bv_checker_self_proving_rejects_forged_tables() {
    let w = SP_W;
    let n = 1usize << w;
    for (op, wrong) in [
        ("bvmul", "bvadd"),
        ("bvsdiv", "bvudiv"),
        ("bvsmod", "bvsrem"),
        ("bvand", "bvor"),
        ("bvashr", "bvlshr"),
    ] {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::bitvec(w));
        let b = terms.mk_var("b", Sort::bitvec(w));
        let lhs = terms.mk_app(ay_core::Symbol::named(op), vec![a, b], Sort::bitvec(w));
        let vals: Vec<Vec<u128>> = (0..n)
            .map(|ai| {
                (0..n)
                    .map(|bi| sp_binary(wrong, ai as u128, bi as u128, w))
                    .collect()
            })
            .collect();
        let table = sp_binary_table(&mut terms, a, b, w, w, &vals);
        let eq = sp_eq(&mut terms, lhs, table);
        let err = validate_theory_lemma_strict(&terms, vec![eq], TheoryLemmaKind::BvBitBlast)
            .expect_err(&format!("{op} must NOT validate against the {wrong} table"));
        assert!(
            matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
            "expected InvalidTheoryLemma for {op} vs {wrong}, got {err:?}"
        );
    }
}

// ============================================================================
// BoolTautology: accept genuine propositional tautologies, reject the rest.
// ============================================================================

#[test]
fn bool_tautology_accepts_double_negation_and_rejects_nontautologies() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_ = |terms: &mut TermStore, a: TermId| terms.mk_not_raw(a);
    let app2 = |terms: &mut TermStore, op: &str, a: TermId, b: TermId| {
        terms.mk_app(ay_core::Symbol::named(op), vec![a, b], Sort::Bool)
    };

    // (= (not (not p)) p) — double-negation elimination, a tautology.
    let nnp = {
        let np = not_(&mut terms, p);
        not_(&mut terms, np)
    };
    let dne = app2(&mut terms, "=", nnp, p);
    assert!(
        validate_theory_lemma_strict(&terms, vec![dne], TheoryLemmaKind::BoolTautology).is_ok(),
        "double-negation elimination must validate"
    );

    // (= p (not p)) — always FALSE, must be rejected.
    let np = not_(&mut terms, p);
    let contradiction = app2(&mut terms, "=", p, np);
    assert!(
        validate_theory_lemma_strict(&terms, vec![contradiction], TheoryLemmaKind::BoolTautology)
            .is_err(),
        "(= p (not p)) is a contradiction, not a tautology"
    );

    // (or p q) — true for some assignments, false for others; not a tautology.
    let orpq = app2(&mut terms, "or", p, q);
    assert!(
        validate_theory_lemma_strict(&terms, vec![orpq], TheoryLemmaKind::BoolTautology).is_err(),
        "(or p q) is satisfiable-but-not-valid, not a tautology"
    );

    // A non-Bool literal must be rejected (purely propositional clauses only).
    let xi = terms.mk_var("xi", Sort::Int);
    assert!(
        validate_theory_lemma_strict(&terms, vec![xi], TheoryLemmaKind::BoolTautology).is_err(),
        "non-Bool literal must be rejected"
    );
}

// ============================================================================
// IteSame: accept (= (ite c x x) x), reject everything else.
// ============================================================================

#[test]
fn ite_same_accepts_identical_branches_and_rejects_the_rest() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let eq = |terms: &mut TermStore, x: TermId, y: TermId| {
        terms.mk_app(ay_core::Symbol::named("="), vec![x, y], Sort::Bool)
    };

    // (= (ite c a a) a) — identical branches equal to the other side: VALID.
    let ite_aa = terms.mk_ite_raw(c, a, a);
    let good = eq(&mut terms, ite_aa, a);
    assert!(
        validate_theory_lemma_strict(&terms, vec![good], TheoryLemmaKind::IteSame).is_ok(),
        "(= (ite c a a) a) must validate"
    );

    // (= (ite c a b) a) — DIFFERENT branches (a != b): not a tautology, reject.
    let ite_ab = terms.mk_ite_raw(c, a, b);
    let diff_branches = eq(&mut terms, ite_ab, a);
    assert!(
        validate_theory_lemma_strict(&terms, vec![diff_branches], TheoryLemmaKind::IteSame)
            .is_err(),
        "(= (ite c a b) a) with distinct branches must be rejected"
    );

    // (= (ite c a a) b) — equal branches but the OTHER side differs: reject.
    let ite_aa2 = terms.mk_ite_raw(c, a, a);
    let wrong_value = eq(&mut terms, ite_aa2, b);
    assert!(
        validate_theory_lemma_strict(&terms, vec![wrong_value], TheoryLemmaKind::IteSame).is_err(),
        "(= (ite c a a) b) with b != a must be rejected"
    );

    // (= (f a) a) — not an ite at all: reject.
    let fa = terms.mk_app(ay_core::Symbol::named("f"), vec![a], Sort::Int);
    let not_ite = eq(&mut terms, fa, a);
    assert!(
        validate_theory_lemma_strict(&terms, vec![not_ite], TheoryLemmaKind::IteSame).is_err(),
        "a non-ite equality must be rejected"
    );
}
