// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// TheoryLit proofs
// ================

// REQUIRES: true (always valid)
// ENSURES: TheoryLit::new(term, value).term == term
// ENSURES: TheoryLit::new(term, value).value == value
#[kani::proof]
fn proof_theory_lit_construction() {
    let term_id: u32 = kani::any();
    let value: bool = kani::any();
    let term = TermId(term_id);
    let lit = TheoryLit::new(term, value);
    assert_eq!(lit.term, term);
    assert_eq!(lit.value, value);
}

// REQUIRES: term1 != term2
// ENSURES: TheoryLit(term1, v) != TheoryLit(term2, v) (distinct terms produce distinct lits)
#[kani::proof]
fn proof_theory_lit_distinct_terms_not_equal() {
    let term1: u32 = kani::any();
    let term2: u32 = kani::any();
    kani::assume(term1 != term2);
    let value: bool = kani::any();
    let lit1 = TheoryLit::new(TermId(term1), value);
    let lit2 = TheoryLit::new(TermId(term2), value);
    assert_ne!(lit1, lit2, "lits with distinct terms must differ");
}

// REQUIRES: lit1.term == lit2.term && lit1.value == lit2.value
// ENSURES: lit1 == lit2 (equality is based on contents)
#[kani::proof]
fn proof_theory_lit_equality_contents() {
    let term_id: u32 = kani::any();
    let value: bool = kani::any();
    let lit1 = TheoryLit::new(TermId(term_id), value);
    let lit2 = TheoryLit::new(TermId(term_id), value);
    assert_eq!(lit1, lit2);
}

// TheoryConflict proofs
// =====================

// REQUIRES: true
// ENSURES: TheoryConflict::new(lits).farkas.is_none()
#[kani::proof]
fn proof_theory_conflict_new_has_no_farkas() {
    let lit = TheoryLit::new(TermId(kani::any()), kani::any());
    let conflict = TheoryConflict::new(vec![lit]);
    assert!(conflict.farkas.is_none());
}

// REQUIRES: true
// ENSURES: TheoryConflict::new(lits).literals.len() == lits.len()
#[kani::proof]
fn proof_theory_conflict_preserves_literals() {
    let lit1 = TheoryLit::new(TermId(kani::any()), kani::any());
    let lit2 = TheoryLit::new(TermId(kani::any()), kani::any());
    let conflict = TheoryConflict::new(vec![lit1, lit2]);
    assert_eq!(conflict.literals.len(), 2);
}

// DiscoveredEquality proofs
// =========================

// REQUIRES: true
// ENSURES: DiscoveredEquality::new(lhs, rhs, reason) constructs correctly
#[kani::proof]
fn proof_discovered_equality_construction() {
    let lhs_id: u32 = kani::any();
    let rhs_id: u32 = kani::any();
    let lhs = TermId(lhs_id);
    let rhs = TermId(rhs_id);
    let eq = DiscoveredEquality::new(lhs, rhs, vec![]);
    assert_eq!(eq.lhs, lhs);
    assert_eq!(eq.rhs, rhs);
    assert!(eq.reason.is_empty());
}
