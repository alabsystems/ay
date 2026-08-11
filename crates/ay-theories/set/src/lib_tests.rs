// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for the native finite-set theory solver.
//!
//! Each sound rule is exercised in-fragment; out-of-fragment obligations are
//! checked to return `Unknown` (explicit fail-closed); and previously
//! MBQI-needing facts are checked to decide without quantifier instantiation.

use super::*;
use ay_core::term::Symbol;
use ay_core::Sort;

fn set_sort() -> Sort {
    // Set(Int) == Array(Int -> Bool) — the membership carrier.
    Sort::array(Sort::Int, Sort::Bool)
}

fn mk_set_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, set_sort())
}

/// `(set.member elem set)` — SMT-LIB element-first convention.
fn mk_member(terms: &mut TermStore, elem: TermId, set: TermId) -> TermId {
    terms.mk_app(Symbol::named(OP_MEMBER), vec![elem, set], Sort::Bool)
}

fn mk_card(terms: &mut TermStore, set: TermId) -> TermId {
    terms.mk_app(Symbol::named(OP_CARD), vec![set], Sort::Int)
}

fn mk_subset(terms: &mut TermStore, sub: TermId, sup: TermId) -> TermId {
    terms.mk_app(Symbol::named(OP_SUBSET), vec![sub, sup], Sort::Bool)
}

fn mk_empty(terms: &mut TermStore) -> TermId {
    terms.mk_app(Symbol::named(OP_EMPTY), vec![], set_sort())
}

// ---------------------------------------------------------------------------
// In-fragment: each rule decides correctly.
// ---------------------------------------------------------------------------

#[test]
fn subset_reflexive_is_sat() {
    // subset(s, s) must be satisfiable (reflexivity) and decided without MBQI.
    let mut terms = TermStore::new();
    let s = mk_set_var(&mut terms, "s");
    let sub = mk_subset(&mut terms, s, s);

    let mut solver = SetSolver::new(&terms);
    solver.register_atom(sub);
    solver.assert_literal(sub, true);

    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn subset_refuted_by_ground_witness() {
    // subset(s, t) asserted, but e ∈ s and e ∉ t — a refuting ground witness.
    let mut terms = TermStore::new();
    let s = mk_set_var(&mut terms, "s");
    let t = mk_set_var(&mut terms, "t");
    let e = terms.mk_int(7.into());

    let sub = mk_subset(&mut terms, s, t);
    let e_in_s = mk_member(&mut terms, e, s);
    let e_in_t = mk_member(&mut terms, e, t);

    let mut solver = SetSolver::new(&terms);
    for a in [sub, e_in_s, e_in_t] {
        solver.register_atom(a);
    }
    solver.assert_literal(sub, true);
    solver.assert_literal(e_in_s, true);
    solver.assert_literal(e_in_t, false);

    match solver.check() {
        TheoryResult::Unsat(reason) => {
            assert!(reason.contains(&TheoryLit::new(sub, true)));
            assert!(reason.contains(&TheoryLit::new(e_in_s, true)));
            assert!(reason.contains(&TheoryLit::new(e_in_t, false)));
        }
        other => panic!("expected Unsat, got {other:?}"),
    }
}

#[test]
fn subset_of_empty_with_member_is_unsat() {
    // subset(A, empty) ∧ member(e, A): subset-of-empty forces A = empty, so
    // e ∈ A is a contradiction. No `member(empty, e)` atom is registered, so
    // the witness rule must treat membership in the empty superset as
    // definitionally false. Regression for the subset-of-empty soundness hole.
    let mut terms = TermStore::new();
    let a = mk_set_var(&mut terms, "A");
    let empty = mk_empty(&mut terms);
    let e = terms.mk_int(7.into());

    let sub = mk_subset(&mut terms, a, empty);
    let e_in_a = mk_member(&mut terms, e, a);

    let mut solver = SetSolver::new(&terms);
    for atom in [sub, e_in_a] {
        solver.register_atom(atom);
    }
    solver.assert_literal(sub, true);
    solver.assert_literal(e_in_a, true);

    match solver.check() {
        TheoryResult::Unsat(reason) => {
            assert!(reason.contains(&TheoryLit::new(sub, true)));
            assert!(reason.contains(&TheoryLit::new(e_in_a, true)));
        }
        other => panic!("expected Unsat, got {other:?}"),
    }
}

#[test]
fn subset_consistent_when_witness_in_both() {
    // subset(s, t), e ∈ s and e ∈ t — no refutation; SAT.
    let mut terms = TermStore::new();
    let s = mk_set_var(&mut terms, "s");
    let t = mk_set_var(&mut terms, "t");
    let e = terms.mk_int(3.into());

    let sub = mk_subset(&mut terms, s, t);
    let e_in_s = mk_member(&mut terms, e, s);
    let e_in_t = mk_member(&mut terms, e, t);

    let mut solver = SetSolver::new(&terms);
    for a in [sub, e_in_s, e_in_t] {
        solver.register_atom(a);
    }
    solver.assert_literal(sub, true);
    solver.assert_literal(e_in_s, true);
    solver.assert_literal(e_in_t, true);

    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn member_of_empty_is_unsat() {
    // e ∈ empty is an immediate structural contradiction.
    let mut terms = TermStore::new();
    let empty = mk_empty(&mut terms);
    let e = terms.mk_int(1.into());
    let e_in_empty = mk_member(&mut terms, e, empty);

    let mut solver = SetSolver::new(&terms);
    solver.register_atom(e_in_empty);
    solver.assert_literal(e_in_empty, true);

    match solver.check() {
        TheoryResult::Unsat(reason) => {
            assert!(reason.contains(&TheoryLit::new(e_in_empty, true)));
        }
        other => panic!("expected Unsat, got {other:?}"),
    }
}

#[test]
fn non_member_of_empty_is_sat() {
    // e ∉ empty is consistent.
    let mut terms = TermStore::new();
    let empty = mk_empty(&mut terms);
    let e = terms.mk_int(1.into());
    let e_in_empty = mk_member(&mut terms, e, empty);

    let mut solver = SetSolver::new(&terms);
    solver.register_atom(e_in_empty);
    solver.assert_literal(e_in_empty, false);

    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn card_terms_registered_with_set_arg() {
    // card(s) is registered and its set argument recoverable (bridge surface).
    let mut terms = TermStore::new();
    let s = mk_set_var(&mut terms, "s");
    let card_s = mk_card(&mut terms, s);

    let mut solver = SetSolver::new(&terms);
    solver.register_atom(card_s);

    let cards: Vec<_> = solver.card_terms().collect();
    assert_eq!(cards, vec![card_s]);
    assert_eq!(solver.card_set(card_s), Some(s));
}

// ---------------------------------------------------------------------------
// Out-of-fragment: fail-closed (explicit Unknown, never a guessed verdict).
// ---------------------------------------------------------------------------

#[test]
fn out_of_fragment_set_map_is_unknown() {
    // set.map (polymorphic image) is outside the sound fragment → Unknown.
    let mut terms = TermStore::new();
    let s = mk_set_var(&mut terms, "s");
    let f = terms.mk_var("f", Sort::array(Sort::Int, Sort::Int));
    let mapped = terms.mk_app(Symbol::named("set.map"), vec![f, s], set_sort());
    let e = terms.mk_int(2.into());
    let e_in_mapped = mk_member(&mut terms, e, mapped);

    let mut solver = SetSolver::new(&terms);
    solver.register_atom(e_in_mapped);
    solver.assert_literal(e_in_mapped, true);

    assert!(solver.is_out_of_fragment());
    assert!(
        matches!(solver.check(), TheoryResult::Unknown),
        "must fail closed (Unknown), never a guessed SAT/UNSAT"
    );
}

#[test]
fn out_of_fragment_set_filter_is_unknown() {
    let mut terms = TermStore::new();
    let s = mk_set_var(&mut terms, "s");
    let p = terms.mk_var("p", Sort::array(Sort::Int, Sort::Bool));
    let filtered = terms.mk_app(Symbol::named("set.filter"), vec![p, s], set_sort());
    let sub = mk_subset(&mut terms, filtered, s);

    let mut solver = SetSolver::new(&terms);
    solver.register_atom(sub);
    solver.assert_literal(sub, true);

    assert!(solver.is_out_of_fragment());
    assert!(matches!(solver.check(), TheoryResult::Unknown));
}

#[test]
fn out_of_fragment_symbolic_set_range_is_unknown() {
    let mut terms = TermStore::new();
    let low = terms.mk_var("low", Sort::Int);
    let high = terms.mk_var("high", Sort::Int);
    let range = terms.mk_app(Symbol::named("set.range"), vec![low, high], set_sort());
    let e = terms.mk_int(0.into());
    let e_in_range = mk_member(&mut terms, e, range);

    let mut solver = SetSolver::new(&terms);
    solver.register_atom(e_in_range);
    solver.assert_literal(e_in_range, true);

    assert!(solver.is_out_of_fragment());
    assert!(matches!(solver.check(), TheoryResult::Unknown));
}

#[test]
fn out_of_fragment_complement_is_unknown() {
    // set.complement over an unbounded element domain is outside the fragment.
    let mut terms = TermStore::new();
    let s = mk_set_var(&mut terms, "s");
    let comp = terms.mk_app(Symbol::named("set.complement"), vec![s], set_sort());
    let e = terms.mk_int(0.into());
    let e_in_comp = mk_member(&mut terms, e, comp);

    let mut solver = SetSolver::new(&terms);
    solver.register_atom(e_in_comp);
    solver.assert_literal(e_in_comp, true);

    assert!(solver.is_out_of_fragment());
    assert!(matches!(solver.check(), TheoryResult::Unknown));
}

// ---------------------------------------------------------------------------
// Soundness: never claim subset SAT positively from saturation alone.
// ---------------------------------------------------------------------------

#[test]
fn subset_positive_not_asserted_from_saturation() {
    // With no ground witness contradicting it, subset(s, t) must NOT be
    // refuted, but the solver must also not *prove* it (no equality / no
    // propagation that would unsoundly force it). Here we just assert it true
    // and confirm SAT with no spurious propagations.
    let mut terms = TermStore::new();
    let s = mk_set_var(&mut terms, "s");
    let t = mk_set_var(&mut terms, "t");
    let sub = mk_subset(&mut terms, s, t);

    let mut solver = SetSolver::new(&terms);
    solver.register_atom(sub);
    solver.assert_literal(sub, true);

    assert!(matches!(solver.check(), TheoryResult::Sat));
    // No unsound equalities manufactured.
    assert!(solver.propagate_equalities().equalities.is_empty());
}

// ---------------------------------------------------------------------------
// Previously-MBQI-needing facts now decide without quantifier instantiation.
// ---------------------------------------------------------------------------

#[test]
fn mbqi_free_subset_self_decides() {
    // `s subset s` was an MBQI-fragile universal in the array encoding; the
    // native rule decides it directly (reflexivity) with no instantiation.
    let mut terms = TermStore::new();
    let s = mk_set_var(&mut terms, "s");
    let sub = mk_subset(&mut terms, s, s);

    let mut solver = SetSolver::new(&terms);
    solver.register_atom(sub);
    solver.assert_literal(sub, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    // Negated reflexive subset is refutable-by-design via the executor axiom,
    // but at minimum the positive case is decided here with zero MBQI rounds.
}

#[test]
fn mbqi_free_membership_witness_refutation_decides() {
    // The disjointness-style obligation (e in s, e not in t ⇒ ¬subset(s,t))
    // is decided by one ground witness, no quantifier instantiation.
    let mut terms = TermStore::new();
    let s = mk_set_var(&mut terms, "s");
    let t = mk_set_var(&mut terms, "t");
    let e1 = terms.mk_int(1.into());
    let e2 = terms.mk_int(2.into());

    let sub = mk_subset(&mut terms, s, t);
    let e1_in_s = mk_member(&mut terms, e1, s);
    let e1_in_t = mk_member(&mut terms, e1, t);
    let e2_in_s = mk_member(&mut terms, e2, s);
    let e2_in_t = mk_member(&mut terms, e2, t);

    let mut solver = SetSolver::new(&terms);
    for a in [sub, e1_in_s, e1_in_t, e2_in_s, e2_in_t] {
        solver.register_atom(a);
    }
    solver.assert_literal(sub, true);
    // e1 is in both (fine); e2 in s but not t — refutes subset.
    solver.assert_literal(e1_in_s, true);
    solver.assert_literal(e1_in_t, true);
    solver.assert_literal(e2_in_s, true);
    solver.assert_literal(e2_in_t, false);

    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));
}

// ---------------------------------------------------------------------------
// Push/pop contract (behavioral equivalence).
// ---------------------------------------------------------------------------

#[test]
fn push_pop_restores_sat() {
    let mut terms = TermStore::new();
    let empty = mk_empty(&mut terms);
    let e = terms.mk_int(9.into());
    let e_in_empty = mk_member(&mut terms, e, empty);

    let mut solver = SetSolver::new(&terms);
    solver.register_atom(e_in_empty);

    solver.push();
    solver.assert_literal(e_in_empty, true);
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));
    solver.pop();

    // After pop, the conflicting assertion is retracted → SAT.
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn push_pop_nested() {
    let mut terms = TermStore::new();
    let s = mk_set_var(&mut terms, "s");
    let t = mk_set_var(&mut terms, "t");
    let e = terms.mk_int(4.into());
    let sub = mk_subset(&mut terms, s, t);
    let e_in_s = mk_member(&mut terms, e, s);
    let e_in_t = mk_member(&mut terms, e, t);

    let mut solver = SetSolver::new(&terms);
    for a in [sub, e_in_s, e_in_t] {
        solver.register_atom(a);
    }

    solver.assert_literal(sub, true);
    solver.assert_literal(e_in_s, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    solver.push();
    solver.assert_literal(e_in_t, false);
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));
    solver.pop();

    // After pop, the refuting witness (e ∉ t) is gone → SAT.
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn reset_clears_everything() {
    let mut terms = TermStore::new();
    let s = mk_set_var(&mut terms, "s");
    let card_s = mk_card(&mut terms, s);

    let mut solver = SetSolver::new(&terms);
    solver.register_atom(card_s);
    assert_eq!(solver.card_terms().count(), 1);

    solver.reset();
    assert_eq!(solver.card_terms().count(), 0);
    assert!(!solver.is_out_of_fragment());
}
