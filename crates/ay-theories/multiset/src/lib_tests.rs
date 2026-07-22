// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for the native multiset theory solver.
//!
//! Each sound structural rule is exercised in-fragment; out-of-fragment
//! obligations are checked to return `Unknown` (explicit fail-closed); and the
//! carrier-shape registration (count atoms, empty terms, subset atoms) is
//! checked. The count *arithmetic* rules (count(empty)=0, count>=0,
//! insert/remove) are ground axioms injected by the executor and exercised in
//! the executor-level end-to-end tests.

use super::*;
use ay_core::term::Symbol;
use ay_core::Sort;

fn multiset_sort() -> Sort {
    // Multiset(Int) == Array(Int -> Int) — the count carrier.
    Sort::array(Sort::Int, Sort::Int)
}

fn mk_multiset_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, multiset_sort())
}

/// `(multiset.count elem multiset)` — SMT-LIB element-first convention.
fn mk_count(terms: &mut TermStore, elem: TermId, multiset: TermId) -> TermId {
    terms.mk_app(Symbol::named(OP_COUNT), vec![elem, multiset], Sort::Int)
}

/// `(select multiset elem)` — the elaborated count shape over the carrier.
fn mk_select_count(terms: &mut TermStore, multiset: TermId, elem: TermId) -> TermId {
    terms.mk_select(multiset, elem)
}

fn mk_subset(terms: &mut TermStore, sub: TermId, sup: TermId) -> TermId {
    terms.mk_app(Symbol::named(OP_SUBSET), vec![sub, sup], Sort::Bool)
}

fn mk_empty(terms: &mut TermStore) -> TermId {
    terms.mk_app(Symbol::named(OP_EMPTY), vec![], multiset_sort())
}

// ---------------------------------------------------------------------------
// In-fragment: structural rules decide correctly.
// ---------------------------------------------------------------------------

#[test]
fn subset_reflexive_is_sat() {
    // subset(m, m) must be satisfiable (reflexivity) and decided without MBQI.
    let mut terms = TermStore::new();
    let m = mk_multiset_var(&mut terms, "m");
    let sub = mk_subset(&mut terms, m, m);

    let mut solver = MultisetSolver::new(&terms);
    solver.register_atom(sub);
    solver.assert_literal(sub, true);

    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn subset_self_negation_is_unsat() {
    // ¬subset(m, m) is unsatisfiable by reflexivity, no quantifier needed.
    let mut terms = TermStore::new();
    let m = mk_multiset_var(&mut terms, "m");
    let sub = mk_subset(&mut terms, m, m);

    let mut solver = MultisetSolver::new(&terms);
    solver.register_atom(sub);
    solver.assert_literal(sub, false);

    match solver.check() {
        TheoryResult::Unsat(reason) => {
            assert!(reason.contains(&TheoryLit::new(sub, false)));
        }
        other => panic!("expected Unsat, got {other:?}"),
    }
}

#[test]
fn count_atoms_registered_via_select_carrier() {
    // count(m, e) is elaborated to select(m, e) over Array(Int -> Int) and must
    // register as a count atom with its multiset recoverable.
    let mut terms = TermStore::new();
    let m = mk_multiset_var(&mut terms, "m");
    let e = terms.mk_int(7.into());
    let count = mk_select_count(&mut terms, m, e);

    let mut solver = MultisetSolver::new(&terms);
    solver.register_atom(count);

    let counts: Vec<_> = solver.count_terms().collect();
    assert_eq!(counts, vec![count]);
    assert_eq!(solver.count_multiset(count), Some(m));
    assert_eq!(solver.count_atom_count(), 1);
}

#[test]
fn count_atoms_registered_via_named_op() {
    // Raw `multiset.count` apps (element-first) also register as count atoms.
    let mut terms = TermStore::new();
    let m = mk_multiset_var(&mut terms, "m");
    let e = terms.mk_int(3.into());
    let count = mk_count(&mut terms, e, m);

    let mut solver = MultisetSolver::new(&terms);
    solver.register_atom(count);

    assert_eq!(solver.count_atom_count(), 1);
    assert_eq!(solver.count_multiset(count), Some(m));
}

#[test]
fn count_term_and_ground_elements_recoverable() {
    // The witness universe and per-element count read are recoverable for the
    // executor's subset↔count obligation generation.
    let mut terms = TermStore::new();
    let m = mk_multiset_var(&mut terms, "m");
    let n = mk_multiset_var(&mut terms, "n");
    let e = terms.mk_int(5.into());
    let cm = mk_select_count(&mut terms, m, e);
    let cn = mk_select_count(&mut terms, n, e);

    let mut solver = MultisetSolver::new(&terms);
    solver.register_atom(cm);
    solver.register_atom(cn);

    assert_eq!(solver.count_term(m, e), Some(cm));
    assert_eq!(solver.count_term(n, e), Some(cn));
    // Both reads are over the same ground element `e`.
    assert_eq!(solver.ground_elements(), vec![e]);
}

#[test]
fn subset_atoms_registered() {
    let mut terms = TermStore::new();
    let m = mk_multiset_var(&mut terms, "m");
    let n = mk_multiset_var(&mut terms, "n");
    let sub = mk_subset(&mut terms, m, n);

    let mut solver = MultisetSolver::new(&terms);
    solver.register_atom(sub);
    assert_eq!(solver.subset_atom_count(), 1);
}

// ---------------------------------------------------------------------------
// Out-of-fragment: fail-closed (explicit Unknown, never a guessed verdict).
// ---------------------------------------------------------------------------

#[test]
fn out_of_fragment_multiset_map_is_unknown() {
    // multiset.map (polymorphic image) is outside the sound fragment → Unknown.
    let mut terms = TermStore::new();
    let m = mk_multiset_var(&mut terms, "m");
    let f = terms.mk_var("f", Sort::array(Sort::Int, Sort::Int));
    let mapped = terms.mk_app(Symbol::named("multiset.map"), vec![f, m], multiset_sort());
    let e = terms.mk_int(2.into());
    let count = mk_select_count(&mut terms, mapped, e);

    let mut solver = MultisetSolver::new(&terms);
    solver.register_atom(count);
    solver.assert_literal(count, true);

    assert!(solver.is_out_of_fragment());
    assert!(
        matches!(solver.check(), TheoryResult::Unknown),
        "must fail closed (Unknown), never a guessed SAT/UNSAT"
    );
}

#[test]
fn out_of_fragment_multiset_filter_is_unknown() {
    let mut terms = TermStore::new();
    let m = mk_multiset_var(&mut terms, "m");
    let p = terms.mk_var("p", Sort::array(Sort::Int, Sort::Bool));
    let filtered = terms.mk_app(
        Symbol::named("multiset.filter"),
        vec![p, m],
        multiset_sort(),
    );
    let sub = mk_subset(&mut terms, filtered, m);

    let mut solver = MultisetSolver::new(&terms);
    solver.register_atom(sub);
    solver.assert_literal(sub, true);

    assert!(solver.is_out_of_fragment());
    assert!(matches!(solver.check(), TheoryResult::Unknown));
}

#[test]
fn out_of_fragment_union_is_unknown() {
    // multiset.union (count = max) needs a domain comprehension → fail-closed.
    let mut terms = TermStore::new();
    let m = mk_multiset_var(&mut terms, "m");
    let n = mk_multiset_var(&mut terms, "n");
    let u = terms.mk_app(Symbol::named("multiset.union"), vec![m, n], multiset_sort());
    let e = terms.mk_int(0.into());
    let count = mk_select_count(&mut terms, u, e);

    let mut solver = MultisetSolver::new(&terms);
    solver.register_atom(count);
    solver.assert_literal(count, true);

    assert!(solver.is_out_of_fragment());
    assert!(matches!(solver.check(), TheoryResult::Unknown));
}

// ---------------------------------------------------------------------------
// Soundness: never claim subset SAT positively from saturation alone.
// ---------------------------------------------------------------------------

#[test]
fn subset_positive_not_asserted_from_saturation() {
    // With no witness contradicting it, subset(m, n) must NOT be refuted, but
    // the solver must also not *prove* it (no spurious propagation).
    let mut terms = TermStore::new();
    let m = mk_multiset_var(&mut terms, "m");
    let n = mk_multiset_var(&mut terms, "n");
    let sub = mk_subset(&mut terms, m, n);

    let mut solver = MultisetSolver::new(&terms);
    solver.register_atom(sub);
    solver.assert_literal(sub, true);

    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert!(solver.propagate_equalities().equalities.is_empty());
}

// ---------------------------------------------------------------------------
// Push/pop contract (behavioral equivalence).
// ---------------------------------------------------------------------------

#[test]
fn push_pop_restores_sat() {
    let mut terms = TermStore::new();
    let m = mk_multiset_var(&mut terms, "m");
    let sub = mk_subset(&mut terms, m, m);

    let mut solver = MultisetSolver::new(&terms);
    solver.register_atom(sub);

    solver.push();
    solver.assert_literal(sub, false);
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));
    solver.pop();

    // After pop, the conflicting assertion is retracted → SAT.
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn push_pop_nested() {
    let mut terms = TermStore::new();
    let m = mk_multiset_var(&mut terms, "m");
    let n = mk_multiset_var(&mut terms, "n");
    let sub_mn = mk_subset(&mut terms, m, n);
    let sub_mm = mk_subset(&mut terms, m, m);

    let mut solver = MultisetSolver::new(&terms);
    for a in [sub_mn, sub_mm] {
        solver.register_atom(a);
    }

    solver.assert_literal(sub_mn, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    solver.push();
    solver.assert_literal(sub_mm, false);
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));
    solver.pop();

    // After pop, the refuting reflexive negation is gone → SAT.
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn reset_clears_everything() {
    let mut terms = TermStore::new();
    let m = mk_multiset_var(&mut terms, "m");
    let e = terms.mk_int(1.into());
    let count = mk_select_count(&mut terms, m, e);
    let empty = mk_empty(&mut terms);
    let _ = empty;

    let mut solver = MultisetSolver::new(&terms);
    solver.register_atom(count);
    assert_eq!(solver.count_terms().count(), 1);

    solver.reset();
    assert_eq!(solver.count_terms().count(), 0);
    assert!(!solver.is_out_of_fragment());
}
