// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for the native map theory solver.
//!
//! Each sound structural rule is exercised in-fragment; out-of-fragment
//! obligations are checked to return `Unknown` (explicit fail-closed); and the
//! carrier-shape registration (get/dom reads, empty terms, subset atoms) is
//! checked. The get/dom *read-through* rules (get(insert)=v, dom(empty)=false,
//! contains_key(insert)=true) are decided by the array solver via store/const
//! read-through and exercised in the executor-level end-to-end tests.

use super::*;
use ay_core::term::Symbol;
use ay_core::Sort;

fn value_sort() -> Sort {
    // Map(Int, Int) value carrier == Array(Int -> Int).
    Sort::array(Sort::Int, Sort::Int)
}

fn dom_sort() -> Sort {
    // Domain carrier == Array(Int -> Bool).
    Sort::array(Sort::Int, Sort::Bool)
}

fn mk_map_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, value_sort())
}

/// `(map.get m k)` — raw named op.
fn mk_get(terms: &mut TermStore, map: TermId, key: TermId) -> TermId {
    terms.mk_app(Symbol::named(OP_GET), vec![map, key], Sort::Int)
}

/// `(select value k)` — the elaborated value-read shape over the carrier.
fn mk_select_get(terms: &mut TermStore, value: TermId, key: TermId) -> TermId {
    terms.mk_select(value, key)
}

/// `(map.contains_key m k)` — raw named op.
fn mk_contains(terms: &mut TermStore, map: TermId, key: TermId) -> TermId {
    terms.mk_app(Symbol::named(OP_CONTAINS_KEY), vec![map, key], Sort::Bool)
}

/// `(select (map.dom m) k)` — the elaborated contains_key shape.
fn mk_dom_select(terms: &mut TermStore, map: TermId, key: TermId) -> TermId {
    let dom = terms.mk_app(Symbol::named(OP_DOM), vec![map], dom_sort());
    terms.mk_select(dom, key)
}

fn mk_subset(terms: &mut TermStore, sub: TermId, sup: TermId) -> TermId {
    terms.mk_app(Symbol::named(OP_SUBSET), vec![sub, sup], Sort::Bool)
}

fn mk_empty(terms: &mut TermStore) -> TermId {
    terms.mk_app(Symbol::named(OP_EMPTY), vec![], value_sort())
}

// ---------------------------------------------------------------------------
// In-fragment: structural rules decide correctly.
// ---------------------------------------------------------------------------

#[test]
fn subset_reflexive_is_sat() {
    // subset(m, m) must be satisfiable (reflexivity) and decided without MBQI.
    let mut terms = TermStore::new();
    let m = mk_map_var(&mut terms, "m");
    let sub = mk_subset(&mut terms, m, m);

    let mut solver = MapSolver::new(&terms);
    solver.register_atom(sub);
    solver.assert_literal(sub, true);

    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn subset_self_negation_is_unsat() {
    // ¬subset(m, m) is unsatisfiable by reflexivity, no quantifier needed.
    let mut terms = TermStore::new();
    let m = mk_map_var(&mut terms, "m");
    let sub = mk_subset(&mut terms, m, m);

    let mut solver = MapSolver::new(&terms);
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
fn get_atoms_registered_via_select_carrier() {
    // get(m, k) is elaborated to select(value, k) over Array(Int -> Int) and
    // must register as a value-read atom with its map recoverable.
    let mut terms = TermStore::new();
    let m = mk_map_var(&mut terms, "m");
    let k = terms.mk_int(7.into());
    let get = mk_select_get(&mut terms, m, k);

    let mut solver = MapSolver::new(&terms);
    solver.register_atom(get);

    let gets: Vec<_> = solver.get_terms().collect();
    assert_eq!(gets, vec![get]);
    assert_eq!(solver.get_map(get), Some(m));
    assert_eq!(solver.get_atom_count(), 1);
}

#[test]
fn get_atoms_registered_via_named_op() {
    // Raw `map.get` apps also register as value-read atoms.
    let mut terms = TermStore::new();
    let m = mk_map_var(&mut terms, "m");
    let k = terms.mk_int(3.into());
    let get = mk_get(&mut terms, m, k);

    let mut solver = MapSolver::new(&terms);
    solver.register_atom(get);

    assert_eq!(solver.get_atom_count(), 1);
    assert_eq!(solver.get_map(get), Some(m));
}

#[test]
fn contains_key_registered_via_dom_select() {
    // contains_key(m, k) is elaborated to select((map.dom m), k) and must
    // register as a domain read, NOT a value read.
    let mut terms = TermStore::new();
    let m = mk_map_var(&mut terms, "m");
    let k = terms.mk_int(5.into());
    let contains = mk_dom_select(&mut terms, m, k);

    let mut solver = MapSolver::new(&terms);
    solver.register_atom(contains);

    assert_eq!(solver.dom_atom_count(), 1);
    assert_eq!(
        solver.get_atom_count(),
        0,
        "a domain select must not be misclassified as a value read"
    );
    assert_eq!(
        solver.dom_map(contains),
        Some(m),
        "the queried map must be recoverable from the domain read"
    );
}

#[test]
fn contains_key_registered_via_named_op() {
    // Raw `map.contains_key` apps register as domain reads.
    let mut terms = TermStore::new();
    let m = mk_map_var(&mut terms, "m");
    let k = terms.mk_int(1.into());
    let contains = mk_contains(&mut terms, m, k);

    let mut solver = MapSolver::new(&terms);
    solver.register_atom(contains);

    assert_eq!(solver.dom_atom_count(), 1);
    assert_eq!(solver.get_atom_count(), 0);
}

#[test]
fn ground_keys_recoverable() {
    // The witness universe is recoverable from present get/dom reads for the
    // executor's subset↔key obligation generation.
    let mut terms = TermStore::new();
    let m = mk_map_var(&mut terms, "m");
    let n = mk_map_var(&mut terms, "n");
    let k = terms.mk_int(9.into());
    let gm = mk_select_get(&mut terms, m, k);
    let dn = mk_dom_select(&mut terms, n, k);

    let mut solver = MapSolver::new(&terms);
    solver.register_atom(gm);
    solver.register_atom(dn);

    let keys = solver.ground_keys();
    assert_eq!(keys, vec![k]);
}

#[test]
fn empty_term_registered() {
    let mut terms = TermStore::new();
    let empty = mk_empty(&mut terms);

    let mut solver = MapSolver::new(&terms);
    solver.register_atom(empty);

    let stats = solver.collect_statistics();
    let empties = stats
        .iter()
        .find(|(name, _)| *name == "map_empty_terms")
        .map(|(_, n)| *n);
    assert_eq!(empties, Some(1));
}

// ---------------------------------------------------------------------------
// Out-of-fragment: fail-closed Unknown (never a guessed verdict).
// ---------------------------------------------------------------------------

#[test]
fn out_of_fragment_op_is_unknown() {
    // map.values is a higher-order image op with no sound ground semantics yet;
    // its presence must force Unknown rather than a guess.
    let mut terms = TermStore::new();
    let m = mk_map_var(&mut terms, "m");
    let values = terms.mk_app(Symbol::named("map.values"), vec![m], value_sort());
    let k = terms.mk_int(0.into());
    let read = terms.mk_select(values, k);

    let mut solver = MapSolver::new(&terms);
    solver.register_atom(read);
    solver.assert_literal(read, true);

    assert!(
        solver.is_out_of_fragment(),
        "map.values must set the out-of-fragment flag"
    );
    assert!(
        matches!(solver.check(), TheoryResult::Unknown),
        "out-of-fragment map op must fail closed to Unknown"
    );
}

#[test]
fn each_out_of_fragment_op_flagged() {
    for op in OUT_OF_FRAGMENT_OPS {
        let mut terms = TermStore::new();
        let m = mk_map_var(&mut terms, "m");
        let app = terms.mk_app(Symbol::named(*op), vec![m], value_sort());
        let k = terms.mk_int(0.into());
        let read = terms.mk_select(app, k);

        let mut solver = MapSolver::new(&terms);
        solver.register_atom(read);
        solver.assert_literal(read, true);

        assert!(
            solver.is_out_of_fragment(),
            "{op} must set the out-of-fragment flag"
        );
        assert!(
            matches!(solver.check(), TheoryResult::Unknown),
            "{op} must fail closed to Unknown"
        );
    }
}

// ---------------------------------------------------------------------------
// push / pop / reset bookkeeping.
// ---------------------------------------------------------------------------

#[test]
fn push_pop_restores_assignment() {
    let mut terms = TermStore::new();
    let m = mk_map_var(&mut terms, "m");
    let sub = mk_subset(&mut terms, m, m);

    let mut solver = MapSolver::new(&terms);
    solver.register_atom(sub);
    solver.push();
    solver.assert_literal(sub, false);
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));
    solver.pop();
    // After pop the ¬subset assertion is gone; the formula is again satisfiable.
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn reset_clears_all_state() {
    let mut terms = TermStore::new();
    let m = mk_map_var(&mut terms, "m");
    let k = terms.mk_int(2.into());
    let get = mk_select_get(&mut terms, m, k);
    let sub = mk_subset(&mut terms, m, m);

    let mut solver = MapSolver::new(&terms);
    solver.register_atom(get);
    solver.register_atom(sub);
    assert_eq!(solver.get_atom_count(), 1);
    assert_eq!(solver.subset_atom_count(), 1);

    solver.reset();
    assert_eq!(solver.get_atom_count(), 0);
    assert_eq!(solver.subset_atom_count(), 0);
    assert_eq!(solver.dom_atom_count(), 0);
    assert!(!solver.is_out_of_fragment());
}
