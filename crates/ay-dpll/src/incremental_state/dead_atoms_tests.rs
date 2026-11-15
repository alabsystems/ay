// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::Symbol;
use ay_core::Sort;

fn lra_atoms(terms: &mut TermStore) -> (TermId, TermId, TermId, TermId) {
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let eq = terms.mk_app(Symbol::named("="), vec![x, y], Sort::Bool);
    let le = terms.mk_app(Symbol::named("<="), vec![x, y], Sort::Bool);
    let lt = terms.mk_app(Symbol::named("<"), vec![x, y], Sort::Bool);
    let or = terms.mk_app(Symbol::named("or"), vec![eq, le], Sort::Bool);
    (eq, le, lt, or)
}

#[test]
fn dead_theory_atoms_are_the_encoded_atoms_no_active_assertion_reaches() {
    let mut terms = TermStore::new();
    let (eq, le, lt, or) = lra_atoms(&mut terms);
    let active: HashSet<TermId> = [le].into_iter().collect();
    let dead = dead_theory_atoms(&terms, [eq, le, lt, or], &active);
    // `or` is Boolean structure, not a theory atom; `le` is active.
    assert_eq!(dead, [eq, lt].into_iter().collect::<HashSet<_>>());
    assert!(dead_theory_atoms(&terms, [le], &active).is_empty());
}

#[test]
fn append_live_theory_atoms_skips_dead_and_stays_append_only() {
    let mut terms = TermStore::new();
    let (eq, le, lt, or) = lra_atoms(&mut terms);
    let mut var_to_term: HashMap<u32, TermId> = HashMap::default();
    var_to_term.insert(3, eq);
    var_to_term.insert(1, le);
    var_to_term.insert(2, or);
    let active: HashSet<TermId> = [le].into_iter().collect();
    let mut dead: HashSet<TermId> = [eq].into_iter().collect();
    let mut atoms = Vec::new();
    let mut set = HashSet::default();

    append_live_theory_atoms(&terms, &var_to_term, &active, &dead, &mut atoms, &mut set);
    assert_eq!(atoms, vec![le], "dead `eq` and Boolean `or` are withheld");

    // A split mints `lt` on a fresh var; it is appended after `le`.
    var_to_term.insert(9, lt);
    append_live_theory_atoms(&terms, &var_to_term, &active, &dead, &mut atoms, &mut set);
    assert_eq!(atoms, vec![le, lt]);

    // Reviving `eq` (old var 3) appends it at the TAIL instead of re-sorting,
    // so a tail-registering consumer sees it.
    dead.remove(&eq);
    append_live_theory_atoms(&terms, &var_to_term, &active, &dead, &mut atoms, &mut set);
    assert_eq!(atoms, vec![le, lt, eq]);
    assert_eq!(set.len(), atoms.len());
}

#[test]
fn append_live_theory_atoms_without_dead_atoms_matches_the_sorted_full_set() {
    // With nothing dead the append-only build must equal the historical
    // one-shot filter: every active-or-theory atom, ascending by SAT var.
    let mut terms = TermStore::new();
    let (eq, le, lt, or) = lra_atoms(&mut terms);
    let mut var_to_term: HashMap<u32, TermId> = HashMap::default();
    for (var, term) in [(7, eq), (2, le), (5, lt), (1, or)] {
        var_to_term.insert(var, term);
    }
    let active = HashSet::default();
    let mut atoms = Vec::new();
    let mut set = HashSet::default();
    append_live_theory_atoms(
        &terms,
        &var_to_term,
        &active,
        &HashSet::default(),
        &mut atoms,
        &mut set,
    );
    let expected: Vec<TermId> = crate::iter_var_to_term_sorted(&var_to_term)
        .map(|(_, term)| term)
        .filter(|term| active.contains(term) || crate::is_theory_atom(&terms, *term))
        .collect();
    assert_eq!(atoms, expected);
}

#[test]
fn encoded_live_atoms_follow_the_root_term_not_the_source_text() {
    // Source assertion `(<= (ite q 0 y) 0)` is encoded as its lifted form
    // `(ite q (<= 0 0) (<= y 0))`: `(<= y 0)` is live although the source text
    // never mentions it.
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::Real);
    let q = terms.mk_var("q", Sort::Bool);
    let zero = terms.mk_rational(num_rational::BigRational::from_integer(0.into()));
    let ite = terms.mk_ite(q, zero, y);
    let source = terms.mk_app(Symbol::named("<="), vec![ite, zero], Sort::Bool);
    let lifted_leaf = terms.mk_app(Symbol::named("<="), vec![y, zero], Sort::Bool);
    let trivial = terms.mk_app(Symbol::named("<="), vec![zero, zero], Sort::Bool);
    let lifted = terms.mk_ite(q, trivial, lifted_leaf);
    let (eq, ..) = lra_atoms(&mut terms);

    let mut var_to_term: HashMap<u32, TermId> = HashMap::default();
    var_to_term.insert(0, lifted);
    var_to_term.insert(1, lifted_leaf);
    var_to_term.insert(2, eq);
    let mut roots: HashMap<TermId, i32> = HashMap::default();
    roots.insert(source, 1); // DIMACS var 1 = 0-indexed var 0 = `lifted`
    let no_alias: HashMap<TermId, u32> = HashMap::default();

    let live = encoded_live_atoms(&terms, &[source], &roots, &var_to_term, &no_alias)
        .expect("every active assertion has a root");
    assert!(
        live.contains(&lifted_leaf),
        "the lifted leaf is live: {live:?}"
    );
    assert!(!live.contains(&eq), "an atom outside the cone is not live");
    let dead = dead_theory_atoms(&terms, var_to_term.values().copied(), &live);
    assert_eq!(dead, [eq].into_iter().collect::<HashSet<_>>());

    // A negated root (`(not A)` encodes to `-var(A)`) reaches the same cone.
    roots.insert(source, -1);
    assert_eq!(
        encoded_live_atoms(&terms, &[source], &roots, &var_to_term, &no_alias),
        Some(live)
    );

    // An active assertion without a recorded root turns the filter OFF.
    assert_eq!(
        encoded_live_atoms(&terms, &[source, eq], &roots, &var_to_term, &no_alias),
        None
    );
    let filter = DeadAtomFilter::for_check_sat(
        true,
        &terms,
        &[source, eq],
        &roots,
        &var_to_term,
        &no_alias,
        &HashSet::default(),
    );
    assert!(!filter.is_on() && filter.withheld() == 0);
}

#[test]
fn an_atom_aliased_onto_another_terms_var_keeps_that_owner_live() {
    // The active assertion `(or (= x y) q)` reaches `(= x y)`, but the encoding
    // put `(= x y)` on the var OWNED by `(<= x y)` (var_to_term[1] = le), so
    // the theory is handed `le` for that literal. `le` must stay live: it is
    // the atom whose truth value the active assertion depends on.
    let mut terms = TermStore::new();
    let (eq, le, lt, _) = lra_atoms(&mut terms);
    let q = terms.mk_var("q", Sort::Bool);
    let source = terms.mk_app(Symbol::named("or"), vec![eq, q], Sort::Bool);
    let mut var_to_term: HashMap<u32, TermId> = HashMap::default();
    var_to_term.insert(0, source);
    var_to_term.insert(1, le);
    var_to_term.insert(2, q);
    var_to_term.insert(3, lt);
    let mut term_to_var: HashMap<TermId, u32> = HashMap::default();
    for (var, term) in &var_to_term {
        term_to_var.insert(*term, *var);
    }
    term_to_var.insert(eq, 1); // the alias
    let mut roots: HashMap<TermId, i32> = HashMap::default();
    roots.insert(source, 1);

    let live = encoded_live_atoms(&terms, &[source], &roots, &var_to_term, &term_to_var)
        .expect("every active assertion has a root");
    assert!(live.contains(&le), "the alias owner is live: {live:?}");
    assert!(!live.contains(&lt), "an unrelated atom stays dead");
    let filter = DeadAtomFilter::for_check_sat(
        true,
        &terms,
        &[source],
        &roots,
        &var_to_term,
        &term_to_var,
        &HashSet::default(),
    );
    assert!(!filter.is_dead(&le) && filter.is_dead(&lt) && filter.withheld() == 1);

    // A syntactically active (Bool UF arg) atom aliased the same way also
    // keeps its owner: here the cone reaches nothing but `q`.
    let mut roots_q: HashMap<TermId, i32> = HashMap::default();
    roots_q.insert(q, 3); // DIMACS var 3 = 0-indexed var 2 = `q`
    let active: HashSet<TermId> = [eq].into_iter().collect();
    let filter = DeadAtomFilter::for_check_sat(
        true,
        &terms,
        &[q],
        &roots_q,
        &var_to_term,
        &term_to_var,
        &active,
    );
    assert!(
        !filter.is_dead(&le) && filter.is_dead(&lt),
        "active alias owner is live"
    );
}
