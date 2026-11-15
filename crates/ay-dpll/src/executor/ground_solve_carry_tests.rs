// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{FarkasAnnotation, Sort, Symbol};
use ay_sat::Literal as SatLiteral;

/// `a = b` and `f(a) = f(b)` over an uninterpreted sort.
fn congruence_atoms(terms: &mut TermStore) -> (TermId, TermId) {
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", u.clone());
    let b = terms.mk_var("b", u.clone());
    let fa = terms.mk_app(Symbol::named("f"), vec![a], u.clone());
    let fb = terms.mk_app(Symbol::named("f"), vec![b], u);
    (terms.mk_eq(a, b), terms.mk_eq(fa, fb))
}

fn from_assertions(_: TermId) -> bool {
    false
}

fn offer_literals(store: &mut GroundSolveCarry, terms: &TermStore, lits: &[TheoryLit]) -> bool {
    store.offer(terms, OfferedConflict::Literals(lits), &from_assertions)
}

/// A store holding the congruence conflict `a = b`, `f(a) != f(b)`.
fn store_with_congruence_conflict(terms: &mut TermStore) -> (GroundSolveCarry, TermId, TermId) {
    let (a_eq_b, fa_eq_fb) = congruence_atoms(terms);
    let mut store = GroundSolveCarry::default();
    assert!(offer_literals(
        &mut store,
        terms,
        &[
            TheoryLit::new(a_eq_b, true),
            TheoryLit::new(fa_eq_fb, false)
        ],
    ));
    (store, a_eq_b, fa_eq_fb)
}

#[test]
fn a_conflict_the_theory_refutes_alone_is_stored_once() {
    let mut terms = TermStore::new();
    let (mut store, a_eq_b, fa_eq_fb) = store_with_congruence_conflict(&mut terms);
    // The same set in another order is the same conflict.
    let reordered = [
        TheoryLit::new(fa_eq_fb, false),
        TheoryLit::new(a_eq_b, true),
    ];
    assert!(!offer_literals(&mut store, &terms, &reordered));
    assert_eq!(store.conflict_count(), 1);
    assert_eq!(store.counters(), (1, 0));
}

/// The one-literal twin of the test above: with `a = b` asserted FALSE the
/// literal set is satisfiable. A search may have learned its clause from
/// context; the store must not keep it.
#[test]
fn a_conflict_that_needs_context_is_not_stored() {
    let mut terms = TermStore::new();
    let (a_eq_b, fa_eq_fb) = congruence_atoms(&mut terms);
    let conflict = [
        TheoryLit::new(a_eq_b, false),
        TheoryLit::new(fa_eq_fb, false),
    ];
    let mut store = GroundSolveCarry::default();
    assert!(!offer_literals(&mut store, &terms, &conflict));
    assert_eq!(store.conflict_count(), 0);
    // A second offer answers from the declined set and stays declined.
    assert!(!offer_literals(&mut store, &terms, &conflict));
    assert_eq!(store.conflict_count(), 0);
}

/// `p(a)`, `not q(a)`: refuted in a query that asserts `forall x. p(x) =>
/// q(x)`, through the instance the gate holds as a support literal, and
/// satisfiable in the theory. The store declines it, and the encoding of a
/// later solve over a problem without that quantifier keeps its model; the
/// clause, had it been carried, would have refuted that problem.
#[test]
fn a_conflict_that_holds_only_through_an_instance_would_refute_a_later_solve() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", u);
    let pa = terms.mk_app(Symbol::named("p"), vec![a], Sort::Bool);
    let qa = terms.mk_app(Symbol::named("q"), vec![a], Sort::Bool);
    let conflict = [TheoryLit::new(pa, true), TheoryLit::new(qa, false)];
    let mut store = GroundSolveCarry::default();
    assert!(!offer_literals(&mut store, &terms, &conflict));

    // A later ground solve: `p(a)` and `not q(a)` are asserted, nothing else.
    let solve_with = |clauses: &[Vec<CarriedLiteral>]| {
        let mut solver = SatSolver::new(2);
        let mut term_to_var = HashMap::default();
        let mut var_to_term = HashMap::default();
        term_to_var.insert(pa, 0u32);
        term_to_var.insert(qa, 1u32);
        var_to_term.insert(0u32, pa);
        var_to_term.insert(1u32, qa);
        let mut next_var = 2u32;
        let mut negations = crate::incremental_proof_cache::IncrementalNegationCache::seed(
            &mut terms.clone(),
            [pa, qa],
            false,
        );
        let added = crate::executor::theories::split_incremental::replay_carried_conflicts(
            &terms,
            &mut solver,
            &mut term_to_var,
            &mut var_to_term,
            &mut next_var,
            &mut negations,
            clauses,
        );
        solver.add_clause(vec![SatLiteral::positive(SatVariable::new(0))]);
        solver.add_clause(vec![SatLiteral::negative(SatVariable::new(1))]);
        (added, solver.solve().into_inner().is_sat())
    };
    let (added, sat) = solve_with(store.conflicts(&terms));
    assert_eq!(added, 0);
    assert!(sat, "nothing carried, so the later solve keeps its model");
    let wrongly_carried = vec![conflict
        .iter()
        .map(|&literal| CarriedLiteral {
            literal,
            minted: false,
        })
        .collect::<Vec<_>>()];
    let (added, sat) = solve_with(&wrongly_carried);
    assert_eq!(added, 1);
    assert!(
        !sat,
        "the twin: carrying the instance-dependent clause refutes a satisfiable solve"
    );
}

/// A Farkas certificate that passes the semantic check is evidence on its
/// own: `x >= 1`, `x <= 0` with unit coefficients.
#[test]
fn a_checked_farkas_certificate_admits_the_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(num_rational::BigRational::from_integer(0.into()));
    let one = terms.mk_rational(num_rational::BigRational::from_integer(1.into()));
    let x_ge_1 = terms.mk_ge(x, one);
    let x_le_0 = terms.mk_le(x, zero);
    let conflict = TheoryConflict::with_farkas(
        vec![TheoryLit::new(x_ge_1, true), TheoryLit::new(x_le_0, true)],
        FarkasAnnotation::from_ints(&[1, 1]),
    );
    let mut store = GroundSolveCarry::default();
    assert!(store.offer(&terms, OfferedConflict::Farkas(&conflict), &from_assertions));
}

/// The twin: a certificate over a SATISFIABLE literal set fails the check,
/// and the fresh solver the store then asks finds the set satisfiable. A
/// certificate is checked, never taken on the theory's word.
#[test]
fn a_forged_farkas_certificate_does_not_admit_a_satisfiable_set() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(num_rational::BigRational::from_integer(0.into()));
    let one = terms.mk_rational(num_rational::BigRational::from_integer(1.into()));
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_1 = terms.mk_le(x, one);
    let conflict = TheoryConflict::with_farkas(
        vec![TheoryLit::new(x_ge_0, true), TheoryLit::new(x_le_1, true)],
        FarkasAnnotation::from_ints(&[1, 1]),
    );
    let mut store = GroundSolveCarry::default();
    assert!(!store.offer(&terms, OfferedConflict::Farkas(&conflict), &from_assertions));
    assert_eq!(store.conflict_count(), 0);
}

#[test]
fn empty_and_tautological_conflicts_are_never_stored() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let mut store = GroundSolveCarry::default();
    assert!(!offer_literals(&mut store, &terms, &[]));
    let both = [TheoryLit::new(p, true), TheoryLit::new(p, false)];
    assert!(!offer_literals(&mut store, &terms, &both));
    assert_eq!(store.conflict_count(), 0);
}

#[test]
fn each_literal_remembers_whether_its_atom_was_minted() {
    let mut terms = TermStore::new();
    let (a_eq_b, fa_eq_fb) = congruence_atoms(&mut terms);
    let mut store = GroundSolveCarry::default();
    assert!(store.offer(
        &terms,
        OfferedConflict::Literals(&[
            TheoryLit::new(a_eq_b, true),
            TheoryLit::new(fa_eq_fb, false)
        ]),
        &|term| term == fa_eq_fb,
    ));
    let stored = store.conflicts(&terms);
    assert_eq!(stored.len(), 1);
    for lit in &stored[0] {
        assert_eq!(lit.minted, lit.literal.term == fa_eq_fb);
    }
}

/// The twin of the test above with BOTH atoms minted: nothing ties the
/// conflict to an assertion, so it is not kept.
#[test]
fn a_conflict_among_minted_atoms_only_is_not_stored() {
    let mut terms = TermStore::new();
    let (a_eq_b, fa_eq_fb) = congruence_atoms(&mut terms);
    let mut store = GroundSolveCarry::default();
    assert!(!store.offer(
        &terms,
        OfferedConflict::Literals(&[
            TheoryLit::new(a_eq_b, true),
            TheoryLit::new(fa_eq_fb, false)
        ]),
        &|_| true,
    ));
    assert_eq!(store.conflict_count(), 0);
}

#[test]
fn a_rolled_back_term_store_empties_the_store() {
    let mut terms = TermStore::new();
    let checkpoint = terms.rollback_checkpoint();
    let (mut store, a_eq_b, _) = store_with_congruence_conflict(&mut terms);
    let mut assignment_by_var = HashMap::default();
    assignment_by_var.insert(0u32, a_eq_b);
    store.remember_assignment(&terms, &assignment_by_var, &[true]);
    assert_eq!(store.conflict_count(), 1);

    // The ids of the stored literals are reclaimed and minted again as other
    // terms: two unrelated Boolean variables now sit where the atoms were.
    terms.rollback_to(checkpoint);
    let p = terms.mk_var("p", Sort::Bool);
    let _q = terms.mk_var("q", Sort::Bool);
    assert!(store.conflicts(&terms).is_empty());
    let mut solver = SatSolver::new(1);
    let mut term_to_var = HashMap::default();
    term_to_var.insert(p, 0u32);
    term_to_var.insert(a_eq_b, 0u32);
    assert_eq!(store.seed_phases(&terms, &mut solver, &term_to_var), 0);
}

/// The twin of the rollback test: a term store that only grew keeps both the
/// conflict and the phases.
#[test]
fn an_appended_term_store_keeps_the_store() {
    let mut terms = TermStore::new();
    let (mut store, a_eq_b, _) = store_with_congruence_conflict(&mut terms);
    let mut assignment_by_var = HashMap::default();
    assignment_by_var.insert(0u32, a_eq_b);
    store.remember_assignment(&terms, &assignment_by_var, &[true]);
    let _later = terms.mk_var("later", Sort::Bool);
    assert_eq!(store.conflicts(&terms).len(), 1);
    let mut solver = SatSolver::new(1);
    let mut term_to_var = HashMap::default();
    term_to_var.insert(a_eq_b, 0u32);
    assert_eq!(store.seed_phases(&terms, &mut solver, &term_to_var), 1);
    assert_eq!(solver.var_phase(SatVariable::new(0)), Some(true));
}

#[test]
fn a_cloned_term_store_is_another_store() {
    let mut terms = TermStore::new();
    let (mut store, _, _) = store_with_congruence_conflict(&mut terms);
    let other = terms.clone();
    assert!(store.conflicts(&other).is_empty());
}

/// A user declaration of `to_real` (or `is_int`) changes what the builtin's
/// existing terms mean; nothing read before it is kept.
#[test]
fn a_shadowed_builtin_empties_the_store() {
    let mut terms = TermStore::new();
    let (mut store, _, _) = store_with_congruence_conflict(&mut terms);
    terms.mark_to_real_shadowed();
    assert!(store.conflicts(&terms).is_empty());

    let mut terms = TermStore::new();
    let (mut store, _, _) = store_with_congruence_conflict(&mut terms);
    terms.mark_is_int_shadowed();
    assert!(store.conflicts(&terms).is_empty());
}

#[test]
fn a_new_query_starts_empty() {
    let mut terms = TermStore::new();
    let (mut store, a_eq_b, _) = store_with_congruence_conflict(&mut terms);
    let mut assignment_by_var = HashMap::default();
    assignment_by_var.insert(0u32, a_eq_b);
    store.remember_assignment(&terms, &assignment_by_var, &[false]);
    store.note_replayed(3);
    assert_eq!(store.counters(), (1, 3));
    store.begin_query();
    assert_eq!(store.counters(), (0, 0));
    assert!(store.conflicts(&terms).is_empty());
    let mut solver = SatSolver::new(1);
    let mut term_to_var = HashMap::default();
    term_to_var.insert(a_eq_b, 0u32);
    assert_eq!(store.seed_phases(&terms, &mut solver, &term_to_var), 0);
}

/// Evidence re-solves search as they did before the store existed.
#[test]
fn no_carry_in_a_proof_tracked_or_evidence_solve() {
    let mut exec = Executor::new();
    exec.quantifier_pipeline_engaged = true;
    assert!(exec.ground_solve_carry_active(false));
    assert!(!exec.ground_solve_carry_active(true), "proof-tracked");
    exec.certification_resolve = true;
    assert!(
        !exec.ground_solve_carry_active(false),
        "certification re-solve"
    );
    exec.certification_resolve = false;
    exec.force_strengthenings_off();
    assert!(!exec.ground_solve_carry_active(false), "checking solve");
    let outer = Executor::new();
    let mut checker = Executor::new();
    checker.force_strengthenings_off();
    let _scope = checker.enter_checking_solve_scope();
    let mut nested = outer;
    nested.quantifier_pipeline_engaged = true;
    assert!(
        !nested.ground_solve_carry_active(false),
        "a probe nested in a checking solve"
    );
    let mut plain = Executor::new();
    plain.quantifier_pipeline_engaged = false;
    assert!(
        !plain.ground_solve_carry_active(false),
        "no quantifier pipeline"
    );
}
