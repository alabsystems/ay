// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What the lazy split loop reads off an `AufLiraSolver` between two rounds:
//! phase hints, and the conflicts of a refuted assignment beside the one
//! `check` reported.

use super::*;
use ay_core::Sort;
use num_bigint::BigInt;

#[test]
fn scoped_models_merge_only_authoritative_real_lra_values() {
    let mut terms = TermStore::new();
    let real = terms.mk_var("r", Sort::Real);
    let integer = terms.mk_var("i", Sort::Int);
    let boolean = terms.mk_var("b", Sort::Bool);
    let mut solver = AufLiraSolver::new(&terms);
    solver.euf.scope_model_to_roots(&[real]);
    for term in [real, integer, boolean] {
        solver.lra.ensure_var_registered(term);
    }
    let (euf, _, _, lra) = solver.extract_all_models();
    assert!(euf.term_values.len() < lra.values.len());
    assert!(crate::combined_solvers::models::real_values_are_merged(
        &euf, &lra, &terms
    ));
    assert!(!euf.term_values.contains_key(&boolean));

    let mut combiner = crate::combined_solvers::combiner::TheoryCombiner::auf_lra(&terms);
    combiner.scope_euf_model_to_roots(&[real]);
    for term in [real, integer, boolean] {
        combiner.lra.as_mut().unwrap().ensure_var_registered(term);
    }
    let (euf, _, lra) = combiner.extract_all_models_auflra();
    assert!(euf.term_values.len() < lra.values.len());
    assert!(crate::combined_solvers::models::real_values_are_merged(
        &euf, &lra, &terms
    ));
    assert!(!euf.term_values.contains_key(&boolean));
}

fn int(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_int(BigInt::from(value))
}

/// `x` with the three bound atoms `(<= 5 x)`, `(<= x 3)` and `(<= 0 x)`.
struct Bounds {
    terms: TermStore,
    at_least_five: TermId,
    at_most_three: TermId,
    at_least_zero: TermId,
    at_most_two: TermId,
}

impl Bounds {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let (zero, two, three, five) = (
            int(&mut terms, 0),
            int(&mut terms, 2),
            int(&mut terms, 3),
            int(&mut terms, 5),
        );
        Self {
            at_least_five: terms.mk_le(five, x),
            at_most_three: terms.mk_le(x, three),
            at_least_zero: terms.mk_le(zero, x),
            at_most_two: terms.mk_le(x, two),
            terms,
        }
    }

    fn atoms(&self) -> [TermId; 4] {
        [
            self.at_least_five,
            self.at_most_three,
            self.at_least_zero,
            self.at_most_two,
        ]
    }
}

/// A solver the split loop reads every sub-solver of.
fn solver_over<'a>(terms: &'a TermStore, atoms: &[TermId]) -> AufLiraSolver<'a> {
    reading(SplitLoopReads::EverySolver, terms, atoms)
}

fn reading<'a>(reads: SplitLoopReads, terms: &'a TermStore, atoms: &[TermId]) -> AufLiraSolver<'a> {
    let mut solver = AufLiraSolver::new(terms).split_loop_reading(reads);
    for &atom in atoms {
        solver.register_atom(atom);
    }
    solver
}

#[test]
fn an_int_atom_reads_its_phase_from_the_int_solver() {
    let bounds = Bounds::new();
    let mut solver = solver_over(&bounds.terms, &bounds.atoms());
    solver.assert_literal(bounds.at_least_five, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Every model of `5 <= x` has `x > 3` and `x >= 0`.
    assert_eq!(solver.suggest_phase(bounds.at_most_three), Some(false));
    assert_eq!(solver.suggest_phase(bounds.at_least_zero), Some(true));
}

#[test]
fn the_twin_bound_gives_the_opposite_phase() {
    let bounds = Bounds::new();
    let mut solver = solver_over(&bounds.terms, &bounds.atoms());
    solver.assert_literal(bounds.at_most_two, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Every model of `x <= 2` has `x <= 3` and `x < 5`.
    assert_eq!(solver.suggest_phase(bounds.at_most_three), Some(true));
    assert_eq!(solver.suggest_phase(bounds.at_least_five), Some(false));
}

/// `a = b = c = d` over an uninterpreted sort, with the equality atoms of
/// `a` and each of `c`, `d`.
struct Chain {
    terms: TermStore,
    links: [TermId; 3],
    a_is_c: TermId,
    a_is_d: TermId,
}

impl Chain {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let sort = Sort::Uninterpreted("U".to_string());
        let [a, b, c, d] = ["a", "b", "c", "d"].map(|name| terms.mk_var(name, sort.clone()));
        Self {
            links: [terms.mk_eq(a, b), terms.mk_eq(b, c), terms.mk_eq(c, d)],
            a_is_c: terms.mk_eq(a, c),
            a_is_d: terms.mk_eq(a, d),
            terms,
        }
    }

    fn atoms(&self) -> Vec<TermId> {
        let mut atoms = self.links.to_vec();
        atoms.extend([self.a_is_c, self.a_is_d]);
        atoms
    }
}

/// `check` on an assignment the theory does not refute. What it answers
/// beside that (a request for model equalities, say) is not what these tests
/// are about.
fn check_without_conflict(solver: &mut AufLiraSolver<'_>) {
    let result = solver.check();
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "{result:?}"
    );
}

#[test]
fn an_equality_the_egraph_holds_is_hinted_true() {
    let chain = Chain::new();
    let mut solver = solver_over(&chain.terms, &chain.atoms());
    solver.assert_literal(chain.links[0], true);
    solver.assert_literal(chain.links[1], true);
    check_without_conflict(&mut solver);

    assert_eq!(solver.suggest_phase(chain.a_is_c), Some(true));
    // `d` is in a class of its own: the default for an equality stands.
    assert_eq!(solver.suggest_phase(chain.a_is_d), Some(false));
}

#[test]
fn a_refuted_check_names_every_violated_disequality() {
    let chain = Chain::new();
    let mut solver = solver_over(&chain.terms, &chain.atoms());
    for link in chain.links {
        solver.assert_literal(link, true);
    }
    solver.assert_literal(chain.a_is_c, false);
    solver.assert_literal(chain.a_is_d, false);
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));

    let conflicts = solver.lra_solver().collect_all_bound_conflicts(true);

    assert_eq!(conflicts.len(), 2, "{conflicts:?}");
    let denies = |atom: TermId| {
        conflicts
            .iter()
            .filter(|conflict| conflict.literals.contains(&TheoryLit::new(atom, false)))
            .count()
    };
    assert_eq!((denies(chain.a_is_c), denies(chain.a_is_d)), (1, 1));
}

#[test]
fn a_disequality_the_egraph_respects_is_not_named() {
    let chain = Chain::new();
    let mut solver = solver_over(&chain.terms, &chain.atoms());
    // Without the last link `d` is apart from `a`, so only `a != c` fails.
    solver.assert_literal(chain.links[0], true);
    solver.assert_literal(chain.links[1], true);
    solver.assert_literal(chain.a_is_c, false);
    solver.assert_literal(chain.a_is_d, false);
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));

    let conflicts = solver.lra_solver().collect_all_bound_conflicts(true);

    assert_eq!(conflicts.len(), 1, "{conflicts:?}");
    assert!(conflicts[0]
        .literals
        .contains(&TheoryLit::new(chain.a_is_c, false)));
}

#[test]
fn a_consistent_check_names_no_conflict() {
    let chain = Chain::new();
    let mut solver = solver_over(&chain.terms, &chain.atoms());
    solver.assert_literal(chain.links[0], true);
    solver.assert_literal(chain.a_is_d, false);
    check_without_conflict(&mut solver);

    assert!(solver
        .lra_solver()
        .collect_all_bound_conflicts(true)
        .is_empty());
}

#[test]
fn contradictory_int_bounds_are_named_with_the_disequalities() {
    let bounds = Bounds::new();
    let mut solver = solver_over(&bounds.terms, &bounds.atoms());
    solver.assert_literal(bounds.at_least_five, true);
    solver.assert_literal(bounds.at_most_three, true);
    assert!(matches!(
        solver.check(),
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    ));

    let conflicts = solver.lra_solver().collect_all_bound_conflicts(true);

    assert!(
        conflicts.iter().any(|conflict| {
            conflict
                .literals
                .contains(&TheoryLit::new(bounds.at_least_five, true))
                && conflict
                    .literals
                    .contains(&TheoryLit::new(bounds.at_most_three, true))
        }),
        "the Int solver's bound conflict is among {conflicts:?}"
    );
}

/// Reading the Real solver only, an equality the E-graph holds keeps the
/// default phase of an equality, and the violated disequalities are left to
/// later rounds.
#[test]
fn reading_the_real_solver_keeps_the_former_hints_and_conflicts() {
    let chain = Chain::new();
    let mut solver = reading(SplitLoopReads::RealSolver, &chain.terms, &chain.atoms());
    solver.assert_literal(chain.links[0], true);
    solver.assert_literal(chain.links[1], true);
    check_without_conflict(&mut solver);
    assert_eq!(solver.suggest_phase(chain.a_is_c), Some(false));

    solver.assert_literal(chain.a_is_c, false);
    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));
    assert!(solver
        .lra_solver()
        .collect_all_bound_conflicts(true)
        .is_empty());
}

/// The split loop hands the solver the value of a Boolean variable under a
/// function only where it reads every solver.
#[test]
fn boolean_argument_values_are_asked_for_with_the_other_reads() {
    let chain = Chain::new();
    let every = reading(SplitLoopReads::EverySolver, &chain.terms, &[]);
    let real = reading(SplitLoopReads::RealSolver, &chain.terms, &[]);

    assert!(every.reads_bool_argument_values());
    assert!(!real.reads_bool_argument_values());
}
