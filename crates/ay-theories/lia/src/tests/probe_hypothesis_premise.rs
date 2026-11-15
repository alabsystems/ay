// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #probe-hypothesis-premise: a conflict PROBE may refute through the
//! placeholders of the shared equalities it was asked to assume.
//!
//! `probe_needed_shared_equalities` proves which shared equalities a conflict
//! needs by replaying the conflict literals in a throwaway probe and adding
//! candidate equalities WITHOUT reasons (`build_conflict_probe`), so the
//! probe's bounds cite the placeholder `(lhs, true)`. Those bounds are
//! justified (3910dce30e), so the integer side checks fold them and name the
//! placeholder in their conflict — which the exit guard
//! (`refuse_unjustified_conflict`, bff0049422) then refused. No probe that
//! needed an equality for an INTEGER refutation could answer `Unsat`, no
//! subset was proved, and the augmented conflict carried the reasons of the
//! whole reachable shared-equality closure. On `im_275_asis` (the BV/LIA
//! bridge's AUF/LIA search, whose `bv2nat(int2bv 33 ..)` residues refute only
//! over the integers) that weaker clause turned `--z3-mode` checks 2-3 from
//! `sat` into `unknown`.
//!
//! The shape below is the smallest such refutation: `2x = y` is satisfiable
//! over the rationals with `y = 3` (`x = 3/2`), so the simplex finds no
//! conflict and only the Diophantine fold refutes, citing `y = 3`'s reason.
//! The end-to-end effect (the probe proves a subset again, so the AUF/LIA
//! search keeps its short clauses) is pinned by group_regression's
//! `bv_lia_int_blast_lane.rs` (`im_275_asis`, `--z3-mode` `sat sat sat`).

use super::*;
use ay_core::TheorySolver;
use ay_lra::GomoryCut;
use num_traits::One;

fn is_unsat(result: &TheoryResult) -> bool {
    matches!(
        result,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    )
}

/// `2x = y`, as an asserted atom.
fn two_x_eq_y(terms: &mut TermStore, x: TermId, y: TermId) -> TermId {
    let two = terms.mk_int(BigInt::from(2));
    let two_x = terms.mk_mul(vec![two, x]);
    terms.mk_eq(two_x, y)
}

/// The probe itself: `2x = y` plus the reasonless hypothesis `y = 3` has no
/// integer solution, and a conflict probe must say so although its conflict
/// names the placeholder `(y, true)`. The same set in an ordinary solver is
/// still not published: outside probes the exit guard is unchanged.
#[test]
fn a_conflict_probe_refutes_through_its_reasonless_hypothesis() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let atom = two_x_eq_y(&mut terms, x, y);

    let mut probe = LiaSolver::new(&terms);
    probe.conflict_probe = true;
    probe.register_atom(atom);
    probe.assert_literal(atom, true);
    probe.assert_shared_equality(y, three, &[]);
    let result = probe.check();
    assert!(
        is_unsat(&result),
        "the probe's hypothesis is a premise of its verdict: {result:?}"
    );
    assert_eq!(probe.unjustified_conflicts_dropped, 0);

    let mut solver = LiaSolver::new(&terms);
    solver.register_atom(atom);
    solver.assert_literal(atom, true);
    solver.assert_shared_equality(y, three, &[]);
    let result = solver.check();
    assert!(
        !is_unsat(&result),
        "outside a probe a conflict naming the placeholder is not published: {result:?}"
    );
}

/// What stays refused in a probe: a GUESS (a pin citing the variable term,
/// with no reasonless shared equality behind it), and the placeholder itself
/// while an NIA guess scope is open, where a guess on `lhs` cites the same
/// term.
#[test]
fn a_conflict_probe_still_refuses_guesses() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let atom = two_x_eq_y(&mut terms, x, y);

    // A rounding-pin-shaped guess `y = 3` (reason = y), no shared equality.
    let mut probe = LiaSolver::new(&terms);
    probe.conflict_probe = true;
    probe.register_atom(atom);
    probe.assert_literal(atom, true);
    let var = probe.lra_solver_mut().ensure_var_registered(y);
    for is_lower in [true, false] {
        probe.lra_solver_mut().add_gomory_cut(
            &GomoryCut {
                coeffs: vec![(var, BigRational::one())],
                bound: BigRational::from_integer(BigInt::from(3)),
                is_lower,
                reasons: Vec::new(),
                source_term: None,
            },
            y,
        );
    }
    let result = probe.check();
    assert!(
        !is_unsat(&result),
        "a guess must not become a refutation, in a probe either: {result:?}"
    );

    // The hypothesis `y = 3` held, but inside a guess scope.
    let mut probe = LiaSolver::new(&terms);
    probe.conflict_probe = true;
    probe.register_atom(atom);
    probe.assert_literal(atom, true);
    probe.push_tentative();
    probe.assert_shared_equality(y, three, &[]);
    let result = probe.check();
    assert!(
        !is_unsat(&result),
        "inside a guess scope the placeholder is indistinguishable from a guess: {result:?}"
    );
}
