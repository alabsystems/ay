// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Push guard level (the development design notes).
//!
//! A clause guard derived from a body lemma at level L is valid only for a
//! query whose body frame lies inside `F_L`; a push from `level` assumes
//! `F_level`, so it must read guards at check level `level + 1`. Reading them
//! at `level` let a guard from a level-(level-1) body lemma justify a push that
//! is not inductive relative to `F_level`, which manufactured a spurious fixed
//! point whose model then failed verification (a demotion).

#![allow(clippy::unwrap_used)]

use super::PdrSolver;
use crate::pdr::config::PdrConfig;
use crate::pdr::frame::{Frame, Lemma};
use crate::pdr::model::{InvariantModel, PredicateInterpretation};
use crate::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId,
};

fn v(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

/// `P` counts 0..=2 (`x = 0 → P(x)`, `P(x) ∧ x < 2 ∧ x' = x + 1 → P(x')`);
/// `U` copies `P` and holds (`P(x) → U(x)`, `U(x) ∧ x' = x → U(x')`);
/// query `U(x) ∧ x ≥ 2 → false` (UNSAFE: U reaches 2 in three steps).
fn copy_problem() -> (ChcProblem, PredicateId, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let u = problem.declare_predicate("U", vec![ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), Some(ChcExpr::eq(v("x"), ChcExpr::Int(0)))),
        ClauseHead::Predicate(p, vec![v("x")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![v("x")])],
            Some(ChcExpr::and(
                ChcExpr::lt(v("x"), ChcExpr::Int(2)),
                ChcExpr::eq(v("x1"), ChcExpr::add(v("x"), ChcExpr::Int(1))),
            )),
        ),
        ClauseHead::Predicate(p, vec![v("x1")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![v("x")])], None),
        ClauseHead::Predicate(u, vec![v("x")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(u, vec![v("x")])], Some(ChcExpr::eq(v("x1"), v("x")))),
        ClauseHead::Predicate(u, vec![v("x1")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(u, vec![v("x")])],
            Some(ChcExpr::ge(v("x"), ChcExpr::Int(2))),
        ),
        ClauseHead::False,
    ));
    (problem, p, u)
}

/// Frames as a run would hold them (legacy frames are LOCAL: a lemma lives in
/// the frame of its level only, and a push from `level` reads `frames[level]`),
/// every lemma valid at its level: `frames[1] = {P: x ≤ 1, U: x ≤ 1}` (within
/// one step P ∈ {0, 1}, U ∈ {0}; planted only with `level_one`),
/// `frames[2] = {P: x ≤ 2, U: x ≤ 1}` (U within two steps copies P within one:
/// {0, 1}), `frames[3] = {P: x ≤ 2}`; plus the guard that
/// `propagate_lemma_to_users` derives on the copy clause from P's level-1 lemma
/// `x ≤ 1`, stored with `max_level = 2`. Returns the copy clause's index and
/// head arguments as well, for the filter assertions.
///
/// `level_one` exists for the fixed-point test below: the legacy fixed-point
/// reader compares CUMULATIVE frames (`cumulative_frame_constraint(i) =
/// ∧ frames[1..=i]`), under which the planted `frames[1]` already makes
/// `F_1 ≡ F_2` (`F_2 = F_1 ∧ {P ≤ 2, U ≤ 1} ≡ F_1`, equal lemma counts) — a
/// fixed point that involves no push and no guard at all. The push tests need
/// `frames[1]` (a push from 1 reads the local `frames[1]`); the fixed-point test
/// plants it empty so that only a push into `frames[3]` can make two frames
/// equal.
#[allow(clippy::type_complexity)]
fn planted_solver_with(
    level_one: bool,
) -> (
    PdrSolver,
    PredicateId,
    PredicateId,
    Lemma,
    usize,
    Vec<ChcExpr>,
) {
    let (problem, p, u) = copy_problem();
    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    }
    // Legacy LOCAL frames (above); the lane reads them as delta frames.
    .with_spacer(crate::pdr::config::SpacerLane::OFF);
    let mut solver = PdrSolver::new(problem, config);
    let xp = ChcExpr::var(solver.canonical_vars(p).expect("P vars")[0].clone());
    let xu = ChcExpr::var(solver.canonical_vars(u).expect("U vars")[0].clone());
    while solver.frames.len() < 4 {
        solver.frames.push(Frame::new());
    }
    let p_le_1 = ChcExpr::le(xp.clone(), ChcExpr::Int(1));
    let p_le_2 = ChcExpr::le(xp, ChcExpr::Int(2));
    let u_le_1 = ChcExpr::le(xu.clone(), ChcExpr::Int(1));
    if level_one {
        solver.frames[1].add_lemma(Lemma::new(p, p_le_1, 1));
        solver.frames[1].add_lemma(Lemma::new(u, u_le_1.clone(), 1));
    }
    solver.frames[2].add_lemma(Lemma::new(p, p_le_2.clone(), 2));
    solver.frames[2].add_lemma(Lemma::new(u, u_le_1.clone(), 2));
    solver.frames[3].add_lemma(Lemma::new(p, p_le_2, 3));
    let (copy_index, copy_head_args) = solver
        .problem
        .clauses_defining_with_index(u)
        .find(|(_, c)| c.body.predicates.first().is_some_and(|(b, _)| *b == p))
        .map(|(i, c)| match &c.head {
            crate::ClauseHead::Predicate(_, args) => (i, args.clone()),
            crate::ClauseHead::False => unreachable!("copy clause has a predicate head"),
        })
        .expect("copy clause");
    solver
        .caches
        .clause_guarded_lemmas
        .insert((u, copy_index), vec![(ChcExpr::le(xu, ChcExpr::Int(1)), 2)]);
    let lemma = Lemma::new(u, u_le_1, 2);
    (solver, p, u, lemma, copy_index, copy_head_args)
}

#[allow(clippy::type_complexity)]
fn planted_solver() -> (
    PdrSolver,
    PredicateId,
    PredicateId,
    Lemma,
    usize,
    Vec<ChcExpr>,
) {
    planted_solver_with(true)
}

#[test]
fn push_check_level_is_the_target_level() {
    assert_eq!(PdrSolver::push_guard_check_level(0), 1);
    assert_eq!(PdrSolver::push_guard_check_level(2), 3);
}

#[test]
fn a_guard_from_a_level_one_body_lemma_justifies_a_push_from_one_not_from_two() {
    let (mut solver, _p, u, lemma, copy_index, head_args) = planted_solver();
    // The filter itself: a push from 1 checks at level 2 (the guard, valid up
    // to level 2, is read); a push from 2 checks at level 3 (it is not).
    assert_ne!(
        solver.clause_guarded_constraint(u, copy_index, &head_args, 2),
        ChcExpr::Bool(true),
        "the level-1 guard is read by a push from level 1"
    );
    assert_eq!(
        solver.clause_guarded_constraint(u, copy_index, &head_args, 3),
        ChcExpr::Bool(true),
        "the level-1 guard is not read by a push from level 2"
    );
    // From level 1 the body frame is F_1: the guard applies (and F_1's own
    // `P: x ≤ 1` agrees), and `U: x ≤ 1` is valid at level 2 (U ∈ {0, 1}).
    assert!(solver.can_push_lemma(&lemma, 1));
    // From level 2 the body frame is F_2 (`P: x ≤ 2`, `U: x ≤ 1`): the self
    // loop is inductive, and ONLY the stale level-1 guard could make the copy
    // clause look so. It must not be assumed: `U: x ≤ 1` is not valid at
    // level 3 (U reaches 2).
    assert!(
        !solver.can_push_lemma(&lemma, 2),
        "a guard valid only at level 1 must not justify a push from level 2"
    );
}

#[test]
fn a_stale_guard_no_longer_manufactures_a_fixed_point_that_fails_verification() {
    // `frames[1]` empty: see `planted_solver_with` (with it planted, the
    // cumulative reader declares `F_1 ≡ F_2` before any push is considered).
    let (mut solver, p, u, lemma, _copy_index, _head_args) = planted_solver_with(false);
    // Reading guards at the source level pushed `U: x ≤ 1` into frames[3],
    // making frames 2 and 3 equal: a "fixed point" whose model
    // {P: x ≤ 2, U: x ≤ 1} is not inductive (U reaches 2) and fails
    // verification — the demotion this fix removes.
    let stale_model = {
        let mut model = InvariantModel::new();
        let xp = ChcExpr::var(solver.canonical_vars(p).unwrap()[0].clone());
        for (pred, formula) in [
            (p, ChcExpr::le(xp, ChcExpr::Int(2))),
            (u, lemma.formula.clone()),
        ] {
            let vars = solver.canonical_vars(pred).unwrap().to_vec();
            model.set(pred, PredicateInterpretation::new(vars, formula));
        }
        model
    };
    assert!(
        !solver.verify_model(&stale_model),
        "the stale-guard fixed point's model must fail verification"
    );

    assert!(
        solver.check_fixed_point().is_none(),
        "no fixed point may be declared on frames a stale guard made equal"
    );
    assert!(
        !solver.frames[3]
            .lemmas
            .iter()
            .any(|l| l.predicate == u && l.formula == lemma.formula),
        "`U: x ≤ 1` must not be pushed to level 3"
    );
}
