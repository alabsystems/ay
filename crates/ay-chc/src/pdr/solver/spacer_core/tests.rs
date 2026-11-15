// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit + property tests of the Spacer lane (owner: **WP-B1-L**;
//! `DESIGN` §9 test list): `LitCube` / `Hist` sanity, the proxied-vs-unproxied
//! core differential (F1 worked example), QuickXplain with injected
//! `Unknown`s (lock L-Q), the oracle shapes on tiny hand CHC problems, the
//! `lemma_from_cores` phases (2-literal core out of a 5-literal cube; a drop
//! that breaks relative inductiveness is rejected; strict LRA bound preserved;
//! LIA divisibility literal kept), confirmation disagreement counted, level-0
//! fact-only queries and the climb to 1 (lock L-0), INV-L3 `Unknown`, lemma
//! `false` only after the empty-seed confirmation, the deadline-aware
//! assumption entry, and the L1 property (the returned cube is UNSAT under
//! `Reach` at its level) on generated counter systems.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::ddmin::quickxplain;
use super::oracle::{map_proxies, Budget, Hyp, Verdict, PROXY_PREFIX};
use super::stats::Hist;
use crate::pdr::config::{PdrConfig, SpacerLane};
use crate::pdr::cube::literals::LitCube;
use crate::pdr::frame::{Frame, Lemma};
use crate::pdr::obligation::ProofObligation;
use crate::pdr::solver::blocking::ClauseCore;
use crate::pdr::solver::{BlockResult, PdrSolver};
use crate::smt::{SmtContext, SmtResult};
use crate::{
    ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId,
};
use std::time::Duration;

fn v(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

fn rv(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Real))
}

fn i(n: i128) -> ChcExpr {
    ChcExpr::Int(n)
}

#[test]
fn litcube_drops_true_and_duplicates_and_keeps_order() {
    let a = ChcExpr::eq(v("x"), ChcExpr::Int(1));
    let b = ChcExpr::le(v("y"), v("x"));
    let cube = LitCube::from_lits(vec![a.clone(), ChcExpr::Bool(true), b.clone(), a.clone()]);
    assert_eq!(cube.len(), 2);
    assert_eq!(cube.lits()[0], a);
    assert_eq!(cube.lits()[1], b);
    assert_eq!(*cube.expr(), ChcExpr::and_all(vec![a.clone(), b.clone()]));
    assert_eq!(cube.pin_count(), 1);
    let canon = vec![
        ChcVar::new("x", ChcSort::Int),
        ChcVar::new("y", ChcSort::Int),
        ChcVar::new("z", ChcSort::Int),
    ];
    assert_eq!(cube.mentioned_canon(&canon), 2);
    assert!(!cube.is_point_cube(&canon));
    let sub = cube.subset(&[true, false]);
    assert_eq!(sub.len(), 1);
    assert_eq!(cube.without(0).lits()[0], b);
    assert!(LitCube::from_lits(Vec::new()).is_empty());
    assert_eq!(cube.lemma_formula(), ChcExpr::not(cube.expr().clone()));
    // The empty cube's lemma is the explicit `false` (§7.5 readers).
    assert_eq!(
        LitCube::from_lits(Vec::new()).lemma_formula(),
        ChcExpr::Bool(false)
    );
}

#[test]
fn litcube_from_expr_round_trips_a_point_cube() {
    let state = ChcExpr::and_all(vec![
        ChcExpr::eq(v("x"), ChcExpr::Int(3)),
        ChcExpr::eq(v("y"), ChcExpr::Int(4)),
    ]);
    let cube = LitCube::from_expr(&state);
    let canon = vec![
        ChcVar::new("x", ChcSort::Int),
        ChcVar::new("y", ChcSort::Int),
    ];
    assert!(cube.is_point_cube(&canon));
    assert_eq!(cube.pin_count(), 2);
    assert_eq!(cube.structural_hash(), state.structural_hash());
}

#[test]
fn hist_quantiles() {
    let mut h = Hist::new();
    for x in [1usize, 2, 2, 3, 10] {
        h.add(x);
    }
    assert_eq!(h.count(), 5);
    assert_eq!(h.quantile(0.5), Some(2));
    assert_eq!(h.quantile(0.9), Some(10));
    assert_eq!(h.quantile(1.0), Some(10));
    assert!(Hist::new().quantile(0.5).is_none());
}

// ---------------------------------------------------------------------------
// Proxy mapping and the deadline-aware assumption entry
// ---------------------------------------------------------------------------

#[test]
fn map_proxies_by_index_ignores_foreign_conjuncts() {
    let p = |k: usize| ChcExpr::var(ChcVar::new(&format!("{PROXY_PREFIX}{k}"), ChcSort::Bool));
    // Preserve this control's identity, but strengthen its old permissive
    // expectation: actual fresh terms determine indices, never suffixes;
    // foreign identities refuse attribution rather than fabricate a core.
    let proxies = vec![p(5), p(8), p(12), p(21)];
    assert_eq!(
        map_proxies(&[p(12), p(5)], &proxies),
        Some(vec![true, false, true, false])
    );
    assert_eq!(map_proxies(&[p(12), v("x")], &proxies), None);
    assert_eq!(map_proxies(&[p(9)], &proxies), None);
    assert_eq!(
        map_proxies(&[v(&format!("{PROXY_PREFIX}5"))], &proxies),
        None
    );
}

/// F1 worked example (`DESIGN` §9): `x' = x + 1 ∧ y' = y`, frame `y ≤ 3`,
/// cube `{x' = 5, y' ≥ x'}`. The unproxied core would be `{y' ≥ x'}` (the
/// `x' = 5` pin is folded into every other conjunct by the equality
/// closure); the proxied core is BOTH literals, which is the true core.
#[test]
fn proxied_core_keeps_the_pin_the_equality_closure_would_fold() {
    let mut smt = SmtContext::new();
    let bg = vec![
        ChcExpr::eq(v("x1"), ChcExpr::add(v("x"), i(1))),
        ChcExpr::eq(v("y1"), v("y")),
        ChcExpr::le(v("y"), i(3)),
    ];
    let lits = vec![ChcExpr::eq(v("x1"), i(5)), ChcExpr::ge(v("y1"), v("x1"))];
    // Unproxied: the pin is substituted away and cannot appear in the core.
    let unproxied = smt.check_sat_with_assumption_conjuncts(&bg, &lits);
    match unproxied {
        SmtResult::UnsatWithCore(c) => {
            assert!(
                !c.conjuncts.iter().any(|e| *e == lits[0]),
                "unproxied core unexpectedly kept the pin: {:?}",
                c.conjuncts
            );
        }
        SmtResult::Unsat => {}
        other => panic!("expected UNSAT, got {other:?}"),
    }
    // Proxied: both literals.
    let proxies: Vec<ChcExpr> = (0..2)
        .map(|k| ChcExpr::var(ChcVar::new(&format!("{PROXY_PREFIX}{k}"), ChcSort::Bool)))
        .collect();
    let mut bg2 = bg.clone();
    bg2.extend(
        proxies
            .iter()
            .zip(lits.iter())
            .map(|(p, l)| ChcExpr::or(ChcExpr::not(p.clone()), l.clone())),
    );
    smt.reset();
    let proxied = smt.check_sat_with_assumption_conjuncts(&bg2, &proxies);
    match proxied {
        SmtResult::UnsatWithCore(c) => {
            assert_eq!(map_proxies(&c.conjuncts, &proxies), Some(vec![true, true]));
        }
        other => panic!("expected UNSAT with a proxy core, got {other:?}"),
    }
}

#[test]
fn assumption_entry_returns_unknown_on_an_expired_deadline_not_a_hang() {
    let mut smt = SmtContext::new();
    let bg = vec![ChcExpr::le(ChcExpr::add(v("a"), v("b")), i(10))];
    let lits = vec![ChcExpr::ge(v("a"), i(1)), ChcExpr::ge(v("b"), i(1))];
    let expired = ay_core::time::Instant::now() - Duration::from_millis(5);
    let started = std::time::Instant::now();
    let r = {
        let _deadline = crate::smt::deadline::ScopedSmtDeadline::install_until(expired);
        smt.check_sat_with_assumption_conjuncts(&bg, &lits)
    };
    assert!(
        matches!(r, SmtResult::Unknown),
        "expired deadline must give Unknown"
    );
    assert!(started.elapsed() < Duration::from_secs(2));
    smt.reset();
    let r = smt.check_sat_with_assumption_conjuncts(&bg, &lits);
    assert!(
        matches!(r, SmtResult::Sat(_)),
        "no deadline: the same query is SAT"
    );
}

// ---------------------------------------------------------------------------
// QuickXplain (lock L-Q)
// ---------------------------------------------------------------------------

fn mask_of(n: usize, on: &[usize]) -> Vec<bool> {
    let mut m = vec![false; n];
    for &k in on {
        m[k] = true;
    }
    m
}

#[test]
fn quickxplain_finds_the_exact_core_when_the_oracle_is_exact() {
    let n = 12;
    let need = [2usize, 7];
    let mut tests = 0;
    let mut budget = Budget::per_call_only(Duration::from_secs(1));
    let (core, exact) = quickxplain(&vec![true; n], 4, &mut budget, |m, _| {
        tests += 1;
        Some(need.iter().all(|&k| m[k]))
    });
    assert!(exact);
    assert_eq!(core, mask_of(n, &need));
    // ≈ 2k·log2(n/k) + 2k = 4·2.58 + 4 ≈ 14 tests (allow slack).
    assert!(tests <= 24, "too many tests: {tests}");
    // The linear loop below `min_lits`.
    let mut budget = Budget::per_call_only(Duration::from_secs(1));
    let (core, exact) = quickxplain(&vec![true; 6], 16, &mut budget, |m, _| Some(m[1] && m[4]));
    assert!(exact);
    assert_eq!(core, mask_of(6, &[1, 4]));
}

#[test]
fn quickxplain_with_injected_unknowns_stays_grounded_and_marks_inexact_on_budget() {
    let n = 10;
    let need = [1usize, 6, 8];
    // Unknown on every subset of size 4..=6 that contains literal 3.
    let oracle = |m: &[bool], _: &mut Budget| {
        let size = m.iter().filter(|b| **b).count();
        if m[3] && (4..=6).contains(&size) {
            return None;
        }
        Some(need.iter().all(|&k| m[k]))
    };
    let mut budget = Budget::per_call_only(Duration::from_secs(1));
    let (core, _exact) = quickxplain(&vec![true; n], 2, &mut budget, oracle);
    // Grounded: the returned set is UNSAT under the exact predicate.
    assert!(
        need.iter().all(|&k| core[k]),
        "core {core:?} is not grounded"
    );
    // Budget exhaustion after 3 oracle calls: still grounded, reported inexact.
    let mut budget = Budget::new(None, Duration::from_secs(1), 3);
    let (core, exact) = quickxplain(&vec![true; n], 2, &mut budget, |m, b| {
        b.count();
        Some(need.iter().all(|&k| m[k]))
    });
    assert!(!exact);
    assert!(
        need.iter().all(|&k| core[k]),
        "core {core:?} is not grounded"
    );
    // A single-literal mask is returned as is without a query.
    let mut budget = Budget::per_call_only(Duration::from_secs(1));
    let (core, exact) = quickxplain(&mask_of(5, &[2]), 2, &mut budget, |_, _| panic!("no query"));
    assert!(exact);
    assert_eq!(core, mask_of(5, &[2]));
}

// ---------------------------------------------------------------------------
// Hand CHC problems
// ---------------------------------------------------------------------------

fn lane_config() -> PdrConfig {
    PdrConfig {
        verbose: false,
        use_negated_equality_splits: false,
        ..PdrConfig::default()
    }
    .with_spacer(SpacerLane::rung(1))
}

/// `P(vars)` with `init`: every var = its init constant; `step`: a list of
/// `(var index, StepKind)`; `query`: `P(vars) ∧ bad → false`.
#[derive(Clone, Copy)]
enum Step {
    Inc(i128),
    Copy,
    /// Copy from another variable index.
    From(usize),
}

fn counter_system(
    names: &[&str],
    init: &[i128],
    steps: &[Step],
    bad: Option<ChcExpr>,
    sort: ChcSort,
) -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![sort.clone(); names.len()]);
    let var = |n: &str| ChcExpr::var(ChcVar::new(n, sort.clone()));
    let konst = |k: i128| match sort {
        ChcSort::Real => ChcExpr::Real(k as i64, 1),
        _ => ChcExpr::Int(k),
    };
    let args: Vec<ChcExpr> = names.iter().map(|n| var(n)).collect();
    let args1: Vec<ChcExpr> = names.iter().map(|n| var(&format!("{n}1"))).collect();
    let init_c = ChcExpr::and_all(
        names
            .iter()
            .zip(init.iter())
            .map(|(n, k)| ChcExpr::eq(var(n), konst(*k))),
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), Some(init_c)),
        ClauseHead::Predicate(p, args.clone()),
    ));
    let step_c = ChcExpr::and_all(names.iter().enumerate().map(|(k, n)| {
        let rhs = match steps[k] {
            Step::Inc(d) => ChcExpr::add(var(n), konst(d)),
            Step::Copy => var(n),
            Step::From(j) => var(names[j]),
        };
        ChcExpr::eq(var(&format!("{n}1")), rhs)
    }));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, args.clone())], Some(step_c)),
        ClauseHead::Predicate(p, args1),
    ));
    if let Some(bad) = bad {
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p, args)], Some(bad)),
            ClauseHead::False,
        ));
    }
    (problem, p)
}

fn solver_with(problem: ChcProblem, frames: usize) -> PdrSolver {
    let mut solver = PdrSolver::new(problem, lane_config());
    assert!(solver.spacer_core, "the lane must be on for these tests");
    while solver.frames.len() < frames {
        solver.frames.push(Frame::new());
    }
    solver
}

fn canon(solver: &PdrSolver, p: PredicateId) -> Vec<ChcExpr> {
    solver
        .canonical_vars(p)
        .unwrap()
        .iter()
        .cloned()
        .map(ChcExpr::var)
        .collect()
}

fn pob(p: PredicateId, lits: Vec<ChcExpr>, level: usize) -> ProofObligation {
    ProofObligation::from_cube(p, LitCube::from_lits(lits), level)
}

fn lemma_cube(lemma: &Lemma) -> LitCube {
    match &lemma.formula {
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => LitCube::from_expr(&args[0]),
        ChcExpr::Bool(false) => LitCube::from_lits(Vec::new()),
        other => panic!("lemma is not Not(cube): {other}"),
    }
}

fn budget() -> Budget {
    Budget::new(None, Duration::from_secs(5), 10_000)
}

/// L1 (S2): the lemma's cube `C` is UNSAT under `Hyp::Inductive` at the
/// lemma's level for every clause of the predicate (facts included):
/// `F_{L-1} ∧ ¬C ∧ T ∧ C'` UNSAT and `Init ∧ C` UNSAT — the relative
/// inductiveness that makes `¬C` sound at `L` (and, under the delta frame,
/// at every level below). `Reach` UNSAT at `L` implies it (S2 (a)); a
/// Phase D climb is backed by (b) only.
fn assert_l1(solver: &mut PdrSolver, p: PredicateId, lemma: &Lemma) {
    let cube = lemma_cube(lemma);
    let mut b = budget();
    match solver.oracle_check_all_clauses(p, lemma.level, &cube, Hyp::Inductive, &mut b) {
        Verdict::Unsat { .. } => {}
        Verdict::Sat(m) => panic!(
            "L1 violated: lemma {} at level {} is SAT under Inductive: {m:?}",
            lemma.formula, lemma.level
        ),
        Verdict::Unknown => panic!("L1: oracle Unknown for {}", lemma.formula),
    }
}

/// Block through `block_linear` and return the lemma.
fn block(solver: &mut PdrSolver, pob: &mut ProofObligation) -> Lemma {
    match solver.block_linear(pob, &[]) {
        BlockResult::Blocked(l) => l,
        BlockResult::Reachable(_) => panic!("unexpected Reachable"),
        BlockResult::AlreadyBlocked => panic!("unexpected AlreadyBlocked"),
        BlockResult::MustReachable(_) => panic!("unexpected MustReachable"),
        BlockResult::Unknown => panic!("unexpected Unknown ({:?})", solver.pending_unknown_class),
    }
}

/// Two-literal core out of a five-literal cube: `P(a, b, c, d, e)`, all
/// copied except `a' = a + 1`; `F_1 = {a ≤ 4, b + c ≤ 1}`; POB
/// `{a = 3, b = 1, c = 1, d = 0, e = 0}` at level 2. The step clause needs
/// both `b = 1` and `c = 1` (`b + c ≤ 1` in the body, copies); the fact needs
/// one of the non-zero pins; Phase B then drops `b = 1` (`c = 1` alone is
/// relatively inductive). The lemma has ≤ 2 literals, none of them a pin
/// of `a`, `d` or `e`, and satisfies L1.
#[test]
fn two_literal_core_from_a_five_literal_cube() {
    let (problem, p) = counter_system(
        &["a", "b", "c", "d", "e"],
        &[0, 0, 0, 0, 0],
        &[Step::Inc(1), Step::Copy, Step::Copy, Step::Copy, Step::Copy],
        Some(ChcExpr::ge(v("a"), i(100))),
        ChcSort::Int,
    );
    let mut solver = solver_with(problem, 4);
    let c = canon(&solver, p);
    solver.frames[1].add_lemma(Lemma::new(p, ChcExpr::le(c[0].clone(), i(4)), 1));
    solver.frames[1].add_lemma(Lemma::new(
        p,
        ChcExpr::le(ChcExpr::add(c[1].clone(), c[2].clone()), i(1)),
        1,
    ));
    let mut pob = pob(
        p,
        vec![
            ChcExpr::eq(c[0].clone(), i(3)),
            ChcExpr::eq(c[1].clone(), i(1)),
            ChcExpr::eq(c[2].clone(), i(1)),
            ChcExpr::eq(c[3].clone(), i(0)),
            ChcExpr::eq(c[4].clone(), i(0)),
        ],
        2,
    );
    let lemma = block(&mut solver, &mut pob);
    let cube = lemma_cube(&lemma);
    assert!(
        cube.len() <= 2,
        "expected ≤ 2 literals, got {}: {}",
        cube.len(),
        lemma.formula
    );
    for lit in cube.lits() {
        let names: Vec<String> = lit.vars().into_iter().map(|x| x.name).collect();
        assert!(
            names
                .iter()
                .all(|nm| nm == &c[1].to_string() || nm == &c[2].to_string()),
            "unexpected literal {lit} in lemma {}",
            lemma.formula
        );
    }
    assert!(lemma.level >= 2);
    assert_l1(&mut solver, p, &lemma);
    let st = &solver.spacer_stats;
    assert_eq!(st.core_confirm_disagree, 0, "proxied cores must confirm");
    assert!(st.seed_core_size_hist.count() >= 1);
    assert_eq!(solver.lane_lemma_pending, Some(true), "Phase B generalised");
}

/// A drop that breaks relative inductiveness is rejected: `P(x, y)` in
/// lockstep (`x' = x + 1 ∧ y' = y + 1`), `F_1 = {x ≤ y}`; POB
/// `{x ≥ 5, y ≤ 3}` at level 2. Dropping `y ≤ 3` leaves `{x ≥ 5}`, whose
/// Q2 `x ≤ y ∧ ¬(x ≥ 5) ∧ step ∧ x' ≥ 5` is SAT (`x = 4`); dropping `x ≥ 5`
/// leaves `{y ≤ 3}`, which the fact clause satisfies (`y = 0`). Both
/// literals survive; the lemma is exactly `¬(x ≥ 5 ∧ y ≤ 3)` at level 2 and
/// Phase D does not climb (`F_2` is empty).
#[test]
fn a_drop_that_breaks_relative_inductiveness_is_rejected() {
    let (problem, p) = counter_system(
        &["x", "y"],
        &[0, 0],
        &[Step::Inc(1), Step::Inc(1)],
        Some(ChcExpr::ge(v("x"), i(100))),
        ChcSort::Int,
    );
    let mut solver = solver_with(problem, 4);
    let c = canon(&solver, p);
    solver.frames[1].add_lemma(Lemma::new(p, ChcExpr::le(c[0].clone(), c[1].clone()), 1));
    let l_x = ChcExpr::ge(c[0].clone(), i(5));
    let l_y = ChcExpr::le(c[1].clone(), i(3));
    let mut pob = pob(p, vec![l_x.clone(), l_y.clone()], 2);
    let lemma = block(&mut solver, &mut pob);
    let cube = lemma_cube(&lemma);
    assert_eq!(
        cube.len(),
        2,
        "both literals must survive: {}",
        lemma.formula
    );
    assert!(cube.lits().contains(&l_x) && cube.lits().contains(&l_y));
    assert_eq!(
        lemma.level, 2,
        "no climb: F_2 is empty and x = 4 reaches x' = 5"
    );
    assert!(
        solver.spacer_stats.ind_gen_queries_b >= 2,
        "both drops were tried"
    );
    assert_l1(&mut solver, p, &lemma);
}

/// Strict LRA bound preserved: `P(x, y)` over Real, `x' = x + 1 ∧ y' = y`,
/// `F_1 = {x ≤ 1}`; POB `{x > 2, y = 1}` at level 2. `x > 2` is essential
/// and strict (`x ≥ 2` would be reachable from `x = 1`); the proxied lane
/// answers `Unknown` on LRA, so the seed is recovered by Phase A. The
/// surviving literal is exactly the strict `x > 2`.
#[test]
fn strict_lra_bound_is_preserved() {
    let (problem, p) = counter_system(
        &["x", "y"],
        &[0, 0],
        &[Step::Inc(1), Step::Copy],
        Some(ChcExpr::ge(rv("x"), ChcExpr::Real(100, 1))),
        ChcSort::Real,
    );
    let mut solver = solver_with(problem, 3);
    let c = canon(&solver, p);
    solver.frames[1].add_lemma(Lemma::new(
        p,
        ChcExpr::le(c[0].clone(), ChcExpr::Real(1, 1)),
        1,
    ));
    let strict = ChcExpr::gt(c[0].clone(), ChcExpr::Real(2, 1));
    let mut pob = pob(
        p,
        vec![
            strict.clone(),
            ChcExpr::eq(c[1].clone(), ChcExpr::Real(1, 1)),
        ],
        2,
    );
    let lemma = block(&mut solver, &mut pob);
    let cube = lemma_cube(&lemma);
    assert!(
        cube.lits().contains(&strict),
        "the strict literal must survive verbatim: {}",
        lemma.formula
    );
    assert!(cube.len() <= 2);
    for lit in cube.lits() {
        assert!(
            !matches!(lit, ChcExpr::Op(ChcOp::Ge, _)),
            "strictness rewritten: {lit}"
        );
    }
    assert_l1(&mut solver, p, &lemma);
    // No proxied core on LRA: the seed came through Phase A (verdict solves).
    assert!(solver.spacer_stats.ind_gen_queries_a >= 1 || cube.len() == 2);
}

/// LIA divisibility literal kept: `P(x)`, init `x = 0`, `x' = x + 2`; POB
/// `{x ≥ 1, x mod 2 = 1}` at level 1. The parity literal alone is
/// relatively inductive (and inductive), `x ≥ 1` is not needed; the lemma
/// keeps the `mod` literal.
#[test]
fn lia_divisibility_literal_is_kept() {
    let (problem, p) = counter_system(
        &["x"],
        &[0],
        &[Step::Inc(2)],
        Some(ChcExpr::eq(
            ChcExpr::Op(ChcOp::Mod, vec![v("x").into(), i(2).into()]),
            i(1),
        )),
        ChcSort::Int,
    );
    let mut solver = solver_with(problem, 3);
    let c = canon(&solver, p);
    let parity = ChcExpr::eq(
        ChcExpr::Op(ChcOp::Mod, vec![c[0].clone().into(), i(2).into()]),
        i(1),
    );
    let mut pob = pob(p, vec![ChcExpr::ge(c[0].clone(), i(1)), parity.clone()], 1);
    let lemma = block(&mut solver, &mut pob);
    let cube = lemma_cube(&lemma);
    assert!(
        cube.lits().contains(&parity),
        "the divisibility literal must be kept: {}",
        lemma.formula
    );
    assert!(cube.len() <= 2);
    assert_l1(&mut solver, p, &lemma);
}

/// Confirmation disagreement is counted and repaired: an injected exact core
/// `{x = 0}` for POB `{x = 0, y = 1}` at level 1 on `x' = x + 1 ∧ y' = y`
/// (init `x = 0 ∧ y = 0`) is SAT under Reach (the fact clause admits
/// `x = 0`); Phase 0 counts the disagreement, falls back to the full cube,
/// and Phase A recovers the real core `{y = 1}`.
#[test]
fn confirmation_disagreement_is_counted_and_the_seed_repaired() {
    let (problem, p) = counter_system(
        &["x", "y"],
        &[0, 0],
        &[Step::Inc(1), Step::Copy],
        Some(ChcExpr::ge(v("x"), i(100))),
        ChcSort::Int,
    );
    let mut solver = solver_with(problem, 3);
    let c = canon(&solver, p);
    let pob = pob(
        p,
        vec![
            ChcExpr::eq(c[0].clone(), i(0)),
            ChcExpr::eq(c[1].clone(), i(1)),
        ],
        1,
    );
    let wrong = |ci: usize| ClauseCore {
        clause_index: ci,
        fact_index: None,
        core: vec![true, false],
        exact: true,
        had_exclusion: false,
        uses_level: None,
    };
    let lemma = solver
        .lemma_from_cores(&pob, &[wrong(0), wrong(1)], &[])
        .expect("a lemma");
    assert_eq!(solver.spacer_stats.core_confirm_disagree, 1);
    let cube = lemma_cube(&lemma);
    assert_eq!(
        cube.lits(),
        &[ChcExpr::eq(c[1].clone(), i(1))],
        "{}",
        lemma.formula
    );
    assert_l1(&mut solver, p, &lemma);
}

/// Lock L-0: level 0 is fact-only and a level-0 lemma reaches level 1 only
/// through a real Q2 at level 1. `{x = 3}` on the unit counter climbs
/// (`x = 0 → x' = 1 ≠ 3`); `{x = 1}` does not (`x = 0 → x' = 1`).
#[test]
fn level_zero_is_fact_only_and_climbs_to_one_only_through_q2() {
    let (problem, p) = counter_system(
        &["x"],
        &[0],
        &[Step::Inc(1)],
        Some(ChcExpr::ge(v("x"), i(100))),
        ChcSort::Int,
    );
    let mut solver = solver_with(problem, 2);
    let c = canon(&solver, p);
    let mut pob3 = pob(p, vec![ChcExpr::eq(c[0].clone(), i(3))], 0);
    let lemma3 = block(&mut solver, &mut pob3);
    assert_eq!(
        lemma3.level, 1,
        "{}: climbed through the level-1 Q2",
        lemma3.formula
    );
    assert!(solver.spacer_stats.ind_gen_queries_d >= 1);
    assert_eq!(solver.spacer_stats.level_climbs, 1);
    assert_l1(&mut solver, p, &lemma3);
    let mut pob1 = pob(p, vec![ChcExpr::eq(c[0].clone(), i(1))], 0);
    let lemma1 = block(&mut solver, &mut pob1);
    assert_eq!(
        lemma1.level, 0,
        "{}: x' = 1 is reachable from init",
        lemma1.formula
    );
    assert_eq!(solver.spacer_stats.level_climbs, 1);
    // Level 0 never issues a single-body query: the oracle at level 0 on a
    // cube the step clause could reach is still UNSAT (fact-only).
    let mut b = budget();
    let reach1 = LitCube::from_lits(vec![ChcExpr::eq(c[0].clone(), i(1))]);
    assert!(matches!(
        solver.oracle_check_all_clauses(p, 0, &reach1, Hyp::Reach, &mut b),
        Verdict::Unsat { .. }
    ));
}

/// INV-L3: an exclusion-tainted block whose exclusion-free confirmation is
/// SAT returns `Unknown`; an untainted-equivalent one (unreachable cube)
/// yields a lemma.
#[test]
fn exclusion_dependent_block_is_unknown_inv_l3() {
    let (problem, p) = counter_system(
        &["x"],
        &[0],
        &[Step::Inc(1)],
        Some(ChcExpr::ge(v("x"), i(100))),
        ChcSort::Int,
    );
    let mut solver = solver_with(problem, 3);
    let c = canon(&solver, p);
    let tainted = |ci: usize| ClauseCore {
        clause_index: ci,
        fact_index: None,
        core: vec![true],
        exact: false,
        had_exclusion: true,
        uses_level: None,
    };
    // {x = 1} at level 1 IS reachable exclusion-free (x = 0 → x' = 1).
    let reachable = pob(p, vec![ChcExpr::eq(c[0].clone(), i(1))], 1);
    let r = solver.lemma_from_cores(&reachable, &[tainted(0), tainted(1)], &[]);
    assert_eq!(r.err(), Some(super::DeriveError::ExclusionDependent));
    // {x = 5} at level 1 is not: the tainted seed is re-established.
    let unreachable = pob(p, vec![ChcExpr::eq(c[0].clone(), i(5))], 1);
    let lemma = solver
        .lemma_from_cores(&unreachable, &[tainted(0), tainted(1)], &[])
        .expect("re-established exclusion-free");
    assert_l1(&mut solver, p, &lemma);
    // And through block_linear the class is recorded.
    let mut pob_r = pob(p, vec![ChcExpr::eq(c[0].clone(), i(1))], 1);
    assert!(matches!(
        solver.block_linear(&mut pob_r, &[]),
        BlockResult::Reachable(_)
    ));
}

/// Lemma `false` only after the empty-seed confirmation (property iv):
/// `Q(y) ← P(x) ∧ x < 0 ∧ y = x` with `F_1(P) = {x ≥ 0}`. An injected EMPTY
/// exact core (the background alone is UNSAT) is confirmed by Phase 0 on the
/// empty cube and yields the explicit `false` at level 2; the same injected
/// empty core on a predicate whose background is SAT is refuted by the
/// confirmation (disagreement counted) and the lemma is not `false`.
#[test]
fn lemma_false_only_after_the_empty_seed_confirmation() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), Some(ChcExpr::eq(v("x"), i(0)))),
        ClauseHead::Predicate(p, vec![v("x")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![v("x")])],
            Some(ChcExpr::eq(v("x1"), ChcExpr::add(v("x"), i(1)))),
        ),
        ClauseHead::Predicate(p, vec![v("x1")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![v("x")])],
            Some(ChcExpr::and(
                ChcExpr::lt(v("x"), i(0)),
                ChcExpr::eq(v("y"), v("x")),
            )),
        ),
        ClauseHead::Predicate(q, vec![v("y")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![v("y")])], Some(ChcExpr::le(v("y"), i(-1)))),
        ClauseHead::False,
    ));
    let mut solver = solver_with(problem, 3);
    let cp = canon(&solver, p);
    let cq = canon(&solver, q);
    solver.frames[1].add_lemma(Lemma::new(p, ChcExpr::ge(cp[0].clone(), i(0)), 1));
    let empty_core = ClauseCore {
        clause_index: 2,
        fact_index: None,
        core: vec![false],
        exact: true,
        had_exclusion: false,
        uses_level: None,
    };
    // Confirmed: F_1(P) ∧ x < 0 is UNSAT on its own ⇒ lemma `false` for Q.
    let pob_q = pob(q, vec![ChcExpr::eq(cq[0].clone(), i(-1))], 2);
    let lemma = solver
        .lemma_from_cores(&pob_q, &[empty_core.clone()], &[])
        .expect("a lemma");
    assert_eq!(
        lemma.formula,
        ChcExpr::Bool(false),
        "lemma false for an unreachable Q"
    );
    assert_eq!(
        solver.spacer_stats.core_confirm_checks, 1,
        "the empty seed was confirmed"
    );
    assert_eq!(solver.spacer_stats.core_confirm_disagree, 0);
    assert_l1(&mut solver, q, &lemma);
    // Refuted: at level 3 the body frame F_2(P) is empty, so x < 0 ∧ y = x is
    // SAT on its own ⇒ the injected empty core disagrees (counted); the full
    // cube {y = 5} IS blocked (y = x < 0) and the lemma is `¬(y = 5)`, never
    // an unconfirmed `false`.
    let pob_q3 = pob(q, vec![ChcExpr::eq(cq[0].clone(), i(5))], 3);
    let lemma3 = solver
        .lemma_from_cores(&pob_q3, &[empty_core], &[])
        .expect("a lemma");
    assert_ne!(lemma3.formula, ChcExpr::Bool(false));
    assert_eq!(solver.spacer_stats.core_confirm_disagree, 1);
    assert_l1(&mut solver, q, &lemma3);
    // Through block_linear: the real cores decide; the lemma is either the
    // confirmed `false` or `¬(y = -1)`, and it satisfies L1 either way.
    let mut pob_b = pob(q, vec![ChcExpr::eq(cq[0].clone(), i(-1))], 2);
    let lemma_b = block(&mut solver, &mut pob_b);
    assert_l1(&mut solver, q, &lemma_b);
}

/// The Q2 shape: `Hyp::Inductive` adds `¬cube(body)` only when the body
/// predicate is the POB's; a cube that is inductive relative to `F_{ℓ-1}`
/// but not reachable-blocked (Reach SAT) shows the two shapes differ.
#[test]
fn inductive_shape_carries_the_negated_cube_on_the_body() {
    let (problem, p) = counter_system(
        &["x"],
        &[0],
        &[Step::Copy],
        Some(ChcExpr::ge(v("x"), i(100))),
        ChcSort::Int,
    );
    let mut solver = solver_with(problem, 3);
    let c = canon(&solver, p);
    // No frame lemma at 1: Reach at level 2 for {x = 7} is SAT (x = 7 → x' = 7),
    // Inductive is UNSAT (¬(x = 7) ∧ x' = x ∧ x' = 7) plus the fact (x = 0).
    let cube = LitCube::from_lits(vec![ChcExpr::eq(c[0].clone(), i(7))]);
    let mut b = budget();
    assert!(matches!(
        solver.oracle_check_all_clauses(p, 2, &cube, Hyp::Reach, &mut b),
        Verdict::Sat(_)
    ));
    assert!(matches!(
        solver.oracle_check_all_clauses(p, 2, &cube, Hyp::Inductive, &mut b),
        Verdict::Unsat { .. }
    ));
    // Push from 1 to 2 with F_1 = {x ≤ 3}: the body frame is frame_hyp(1).
    solver.frames[1].add_lemma(Lemma::new(p, ChcExpr::le(c[0].clone(), i(3)), 1));
    assert!(matches!(
        solver.oracle_check_all_clauses(p, 1, &cube, Hyp::Push, &mut b),
        Verdict::Unsat { .. }
    ));
}

/// L1 property on generated 2–4-variable counter systems (deterministic
/// LCG): pins, a `var = var` literal and a bound; the lemma from
/// `block_linear` is UNSAT under `Reach` at its level, and `Unknown` never
/// comes back from a blocked POB (lock L2 on this set).
#[test]
fn l1_property_on_generated_counter_systems() {
    let mut seed: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = |m: u64| {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (seed >> 33) % m
    };
    let names = ["a", "b", "c", "d"];
    let mut lemmas = 0;
    for _case in 0..12 {
        let nv = 2 + next(3) as usize;
        let init: Vec<i128> = (0..nv).map(|_| next(3) as i128).collect();
        let steps: Vec<Step> = (0..nv)
            .map(|k| match next(3) {
                0 => Step::Inc(1 + next(2) as i128),
                1 => Step::Copy,
                _ => Step::From((k + 1) % nv),
            })
            .collect();
        let (problem, p) = counter_system(
            &names[..nv],
            &init,
            &steps,
            Some(ChcExpr::ge(v(names[0]), i(1000))),
            ChcSort::Int,
        );
        let mut solver = solver_with(problem, 4);
        let c = canon(&solver, p);
        // One frame-1 lemma: an upper bound on the first variable.
        solver.frames[1].add_lemma(Lemma::new(p, ChcExpr::le(c[0].clone(), i(5)), 1));
        // A POB the bound makes unreachable at level 2: first var pinned
        // well above the bound, the rest pinned / related.
        let mut lits = vec![ChcExpr::eq(c[0].clone(), i(50 + next(10) as i128))];
        for k in 1..nv {
            match next(3) {
                0 => lits.push(ChcExpr::eq(c[k].clone(), i(next(4) as i128))),
                1 => lits.push(ChcExpr::eq(c[k].clone(), c[k - 1].clone())),
                _ => lits.push(ChcExpr::ge(c[k].clone(), i(next(4) as i128))),
            }
        }
        let mut pob = pob(p, lits, 2);
        match solver.block_linear(&mut pob, &[]) {
            BlockResult::Blocked(lemma) => {
                lemmas += 1;
                assert_l1(&mut solver, p, &lemma);
                assert!(lemma.level >= 2 && lemma.level <= 3);
            }
            BlockResult::Reachable(_) | BlockResult::MustReachable(_) => {}
            BlockResult::AlreadyBlocked => panic!("no already-blocked pre-check in the lane"),
            BlockResult::Unknown => panic!("L2: Unknown from a blocked linear POB"),
        }
        assert_eq!(solver.spacer_stats.core_confirm_disagree, 0);
    }
    assert!(
        lemmas >= 6,
        "the generator must produce blocked POBs ({lemmas})"
    );
}

/// Budget arithmetic: `ind_gen_budget` respects the solve deadline share and
/// the per-call cap; the drop order puts Booleans last.
#[test]
fn budget_and_drop_order_shapes() {
    let (problem, p) = counter_system(&["x"], &[0], &[Step::Inc(1)], None, ChcSort::Int);
    let mut solver = solver_with(problem, 2);
    let _ = p;
    solver.solve_deadline = Some(ay_core::time::Instant::now() + Duration::from_secs(40));
    let b = solver.ind_gen_budget();
    assert_eq!(b.max_calls, 64);
    assert_eq!(b.per_call, Duration::from_secs(2));
    let d = b.deadline.unwrap();
    let left = d.saturating_duration_since(ay_core::time::Instant::now());
    assert!(
        left <= Duration::from_secs(17) && left >= Duration::from_secs(14),
        "{left:?}"
    );
    solver.solve_deadline = None;
    assert!(solver.ind_gen_budget().deadline.is_none());
    let mut b = Budget::new(None, Duration::from_secs(1), 2);
    assert!(!b.exhausted());
    b.count();
    b.count();
    assert!(b.exhausted());
}

// ---------------------------------------------------------------------------
// Whole solves with the lane at rung 1 (`block_linear` dispatched by S)
// ---------------------------------------------------------------------------

fn production_lane_config(secs: u64) -> PdrConfig {
    let mut c = PdrConfig::production(false);
    c.solve_timeout = Some(Duration::from_secs(secs));
    c.with_spacer(SpacerLane::rung(1))
}

/// Lock L2 on tiny problems: with the lane on, a safe counter is `Safe`, an
/// unsafe lockstep system is `Unsafe`, every blocked POB produced exactly one
/// lemma (`lemmas / blocked == 1.00` when any POB was blocked), and no
/// `Unknown` came back from a blocked linear POB.
#[test]
fn whole_solve_rung1_safe_counter_and_unsafe_two_var() {
    // Safe: x = 0; x' = x + 1; x < 0 → false.
    let (problem, _) = counter_system(
        &["x"],
        &[0],
        &[Step::Inc(1)],
        Some(ChcExpr::lt(v("x"), i(0))),
        ChcSort::Int,
    );
    let mut solver = PdrSolver::new(problem, production_lane_config(30));
    assert!(solver.spacer_core);
    let run = solver.solve_with_stats();
    assert!(
        matches!(run.result, crate::pdr::PdrResult::Safe(_)),
        "safe counter under the lane: {:?}",
        std::mem::discriminant(&run.result)
    );
    let st = &solver.spacer_stats;
    if st.blocked_pobs > 0 {
        assert_eq!(st.lemmas, st.blocked_pobs, "one lemma per blocked POB");
    }
    assert!(
        st.root_unknown_by_class.is_empty() && st.child_unknown_by_class.is_empty(),
        "L2: {:?} / {:?}",
        st.root_unknown_by_class,
        st.child_unknown_by_class
    );
    // Unsafe: x = 0 ∧ y = 0; x' = x + 1 ∧ y' = y + 2; y ≥ 5 → false (depth 3).
    let (problem, _) = counter_system(
        &["x", "y"],
        &[0, 0],
        &[Step::Inc(1), Step::Inc(2)],
        Some(ChcExpr::ge(v("y"), i(5))),
        ChcSort::Int,
    );
    let mut solver = PdrSolver::new(problem, production_lane_config(30));
    let run = solver.solve_with_stats();
    assert!(
        matches!(run.result, crate::pdr::PdrResult::Unsafe(_)),
        "unsafe two-var under the lane"
    );
    let st = &solver.spacer_stats;
    if st.blocked_pobs > 0 {
        assert_eq!(st.lemmas, st.blocked_pobs, "one lemma per blocked POB");
    }
    assert_eq!(st.core_confirm_disagree, 0);
}

/// A safe two-counter system that needs a real inductive lemma (not a point
/// exclusion): `x = 0 ∧ y = 0; x' = x + 1 ∧ y' = y + 1; x ≠ y → false`.
/// Under the lane the solve is `Safe` with multi-literal lemmas allowed and
/// zero disagreements; every lane lemma satisfies L1 at its level.
#[test]
fn whole_solve_rung1_lockstep_equality_is_safe() {
    let (problem, p) = counter_system(
        &["x", "y"],
        &[0, 0],
        &[Step::Inc(1), Step::Inc(1)],
        Some(ChcExpr::not(ChcExpr::eq(v("x"), v("y")))),
        ChcSort::Int,
    );
    let mut solver = PdrSolver::new(problem, production_lane_config(30));
    let run = solver.solve_with_stats();
    assert!(
        matches!(run.result, crate::pdr::PdrResult::Safe(_)),
        "lockstep equality is safe"
    );
    let st = &solver.spacer_stats;
    assert_eq!(st.core_confirm_disagree, 0);
    if st.blocked_pobs > 0 {
        assert_eq!(st.lemmas, st.blocked_pobs);
    }
    // Every lemma in the frames for P is relatively inductive at its level
    // (the lane's ones by construction; discovery's ones by admission).
    let lemmas: Vec<Lemma> = solver
        .frames
        .iter()
        .flat_map(|f| f.lemmas.iter().cloned())
        .filter(|l| l.predicate == p && l.level >= 1)
        .collect();
    for lemma in lemmas.iter().take(16) {
        if matches!(lemma.formula, ChcExpr::Op(ChcOp::Not, _)) {
            assert_l1(&mut solver, p, lemma);
        }
    }
}

/// `P(b, a) ← b = 0 ∧ a = 7` (the fact's head letters swapped against the
/// step's), `P(a1, b1) ← P(a, b) ∧ a1 = a + 1 ∧ b1 = b`, bad `bad(a, b)`.
fn swapped_letters_problem(bad: ChcExpr) -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            Vec::new(),
            Some(ChcExpr::and(
                ChcExpr::eq(v("b"), i(0)),
                ChcExpr::eq(v("a"), i(7)),
            )),
        ),
        ClauseHead::Predicate(p, vec![v("b"), v("a")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![v("a"), v("b")])],
            Some(ChcExpr::and(
                ChcExpr::eq(v("a1"), ChcExpr::add(v("a"), i(1))),
                ChcExpr::eq(v("b1"), v("b")),
            )),
        ),
        ClauseHead::Predicate(p, vec![v("a1"), v("b1")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![v("a"), v("b")])], Some(bad)),
        ClauseHead::False,
    ));
    (problem, p)
}

/// Root cause of the R1 `core_confirm_disagree` rows (car_5 16/34,
/// two_counters 1/10, all at level 1): the legacy prev-level-0 Q1 conjoins the
/// fact clause's constraint with the step clause's under the SAME variable
/// names, so a fact variable is captured by an unrelated step variable of the
/// same name (VMT/lustre encodings reuse letters across clauses at different
/// roles). Here the step's body `(a, b)` meets the fact's head `(b, a)`: the
/// unrenamed query holds `a = b ∧ b = a ∧ b = 0 ∧ a = 7` — UNSAT — although the
/// init state is (0, 7) and (1, 7) is one step away. Under the lane the fact is
/// renamed apart: the level-1 POB `{p0 = 1, p1 = 7}` is Reachable, and a whole
/// solve with bad `p0 ≥ 2 ∧ p1 = 7` is Unsafe with no disagreement.
#[test]
fn prev_level_zero_q1_renames_fact_variables_apart_under_the_lane() {
    let (problem, p) = swapped_letters_problem(ChcExpr::and(
        ChcExpr::ge(v("a"), i(2)),
        ChcExpr::eq(v("b"), i(7)),
    ));
    let mut solver = solver_with(problem.clone(), 3);
    let c = canon(&solver, p);
    let mut pob1 = pob(
        p,
        vec![
            ChcExpr::eq(c[0].clone(), i(1)),
            ChcExpr::eq(c[1].clone(), i(7)),
        ],
        1,
    );
    match solver.block_linear(&mut pob1, &[]) {
        BlockResult::Reachable(pred) => {
            assert_eq!(pred.predicate, p);
        }
        BlockResult::Blocked(l) => panic!(
            "fact-local capture: reachable POB blocked with {} (seed from the conflated query)",
            l.formula
        ),
        other => panic!("unexpected {:?}", std::mem::discriminant(&other)),
    }
    // Lane off (HEAD): reported, not asserted — the legacy query is the
    // conflated one (a HEAD defect outside the lane's files, see the WP-L
    // status report).
    let mut legacy = PdrSolver::new(problem.clone(), test_lane_off_config());
    while legacy.frames.len() < 3 {
        legacy.frames.push(Frame::new());
    }
    let mut pob_l = pob(
        p,
        vec![
            ChcExpr::eq(c[0].clone(), i(1)),
            ChcExpr::eq(c[1].clone(), i(7)),
        ],
        1,
    );
    let legacy_reach = legacy.check_predecessor_reachability(&mut pob_l, &[]);
    eprintln!(
        "fact-capture probe, lane OFF: level-1 POB {{p0=1, p1=7}} is {}",
        if legacy_reach.is_ok() {
            "BLOCKED (spurious UNSAT: fact variables captured)"
        } else {
            "not blocked"
        }
    );
    // Whole solve at rung 1: Unsafe (0,7) → (1,7) → (2,7).
    let mut solver = PdrSolver::new(problem, production_lane_config(30));
    let run = solver.solve_with_stats();
    assert!(
        matches!(run.result, crate::pdr::PdrResult::Unsafe(_)),
        "swapped-letters counter is unsafe at depth 2"
    );
    assert_eq!(solver.spacer_stats.core_confirm_disagree, 0);
    assert_eq!(solver.spacer_stats.q1_seed_refuted, 0);
}

fn test_lane_off_config() -> PdrConfig {
    PdrConfig {
        verbose: false,
        use_negated_equality_splits: false,
        ..PdrConfig::default()
    }
    .with_spacer(SpacerLane::OFF)
}
