// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Spacer lane on nonlinear problems (`SpacerLane::nonlinear`,
//! `blocking/reachability/nonlinear.rs`): construction gates, the hyperedge
//! oracle, Safe proofs over hyperedges, counterexample trees built from reach
//! facts (verified by the PDR's own counterexample check before they are
//! returned), and the legacy bypass of `without_nonlinear_lane`.

use super::oracle::{Budget, Hyp, Verdict};
use crate::pdr::config::{PdrConfig, SpacerLane};
use crate::pdr::cube::literals::LitCube;
use crate::pdr::solver::PdrSolver;
use crate::pdr::PdrResult;
use crate::{ChcExpr, ChcParser, ChcProblem, ChcVar};
use std::time::Duration;

fn parse(text: &str) -> ChcProblem {
    ChcParser::parse(text).expect("test CHC parses")
}

fn lane_config(nonlinear: bool) -> PdrConfig {
    let mut lane = SpacerLane::rung(2);
    lane.nonlinear = nonlinear;
    let mut config = PdrConfig::default().with_spacer(lane);
    config.verbose = false;
    config.solve_timeout = Some(Duration::from_secs(30));
    config
}

fn solve(text: &str, nonlinear: bool) -> (PdrResult, PdrSolver) {
    let mut solver = PdrSolver::new(parse(text), lane_config(nonlinear));
    let result = solver.solve();
    (result, solver)
}

/// hopv `repeat`: `R2(a, b) ⇐ a = b + 1`, `R5(a, a, 0)`,
/// `R2(g, f) ∧ R5(f, c, e) ∧ e = b - 1 ∧ b ≠ 0 ⇒ R5(g, c, b)`,
/// `R5(c, 0, a) ∧ c ≠ a ⇒ false`. Safe: `R2(a,b) ⇒ a = b + 1`,
/// `R5(a, c, b) ⇒ a = c + b`. The legacy pipeline enumerates level-0 points
/// here; the lane needs the hyperedge's frame-at-level-0 = facts.
const REPEAT: &str = r"
(set-logic HORN)
(declare-fun R2 (Int Int) Bool)
(declare-fun R5 (Int Int Int) Bool)
(assert (forall ((A Int) (B Int)) (=> (= A (+ B 1)) (R2 A B))))
(assert (forall ((A Int) (C Int) (B Int)) (=> (and (= A C) (= B 0)) (R5 A C B))))
(assert (forall ((G Int) (F Int) (C Int) (E Int) (B Int))
  (=> (and (R2 G F) (R5 F C E) (= E (- B 1)) (not (= B 0))) (R5 G C B))))
(assert (forall ((C Int) (A Int)) (=> (and (R5 C 0 A) (not (= C A))) false)))
(check-sat)
";

/// `F(n, x)`: Fibonacci through a two-body step. Unsafe: `F(5, 5)` is
/// reachable (fib 0..5 = 0 1 1 2 3 5) and the query forbids it.
const FIB_UNSAFE: &str = r"
(set-logic HORN)
(declare-fun F (Int Int) Bool)
(assert (forall ((N Int) (X Int)) (=> (and (= N 0) (= X 0)) (F N X))))
(assert (forall ((N Int) (X Int)) (=> (and (= N 1) (= X 1)) (F N X))))
(assert (forall ((N Int) (A Int) (B Int) (X Int))
  (=> (and (F (- N 1) A) (F (- N 2) B) (>= N 2) (= X (+ A B))) (F N X))))
(assert (forall ((N Int) (X Int)) (=> (and (F N X) (= N 5) (= X 5)) false)))
(check-sat)
";

/// The same system with a true property: Fibonacci values are nonnegative.
const FIB_SAFE: &str = r"
(set-logic HORN)
(declare-fun F (Int Int) Bool)
(assert (forall ((N Int) (X Int)) (=> (and (= N 0) (= X 0)) (F N X))))
(assert (forall ((N Int) (X Int)) (=> (and (= N 1) (= X 1)) (F N X))))
(assert (forall ((N Int) (A Int) (B Int) (X Int))
  (=> (and (F (- N 1) A) (F (- N 2) B) (>= N 2) (= X (+ A B))) (F N X))))
(assert (forall ((N Int) (X Int)) (=> (and (F N X) (< X 0)) false)))
(check-sat)
";

/// Two predicates joined by a hyperedge whose join is unsafe only through
/// DEEP derivations of both atoms: `P` counts up by 1 from 0, `Q` counts up
/// by 2 from 0, and `P(x) ∧ Q(y) ⇒ S(x + y)`; `S(7) ⇒ false` is reachable
/// (e.g. x = 1, y = 6 or x = 3, y = 4).
const JOIN_UNSAFE: &str = r"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun S (Int) Bool)
(assert (forall ((X Int)) (=> (= X 0) (P X))))
(assert (forall ((X Int) (Y Int)) (=> (and (P X) (= Y (+ X 1))) (P Y))))
(assert (forall ((X Int)) (=> (= X 0) (Q X))))
(assert (forall ((X Int) (Y Int)) (=> (and (Q X) (= Y (+ X 2))) (Q Y))))
(assert (forall ((X Int) (Y Int) (Z Int)) (=> (and (P X) (Q Y) (= Z (+ X Y))) (S Z))))
(assert (forall ((Z Int)) (=> (and (S Z) (= Z 7)) false)))
(check-sat)
";

/// The same join with a true property: `x ≥ 0 ∧ y ≥ 0 ⇒ x + y ≥ 0`.
const JOIN_SAFE: &str = r"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun S (Int) Bool)
(assert (forall ((X Int)) (=> (= X 0) (P X))))
(assert (forall ((X Int) (Y Int)) (=> (and (P X) (= Y (+ X 1))) (P Y))))
(assert (forall ((X Int)) (=> (= X 0) (Q X))))
(assert (forall ((X Int) (Y Int)) (=> (and (Q X) (= Y (+ X 2))) (Q Y))))
(assert (forall ((X Int) (Y Int) (Z Int)) (=> (and (P X) (Q Y) (= Z (+ X Y))) (S Z))))
(assert (forall ((Z Int)) (=> (and (S Z) (< Z 0)) false)))
(check-sat)
";

#[test]
fn nonlinear_lane_construction_gates() {
    let solver = PdrSolver::new(parse(REPEAT), lane_config(true));
    assert!(!solver.problem_is_linear);
    assert!(
        solver.spacer_core,
        "rung 2 runs the lane on nonlinear problems"
    );
    assert!(solver.lane_nonlinear);
    assert!(
        !solver.config.use_pob_push,
        "the lane runs with the Spacer profile"
    );

    let solver = PdrSolver::new(parse(REPEAT), lane_config(false));
    assert!(!solver.spacer_core);
    assert!(!solver.lane_nonlinear);
    assert_eq!(solver.spacer_stats.lane_bypassed_nonlinear, 1);
    assert!(
        solver.config.use_pob_push,
        "a bypassed problem keeps its profile"
    );

    // The portfolio's second PDR keeps the legacy profile on nonlinear problems.
    let splits = PdrConfig::portfolio_variant_with_splits();
    assert!(!splits.spacer.nonlinear);
    assert!(!PdrConfig::portfolio_spacer_variant().spacer.nonlinear);
    let solver = PdrSolver::new(parse(REPEAT), splits);
    assert!(!solver.lane_nonlinear);

    // `nonlinear` without `free_pob` is refused.
    let mut lane = SpacerLane::rung(1);
    lane.nonlinear = true;
    assert!(!lane.validate(false).nonlinear);
}

#[test]
fn nonlinear_lane_proves_repeat_safe() {
    let (result, solver) = solve(REPEAT, true);
    assert!(
        matches!(result, PdrResult::Safe(_)),
        "repeat is safe; got {result:?}"
    );
    assert!(
        solver.spacer_stats.nl_q1 > 0,
        "the hyperedge went through the lane"
    );
}

#[test]
fn nonlinear_lane_finds_fibonacci_counterexample_tree() {
    let (result, solver) = solve(FIB_UNSAFE, true);
    let PdrResult::Unsafe(cex) = result else {
        panic!("F(5, 5) is reachable; got {result:?}");
    };
    assert!(solver.spacer_stats.nl_reach_facts > 0);
    assert!(
        solver.spacer_stats.nl_cex > 0,
        "the tree came from reach facts"
    );
    let witness = cex
        .witness
        .expect("reach-fact counterexamples carry a derivation tree");
    // fib(5) needs fib(4) and fib(3): a tree, not a path.
    assert!(
        witness.entries.iter().any(|e| e.premises.len() == 2),
        "a two-premise (hyperedge) derivation step"
    );
}

#[test]
fn nonlinear_lane_proves_fibonacci_nonnegative() {
    let (result, solver) = solve(FIB_SAFE, true);
    assert!(
        matches!(result, PdrResult::Safe(_)),
        "fib values are nonnegative; got {result:?}"
    );
    assert!(solver.spacer_stats.nl_q1 > 0);
}

#[test]
fn nonlinear_lane_join_unsafe_and_safe() {
    let (result, solver) = solve(JOIN_UNSAFE, true);
    assert!(
        matches!(result, PdrResult::Unsafe(_)),
        "S(7) is reachable; got {result:?}"
    );
    assert!(solver.spacer_stats.nl_reach_facts > 0);
    let (result, _) = solve(JOIN_SAFE, true);
    assert!(
        matches!(result, PdrResult::Safe(_)),
        "x + y >= 0; got {result:?}"
    );
}

/// The hyperedge oracle: `Reach` on `S`'s cube `z = 7` at level 1 has only
/// the facts of `P` and `Q` as body hypotheses (`x = 0`, `y = 0`), so it is
/// UNSAT with the one-literal core; at level 2 (bodies = true frames) it is SAT.
#[test]
fn hyperedge_oracle_uses_facts_at_frame_zero() {
    let mut solver = PdrSolver::new(parse(JOIN_UNSAFE), lane_config(true));
    assert!(solver.lane_nonlinear);
    while solver.frames.len() < 3 {
        solver.frames.push(crate::pdr::frame::Frame::new());
    }
    let s = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "S")
        .unwrap()
        .id;
    let canon: Vec<ChcVar> = solver.canonical_vars(s).unwrap().to_vec();
    let cube = LitCube::from_lits(vec![ChcExpr::eq(
        ChcExpr::var(canon[0].clone()),
        ChcExpr::Int(7),
    )]);
    let mut budget = Budget::per_call_only(Duration::from_secs(5));
    match solver.oracle_check_all_clauses(s, 1, &cube, Hyp::Reach, &mut budget) {
        Verdict::Unsat { core, .. } => assert_eq!(core.len(), 1),
        Verdict::Sat(_) => panic!("level 1: P and Q are their facts (0, 0), z = 0"),
        Verdict::Unknown => panic!("level 1 Reach must decide"),
    }
    match solver.oracle_check_all_clauses(s, 2, &cube, Hyp::Reach, &mut budget) {
        Verdict::Sat(_) => {}
        _ => panic!("level 2: no lemma on P or Q yet, z = 7 is consistent"),
    }
}

/// A multi-atom QUERY (`P(x) ∧ Q(y) ∧ x + y = 7 → false`): no root POB
/// exists; the lane's query step covers both atoms and builds a ground
/// derivation of `false`.
const HYPER_QUERY_UNSAFE: &str = r"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((X Int)) (=> (= X 0) (P X))))
(assert (forall ((X Int) (Y Int)) (=> (and (P X) (= Y (+ X 1))) (P Y))))
(assert (forall ((X Int)) (=> (= X 0) (Q X))))
(assert (forall ((X Int) (Y Int)) (=> (and (Q X) (= Y (+ X 2))) (Q Y))))
(assert (forall ((X Int) (Y Int)) (=> (and (P X) (Q Y) (= (+ X Y) 7)) false)))
(check-sat)
";

/// The same system with a true multi-atom property.
const HYPER_QUERY_SAFE: &str = r"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((X Int)) (=> (= X 0) (P X))))
(assert (forall ((X Int) (Y Int)) (=> (and (P X) (= Y (+ X 1))) (P Y))))
(assert (forall ((X Int)) (=> (= X 0) (Q X))))
(assert (forall ((X Int) (Y Int)) (=> (and (Q X) (= Y (+ X 2))) (Q Y))))
(assert (forall ((X Int) (Y Int)) (=> (and (P X) (Q Y) (< (+ X Y) 0)) false)))
(check-sat)
";

#[test]
fn nonlinear_lane_multi_atom_query_ground_counterexample() {
    let (result, solver) = solve(HYPER_QUERY_UNSAFE, true);
    let PdrResult::Unsafe(cex) = result else {
        panic!("x + y = 7 is reachable; got {result:?}");
    };
    let ground = cex
        .ground_derivation
        .as_ref()
        .expect("the lane's counterexamples carry a ground derivation");
    assert!(
        crate::ground_derivation::validate_ground_derivation(&solver.problem, ground).is_ok(),
        "the ground derivation replays on the problem"
    );
    let root = &ground.steps[ground.query_step];
    assert_eq!(root.premises.len(), 2, "both query atoms are premises");
}

#[test]
fn nonlinear_lane_multi_atom_query_safe() {
    let (result, solver) = solve(HYPER_QUERY_SAFE, true);
    assert!(
        matches!(result, PdrResult::Safe(_)),
        "x + y >= 0; got {result:?}"
    );
    assert!(solver.spacer_stats.nl_q1 > 0);
}

/// Every lane counterexample (single-body query included) replays as a
/// ground derivation.
#[test]
fn nonlinear_lane_fibonacci_ground_derivation_replays() {
    let (result, solver) = solve(FIB_UNSAFE, true);
    let PdrResult::Unsafe(cex) = result else {
        panic!("F(5, 5) is reachable; got {result:?}");
    };
    if let Some(ground) = cex.ground_derivation.as_ref() {
        assert!(
            crate::ground_derivation::validate_ground_derivation(&solver.problem, ground).is_ok()
        );
    } else {
        assert_eq!(
            solver.spacer_stats.nl_cex, 0,
            "lane counterexamples carry one"
        );
    }
}

/// The CHC-COMP nullary-fail pattern around a two-atom join:
/// `P(x) ∧ Q(y) ∧ x + y = 7 ⇒ FAIL`, `FAIL ⇒ false`. `PdrSolver::new`
/// expands it into the query `P(x) ∧ Q(y) ∧ x + y = 7 ⇒ false` and drops
/// both originals, so the search's derivation indexes the expanded clauses.
const NULLARY_FAIL_UNSAFE: &str = r"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun FAIL () Bool)
(assert (forall ((X Int)) (=> (= X 0) (P X))))
(assert (forall ((X Int) (Y Int)) (=> (and (P X) (= Y (+ X 1))) (P Y))))
(assert (forall ((X Int)) (=> (= X 0) (Q X))))
(assert (forall ((X Int) (Y Int)) (=> (and (Q X) (= Y (+ X 2))) (Q Y))))
(assert (forall ((X Int) (Y Int)) (=> (and (P X) (Q Y) (= (+ X Y) 7)) FAIL)))
(assert (forall ((CHC_COMP_UNUSED Bool)) (=> (and FAIL) false)))
(check-sat)
";

/// The expansion's clause origins, and the Unsafe result's derivation
/// restated over the INPUT problem: the root is the `FAIL ⇒ false` query and
/// its premise the step through `P ∧ Q ⇒ FAIL` (callers validate there).
#[test]
fn nullary_expansion_counterexample_restated_over_the_input_problem() {
    use crate::problem::ExpandedClauseOrigin;
    let input = parse(NULLARY_FAIL_UNSAFE);
    let mut expanded = input.clone();
    let expansion = expanded
        .expand_nullary_fail_queries_recorded(false)
        .expect("the nullary fail pattern expands");
    assert_eq!(
        expansion.origins(),
        &[
            ExpandedClauseOrigin::Kept(0),
            ExpandedClauseOrigin::Kept(1),
            ExpandedClauseOrigin::Kept(2),
            ExpandedClauseOrigin::Kept(3),
            ExpandedClauseOrigin::Expanded {
                into_fail: 4,
                fail_query: 5
            },
        ]
    );
    let mut solver = PdrSolver::new(input.clone(), lane_config(true));
    let result = solver.solve();
    let PdrResult::Unsafe(cex) = result else {
        panic!("x = 1, y = 6 reaches FAIL; got {result:?}");
    };
    let ground = cex
        .ground_derivation
        .as_ref()
        .expect("the restated derivation validates on the input problem");
    assert!(crate::ground_derivation::validate_ground_derivation(&input, ground).is_ok());
    let root = &ground.steps[ground.query_step];
    assert_eq!(root.clause_index, 5, "the root is the input's FAIL query");
    assert_eq!(root.premises.len(), 1);
    assert_eq!(ground.steps[root.premises[0]].clause_index, 4);
}

#[test]
fn nonlinear_construction_preserves_every_explicit_frame_ceiling() {
    for ceiling in [0, 1, 3, 19, 20, 50, 99, 100, 101] {
        let config = lane_config(true).with_max_frames(ceiling);
        let solver = PdrSolver::new(parse(REPEAT), config);
        assert!(solver.lane_nonlinear);
        assert!(solver.spacer_core);
        assert_eq!(solver.config.max_frames, ceiling, "ceiling {ceiling}");
    }
}

#[test]
fn nonlinear_selection_never_promotes_an_ambiguous_default_frame_ceiling() {
    // max_frames is a public number: default20 and explicit20 cannot be
    // distinguished here. Neither is permission to grant 100 frames.
    let default_ceiling = PdrConfig::default().max_frames;
    for nonlinear in [false, true] {
        let config = lane_config(nonlinear);
        assert_eq!(config.max_frames, default_ceiling);
        let solver = PdrSolver::new(parse(REPEAT), config);
        assert_eq!(solver.lane_nonlinear, nonlinear);
        assert_eq!(solver.config.max_frames, default_ceiling);
    }
}

#[test]
fn frame_ceiling_is_independent_of_existing_builder_order() {
    let mut lane = SpacerLane::rung(2);
    lane.nonlinear = true;
    let before = PdrConfig::default().with_max_frames(3).with_spacer(lane);
    let after = PdrConfig::default().with_spacer(lane).with_max_frames(3);
    for config in [before, after] {
        let solver = PdrSolver::new(parse(REPEAT), config);
        assert!(solver.lane_nonlinear);
        assert_eq!(solver.config.max_frames, 3);
    }
}
