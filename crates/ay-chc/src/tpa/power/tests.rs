// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::bool_partition::{classify_bool_partition, normalize_constraints_for_partition};
use super::*;
use crate::expr_vars::expr_var_names;
use crate::farkas::parse_linear_constraint;
use crate::tpa::TpaConfig;
use crate::{ChcProblem, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

fn contains_ite(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Op(crate::ChcOp::Ite, _) => true,
        ChcExpr::Op(_, args) => args.iter().any(|arg| contains_ite(arg)),
        _ => false,
    }
}

#[test]
fn test_normalize_constraints_for_partition_eliminates_arithmetic_ite() {
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let mut substitutions = FxHashMap::default();
    substitutions.insert(flag.name.clone(), ChcExpr::Bool(true));

    let normalized = normalize_constraints_for_partition(
        &[ChcExpr::eq(
            ChcExpr::var(y),
            ChcExpr::ite(
                ChcExpr::var(flag),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                ChcExpr::add(ChcExpr::var(x), ChcExpr::int(2)),
            ),
        )],
        &substitutions,
    );

    assert!(
        !normalized.unsat,
        "normalized branch should remain feasible"
    );
    assert!(
        normalized
            .constraints
            .iter()
            .all(|constraint| !contains_ite(constraint)),
        "normalized constraints should be ITE-free: {:?}",
        normalized.constraints
    );
    assert!(
        normalized
            .constraints
            .iter()
            .any(|constraint| parse_linear_constraint(constraint).is_some()),
        "normalized branch should expose at least one linear constraint: {:?}",
        normalized.constraints
    );
}

#[test]
fn test_full_bool_partition_interpolant_excludes_local_bools() {
    let a = ChcVar::new("a", ChcSort::Bool);
    let s = ChcVar::new("s", ChcSort::Bool);
    let b = ChcVar::new("b", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::Int);

    let a_constraints = vec![
        ChcExpr::implies(
            ChcExpr::var(a.clone()),
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ),
        ChcExpr::implies(
            ChcExpr::not(ChcExpr::var(a)),
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ),
        ChcExpr::implies(
            ChcExpr::var(s.clone()),
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ),
        ChcExpr::implies(
            ChcExpr::not(ChcExpr::var(s.clone())),
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ),
    ];
    let b_constraints = vec![
        ChcExpr::implies(
            ChcExpr::var(s.clone()),
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ),
        ChcExpr::implies(
            ChcExpr::not(ChcExpr::var(s.clone())),
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(2)),
        ),
        ChcExpr::implies(
            ChcExpr::var(b.clone()),
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(5)),
        ),
        ChcExpr::implies(
            ChcExpr::not(ChcExpr::var(b)),
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(6)),
        ),
    ];
    let shared_vars: FxHashSet<String> = FxHashSet::from_iter([x.name, s.name]);

    let partition = classify_bool_partition(&a_constraints, &b_constraints);
    assert_eq!(
        partition
            .a_local
            .iter()
            .map(|var| var.name.clone())
            .collect::<Vec<_>>(),
        vec!["a".to_string()]
    );
    assert_eq!(
        partition
            .shared
            .iter()
            .map(|var| var.name.clone())
            .collect::<Vec<_>>(),
        vec!["s".to_string()]
    );
    assert_eq!(
        partition
            .b_local
            .iter()
            .map(|var| var.name.clone())
            .collect::<Vec<_>>(),
        vec!["b".to_string()]
    );

    let mut solver = TpaSolver::new(ChcProblem::new(), TpaConfig::default());
    let Some(interpolant) = solver.interpolate_with_full_bool_partitioning(
        &a_constraints,
        &b_constraints,
        &shared_vars,
        &partition,
    ) else {
        return;
    };

    assert!(
        solver.validate_recombined_interpolant(
            &a_constraints,
            &b_constraints,
            &interpolant,
            &shared_vars
        ),
        "recombined interpolant must satisfy Craig validation"
    );

    let vars = expr_var_names(&interpolant);
    assert!(
        !vars.contains("a"),
        "A-local Bool leaked into interpolant: {interpolant}"
    );
    assert!(
        !vars.contains("b"),
        "B-local Bool leaked into interpolant: {interpolant}"
    );
    assert!(
        vars.iter().all(|name| shared_vars.contains(name)),
        "interpolant must mention only shared vars, got {vars:?}"
    );
}

// =========================================================================
// Split-TPA fixed-point machinery unit tests (#chc25-split-tpa)
// =========================================================================

/// Build a solver over the increment TS `x' = x + 1`, `init: x = 0`, with the
/// supplied query. Returns the solver (with its transition system installed)
/// plus a clonable copy of the transition system for direct helper calls.
fn make_increment_solver(
    query: ChcExpr,
) -> (TpaSolver, crate::transition_system::TransitionSystem) {
    use crate::transition_system::TransitionSystem;
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let x1 = ChcVar::new("x_1", ChcSort::Int);
    let ts = TransitionSystem::new(
        inv,
        vec![x.clone()],
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::eq(
            ChcExpr::var(x1),
            ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
        ),
        query,
    );
    let mut solver = TpaSolver::new(problem, TpaConfig::default());
    solver.transition_system = Some(ts.clone());
    (solver, ts)
}

fn state_ge(bound: i128) -> ChcExpr {
    ChcExpr::ge(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::int(bound),
    )
}

fn state_le(bound: i128) -> ChcExpr {
    ChcExpr::le(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::int(bound),
    )
}

#[test]
fn test_squash_invariants_caps_at_limit() {
    let x = ChcVar::new("x", ChcSort::Int);
    let mut candidates: Vec<ChcExpr> = (0..300)
        .map(|i| ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(i)))
        .collect();
    squash_invariants(&mut candidates);
    assert!(
        candidates.len() <= HOUDINI_CANDIDATE_CAP,
        "squash must cap candidate count at {HOUDINI_CANDIDATE_CAP}, got {}",
        candidates.len()
    );
    assert!(
        !candidates.is_empty(),
        "squash must not empty the candidate list"
    );
}

#[test]
fn test_houdini_filter_keeps_inductive_drops_others() {
    // Under x' = x + 1: (x >= 0) is inductive; (x <= 5) is not.
    let (mut solver, ts) = make_increment_solver(ChcExpr::lt(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::int(0),
    ));
    let inductive = state_ge(0);
    let not_inductive = state_le(5);
    solver.houdini_filter_state(&[inductive.clone(), not_inductive.clone()], &ts);
    assert!(
        solver.state_invariants.contains(&inductive),
        "x >= 0 is inductive and must be retained: {:?}",
        solver.state_invariants
    );
    assert!(
        !solver.state_invariants.contains(&not_inductive),
        "x <= 5 is not inductive and must be dropped: {:?}",
        solver.state_invariants
    );
}

#[test]
fn test_record_safe_accepts_inductive_and_safe() {
    // query x < 0: (x >= 0) is inductive AND separates init from query.
    let (mut solver, ts) = make_increment_solver(ChcExpr::lt(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::int(0),
    ));
    let recorded = solver.record_safe_state_invariant(state_ge(0), 1, &ts);
    assert!(
        recorded,
        "inductive + safe invariant must be recorded as Safe"
    );
    assert!(
        solver.explanation.is_some(),
        "recording Safe must populate the safety explanation"
    );
}

#[test]
fn test_record_safe_rejects_inductive_but_unsafe() {
    // query x >= 5: (x >= 0) is inductive but x = 5 is reachable, so the safety
    // check must fail and nothing is recorded (fail-closed).
    let (mut solver, ts) = make_increment_solver(ChcExpr::ge(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::int(5),
    ));
    let recorded = solver.record_safe_state_invariant(state_ge(0), 1, &ts);
    assert!(
        !recorded,
        "an inductive-but-unsafe invariant must be rejected by the safety gate"
    );
    assert!(
        solver.explanation.is_none(),
        "no safety explanation may be recorded when the gate fails"
    );
}

#[test]
fn test_record_safe_rejects_non_inductive_candidate() {
    // query x < 0 is safe, but (x <= 100) is NOT closed under x' = x + 1
    // (from x = 100, x' = 101 escapes), so consecution must fail.
    let (mut solver, ts) = make_increment_solver(ChcExpr::lt(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::int(0),
    ));
    let recorded = solver.record_safe_state_invariant(state_le(100), 1, &ts);
    assert!(
        !recorded,
        "a non-inductive candidate must be rejected by consecution"
    );
}
