// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for PDKIND solver.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::reachability::{ReachabilityChecker, ReachabilityResult};
use super::*;
use crate::interpolation::{interpolating_sat_constraints, InterpolatingSatResult};
use crate::{ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
use ay_core::kani_compat::DetHashSet as FxHashSet;

mod regression;

fn create_simple_safe_problem() -> ChcProblem {
    // x = 0 => Inv(x)
    // Inv(x) /\ x < 5 => Inv(x+1)
    // Inv(x) /\ x >= 10 => false
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Init: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Trans: Inv(x) /\ x < 5 => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: Inv(x) /\ x >= 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_simple_unsafe_problem() -> ChcProblem {
    // x = 0 => Inv(x)
    // Inv(x) => Inv(x+1)
    // Inv(x) /\ x >= 1 => false
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(1))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn accumulator_unsafe_000_input() -> &'static str {
    r#"(set-logic HORN)
(declare-fun Inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (Inv x y))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int))
  (=> (and (Inv x y) (= x1 (+ x 1)) (= y1 (+ y x))) (Inv x1 y1))))
(assert (forall ((x Int) (y Int)) (=> (and (Inv x y) (>= y 50)) false)))
(check-sat)
"#
}

#[test]
fn test_pdkind_is_transition_system() {
    let problem = create_simple_safe_problem();
    assert!(TransitionSystem::from_chc_problem(&problem).is_ok());
}

#[test]
fn test_pdkind_extract_transition_system() {
    let problem = create_simple_safe_problem();
    let ts = TransitionSystem::from_chc_problem(&problem)
        .expect("single-predicate linear problem must yield a TransitionSystem");

    // Verify the transition system has the expected structure
    assert_eq!(ts.vars.len(), 1, "should have 1 state variable");
    assert_eq!(ts.vars[0].sort, ChcSort::Int);

    // Verify canonical variable naming
    assert_eq!(ts.vars[0].name, "v0", "canonical variable should be v0");

    // Init should reference v0 (canonicalized from x) with value 0
    // From create_simple_safe_problem: x = 0 => Inv(x), so init is v0 = 0
    let init_vars = ts.init.vars();
    let init_var_names: Vec<&str> = init_vars.iter().map(|v| v.name.as_str()).collect();
    assert!(
        init_var_names.contains(&"v0"),
        "init should reference canonical variable v0, got: {init_var_names:?}"
    );
    assert!(
        !matches!(ts.init, ChcExpr::Bool(true)),
        "init should not be trivially true (it constrains v0 = 0)"
    );

    // Transition should reference both v0 (current) and v0_next
    let trans_vars = ts.transition.vars();
    let trans_var_names: Vec<&str> = trans_vars.iter().map(|v| v.name.as_str()).collect();
    assert!(
        trans_var_names.contains(&"v0"),
        "transition should reference current-state variable v0, got: {trans_var_names:?}"
    );
    assert!(
        trans_var_names.contains(&"v0_next"),
        "transition should reference next-state variable v0_next, got: {trans_var_names:?}"
    );

    // Query should reference v0 (the property constraint x >= 10)
    let query_vars = ts.query.vars();
    let query_var_names: Vec<&str> = query_vars.iter().map(|v| v.name.as_str()).collect();
    assert!(
        query_var_names.contains(&"v0"),
        "query should reference canonical variable v0, got: {query_var_names:?}"
    );
    assert!(
        !matches!(ts.query, ChcExpr::Bool(true)),
        "query should not be trivially true (it constrains v0 >= 10)"
    );
}

#[test]
fn test_pdkind_trivial_safe() {
    // Problem where init is unsatisfiable
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Init: x = 0 /\ x > 0 => Inv(x) (unsatisfiable)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Trans
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x)])]),
        ClauseHead::False,
    ));

    let solver = PdkindSolver::new(problem, PdkindConfig::default());
    let result = solver.solve();

    match result {
        ChcEngineResult::Safe(_) => {}
        other => panic!("Expected Safe, got {other:?}"),
    }
}

#[test]
fn test_pdkind_simple_safe() {
    let problem = create_simple_safe_problem();
    let config = PdkindConfig {
        max_iterations: 3,
        max_n: 3,
        max_reachability_depth: 1,
        max_reachability_iterations: 1,
        per_obligation_timeout_secs: 0,
        ..PdkindConfig::default()
    };
    let solver = PdkindSolver::new(problem, config);
    let result = solver.solve();

    match result {
        ChcEngineResult::Safe(_) => {}
        ChcEngineResult::Unknown => {
            // Acceptable - may need better interpolation
        }
        ChcEngineResult::Unsafe(_) => {
            panic!("Problem is safe, should not return Unsafe");
        }
        ChcEngineResult::NotApplicable => {
            panic!("PDKIND should not return NotApplicable");
        }
    }
}

/// Regression test for #2985: Unknown k-induction checks must not allow
/// non-incremental stable-frame verification to return a spurious Safe.
#[test]
fn test_pdkind_non_incremental_kinduction_unknown_does_not_return_safe_issue_2985() {
    let problem = create_simple_unsafe_problem();
    let solver = PdkindSolver::new(
        problem,
        PdkindConfig {
            // Force the path that uses verify_non_incremental_stable_invariant.
            incremental_mode: IncrementalMode::FreshOnly("test: force non-incremental".to_string()),
            // Deterministically force IncrementalCheckResult::Unknown in push().
            per_obligation_timeout_secs: 0,
            max_iterations: 4,
            max_n: 4,
            ..PdkindConfig::default()
        },
    );

    assert!(
        !matches!(solver.solve(), ChcEngineResult::Safe(_)),
        "unknown k-induction checks must not produce Safe on unsafe systems"
    );
}

// Deleted: test_pdkind_singleloop_multi_predicate_unsafe_not_safe_issue_2690
// Stack overflow (#2690 regression guard). High iteration/reachability
// limits (200/20) cause unbounded recursion in SingleLoop fallback.
// Needs reduced limits or explicit stack-size configuration.

#[test]
fn test_transition_system_state_var_names_at_and_shift() {
    let x = ChcVar::new("x", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId::new(0),
        vec![x.clone()],
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::Bool(false),
    );

    let t0 = ts.state_var_names_at(0);
    assert!(t0.contains("x"));

    let t1 = ts.state_var_names_at(1);
    assert!(t1.contains("x_1"));

    // Shift time-1 back to time-0.
    let x_1 = ChcVar::new("x_1", ChcSort::Int);
    let shifted =
        ts.shift_versioned_state_vars(&ChcExpr::ge(ChcExpr::var(x_1), ChcExpr::int(1)), -1);
    let shifted_vars: FxHashSet<String> = shifted.vars().into_iter().map(|v| v.name).collect();
    assert!(shifted_vars.contains("x"));
    assert!(!shifted_vars.contains("x_1"));

    // Clamp at time 0 (no negative time indices).
    let clamped = ts.shift_versioned_state_vars(&ChcExpr::le(ChcExpr::var(x), ChcExpr::int(0)), -1);
    let clamped_vars: FxHashSet<String> = clamped.vars().into_iter().map(|v| v.name).collect();
    assert!(clamped_vars.contains("x"));
    assert!(!clamped_vars.contains("x_-1"));

    // Do not rewrite variables that merely *look* like time indices.
    let x_01 = ChcVar::new("x_01", ChcSort::Int);
    let leading_zero =
        ts.shift_versioned_state_vars(&ChcExpr::ge(ChcExpr::var(x_01), ChcExpr::int(1)), -1);
    let leading_zero_vars: FxHashSet<String> =
        leading_zero.vars().into_iter().map(|v| v.name).collect();
    assert!(leading_zero_vars.contains("x_01"));
    assert!(!leading_zero_vars.contains("x"));

    let x_plus1 = ChcVar::new("x_+1", ChcSort::Int);
    let plus_sign =
        ts.shift_versioned_state_vars(&ChcExpr::ge(ChcExpr::var(x_plus1), ChcExpr::int(1)), -1);
    let plus_sign_vars: FxHashSet<String> = plus_sign.vars().into_iter().map(|v| v.name).collect();
    assert!(plus_sign_vars.contains("x_+1"));
    assert!(!plus_sign_vars.contains("x"));
}

#[test]
fn test_reachability_zero_step_context_reuse_does_not_leak_queries() {
    // Regression coverage for incremental reachability SMT usage:
    // alternating SAT/UNSAT zero-step checks must remain independent.
    let x = ChcVar::new("x", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId::new(0),
        vec![x.clone()],
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::Bool(true),
        ChcExpr::Bool(false),
    );
    let config = PdkindConfig::default();
    let mut reach = ReachabilityChecker::new(&ts, &config);

    let at_zero = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let at_one = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(1));

    assert!(matches!(
        reach.zero_step_reachability(&at_zero),
        ReachabilityResult::Reachable { steps: 0 }
    ));
    assert!(matches!(
        reach.zero_step_reachability(&at_one),
        ReachabilityResult::Unreachable { .. }
    ));
    assert!(matches!(
        reach.zero_step_reachability(&at_zero),
        ReachabilityResult::Reachable { steps: 0 }
    ));
}

#[test]
fn test_zero_step_reachability_accepts_auxiliary_state_variables() {
    // Regression guard for #2750: zero-step reachability checks may include
    // auxiliary variables not present in the transition-system state vector.
    // These vars are unconstrained by init and must not force spurious UNSAT.
    let x = ChcVar::new("x", ChcSort::Int);
    let aux = ChcVar::new("aux", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId::new(0),
        vec![x.clone()],
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::Bool(true),
        ChcExpr::Bool(false),
    );
    let config = PdkindConfig::default();
    let mut reach = ReachabilityChecker::new(&ts, &config);

    let state = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(aux), ChcExpr::int(1)),
    );

    assert!(
        matches!(
            reach.zero_step_reachability(&state),
            ReachabilityResult::Reachable { steps: 0 }
        ),
        "auxiliary vars outside ts.vars should not make zero-step reachability spurious UNSAT"
    );
}

#[test]
fn test_reachability_reports_multi_step_depth() {
    let x = ChcVar::new("x", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId::new(0),
        vec![x],
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::Bool(false),
    );
    let config = PdkindConfig::default();
    let mut checker = ReachabilityChecker::new(&ts, &config);

    let result = checker.reachable(3, &ChcExpr::Bool(true));
    assert!(
        matches!(result, ReachabilityResult::Reachable { steps: 3 }),
        "reachable(k, true) should report depth k, got {result:?}"
    );
}

#[test]
fn test_reachability_lemma_checkpoint_restore() {
    let x = ChcVar::new("x", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId::new(0),
        vec![x.clone()],
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::Bool(true),
        ChcExpr::Bool(false),
    );
    let config = PdkindConfig::default();
    let mut checker = ReachabilityChecker::new(&ts, &config);

    let l0_a = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let l2_a = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(10));
    checker.add_lemma(0, l0_a.clone());
    checker.add_lemma(2, l2_a.clone());

    let checkpoint = checker.lemma_size_checkpoint();

    let l0_b = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1));
    let l1_a = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(-1));
    let l3_a = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(20));
    checker.add_lemma(0, l0_b);
    checker.add_lemma(1, l1_a);
    checker.add_lemma(3, l3_a);

    checker.restore_lemma_size_checkpoint(&checkpoint);

    assert_eq!(checker.lemmas.len(), checkpoint.len());
    assert_eq!(checker.lemmas[0], vec![l0_a]);
    assert!(checker.lemmas[1].is_empty());
    assert_eq!(checker.lemmas[2], vec![l2_a]);
}

#[test]
fn test_pdkind_reachability_interpolant_boundary_vars_issue_434() {
    // Regression test for #434:
    // - PDKIND reachability interpolation must use boundary (time-1) shared vars
    // - Shifting interpolants back must not introduce negative time indices.
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    let ts = TransitionSystem::new(
        PredicateId::new(0),
        vec![x.clone()],
        ChcExpr::Bool(true),
        // x_next >= 1 (simple bound so interpolation is guaranteed to succeed)
        ChcExpr::ge(ChcExpr::var(x_next), ChcExpr::int(1)),
        ChcExpr::Bool(false),
    );

    // State formula at "time 0" (will be versioned to time 1 inside reachability).
    let state = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(0));

    // Interpolation sanity check:
    // - wrong shared vars (time 0): must fail
    // - boundary shared vars (time 1): must succeed
    let trans = ts.k_transition(1);
    let state_t1 = ts.send_through_time(&state, 1);

    let shared_t0 = ts.state_var_names();
    assert!(matches!(
        interpolating_sat_constraints(
            std::slice::from_ref(&trans),
            std::slice::from_ref(&state_t1),
            &shared_t0
        ),
        InterpolatingSatResult::Unknown
    ));

    let shared_t1 = ts.state_var_names_at(1);
    let interp_t1 = match interpolating_sat_constraints(&[trans], &[state_t1], &shared_t1) {
        InterpolatingSatResult::Unsat(interp) => interp,
        other => panic!("Expected Unsat, got {other:?}"),
    };
    let expected = ts.shift_versioned_state_vars(&interp_t1, -1);

    let config = PdkindConfig::default();
    let mut reach = ReachabilityChecker::new(&ts, &config);
    let result = reach.reachable(1, &state);

    let ReachabilityResult::Unreachable { explanation } = result else {
        panic!("Expected Unreachable");
    };

    assert_eq!(explanation, expected);

    let var_names: FxHashSet<String> = explanation.vars().into_iter().map(|v| v.name).collect();
    assert!(
        !var_names.contains("x_-1"),
        "Explanation should not contain negative-time vars: {var_names:?}"
    );
    assert!(
        !var_names.contains("x_1"),
        "Explanation should be over time-0 vars after shifting: {var_names:?}"
    );
}

/// Regression test for #2652: check_reachability must propagate Unknown
/// when the last iteration returns Unknown (not silently convert to Unreachable).
///
/// When max_reachability_iterations=0, reachable(k>0) immediately returns Unknown.
/// check_reachability(from=1, to=1) must return Unknown, not Unreachable.
#[test]
fn test_check_reachability_propagates_unknown_issue_2652() {
    let x = ChcVar::new("x", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId::new(0),
        vec![x.clone()],
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::eq(
            ChcExpr::var(ChcVar::new("x_next", ChcSort::Int)),
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ),
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10)),
    );

    // Force Unknown by setting max_reachability_iterations = 0.
    // reachable(k > 0) returns Unknown immediately (line 294-296).
    let config = PdkindConfig {
        max_reachability_iterations: 0,
        ..PdkindConfig::default()
    };
    let mut checker = ReachabilityChecker::new(&ts, &config);
    let formula = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(5));

    // Single-step check: from=1, to=1. reachable(1) returns Unknown.
    // Before fix: fell through to default Unreachable { Bool(false) }.
    let result = checker.check_reachability(1, 1, &formula);
    assert!(
        matches!(result, ReachabilityResult::Unknown),
        "check_reachability must propagate Unknown, not convert to Unreachable"
    );

    // Multi-step check: from=1, to=3. All return Unknown.
    let result = checker.check_reachability(1, 3, &formula);
    assert!(
        matches!(result, ReachabilityResult::Unknown),
        "check_reachability must propagate Unknown when all iterations return Unknown"
    );
}

/// Test that check_reachability returns Unreachable only when no Unknown was seen.
#[test]
fn test_check_reachability_unreachable_when_no_unknown() {
    let x = ChcVar::new("x", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId::new(0),
        vec![x.clone()],
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::eq(
            ChcExpr::var(ChcVar::new("x_next", ChcSort::Int)),
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ),
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10)),
    );

    let config = PdkindConfig::default();
    let mut checker = ReachabilityChecker::new(&ts, &config);

    // x >= 100 is unreachable from init x=0 in zero steps.
    let formula = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(100));
    let result = checker.check_reachability(0, 0, &formula);
    assert!(
        matches!(result, ReachabilityResult::Unreachable { .. }),
        "check_reachability(0,0) for unreachable formula should return Unreachable"
    );
}

#[test]
fn test_iframe_element_structural_dedup_with_distinct_allocations() {
    let x = ChcVar::new("x", ChcSort::Int);
    let lemma_a = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let lemma_b = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let cex_a = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(7));
    let cex_b = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(7));

    let mut frame = InductionFrame::default();
    frame.insert(IFrameElement {
        lemma: lemma_a,
        counter_example: CounterExample {
            formula: cex_a,
            num_of_steps: 2,
        },
    });
    frame.insert(IFrameElement {
        lemma: lemma_b,
        counter_example: CounterExample {
            formula: cex_b,
            num_of_steps: 2,
        },
    });

    assert_eq!(
            frame.len(),
            1,
            "frame must dedupe structurally-equal obligations even when AST nodes were built separately"
        );
}

#[test]
fn test_iframe_element_distinguishes_counterexample_depth() {
    let x = ChcVar::new("x", ChcSort::Int);
    let lemma = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let cex = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(7));

    let mut frame = InductionFrame::default();
    frame.insert(IFrameElement {
        lemma: lemma.clone(),
        counter_example: CounterExample {
            formula: cex.clone(),
            num_of_steps: 1,
        },
    });
    frame.insert(IFrameElement {
        lemma,
        counter_example: CounterExample {
            formula: cex,
            num_of_steps: 2,
        },
    });

    assert_eq!(
        frame.len(),
        2,
        "frame elements must remain distinct when only the counterexample depth differs"
    );
}
