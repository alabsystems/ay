// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for SAT warm state preservation across CEGAR iterations (#3762).
//!
//! Validates that `SatWarmState` correctly extracts and imports learned clauses,
//! VSIDS activity scores, and phase hints between solver instances.

use super::*;
use crate::SatWarmState;
use ay_sat::{
    Literal, SatGuidanceImportLevel, SatGuidanceImportReason, Solver as SatSolver, Variable,
};

/// #3762: SatWarmState::extract captures learned clauses from a solver.
#[test]
fn sat_warm_state_extracts_learned_clauses() {
    let mut solver = SatSolver::new(5);

    // Add some original clauses (these should NOT appear in warm state).
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::positive(Variable::new(2)),
    ]);

    // Add a "preserved learned" clause to simulate a prior solve's learned clause.
    let learned = vec![
        Literal::positive(Variable::new(3)),
        Literal::negative(Variable::new(4)),
    ];
    solver.add_preserved_learned(learned.clone());

    let warm = SatWarmState::extract(&solver);

    // The preserved learned clause should be in the warm state.
    assert!(
        !warm.learned_clauses.is_empty(),
        "warm state should contain the learned clause"
    );
    assert!(!warm.is_empty(), "warm state should not be empty");
}

/// #3762: SatWarmState::import_into seeds a fresh solver with learned clauses.
#[test]
fn sat_warm_state_imports_into_fresh_solver() {
    // Create a solver with some learned clauses.
    let mut solver1 = SatSolver::new(5);
    solver1.add_clause(vec![Literal::positive(Variable::new(0))]);
    let learned = vec![
        Literal::positive(Variable::new(1)),
        Literal::negative(Variable::new(2)),
    ];
    solver1.add_preserved_learned(learned.clone());

    // Extract warm state.
    let warm = SatWarmState::extract(&solver1);

    // Create a fresh solver and import.
    let mut solver2 = SatSolver::new(5);
    solver2.add_clause(vec![Literal::positive(Variable::new(0))]);
    let report = warm.import_into_with_report(&mut solver2);

    assert_eq!(
        report.decision.level,
        SatGuidanceImportLevel::ExactReplayHints
    );
    assert!(
        report.imported_learned_clauses > 0,
        "should import at least one learned clause"
    );
}

/// #8883: Same variable/clause counts are not enough for warm-state import.
#[test]
fn sat_warm_state_rejects_formula_tamper() {
    let mut solver1 = SatSolver::new(3);
    solver1.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    solver1.set_var_phase(Variable::new(2), true);
    solver1.add_preserved_learned(vec![
        Literal::negative(Variable::new(0)),
        Literal::positive(Variable::new(2)),
    ]);
    let warm = SatWarmState::extract(&solver1);

    let mut solver2 = SatSolver::new(3);
    solver2.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::negative(Variable::new(1)),
    ]);

    let report = warm.import_into_with_report(&mut solver2);

    assert_eq!(report.decision.level, SatGuidanceImportLevel::Reject);
    assert_eq!(
        report.decision.reason,
        SatGuidanceImportReason::FormulaTampered
    );
    assert_eq!(report.imported_learned_clauses, 0);
    assert_eq!(report.variable_activity_hints, 0);
    assert_eq!(report.phase_hints, 0);
    assert_eq!(
        solver2.var_phase(Variable::new(2)),
        None,
        "heuristic phase hints must not import after formula tamper rejection"
    );
}

/// #8935: Legacy v1 warm state remains readable but cannot replay learned clauses.
#[test]
fn legacy_sat_warm_state_imports_only_heuristic_hints() {
    let warm = SatWarmState {
        formula_fingerprint: None,
        learned_clauses: vec![vec![Literal::positive(Variable::new(0))]],
        variable_activities: Vec::new(),
        phase_hints: vec![(1, false)],
        prior_conflicts: 7,
    };

    let mut solver = SatSolver::new(2);
    let report = warm.import_into_with_report(&mut solver);

    assert_eq!(
        report.decision.level,
        SatGuidanceImportLevel::HeuristicHintsOnly
    );
    assert_eq!(
        report.decision.reason,
        SatGuidanceImportReason::LegacyGuidanceMissingFingerprint
    );
    assert_eq!(report.imported_learned_clauses, 0);
    assert_eq!(solver.var_phase(Variable::new(1)), Some(false));
}

/// #3762: SatWarmState round-trip preserves VSIDS activity.
#[test]
fn sat_warm_state_preserves_vsids_activities() {
    let mut solver1 = SatSolver::new(5);

    // Bump some variables' activity.
    solver1.bump_variable_activity(Variable::new(0));
    solver1.bump_variable_activity(Variable::new(0));
    solver1.bump_variable_activity(Variable::new(2));

    let warm = SatWarmState::extract(&solver1);

    // Variables 0 and 2 should have activity, 1/3/4 should not.
    let active_vars: Vec<usize> = warm.variable_activities.iter().map(|&(i, _)| i).collect();
    assert!(active_vars.contains(&0), "var 0 should be in activities");
    assert!(active_vars.contains(&2), "var 2 should be in activities");

    // Import into fresh solver and verify the activities are seeded.
    let mut solver2 = SatSolver::new(5);
    warm.import_into(&mut solver2);

    // After import, bumped variables should have non-zero activity.
    let act0 = solver2.activity(Variable::new(0));
    let act1 = solver2.activity(Variable::new(1));
    assert!(
        act0 > act1,
        "var 0 (bumped) should have higher activity than var 1 (not bumped): {} vs {}",
        act0,
        act1,
    );
}

/// #3762: SatWarmState preserves phase hints.
#[test]
fn sat_warm_state_preserves_phase_hints() {
    let mut solver1 = SatSolver::new(4);
    solver1.set_var_phase(Variable::new(0), true);
    solver1.set_var_phase(Variable::new(2), false);

    let warm = SatWarmState::extract(&solver1);

    assert!(
        !warm.phase_hints.is_empty(),
        "phase hints should be exported"
    );

    // Import and verify.
    let mut solver2 = SatSolver::new(4);
    warm.import_into(&mut solver2);

    assert_eq!(
        solver2.var_phase(Variable::new(0)),
        Some(true),
        "var 0 phase should be true"
    );
    assert_eq!(
        solver2.var_phase(Variable::new(2)),
        Some(false),
        "var 2 phase should be false"
    );
}

/// #3762: Empty SatWarmState is correctly detected.
#[test]
fn sat_warm_state_default_is_empty() {
    let warm = SatWarmState::default();
    assert!(warm.is_empty(), "default warm state should be empty");
    assert!(warm.formula_fingerprint.is_none());
    assert!(warm.learned_clauses.is_empty());
    assert!(warm.variable_activities.is_empty());
    assert!(warm.phase_hints.is_empty());
}

/// #3762: SatWarmState::extract from a fresh solver produces non-empty state
/// only if there are activities/phases set.
#[test]
fn sat_warm_state_extract_from_fresh_solver() {
    let solver = SatSolver::new(3);
    let warm = SatWarmState::extract(&solver);

    // Fresh solver has no learned clauses, no activities, no phases.
    assert!(warm.learned_clauses.is_empty());
    // VSIDS may have initial activity from constructor, so just check it's valid.
    assert_eq!(warm.prior_conflicts, 0);
}

/// #3762: SatWarmState import handles variable count mismatch gracefully.
#[test]
fn sat_warm_state_import_var_count_mismatch() {
    let mut solver1 = SatSolver::new(10);
    solver1.bump_variable_activity(Variable::new(8));
    solver1.set_var_phase(Variable::new(9), true);

    let warm = SatWarmState::extract(&solver1);

    // Import into a smaller solver — should not panic.
    let mut solver2 = SatSolver::new(3);
    let _imported = warm.import_into(&mut solver2);
    // The import should handle out-of-range variables gracefully.
}

/// #3762: SatWarmState into_sat_state/from_sat_state preserves SAT state
/// for the QF_S CEGAR path (regression test for existing behavior).
#[test]
fn qf_s_sat_state_preservation_round_trip() {
    let mut terms = TermStore::new();
    let theory = PropositionalTheory;

    // Create a simple formula: (a OR b) AND (NOT a OR c)
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let a_or_b = terms.mk_or(vec![a, b]);
    let not_a = terms.mk_not(a);
    let not_a_or_c = terms.mk_or(vec![not_a, c]);

    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform_all(&[a_or_b, not_a_or_c]);

    let mut dpll = DpllT::from_tseitin(&terms, &result, theory);
    dpll.sat_solver_mut().set_preprocess_enabled(false);

    // Solve to populate learned clauses and VSIDS.
    let sat_result = dpll.solve().unwrap();
    assert!(matches!(sat_result, SatResult::Sat(_)));

    // Extract SAT state and rebuild with fresh theory.
    let sat_state = dpll.into_sat_state();
    let theory2 = PropositionalTheory;
    let mut dpll2 = DpllT::from_sat_state(&terms, theory2, sat_state);

    // Should still be satisfiable.
    let sat_result2 = dpll2.solve().unwrap();
    assert!(matches!(sat_result2, SatResult::Sat(_)));
}
