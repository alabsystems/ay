// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn add_swap_pair_formula(solver: &mut Solver) -> (Variable, Variable, Variable) {
    let x0 = Variable(0);
    let x1 = Variable(1);
    let z = Variable(2);

    // x0 and x1 are interchangeable in this formula.
    assert!(solver.add_clause(vec![Literal::positive(x0), Literal::positive(z)]));
    assert!(solver.add_clause(vec![Literal::positive(x1), Literal::positive(z)]));
    assert!(solver.add_clause(vec![Literal::negative(x0), Literal::negative(z)]));
    assert!(solver.add_clause(vec![Literal::negative(x1), Literal::negative(z)]));
    (x0, x1, z)
}

#[test]
fn test_preprocess_symmetry_adds_binary_order_clause_for_swap_pair() {
    let mut solver = Solver::new(3);
    solver.cold.symmetry_enabled = true; // #8190: symmetry defaults off

    let (x0, x1, _z) = add_swap_pair_formula(&mut solver);

    let before = solver.arena.active_clause_count();
    let (unsat, changed) = solver.preprocess_symmetry();
    assert!(!unsat, "symmetry preprocessing should not derive UNSAT");
    assert!(changed, "symmetry preprocessing should emit an SBP");
    assert_eq!(
        solver.arena.active_clause_count(),
        before + 1,
        "expected one ordinary binary SBP clause",
    );

    let expected = vec![Literal::positive(x0), Literal::negative(x1)];
    let found = solver
        .arena
        .active_indices()
        .filter(|&clause_idx| !solver.arena.is_learned(clause_idx))
        .map(|clause_idx| {
            let mut lits = solver.arena.literals(clause_idx).to_vec();
            lits.sort_unstable_by_key(|lit| lit.raw());
            lits
        })
        .any(|lits| lits == expected);

    assert!(found, "expected symmetry SBP clause {expected:?} in arena");
    assert_eq!(solver.cold.symmetry_stats.pairs_detected, 1);
    assert_eq!(solver.cold.symmetry_stats.sb_clauses_added, 1);
    assert!(
        !solver
            .cold
            .symmetry_stats
            .routes
            .iter()
            .any(|(route, _)| *route == "signed"),
        "a non-one-shot solver must not attempt signed symmetry"
    );
}

#[test]
fn signed_symmetry_runs_only_for_an_explicit_one_shot_solver() {
    let mut solver = Solver::new(3);
    solver.set_symmetry_oneshot(true);
    let (_x0, _x1, _z) = add_swap_pair_formula(&mut solver);

    let before = solver.arena.active_clause_count();
    let (unsat, changed) = solver.preprocess_symmetry();
    assert!(!unsat);

    if std::env::var_os("AY_SAT_SIGNED_SYMMETRY").is_some() {
        // The opt-in route runs before the ordinary detector. This formula has
        // two verified signed generators; their SBPs can be binary or unit.
        assert!(changed);
        assert_eq!(solver.arena.active_clause_count(), before + 2);
        assert!(solver
            .cold
            .symmetry_stats
            .routes
            .iter()
            .any(|(route, outcome)| route == &"signed" && outcome == "added 2 clauses"));
        assert_eq!(solver.cold.symmetry_stats.pairs_detected, 2);
        assert_eq!(solver.cold.symmetry_stats.sb_clauses_added, 2);
        assert_eq!(solver.cold.symmetry_stats.last_skipped_reason, None);
    } else {
        assert!(!solver
            .cold
            .symmetry_stats
            .routes
            .iter()
            .any(|(route, _)| *route == "signed"));
    }
}

#[test]
fn signed_symmetry_env_cannot_remove_models_from_an_assumption_solver() {
    let mut solver = Solver::new(3);
    let (x0, _x1, _z) = add_swap_pair_formula(&mut solver);

    let before = solver.arena.active_clause_count();
    let (unsat, changed) = solver.preprocess_symmetry();
    assert!(!unsat);
    assert!(!changed, "a non-one-shot solver must not emit signed SBPs");
    assert_eq!(solver.arena.active_clause_count(), before);
    assert!(!solver
        .cold
        .symmetry_stats
        .routes
        .iter()
        .any(|(route, _)| *route == "signed"));

    let result = solver
        .solve_with_assumptions(&[Literal::negative(x0)])
        .into_inner();
    assert!(
        matches!(&result, AssumeResult::Sat(model) if !model[x0.id() as usize]),
        "the model selected by the assumption must remain SAT, got {result:?}"
    );
}

#[test]
fn signed_symmetry_search_telemetry_survives_later_route_outcomes() {
    let mut solver = Solver::new(3);
    solver.set_symmetry_oneshot(true);
    solver.cold.symmetry_enabled = true;
    assert!(solver.add_clause(vec![Literal::positive(Variable(0))]));
    assert!(solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]));
    assert!(solver.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ]));

    let (unsat, changed) = solver.preprocess_symmetry();
    assert!(!unsat);
    assert!(!changed);
    assert_eq!(
        solver.cold.symmetry_stats.last_skipped_reason,
        Some(crate::symmetry::SymmetrySkipReason::NoPairs)
    );
    if std::env::var_os("AY_SAT_SIGNED_SYMMETRY").is_some() {
        assert!(solver
            .cold
            .symmetry_stats
            .routes
            .iter()
            .any(|(route, outcome)| route == &"signed" && outcome == "ran, found nothing"));
    } else {
        assert!(!solver
            .cold
            .symmetry_stats
            .routes
            .iter()
            .any(|(route, _)| *route == "signed"));
    }
}

#[test]
fn test_preprocess_symmetry_skips_drat_proof_mode() {
    // DRAT proof mode: SBP clauses are RAT w.r.t. the symmetry pivot, but
    // when interleaved with other proof steps (congruence equivalence
    // binaries), the external DRAT checker may reject the RAT derivation.
    // CaDiCaL has no symmetry breaking, so there is no reference for
    // DRAT-compatible SBP emission. Symmetry is disabled in all proof
    // modes (#8011).
    let mut solver = Solver::with_proof(3, Vec::<u8>::new());
    solver.cold.symmetry_enabled = true; // #8190: symmetry defaults off; enable to test proof-mode skip

    let x0 = Variable(0);
    let x1 = Variable(1);
    let z = Variable(2);

    // Symmetric formula: x0 and x1 are interchangeable.
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(z)]);
    solver.add_clause(vec![Literal::positive(x1), Literal::positive(z)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::negative(z)]);
    solver.add_clause(vec![Literal::negative(x1), Literal::negative(z)]);

    let (unsat, changed) = solver.preprocess_symmetry();
    assert!(!unsat);
    assert!(!changed, "symmetry should be skipped in DRAT proof mode");
    assert_eq!(
        solver.cold.symmetry_stats.last_skipped_reason,
        Some(crate::symmetry::SymmetrySkipReason::ProofMode),
    );
}

#[test]
fn test_preprocess_symmetry_drat_proof_has_no_sbp_clause() {
    // Verify that DRAT proof mode does NOT emit SBP clauses (#8011).
    // Symmetry is disabled in all proof modes because SBP RAT clauses
    // can fail external DRAT checking when interleaved with congruence.
    use std::io::{Result, Write};
    use std::sync::{Arc, Mutex};

    let proof_buf: Arc<Mutex<Vec<u8>>> = Arc::new(Mutex::new(Vec::new()));
    let buf_clone = Arc::clone(&proof_buf);

    struct SharedWriter(Arc<Mutex<Vec<u8>>>);
    impl Write for SharedWriter {
        fn write(&mut self, buf: &[u8]) -> Result<usize> {
            self.0.lock().unwrap().extend_from_slice(buf);
            Ok(buf.len())
        }
        fn flush(&mut self) -> Result<()> {
            Ok(())
        }
    }

    let mut solver = Solver::with_proof(3, SharedWriter(buf_clone));
    solver.cold.symmetry_enabled = true; // #8190: symmetry defaults off; enable to test proof-mode skip

    let x0 = Variable(0);
    let x1 = Variable(1);
    let z = Variable(2);

    solver.add_clause(vec![Literal::positive(x0), Literal::positive(z)]);
    solver.add_clause(vec![Literal::positive(x1), Literal::positive(z)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::negative(z)]);
    solver.add_clause(vec![Literal::negative(x1), Literal::negative(z)]);

    let (unsat, changed) = solver.preprocess_symmetry();
    assert!(!unsat);
    assert!(!changed, "symmetry should be skipped in DRAT proof mode");

    // The DRAT proof should NOT contain any SBP clauses.
    let proof_bytes = proof_buf.lock().unwrap();
    let proof_str = String::from_utf8_lossy(&proof_bytes);
    assert!(
        !proof_str.contains("1 -2 0"),
        "DRAT proof should NOT contain SBP clause in proof mode, got: {proof_str}"
    );
}

#[test]
fn test_preprocess_symmetry_skips_lrat_mode() {
    // LRAT mode requires explicit resolution hints; symmetry should be skipped.
    use crate::ProofOutput;
    let mut solver = Solver::with_proof_output(3, ProofOutput::lrat_text(Vec::<u8>::new(), 4));
    solver.cold.symmetry_enabled = true; // #8190: symmetry defaults off; enable to test proof-mode skip

    let x0 = Variable(0);
    let x1 = Variable(1);
    let z = Variable(2);

    solver.add_clause(vec![Literal::positive(x0), Literal::positive(z)]);
    solver.add_clause(vec![Literal::positive(x1), Literal::positive(z)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::negative(z)]);
    solver.add_clause(vec![Literal::negative(x1), Literal::negative(z)]);

    let (unsat, changed) = solver.preprocess_symmetry();
    assert!(!unsat);
    assert!(!changed);
    assert_eq!(
        solver.cold.symmetry_stats.last_skipped_reason,
        Some(crate::symmetry::SymmetrySkipReason::ProofMode),
    );
}

#[test]
fn test_preprocess_symmetry_skips_bare_lrat_id_tracking_mode() {
    // `enable_lrat()` can activate LRAT clause-ID tracking without an external
    // proof writer. Symmetry must still skip, otherwise SBP clauses enter the
    // clause DB with no checker-consumable witness.
    let mut solver = Solver::new(3);
    solver.enable_lrat();
    solver.cold.symmetry_enabled = true; // #8190: symmetry defaults off

    let x0 = Variable(0);
    let x1 = Variable(1);
    let z = Variable(2);

    solver.add_clause(vec![Literal::positive(x0), Literal::positive(z)]);
    solver.add_clause(vec![Literal::positive(x1), Literal::positive(z)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::negative(z)]);
    solver.add_clause(vec![Literal::negative(x1), Literal::negative(z)]);

    let before = solver.arena.active_clause_count();
    let (unsat, changed) = solver.preprocess_symmetry();
    assert!(!unsat);
    assert!(!changed);
    assert_eq!(
        solver.arena.active_clause_count(),
        before,
        "LRAT tracking mode must not add proofless SBP clauses",
    );
    assert_eq!(
        solver.cold.symmetry_stats.last_skipped_reason,
        Some(crate::symmetry::SymmetrySkipReason::ProofMode),
    );
    assert_eq!(solver.cold.symmetry_stats.sb_clauses_added, 0);
}

#[test]
fn test_preprocess_symmetry_skips_clause_trace_reconstruction_mode() {
    // Clause trace is the SMT proof-reconstruction surface. Until SBP additions
    // carry resolution hints, symmetry must not add derived trace entries.
    let mut solver = Solver::new(3);
    solver.enable_clause_trace();
    solver.cold.symmetry_enabled = true; // #8190: symmetry defaults off

    let x0 = Variable(0);
    let x1 = Variable(1);
    let z = Variable(2);

    solver.add_clause(vec![Literal::positive(x0), Literal::positive(z)]);
    solver.add_clause(vec![Literal::positive(x1), Literal::positive(z)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::negative(z)]);
    solver.add_clause(vec![Literal::negative(x1), Literal::negative(z)]);

    let before_clauses = solver.arena.active_clause_count();
    let before_trace_len = solver
        .clause_trace()
        .expect("clause trace enabled")
        .entries()
        .len();

    let (unsat, changed) = solver.preprocess_symmetry();
    assert!(!unsat);
    assert!(!changed);
    assert_eq!(
        solver.arena.active_clause_count(),
        before_clauses,
        "clause trace mode must not add proofless SBP clauses",
    );

    let trace = solver.clause_trace().expect("clause trace enabled");
    assert_eq!(
        trace.entries().len(),
        before_trace_len,
        "symmetry skip must leave the reconstruction trace unchanged",
    );
    assert!(
        trace.entries().iter().all(|entry| entry.is_original),
        "trace should contain only the input clauses when symmetry is skipped",
    );
    assert_eq!(
        solver.cold.symmetry_stats.last_skipped_reason,
        Some(crate::symmetry::SymmetrySkipReason::ProofMode),
    );
    assert_eq!(solver.cold.symmetry_stats.sb_clauses_added, 0);
}
