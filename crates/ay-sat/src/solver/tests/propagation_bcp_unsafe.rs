// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential tests: safe BCP vs unsafe BCP (#7989).
//!
//! Every test creates two identical solver instances, applies the same
//! decisions, runs safe BCP on one and unsafe BCP on the other, then
//! asserts that trail, qhead, and conflict results are identical.
//!
//! Gated on `#[cfg(feature = "raw-pointer-bcp")]` — these tests only compile
//! when the unsafe BCP implementation is present.

use super::*;
use crate::solver::propagation::bcp_mode;
use crate::solver::solver_stats::BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Literal from a DIMACS-style signed integer.
/// Positive n => positive literal for variable (n-1).
/// Negative n => negative literal for variable (|n|-1).
fn lit(dimacs: i32) -> Literal {
    assert!(dimacs != 0, "DIMACS literal 0 is invalid");
    let var = Variable(dimacs.unsigned_abs() - 1);
    if dimacs > 0 {
        Literal::positive(var)
    } else {
        Literal::negative(var)
    }
}

/// Build a solver from DIMACS-style clause descriptions.
/// `num_vars`: number of variables.
/// `clauses`: each inner vec is a clause of signed DIMACS literals.
fn build_solver(num_vars: usize, clauses: &[Vec<i32>]) -> Solver {
    let mut solver = Solver::new(num_vars);
    for clause in clauses {
        let lits: Vec<Literal> = clause.iter().map(|&d| lit(d)).collect();
        solver.add_clause(lits);
    }
    solver.initialize_watches();
    let _ = solver.process_initial_clauses();
    // NOTE: do NOT run BCP here — let run_bcp_comparison control when BCP runs
    // so we can compare safe vs unsafe on the initial propagation too.
    solver
}

fn bcp_long_bucket_index(labels: &[&str; 5], label: &str) -> usize {
    labels
        .iter()
        .position(|&candidate| candidate == label)
        .expect("BCP long-scan bucket label")
}

fn enable_bcp_learned_1963_blocker_cert_elision_for_test(solver: &mut Solver) {
    solver
        .stats
        .set_bcp_learned_1963_blocker_cert_elision_test_enabled(true);
}

fn enable_bcp_learned_1963_blocker_cert_shadow_for_test(solver: &mut Solver) {
    solver
        .stats
        .set_bcp_learned_1963_blocker_cert_shadow_test_enabled(true);
}

fn enable_bcp_learned_1963_blocker_cert_false_reject_demote_for_test(solver: &mut Solver) {
    solver
        .stats
        .set_bcp_learned_1963_blocker_cert_false_reject_demote_test_enabled(true);
}

fn seed_bcp_learned_1963_blocker_cert_repeats(
    solver: &mut Solver,
    clause_idx: usize,
    position: usize,
    literal_raw: u32,
    repeats: u8,
) {
    for _ in 0..repeats {
        solver.stats.record_bcp_learned_1963_blocker_cert_populate(
            clause_idx,
            position,
            literal_raw,
            true,
        );
    }
}

fn seed_bcp_learned_1963_blocker_cert(
    solver: &mut Solver,
    clause_idx: usize,
    position: usize,
    literal_raw: u32,
) {
    seed_bcp_learned_1963_blocker_cert_repeats(
        solver,
        clause_idx,
        position,
        literal_raw,
        BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS,
    );
}

fn stage_bcp_blocker_cert_false_start_wrap(
    solver: &mut Solver,
    clause_idx: usize,
    clause_len: usize,
    saved_pos: usize,
    true_slot: usize,
) {
    assert!(saved_pos > true_slot);
    assert!(true_slot >= 3);
    assert!(saved_pos < clause_len);

    solver.decide(Literal::positive(Variable(true_slot as u32)));
    solver.qhead = solver.trail.len();
    solver.decide(Literal::negative(Variable(2)));
    solver.qhead = solver.trail.len();
    for slot in saved_pos..clause_len {
        if slot != true_slot {
            solver.decide(Literal::negative(Variable(slot as u32)));
            solver.qhead = solver.trail.len();
        }
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);
}

fn learned_tail_reorder_fixture(clause_len: usize) -> (Solver, Vec<Literal>) {
    let mut solver = Solver::new(clause_len);
    for i in 0..clause_len {
        solver.var_data[i].level = 0;
        solver.var_data[i].trail_pos = 0;
    }
    solver.var_data[0].level = 99;
    solver.var_data[0].trail_pos = 99;
    solver.var_data[1].level = 10;
    solver.var_data[1].trail_pos = 10;
    solver.var_data[2].level = 1;
    solver.var_data[3].level = 3;
    solver.var_data[4].level = 2;
    let lits = (0..clause_len)
        .map(|i| Literal::positive(Variable(i as u32)))
        .collect();
    (solver, lits)
}

fn arena_clause_literals(solver: &Solver, idx: usize) -> Vec<Literal> {
    (0..solver.arena.len_of(idx))
        .map(|slot| solver.arena.literal(idx, slot))
        .collect()
}

/// Snapshot of solver state after BCP, for comparison.
#[derive(Debug, PartialEq)]
struct BcpSnapshot {
    trail: Vec<Literal>,
    qhead: usize,
    conflict: Option<u32>, // ClauseRef.0 if conflict, None otherwise
}

fn snapshot(solver: &Solver, conflict: Option<ClauseRef>) -> BcpSnapshot {
    BcpSnapshot {
        trail: solver.trail.clone(),
        qhead: solver.qhead,
        conflict: conflict.map(|c| c.0),
    }
}

/// Run BCP comparison: build two identical solvers, apply decisions,
/// run safe vs unsafe BCP, assert identical outcomes.
///
/// Returns the safe BCP snapshot for further inspection if needed.
fn run_bcp_comparison(num_vars: usize, clauses: &[Vec<i32>], decisions: &[i32]) -> BcpSnapshot {
    let mut safe_solver = build_solver(num_vars, clauses);
    let mut unsafe_solver = build_solver(num_vars, clauses);

    // Verify identical starting state
    assert_eq!(
        safe_solver.trail.len(),
        unsafe_solver.trail.len(),
        "solvers should have identical trail length after setup"
    );
    assert_eq!(
        safe_solver.qhead, unsafe_solver.qhead,
        "solvers should have identical qhead after setup"
    );

    // Run initial BCP to drain unit propagations from process_initial_clauses.
    // Compare safe vs unsafe even on initial propagation.
    let mut safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let mut unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    if safe_conflict.is_some() || unsafe_conflict.is_some() {
        // Initial BCP found conflict (e.g. contradictory units) — compare and return early.
        let safe_snap = snapshot(&safe_solver, safe_conflict);
        let unsafe_snap = snapshot(&unsafe_solver, unsafe_conflict);
        assert_eq!(
            safe_snap, unsafe_snap,
            "safe and unsafe BCP produced different results on initial propagation.\n\
             Safe:   {safe_snap:?}\n\
             Unsafe: {unsafe_snap:?}"
        );
        return safe_snap;
    }

    // Apply decisions one at a time, running BCP after each.
    for &dec in decisions {
        let decision_lit = lit(dec);

        // Skip if variable already assigned from prior propagation
        if safe_solver.var_is_assigned(decision_lit.variable().index()) {
            continue;
        }

        safe_solver.decide(decision_lit);
        unsafe_solver.decide(decision_lit);

        safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
        unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

        if safe_conflict.is_some() {
            break;
        }
    }

    let safe_snap = snapshot(&safe_solver, safe_conflict);
    let unsafe_snap = snapshot(&unsafe_solver, unsafe_conflict);

    assert_eq!(
        safe_snap, unsafe_snap,
        "safe and unsafe BCP produced different results.\n\
         Safe:   {safe_snap:?}\n\
         Unsafe: {unsafe_snap:?}"
    );

    safe_snap
}

fn run_search_route_comparison(
    mut routed_solver: Solver,
    mut reference_solver: Solver,
    decisions: &[i32],
    mut reference_propagate: impl FnMut(&mut Solver) -> Option<ClauseRef>,
) -> (BcpSnapshot, BcpSnapshot) {
    let mut routed_conflict = routed_solver.search_propagate();
    let mut reference_conflict = reference_propagate(&mut reference_solver);

    for &dec in decisions {
        if routed_conflict.is_some() || reference_conflict.is_some() {
            break;
        }

        let decision_lit = lit(dec);
        assert_eq!(
            routed_solver.var_is_assigned(decision_lit.variable().index()),
            reference_solver.var_is_assigned(decision_lit.variable().index()),
            "route/reference assignment state diverged before decision {dec}"
        );
        if routed_solver.var_is_assigned(decision_lit.variable().index()) {
            continue;
        }

        routed_solver.decide(decision_lit);
        reference_solver.decide(decision_lit);
        routed_conflict = routed_solver.search_propagate();
        reference_conflict = reference_propagate(&mut reference_solver);
    }

    (
        snapshot(&routed_solver, routed_conflict),
        snapshot(&reference_solver, reference_conflict),
    )
}

#[test]
fn test_search_inplace_watch_scan_gate_default_on_matches_safe_search() {
    let clauses = &[vec![-1, 2], vec![-2, 3, 4, 5, 6], vec![-3, -4, 6]];
    let routed_solver = build_solver(6, clauses);
    let reference_solver = build_solver(6, clauses);
    // The in-place SEARCH BCP path is the default (cold.rs): the same 2WL
    // algorithm as the safe deferred-copy path, without the per-propagation
    // watch-list memcpys. This test pins that the default route stays
    // bit-identical to the safe path.
    assert!(
        routed_solver.bcp_search_inplace_watch_scan_enabled(),
        "SEARCH in-place watch scan gate defaults on"
    );

    let (routed, safe) =
        run_search_route_comparison(routed_solver, reference_solver, &[1, -4, -5], |solver| {
            solver.propagate_bcp::<{ bcp_mode::SEARCH }>()
        });

    assert_eq!(
        routed, safe,
        "default in-place SEARCH route must match the safe BCP path"
    );
}

#[test]
fn test_search_inplace_watch_scan_gate_enabled_matches_direct_unsafe_search() {
    let clauses = &[vec![1, 2, 3, 4, 5, 6], vec![-6, 7], vec![-7, 8]];
    let mut routed_solver = build_solver(8, clauses);
    let reference_solver = build_solver(8, clauses);
    routed_solver.set_bcp_search_inplace_watch_scan_enabled(true);
    assert!(
        routed_solver.bcp_search_inplace_watch_scan_enabled(),
        "SEARCH in-place watch scan gate should reflect explicit enable"
    );

    let (routed, unsafe_direct) = run_search_route_comparison(
        routed_solver,
        reference_solver,
        &[-1, -2, -3, -4, -5],
        Solver::propagate_bcp_unsafe_search,
    );

    assert_eq!(
        routed, unsafe_direct,
        "enabled SEARCH route must match direct unsafe BCP"
    );
}

#[test]
fn test_search_inplace_watch_scan_route_records_exercise() {
    let clauses = &[vec![-1, 2], vec![-2, 3, 4, 5, 6]];
    let mut solver = build_solver(6, clauses);
    solver.set_bcp_search_inplace_watch_scan_enabled(true);

    assert!(solver.bcp_search_inplace_watch_scan_route_enabled());
    assert_eq!(solver.bcp_search_inplace_watch_scan_exercise_count(), 0);

    let _ = solver.search_propagate();

    assert!(solver.bcp_search_inplace_watch_scan_exercised());
    assert_eq!(solver.bcp_search_inplace_watch_scan_exercise_count(), 1);
}

// ---------------------------------------------------------------------------
// Test 1: Unit propagation
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_on_unit_propagation() {
    // Formula: (1) AND (-1 v 2) AND (-2 v 3)
    // Unit clause forces x0=true, then chain propagation: x1=true, x2=true.
    let snap = run_bcp_comparison(
        3,
        &[vec![1], vec![-1, 2], vec![-2, 3]],
        &[], // no decisions needed — unit propagation from level 0
    );
    assert!(snap.conflict.is_none(), "no conflict expected");
    assert_eq!(snap.trail.len(), 3, "all 3 variables should be assigned");
    assert_eq!(snap.qhead, 3, "qhead should match trail length");
}

// ---------------------------------------------------------------------------
// Test 2: Conflict detection
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_on_conflict() {
    // Formula: (-1 v -2) AND (1) AND (2)
    // Unit clauses force x0=true and x1=true, but (-1 v -2) conflicts.
    let snap = run_bcp_comparison(2, &[vec![-1, -2], vec![1], vec![2]], &[]);
    assert!(
        snap.conflict.is_some(),
        "conflict expected from contradictory unit clauses"
    );
}

// ---------------------------------------------------------------------------
// Test 3: Binary clauses only
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_binary_clauses() {
    // All binary: (-1 v 2), (-2 v 3), (-3 v 4), (-4 v 5)
    // Decide x0=true => chain: x1..x4 all true.
    let snap = run_bcp_comparison(
        5,
        &[vec![-1, 2], vec![-2, 3], vec![-3, 4], vec![-4, 5]],
        &[1], // decide x0 = true
    );
    assert!(snap.conflict.is_none(), "no conflict expected");
    // trail: level-0 propagations (none) + decision (1) + propagated (4) = 5
    assert_eq!(snap.trail.len(), 5, "all 5 variables should be assigned");
}

// ---------------------------------------------------------------------------
// Test 4: Long clauses (5+ literals)
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_long_clauses() {
    // 5-literal clause: (-1 v -2 v -3 v -4 v 5)
    // Decide x0=true, x1=true, x2=true, x3=true => forces x4=true.
    let snap = run_bcp_comparison(
        5,
        &[vec![-1, -2, -3, -4, 5]],
        &[1, 2, 3, 4], // four decisions to make the clause unit
    );
    assert!(snap.conflict.is_none(), "no conflict expected");
    assert_eq!(snap.trail.len(), 5, "all 5 variables should be assigned");
}

// ---------------------------------------------------------------------------
// Test 5: Replacement scan (saved_pos updates)
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_replacement_scan() {
    // Long clause where BCP must scan past false literals to find a replacement watch.
    // Clause: (1 v 2 v 3 v 4 v 5 v 6)
    // Decide -1 => watch moves. Decide -2 => watch moves again. Etc.
    // Each decision forces the replacement scan to find the next unassigned literal.
    let snap = run_bcp_comparison(
        6,
        &[vec![1, 2, 3, 4, 5, 6]],
        &[-1, -2, -3, -4, -5], // falsify first 5 => forces x5=true
    );
    assert!(snap.conflict.is_none(), "no conflict expected");
    assert_eq!(snap.trail.len(), 6, "all 6 variables should be assigned");
}

#[test]
fn test_unsafe_bcp_len18_saved_pos_telemetry_matches_safe() {
    let clause: Vec<i32> = (1..=18).collect();
    let mut safe_solver = build_solver(18, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(18, std::slice::from_ref(&clause));
    safe_solver.set_bcp_telemetry_enabled(true);
    unsafe_solver.set_bcp_telemetry_enabled(true);

    assert!(safe_solver
        .propagate_bcp::<{ bcp_mode::SEARCH }>()
        .is_none());
    assert!(unsafe_solver.propagate_bcp_unsafe_search().is_none());

    for decision in [-1, -2] {
        let decision_lit = lit(decision);
        safe_solver.decide(decision_lit);
        unsafe_solver.decide(decision_lit);
        assert!(safe_solver
            .propagate_bcp::<{ bcp_mode::SEARCH }>()
            .is_none());
        assert!(unsafe_solver.propagate_bcp_unsafe_search().is_none());
    }

    assert_eq!(
        safe_solver.bcp_saved_pos_stats(),
        unsafe_solver.bcp_saved_pos_stats(),
        "safe and unsafe BCP must expose identical saved-position telemetry"
    );
    let stats = unsafe_solver.bcp_saved_pos_stats();
    assert_eq!(stats.len18_scans, 2);
    assert_eq!(stats.len18_start_false, 1);
    assert_eq!(stats.len18_found_unassigned, 2);
    assert_eq!(stats.len18_found_true, 0);
    assert_eq!(stats.len18_no_replacement, 0);
    assert_eq!(stats.long_scans, stats.len18_scans);
    assert_eq!(stats.long_start_false, stats.len18_start_false);
}

#[test]
fn test_unsafe_bcp_len18_long_scan_counters_match_safe() {
    let clause: Vec<i32> = (1..=18).collect();
    let mut safe_solver = build_solver(18, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(18, std::slice::from_ref(&clause));
    safe_solver.set_bcp_telemetry_enabled(true);
    unsafe_solver.set_bcp_telemetry_enabled(true);

    let safe_clause = safe_solver
        .arena
        .active_indices()
        .next()
        .expect("safe clause");
    let unsafe_clause = unsafe_solver
        .arena
        .active_indices()
        .next()
        .expect("unsafe clause");
    safe_solver.arena.set_learned(safe_clause, true);
    unsafe_solver.arena.set_learned(unsafe_clause, true);

    for var in 2..18 {
        let decision = Literal::negative(Variable(var));
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        safe_solver.qhead = safe_solver.trail.len();
        unsafe_solver.qhead = unsafe_solver.trail.len();
    }
    let decision = Literal::negative(Variable(0));
    safe_solver.decide(decision);
    unsafe_solver.decide(decision);

    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();
    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "safe and unsafe BCP should match on learned len-18 unit outcome"
    );
    assert_eq!(
        safe_solver.bcp_long_scan_stats(),
        unsafe_solver.bcp_long_scan_stats(),
        "safe and unsafe long-scan diagnostics should match"
    );

    let stats = unsafe_solver.bcp_long_scan_stats();
    let len18 = bcp_long_bucket_index(&stats.bucket_labels, "18");
    assert_eq!(stats.scans_by_len[len18], 1);
    assert_eq!(stats.learned_scans_by_len[len18], 1);
    assert_eq!(stats.no_replacement_by_len[len18], 1);
    assert_eq!(stats.unit_by_len[len18], 1);
    assert_eq!(stats.learned_no_replacement_by_len[len18], 1);
}

#[test]
fn test_unsafe_bcp_len18_false_saved_pos_reset_matches_safe() {
    let clause: Vec<i32> = (1..=18).collect();
    let mut safe_solver = build_solver(18, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(18, std::slice::from_ref(&clause));
    let safe_clause = safe_solver
        .arena
        .active_indices()
        .next()
        .expect("safe clause");
    let unsafe_clause = unsafe_solver
        .arena
        .active_indices()
        .next()
        .expect("unsafe clause");

    let false_saved_tail = lit(-18);
    safe_solver.decide(false_saved_tail);
    unsafe_solver.decide(false_saved_tail);
    safe_solver.qhead = safe_solver.trail.len();
    unsafe_solver.qhead = unsafe_solver.trail.len();
    safe_solver.arena.set_saved_pos(safe_clause, 17);
    unsafe_solver.arena.set_saved_pos(unsafe_clause, 17);
    safe_solver.set_bcp_telemetry_enabled(true);
    unsafe_solver.set_bcp_telemetry_enabled(true);

    let decision = lit(-1);
    safe_solver.decide(decision);
    unsafe_solver.decide(decision);
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "len-18 false saved-position reset should preserve safe/unsafe parity"
    );
    assert_eq!(
        safe_solver.arena.literal(safe_clause, 0),
        lit(3),
        "safe BCP should move the first tail slot into the watch"
    );
    assert_eq!(
        unsafe_solver.arena.literal(unsafe_clause, 0),
        lit(3),
        "unsafe BCP should move the first tail slot into the watch"
    );
    assert_eq!(safe_solver.arena.saved_pos(safe_clause), 2);
    assert_eq!(unsafe_solver.arena.saved_pos(unsafe_clause), 2);
    assert_eq!(
        safe_solver.bcp_stats(),
        unsafe_solver.bcp_stats(),
        "len-18 scan telemetry should match"
    );
    assert_eq!(
        safe_solver.bcp_stats().2,
        1,
        "len-18 reset should scan only the first tail replacement"
    );
    assert_eq!(
        safe_solver.bcp_saved_pos_stats(),
        unsafe_solver.bcp_saved_pos_stats(),
        "saved-position telemetry should match"
    );
    let saved_stats = safe_solver.bcp_saved_pos_stats();
    assert_eq!(saved_stats.len18_scans, 1);
    assert_eq!(saved_stats.len18_start_false, 1);
    assert_eq!(saved_stats.len18_found_unassigned, 1);
}

#[test]
fn test_unsafe_bcp_len18_false_saved_pos_reset_skip_matches_safe() {
    let clause_len = 18;
    let saved_pos = 8;
    let replacement_pos = saved_pos + 1;
    let clause: Vec<i32> = (1..=clause_len as i32).collect();
    let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
    let safe_clause = safe_solver
        .arena
        .active_indices()
        .next()
        .expect("safe clause");
    let unsafe_clause = unsafe_solver
        .arena
        .active_indices()
        .next()
        .expect("unsafe clause");

    for slot in 2..=saved_pos {
        let decision = Literal::negative(Variable(slot as u32));
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        safe_solver.qhead = safe_solver.trail.len();
        unsafe_solver.qhead = unsafe_solver.trail.len();
    }
    safe_solver.arena.set_saved_pos(safe_clause, saved_pos);
    unsafe_solver.arena.set_saved_pos(unsafe_clause, saved_pos);
    safe_solver.set_bcp_telemetry_enabled(true);
    unsafe_solver.set_bcp_telemetry_enabled(true);

    let decision = lit(-1);
    safe_solver.decide(decision);
    unsafe_solver.decide(decision);
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "known-false saved-start skip should preserve safe/unsafe parity"
    );
    assert_eq!(
        safe_solver.arena.literal(safe_clause, 0),
        Literal::positive(Variable(replacement_pos as u32)),
        "safe BCP should move the first non-false tail after the skipped slot into the watch"
    );
    assert_eq!(
        unsafe_solver.arena.literal(unsafe_clause, 0),
        Literal::positive(Variable(replacement_pos as u32)),
        "unsafe BCP should move the first non-false tail after the skipped slot into the watch"
    );
    assert_eq!(safe_solver.arena.saved_pos(safe_clause), replacement_pos);
    assert_eq!(
        unsafe_solver.arena.saved_pos(unsafe_clause),
        replacement_pos
    );
    assert_eq!(
        safe_solver.bcp_stats(),
        unsafe_solver.bcp_stats(),
        "scan telemetry should match after skipping the known-false saved-start slot"
    );
    assert_eq!(safe_solver.bcp_stats().2, (replacement_pos - 2) as u64);
    assert_eq!(
        safe_solver.bcp_saved_pos_stats(),
        unsafe_solver.bcp_saved_pos_stats(),
        "saved-position telemetry should match"
    );
    assert_eq!(
        safe_solver.bcp_long_scan_stats(),
        unsafe_solver.bcp_long_scan_stats(),
        "long-scan telemetry should match"
    );
}

#[test]
fn test_unsafe_bcp_learned_false_start_reset_buckets_match_safe() {
    for (clause_len, saved_pos, bucket_label) in [
        (9usize, 5usize, "9-17"),
        (18usize, 12usize, "18"),
        (32usize, 20usize, "19-63"),
    ] {
        let clause: Vec<i32> = (1..=clause_len as i32).collect();
        let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let safe_clause = safe_solver
            .arena
            .active_indices()
            .next()
            .expect("safe clause");
        let unsafe_clause = unsafe_solver
            .arena
            .active_indices()
            .next()
            .expect("unsafe clause");
        safe_solver.arena.set_learned(safe_clause, true);
        unsafe_solver.arena.set_learned(unsafe_clause, true);
        safe_solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);
        unsafe_solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);

        for slot in saved_pos..clause_len {
            let decision = Literal::negative(Variable(slot as u32));
            safe_solver.decide(decision);
            unsafe_solver.decide(decision);
            safe_solver.qhead = safe_solver.trail.len();
            unsafe_solver.qhead = unsafe_solver.trail.len();
        }
        safe_solver.arena.set_saved_pos(safe_clause, saved_pos);
        unsafe_solver.arena.set_saved_pos(unsafe_clause, saved_pos);
        safe_solver.set_bcp_telemetry_enabled(true);
        unsafe_solver.set_bcp_telemetry_enabled(true);

        let decision = lit(-1);
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
        let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

        assert_eq!(
            snapshot(&safe_solver, safe_conflict),
            snapshot(&unsafe_solver, unsafe_conflict),
            "len-{clause_len} learned false-start reset should preserve safe/unsafe parity"
        );
        assert_eq!(safe_conflict, None);
        assert_eq!(
            safe_solver.arena.saved_pos(safe_clause),
            unsafe_solver.arena.saved_pos(unsafe_clause),
            "len-{clause_len} saved_pos should match after reset"
        );
        assert_eq!(
            safe_solver.arena.saved_pos(safe_clause),
            2,
            "len-{clause_len} reset should record the first tail slot"
        );
        assert_eq!(
            safe_solver.arena.literal(safe_clause, 0),
            unsafe_solver.arena.literal(unsafe_clause, 0),
            "len-{clause_len} watched replacement should match"
        );
        assert_eq!(
            safe_solver.arena.literal(safe_clause, 0),
            lit(3),
            "len-{clause_len} reset should move the first tail literal into the watch"
        );
        assert_eq!(
            safe_solver.bcp_stats(),
            unsafe_solver.bcp_stats(),
            "len-{clause_len} scan telemetry should match"
        );
        assert_eq!(
            safe_solver.bcp_stats().2,
            1,
            "len-{clause_len} reset should check only the first tail slot"
        );
        assert_eq!(
            safe_solver.bcp_saved_pos_stats(),
            unsafe_solver.bcp_saved_pos_stats(),
            "len-{clause_len} saved-position telemetry should match"
        );
        assert_eq!(
            safe_solver.bcp_long_scan_stats(),
            unsafe_solver.bcp_long_scan_stats(),
            "len-{clause_len} long-scan telemetry should match"
        );
        let long_stats = safe_solver.bcp_long_scan_stats();
        let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, bucket_label);
        assert_eq!(long_stats.scan_steps_by_len[bucket], 1);
        assert_eq!(long_stats.learned_scan_steps_by_len[bucket], 1);
    }
}

#[test]
fn test_unsafe_bcp_learned_1963_false_saved_pos_reset_matches_safe() {
    let clause_len = 32;
    let saved_pos = 20;
    let clause: Vec<i32> = (1..=clause_len as i32).collect();
    let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
    let safe_clause = safe_solver
        .arena
        .active_indices()
        .next()
        .expect("safe clause");
    let unsafe_clause = unsafe_solver
        .arena
        .active_indices()
        .next()
        .expect("unsafe clause");
    safe_solver.arena.set_learned(safe_clause, true);
    unsafe_solver.arena.set_learned(unsafe_clause, true);
    safe_solver.set_bcp_learned_1963_false_saved_pos_reset_enabled(true);
    unsafe_solver.set_bcp_learned_1963_false_saved_pos_reset_enabled(true);

    for slot in saved_pos..clause_len {
        let decision = Literal::negative(Variable(slot as u32));
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        safe_solver.qhead = safe_solver.trail.len();
        unsafe_solver.qhead = unsafe_solver.trail.len();
    }
    safe_solver.arena.set_saved_pos(safe_clause, saved_pos);
    unsafe_solver.arena.set_saved_pos(unsafe_clause, saved_pos);
    safe_solver.set_bcp_telemetry_enabled(true);
    unsafe_solver.set_bcp_telemetry_enabled(true);

    let decision = lit(-1);
    safe_solver.decide(decision);
    unsafe_solver.decide(decision);
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "learned 19-63 false-start reset should preserve safe/unsafe parity"
    );
    assert_eq!(
        safe_solver.arena.saved_pos(safe_clause),
        unsafe_solver.arena.saved_pos(unsafe_clause),
        "learned 19-63 saved_pos should match after reset"
    );
    assert_eq!(safe_solver.arena.saved_pos(safe_clause), 2);
    assert_eq!(
        safe_solver.arena.literal(safe_clause, 0),
        unsafe_solver.arena.literal(unsafe_clause, 0),
        "learned 19-63 watched replacement should match"
    );
    assert_eq!(
        safe_solver.bcp_stats(),
        unsafe_solver.bcp_stats(),
        "learned 19-63 scan telemetry should match"
    );
    assert_eq!(
        safe_solver.bcp_stats().2,
        1,
        "learned 19-63 reset should check only the first tail slot"
    );
    assert_eq!(
        safe_solver.bcp_saved_pos_stats(),
        unsafe_solver.bcp_saved_pos_stats(),
        "learned 19-63 saved-position telemetry should match"
    );
    assert_eq!(
        safe_solver.bcp_long_scan_stats(),
        unsafe_solver.bcp_long_scan_stats(),
        "learned 19-63 long-scan telemetry should match"
    );
    let long_stats = safe_solver.bcp_long_scan_stats();
    let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, "19-63");
    assert_eq!(long_stats.scan_steps_by_len[bucket], 1);
    assert_eq!(long_stats.learned_scan_steps_by_len[bucket], 1);
}

#[test]
fn test_unsafe_bcp_learned_1963_false_saved_pos_reset_no_replacement_matches_safe() {
    let clause_len = 32;
    let saved_pos = 20;
    let expected_steps = (clause_len - 2 - 1) as u64;
    let clause: Vec<i32> = (1..=clause_len as i32).collect();
    let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
    let safe_clause = safe_solver
        .arena
        .active_indices()
        .next()
        .expect("safe clause");
    let unsafe_clause = unsafe_solver
        .arena
        .active_indices()
        .next()
        .expect("unsafe clause");
    safe_solver.arena.set_learned(safe_clause, true);
    unsafe_solver.arena.set_learned(unsafe_clause, true);
    safe_solver.set_bcp_learned_1963_false_saved_pos_reset_enabled(true);
    unsafe_solver.set_bcp_learned_1963_false_saved_pos_reset_enabled(true);

    for slot in 2..clause_len {
        let decision = Literal::negative(Variable(slot as u32));
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        safe_solver.qhead = safe_solver.trail.len();
        unsafe_solver.qhead = unsafe_solver.trail.len();
    }
    safe_solver.arena.set_saved_pos(safe_clause, saved_pos);
    unsafe_solver.arena.set_saved_pos(unsafe_clause, saved_pos);
    safe_solver.set_bcp_telemetry_enabled(true);
    unsafe_solver.set_bcp_telemetry_enabled(true);

    let decision = lit(-1);
    safe_solver.decide(decision);
    unsafe_solver.decide(decision);
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "learned 19-63 no-replacement reset path should preserve safe/unsafe parity"
    );
    assert_eq!(
        safe_solver.arena.saved_pos(safe_clause),
        unsafe_solver.arena.saved_pos(unsafe_clause),
        "no-replacement saved_pos should match"
    );
    assert_eq!(
        safe_solver.arena.saved_pos(safe_clause),
        saved_pos,
        "learned 19-63 reset must not rewrite saved_pos on no-replacement unit paths"
    );
    assert_eq!(
        safe_solver.bcp_stats(),
        unsafe_solver.bcp_stats(),
        "learned 19-63 no-replacement scan telemetry should match"
    );
    assert_eq!(
        safe_solver.bcp_stats().2,
        expected_steps,
        "learned 19-63 reset should full-scan every tail slot except the known-false saved start"
    );
    assert_eq!(
        safe_solver.bcp_saved_pos_stats(),
        unsafe_solver.bcp_saved_pos_stats(),
        "learned 19-63 no-replacement saved-position telemetry should match"
    );
    assert_eq!(
        safe_solver.bcp_long_scan_stats(),
        unsafe_solver.bcp_long_scan_stats(),
        "learned 19-63 no-replacement long-scan telemetry should match"
    );
    let long_stats = safe_solver.bcp_long_scan_stats();
    let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, "19-63");
    assert_eq!(long_stats.scan_steps_by_len[bucket], expected_steps);
    assert_eq!(long_stats.learned_scan_steps_by_len[bucket], expected_steps);
    assert_eq!(long_stats.no_replacement_by_len[bucket], 1);
    assert_eq!(long_stats.learned_no_replacement_by_len[bucket], 1);
}

#[test]
fn test_unsafe_bcp_learned_1963_true_tail_relocation_matches_safe() {
    let clause_len = 32;
    let true_slot = 3usize;
    let clause: Vec<i32> = (1..=clause_len as i32).collect();
    let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
    let safe_clause = safe_solver
        .arena
        .active_indices()
        .next()
        .expect("safe clause");
    let unsafe_clause = unsafe_solver
        .arena
        .active_indices()
        .next()
        .expect("unsafe clause");
    safe_solver.arena.set_learned(safe_clause, true);
    unsafe_solver.arena.set_learned(unsafe_clause, true);
    safe_solver.set_bcp_telemetry_enabled(true);
    unsafe_solver.set_bcp_telemetry_enabled(true);
    safe_solver.set_bcp_learned_1963_true_tail_relocation_enabled(true);
    unsafe_solver.set_bcp_learned_1963_true_tail_relocation_enabled(true);

    let true_tail = lit((true_slot + 1) as i32);
    safe_solver.decide(true_tail);
    unsafe_solver.decide(true_tail);
    safe_solver.qhead = safe_solver.trail.len();
    unsafe_solver.qhead = unsafe_solver.trail.len();
    safe_solver.arena.set_saved_pos(safe_clause, true_slot);
    unsafe_solver.arena.set_saved_pos(unsafe_clause, true_slot);

    safe_solver.decide(lit(-1));
    unsafe_solver.decide(lit(-1));
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "learned 19-63 true-tail relocation should preserve safe/unsafe parity"
    );
    assert_eq!(
        safe_solver.arena.literal(safe_clause, 0),
        unsafe_solver.arena.literal(unsafe_clause, 0),
        "relocated watched literal should match"
    );
    assert_eq!(safe_solver.arena.literal(safe_clause, 0), true_tail);
    assert_eq!(
        safe_solver.arena.literal(safe_clause, true_slot),
        unsafe_solver.arena.literal(unsafe_clause, true_slot),
        "tail slot receiving the falsified watch should match"
    );
    assert_eq!(safe_solver.arena.literal(safe_clause, true_slot), lit(1));
    assert_eq!(
        safe_solver.arena.saved_pos(safe_clause),
        unsafe_solver.arena.saved_pos(unsafe_clause),
        "saved_pos should match after true-tail relocation"
    );
    assert_eq!(safe_solver.arena.saved_pos(safe_clause), true_slot + 1);
    assert_eq!(safe_solver.watches.len_of(lit(1)), 0);
    assert_eq!(unsafe_solver.watches.len_of(lit(1)), 0);
    assert_eq!(safe_solver.watches.len_of(true_tail), 1);
    assert_eq!(unsafe_solver.watches.len_of(true_tail), 1);
    assert_eq!(
        safe_solver.bcp_long_scan_stats(),
        unsafe_solver.bcp_long_scan_stats(),
        "safe and unsafe BCP should expose identical relocation telemetry"
    );
    let long_stats = safe_solver.bcp_long_scan_stats();
    assert!(long_stats.learned_1963_true_tail_relocation_enabled);
    assert_eq!(long_stats.learned_1963_true_tail_relocation_attempts, 1);
    assert_eq!(long_stats.learned_1963_true_tail_relocation_moves, 1);
}

#[test]
fn test_unsafe_bcp_learned_618_true_tail_relocation_matches_safe() {
    for clause_len in [6usize, 18usize] {
        let true_slot = 3usize;
        let clause: Vec<i32> = (1..=clause_len as i32).collect();
        let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let safe_clause = safe_solver
            .arena
            .active_indices()
            .next()
            .expect("safe clause");
        let unsafe_clause = unsafe_solver
            .arena
            .active_indices()
            .next()
            .expect("unsafe clause");
        safe_solver.arena.set_learned(safe_clause, true);
        unsafe_solver.arena.set_learned(unsafe_clause, true);
        safe_solver.set_bcp_telemetry_enabled(true);
        unsafe_solver.set_bcp_telemetry_enabled(true);
        safe_solver.set_bcp_learned_618_true_tail_relocation_enabled(true);
        unsafe_solver.set_bcp_learned_618_true_tail_relocation_enabled(true);

        let true_tail = lit((true_slot + 1) as i32);
        safe_solver.decide(true_tail);
        unsafe_solver.decide(true_tail);
        safe_solver.qhead = safe_solver.trail.len();
        unsafe_solver.qhead = unsafe_solver.trail.len();
        safe_solver.arena.set_saved_pos(safe_clause, true_slot);
        unsafe_solver.arena.set_saved_pos(unsafe_clause, true_slot);

        safe_solver.decide(lit(-1));
        unsafe_solver.decide(lit(-1));
        let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
        let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

        assert_eq!(
            snapshot(&safe_solver, safe_conflict),
            snapshot(&unsafe_solver, unsafe_conflict),
            "learned 6-18 true-tail relocation should preserve safe/unsafe parity for len-{clause_len}"
        );
        assert_eq!(
            safe_solver.arena.literal(safe_clause, 0),
            unsafe_solver.arena.literal(unsafe_clause, 0),
            "len-{clause_len} relocated watched literal should match"
        );
        assert_eq!(safe_solver.arena.literal(safe_clause, 0), true_tail);
        assert_eq!(
            safe_solver.arena.literal(safe_clause, true_slot),
            unsafe_solver.arena.literal(unsafe_clause, true_slot),
            "len-{clause_len} tail slot receiving the falsified watch should match"
        );
        assert_eq!(safe_solver.arena.literal(safe_clause, true_slot), lit(1));
        assert_eq!(
            safe_solver.arena.saved_pos(safe_clause),
            unsafe_solver.arena.saved_pos(unsafe_clause),
            "len-{clause_len} saved_pos should match after 6-18 true-tail relocation"
        );
        assert_eq!(safe_solver.arena.saved_pos(safe_clause), true_slot + 1);
        assert_eq!(safe_solver.watches.len_of(lit(1)), 0);
        assert_eq!(unsafe_solver.watches.len_of(lit(1)), 0);
        assert_eq!(safe_solver.watches.len_of(true_tail), 1);
        assert_eq!(unsafe_solver.watches.len_of(true_tail), 1);
        assert_eq!(
            safe_solver.bcp_long_scan_stats(),
            unsafe_solver.bcp_long_scan_stats(),
            "safe and unsafe BCP should expose identical 6-18 relocation telemetry"
        );
        let long_stats = safe_solver.bcp_long_scan_stats();
        assert!(long_stats.learned_618_true_tail_relocation_enabled);
        assert_eq!(long_stats.learned_618_true_tail_relocation_attempts, 1);
        assert_eq!(long_stats.learned_618_true_tail_relocation_moves, 1);
        assert_eq!(long_stats.learned_1963_true_tail_relocation_attempts, 0);
    }
}

fn assert_tail_reorder_gate_matches_safe<F>(clause_len: usize, enable_gate: F, label: &str)
where
    F: Fn(&mut Solver),
{
    let (mut safe_solver, safe_lits) = learned_tail_reorder_fixture(clause_len);
    let (mut unsafe_solver, unsafe_lits) = learned_tail_reorder_fixture(clause_len);
    safe_solver.set_bcp_telemetry_enabled(true);
    unsafe_solver.set_bcp_telemetry_enabled(true);
    enable_gate(&mut safe_solver);
    enable_gate(&mut unsafe_solver);

    let safe_clause = safe_solver.add_learned_clause(safe_lits, 4, &[]).0 as usize;
    let unsafe_clause = unsafe_solver.add_learned_clause(unsafe_lits, 4, &[]).0 as usize;

    assert_eq!(
        arena_clause_literals(&safe_solver, safe_clause),
        arena_clause_literals(&unsafe_solver, unsafe_clause),
        "creation-time learned {label} tail reorder should produce identical safe/unsafe clauses"
    );
    assert_eq!(safe_solver.arena.literal(safe_clause, 0), lit(1));
    assert_eq!(safe_solver.arena.literal(safe_clause, 1), lit(2));
    assert_eq!(safe_solver.arena.literal(safe_clause, 2), lit(4));
    assert_eq!(safe_solver.arena.literal(safe_clause, 3), lit(5));
    assert_eq!(safe_solver.arena.literal(safe_clause, 4), lit(3));

    safe_solver.decide(lit(-1));
    unsafe_solver.decide(lit(-1));
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "safe and unsafe BCP should remain in parity after learned {label} tail reorder"
    );
    assert_eq!(
        safe_solver.bcp_long_scan_stats(),
        unsafe_solver.bcp_long_scan_stats(),
        "safe and unsafe BCP should expose identical learned {label} tail reorder telemetry"
    );
}

#[test]
fn test_unsafe_bcp_learned_617_tail_reorder_gate_matches_safe() {
    for clause_len in [6usize, 17usize] {
        assert_tail_reorder_gate_matches_safe(
            clause_len,
            |solver| solver.set_bcp_learned_617_tail_reorder_enabled(true),
            "6-17",
        );
    }
}

#[test]
fn test_unsafe_bcp_learned_18_tail_reorder_gate_matches_safe() {
    assert_tail_reorder_gate_matches_safe(
        18,
        |solver| solver.set_bcp_learned_18_tail_reorder_enabled(true),
        "18",
    );
}

#[test]
fn test_unsafe_bcp_learned_1963_tail_reorder_gate_matches_safe() {
    assert_tail_reorder_gate_matches_safe(
        32,
        |solver| solver.set_bcp_learned_1963_tail_reorder_enabled(true),
        "19-63",
    );
}

#[test]
fn test_unsafe_bcp_learned_1963_budget_tail_reorder_gate_matches_safe() {
    assert_tail_reorder_gate_matches_safe(
        32,
        |solver| solver.set_bcp_learned_1963_tail_reorder_swap_budget(Some(2)),
        "19-63 budgeted",
    );
}

#[test]
fn test_unsafe_bcp_learned_1963_true_tail_relocation_saved_pos_wrap_matches_safe() {
    let clause_len = 32;
    let true_slot = clause_len - 1;
    let clause: Vec<i32> = (1..=clause_len as i32).collect();
    let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
    let safe_clause = safe_solver
        .arena
        .active_indices()
        .next()
        .expect("safe clause");
    let unsafe_clause = unsafe_solver
        .arena
        .active_indices()
        .next()
        .expect("unsafe clause");
    safe_solver.arena.set_learned(safe_clause, true);
    unsafe_solver.arena.set_learned(unsafe_clause, true);
    safe_solver.set_bcp_telemetry_enabled(true);
    unsafe_solver.set_bcp_telemetry_enabled(true);
    safe_solver.set_bcp_learned_1963_true_tail_relocation_enabled(true);
    unsafe_solver.set_bcp_learned_1963_true_tail_relocation_enabled(true);

    let true_tail = lit((true_slot + 1) as i32);
    safe_solver.decide(true_tail);
    unsafe_solver.decide(true_tail);
    safe_solver.qhead = safe_solver.trail.len();
    unsafe_solver.qhead = unsafe_solver.trail.len();
    safe_solver.arena.set_saved_pos(safe_clause, true_slot);
    unsafe_solver.arena.set_saved_pos(unsafe_clause, true_slot);

    safe_solver.decide(lit(-1));
    unsafe_solver.decide(lit(-1));
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "learned 19-63 true-tail relocation wrap should preserve safe/unsafe parity"
    );
    assert_eq!(
        safe_solver.arena.saved_pos(safe_clause),
        unsafe_solver.arena.saved_pos(unsafe_clause),
        "wrapped saved_pos should match"
    );
    assert_eq!(safe_solver.arena.saved_pos(safe_clause), 2);
    assert_eq!(safe_solver.arena.literal(safe_clause, 0), true_tail);
    assert_eq!(
        unsafe_solver.arena.literal(unsafe_clause, 0),
        true_tail,
        "unsafe BCP should relocate the same true tail"
    );
}

#[test]
fn test_unsafe_bcp_satisfied_other_watch_blocker_miss_skips_saved_pos_scan() {
    let clause = vec![1, 2, 3, 4, 5, 6];
    let mut safe_solver = build_solver(6, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(6, std::slice::from_ref(&clause));
    let safe_clause = safe_solver
        .arena
        .active_indices()
        .next()
        .expect("safe clause");
    let unsafe_clause = unsafe_solver
        .arena
        .active_indices()
        .next()
        .expect("unsafe clause");
    let watch_lit = lit(1);
    let other_watch = lit(2);
    let stale_blocker = lit(3);

    safe_solver.decide(other_watch);
    unsafe_solver.decide(other_watch);
    assert!(safe_solver
        .propagate_bcp::<{ bcp_mode::SEARCH }>()
        .is_none());
    assert!(unsafe_solver.propagate_bcp_unsafe_search().is_none());

    safe_solver.arena.set_saved_pos(safe_clause, 4);
    unsafe_solver.arena.set_saved_pos(unsafe_clause, 4);
    let safe_clause_raw = safe_solver.watches.clause_raw(watch_lit, 0);
    let unsafe_clause_raw = unsafe_solver.watches.clause_raw(watch_lit, 0);
    safe_solver
        .watches
        .set_entry(watch_lit, 0, stale_blocker.0, safe_clause_raw);
    unsafe_solver
        .watches
        .set_entry(watch_lit, 0, stale_blocker.0, unsafe_clause_raw);
    safe_solver.set_bcp_telemetry_enabled(true);
    unsafe_solver.set_bcp_telemetry_enabled(true);

    let decision = lit(-1);
    safe_solver.decide(decision);
    unsafe_solver.decide(decision);
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "satisfied other-watch blocker miss should preserve safe/unsafe parity"
    );
    assert_eq!(
        safe_solver.watches.blocker(watch_lit, 0),
        other_watch,
        "safe BCP should refresh blocker to the satisfied other watch"
    );
    assert_eq!(
        unsafe_solver.watches.blocker(watch_lit, 0),
        other_watch,
        "unsafe BCP should refresh blocker to the satisfied other watch"
    );
    assert_eq!(safe_solver.arena.saved_pos(safe_clause), 4);
    assert_eq!(unsafe_solver.arena.saved_pos(unsafe_clause), 4);
    assert_eq!(
        safe_solver.bcp_stats(),
        (0, 0, 0),
        "safe path should skip replacement scanning"
    );
    assert_eq!(
        unsafe_solver.bcp_stats(),
        (0, 0, 0),
        "unsafe path should skip replacement scanning"
    );
    assert_eq!(safe_solver.bcp_saved_pos_stats().long_scans, 0);
    assert_eq!(unsafe_solver.bcp_saved_pos_stats().long_scans, 0);
}

#[test]
fn test_unsafe_bcp_no_replacement_unit_blocker_refresh_matches_safe() {
    let clause = vec![1, 2, 3, 4, 5, 6];
    let mut safe_solver = build_solver(6, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(6, std::slice::from_ref(&clause));
    let watch_lit = lit(1);
    let implied_watch = lit(2);
    let stale_false_blocker = lit(3);

    for decision in [-3, -4, -5, -6] {
        safe_solver.decide(lit(decision));
        unsafe_solver.decide(lit(decision));
        safe_solver.qhead = safe_solver.trail.len();
        unsafe_solver.qhead = unsafe_solver.trail.len();
    }

    let safe_clause_raw = safe_solver.watches.clause_raw(watch_lit, 0);
    let unsafe_clause_raw = unsafe_solver.watches.clause_raw(watch_lit, 0);
    safe_solver
        .watches
        .set_entry(watch_lit, 0, stale_false_blocker.0, safe_clause_raw);
    unsafe_solver
        .watches
        .set_entry(watch_lit, 0, stale_false_blocker.0, unsafe_clause_raw);

    safe_solver.decide(lit(-1));
    unsafe_solver.decide(lit(-1));
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "no-replacement unit blocker refresh should preserve safe/unsafe parity"
    );
    assert_eq!(
        safe_solver.watches.blocker(watch_lit, 0),
        implied_watch,
        "safe BCP should refresh the kept blocker to the implied watch"
    );
    assert_eq!(
        unsafe_solver.watches.blocker(watch_lit, 0),
        implied_watch,
        "unsafe BCP should refresh the kept blocker to the implied watch"
    );
}

#[test]
fn test_unsafe_bcp_learned_1963_no_replacement_unit_refresh_disable_matches_safe() {
    let clause: Vec<i32> = (1..=32).collect();
    let mut safe_solver = build_solver(32, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(32, std::slice::from_ref(&clause));
    let safe_clause = safe_solver
        .arena
        .active_indices()
        .next()
        .expect("safe clause");
    let unsafe_clause = unsafe_solver
        .arena
        .active_indices()
        .next()
        .expect("unsafe clause");
    let watch_lit = lit(1);
    let implied_watch = lit(2);
    let stale_false_blocker = lit(3);

    safe_solver.arena.set_learned(safe_clause, true);
    unsafe_solver.arena.set_learned(unsafe_clause, true);
    safe_solver.set_bcp_disable_learned_1963_no_replacement_unit_blocker_refresh_enabled(true);
    unsafe_solver.set_bcp_disable_learned_1963_no_replacement_unit_blocker_refresh_enabled(true);

    for var in 3..=32 {
        let decision = lit(-var);
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        safe_solver.qhead = safe_solver.trail.len();
        unsafe_solver.qhead = unsafe_solver.trail.len();
    }

    let safe_clause_raw = safe_solver.watches.clause_raw(watch_lit, 0);
    let unsafe_clause_raw = unsafe_solver.watches.clause_raw(watch_lit, 0);
    safe_solver
        .watches
        .set_entry(watch_lit, 0, stale_false_blocker.0, safe_clause_raw);
    unsafe_solver
        .watches
        .set_entry(watch_lit, 0, stale_false_blocker.0, unsafe_clause_raw);

    safe_solver.decide(lit(-1));
    unsafe_solver.decide(lit(-1));
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "learned 19-63 blocker-refresh disable should preserve safe/unsafe parity"
    );
    assert_eq!(
        safe_solver.watches.blocker(watch_lit, 0),
        stale_false_blocker,
        "safe BCP should keep the existing blocker when the experiment is enabled"
    );
    assert_eq!(
        unsafe_solver.watches.blocker(watch_lit, 0),
        stale_false_blocker,
        "unsafe BCP should keep the existing blocker when the experiment is enabled"
    );
    assert_eq!(safe_solver.lit_val(implied_watch), 1);
    assert_eq!(unsafe_solver.lit_val(implied_watch), 1);
}

#[test]
fn test_unsafe_bcp_saved_pos_advance_matches_safe() {
    let clause: Vec<i32> = (1..=18).collect();
    let mut safe_solver = build_solver(18, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(18, std::slice::from_ref(&clause));
    safe_solver.set_bcp_telemetry_enabled(true);
    unsafe_solver.set_bcp_telemetry_enabled(true);
    safe_solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);
    unsafe_solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);

    assert!(safe_solver
        .propagate_bcp::<{ bcp_mode::SEARCH }>()
        .is_none());
    assert!(unsafe_solver.propagate_bcp_unsafe_search().is_none());

    let safe_clause = safe_solver
        .arena
        .active_indices()
        .next()
        .expect("safe clause");
    let unsafe_clause = unsafe_solver
        .arena
        .active_indices()
        .next()
        .expect("unsafe clause");
    safe_solver.arena.set_learned(safe_clause, true);
    unsafe_solver.arena.set_learned(unsafe_clause, true);

    let first_decision = lit(-1);
    safe_solver.decide(first_decision);
    unsafe_solver.decide(first_decision);
    assert!(safe_solver
        .propagate_bcp::<{ bcp_mode::SEARCH }>()
        .is_none());
    assert!(unsafe_solver.propagate_bcp_unsafe_search().is_none());
    assert_eq!(
        safe_solver.arena.saved_pos(safe_clause),
        unsafe_solver.arena.saved_pos(unsafe_clause),
        "safe and unsafe BCP should match after a saved_pos hit"
    );
    assert_eq!(
        safe_solver.arena.saved_pos(safe_clause),
        2,
        "unassigned replacement at the current saved_pos should not advance"
    );

    let second_decision = lit(-2);
    safe_solver.decide(second_decision);
    unsafe_solver.decide(second_decision);
    assert!(safe_solver
        .propagate_bcp::<{ bcp_mode::SEARCH }>()
        .is_none());
    assert!(unsafe_solver.propagate_bcp_unsafe_search().is_none());

    assert_eq!(
        safe_solver.arena.saved_pos(safe_clause),
        unsafe_solver.arena.saved_pos(unsafe_clause),
        "safe and unsafe BCP should end with the same saved_pos"
    );
    assert_eq!(
        safe_solver.arena.saved_pos(safe_clause),
        4,
        "unassigned replacement after a saved_pos miss should advance past the replacement"
    );
    assert_eq!(
        safe_solver.arena.literal(safe_clause, 0),
        unsafe_solver.arena.literal(unsafe_clause, 0),
        "watch 0 should match after safe/unsafe BCP"
    );
    assert_eq!(
        safe_solver.arena.literal(safe_clause, 1),
        unsafe_solver.arena.literal(unsafe_clause, 1),
        "watch 1 should match after safe/unsafe BCP"
    );
    assert_eq!(
        safe_solver.bcp_saved_pos_stats(),
        unsafe_solver.bcp_saved_pos_stats(),
        "safe and unsafe BCP must expose identical saved-position telemetry"
    );
    let stats = unsafe_solver.bcp_saved_pos_stats();
    assert_eq!(stats.len18_scans, 2);
    assert_eq!(
        stats.len18_start_false, 1,
        "miss-gated advance should leave one scan starting on the swapped false tail slot"
    );
    assert_eq!(stats.len18_found_unassigned, 2);
    assert_eq!(stats.len18_found_true, 0);
    assert_eq!(stats.len18_no_replacement, 0);
}

#[test]
fn test_unsafe_bcp_saved_pos_advance_guard_matches_safe() {
    let clause: Vec<i32> = (1..=18).collect();
    let mut safe_solver = build_solver(18, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(18, std::slice::from_ref(&clause));
    safe_solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);
    unsafe_solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);

    let safe_clause = safe_solver
        .arena
        .active_indices()
        .next()
        .expect("safe clause");
    let unsafe_clause = unsafe_solver
        .arena
        .active_indices()
        .next()
        .expect("unsafe clause");
    safe_solver.arena.set_learned(safe_clause, true);
    unsafe_solver.arena.set_learned(unsafe_clause, true);

    for decision in [lit(-3), lit(-5)] {
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        safe_solver.qhead = safe_solver.trail.len();
        unsafe_solver.qhead = unsafe_solver.trail.len();
    }

    let decision = lit(-1);
    safe_solver.decide(decision);
    unsafe_solver.decide(decision);
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "guarded saved-pos advance should keep safe and unsafe BCP in parity"
    );
    assert_eq!(
        safe_solver.arena.saved_pos(safe_clause),
        unsafe_solver.arena.saved_pos(unsafe_clause),
        "guarded saved_pos should match"
    );
    assert_eq!(
        safe_solver.arena.saved_pos(safe_clause),
        3,
        "guarded advance should keep saved_pos on the replacement when the next tail slot is false"
    );
}

#[test]
fn test_unsafe_bcp_saved_pos_advance_original_clause_matches_safe() {
    let clause: Vec<i32> = (1..=18).collect();
    let mut safe_solver = build_solver(18, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(18, std::slice::from_ref(&clause));
    safe_solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);
    unsafe_solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);

    let safe_clause = safe_solver
        .arena
        .active_indices()
        .next()
        .expect("safe clause");
    let unsafe_clause = unsafe_solver
        .arena
        .active_indices()
        .next()
        .expect("unsafe clause");

    safe_solver.decide(lit(-3));
    unsafe_solver.decide(lit(-3));
    safe_solver.qhead = safe_solver.trail.len();
    unsafe_solver.qhead = unsafe_solver.trail.len();

    safe_solver.decide(lit(-1));
    unsafe_solver.decide(lit(-1));
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "original-clause saved-pos policy should keep safe and unsafe BCP in parity"
    );
    assert_eq!(
        safe_solver.arena.saved_pos(safe_clause),
        unsafe_solver.arena.saved_pos(unsafe_clause),
        "original-clause saved_pos should match"
    );
    assert_eq!(
        safe_solver.arena.saved_pos(safe_clause),
        3,
        "default-off advance policy should not step past replacements in original clauses"
    );
}

#[test]
fn test_unsafe_bcp_len3_replacement_then_unit() {
    // Len-3 specialized scan has a single replacement candidate at slot 2.
    // Falsify the first two literals; the first BCP pass must move the watch
    // to 3, and the second must observe the moved watch and propagate 3.
    let snap = run_bcp_comparison(3, &[vec![1, 2, 3]], &[-1, -2]);
    assert!(snap.conflict.is_none(), "no conflict expected");
    assert!(
        snap.trail.contains(&lit(3)),
        "len-3 replacement watch should later propagate literal 3"
    );
}

#[test]
fn test_unsafe_bcp_len4_replacement_scans_second_tail_then_unit() {
    // Len-4 specialized scan must skip a false slot-2 tail literal and move
    // the watch to the unassigned slot-3 tail literal.
    let snap = run_bcp_comparison(4, &[vec![1, 2, 3, 4]], &[-3, -1, -2]);
    assert!(snap.conflict.is_none(), "no conflict expected");
    assert!(
        snap.trail.contains(&lit(4)),
        "len-4 replacement watch should later propagate literal 4"
    );
}

fn assert_len5_short_scan_replacement(
    false_tail_dimacs: &[i32],
    expected_watched_dimacs: i32,
    expected_scan_steps: u64,
) {
    let clause = vec![1, 2, 3, 4, 5];
    let mut safe_solver = build_solver(5, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(5, std::slice::from_ref(&clause));
    let safe_clause = safe_solver
        .arena
        .active_indices()
        .next()
        .expect("safe clause");
    let unsafe_clause = unsafe_solver
        .arena
        .active_indices()
        .next()
        .expect("unsafe clause");

    for &dimacs in false_tail_dimacs {
        let decision = lit(-dimacs);
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        safe_solver.qhead = safe_solver.trail.len();
        unsafe_solver.qhead = unsafe_solver.trail.len();
    }
    safe_solver.set_bcp_telemetry_enabled(true);
    unsafe_solver.set_bcp_telemetry_enabled(true);

    let decision = lit(-1);
    safe_solver.decide(decision);
    unsafe_solver.decide(decision);
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "len-5 safe and unsafe BCP should match"
    );
    assert_eq!(safe_conflict, None, "replacement case should not conflict");
    assert_eq!(
        safe_solver.arena.literal(safe_clause, 0),
        lit(expected_watched_dimacs),
        "len-5 replacement should become watched in safe BCP"
    );
    assert_eq!(
        unsafe_solver.arena.literal(unsafe_clause, 0),
        lit(expected_watched_dimacs),
        "len-5 replacement should become watched in unsafe BCP"
    );
    assert_eq!(
        safe_solver.bcp_stats(),
        unsafe_solver.bcp_stats(),
        "len-5 scan telemetry should match"
    );
    assert_eq!(
        safe_solver.bcp_stats().2,
        expected_scan_steps,
        "len-5 scan should increment once for each checked tail literal"
    );
    assert_eq!(
        safe_solver.bcp_saved_pos_stats().long_scans,
        0,
        "len-5 short scan should not use saved-position telemetry"
    );
    assert_eq!(
        unsafe_solver.bcp_saved_pos_stats().long_scans,
        0,
        "unsafe len-5 short scan should not use saved-position telemetry"
    );
}

#[test]
fn test_unsafe_bcp_len5_replacement_scan_counts_by_tail_slot() {
    assert_len5_short_scan_replacement(&[], 3, 1);
    assert_len5_short_scan_replacement(&[3], 4, 2);
    assert_len5_short_scan_replacement(&[3, 4], 5, 3);
}

#[test]
fn test_unsafe_bcp_len5_replacement_scans_third_tail_matches_safe() {
    assert_len5_short_scan_replacement(&[3, 4], 5, 3);
}

#[test]
fn test_unsafe_bcp_len5_no_replacement_unit_matches_safe() {
    let clause = vec![1, 2, 3, 4, 5];
    let mut safe_solver = build_solver(5, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(5, std::slice::from_ref(&clause));

    for dimacs in [3, 4, 5] {
        let decision = lit(-dimacs);
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        safe_solver.qhead = safe_solver.trail.len();
        unsafe_solver.qhead = unsafe_solver.trail.len();
    }
    safe_solver.set_bcp_telemetry_enabled(true);
    unsafe_solver.set_bcp_telemetry_enabled(true);

    let decision = lit(-1);
    safe_solver.decide(decision);
    unsafe_solver.decide(decision);
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "len-5 no-replacement unit propagation should match"
    );
    assert_eq!(safe_conflict, None);
    assert!(safe_solver.trail.contains(&lit(2)));
    assert_eq!(
        safe_solver.bcp_stats(),
        unsafe_solver.bcp_stats(),
        "len-5 scan telemetry should match"
    );
    assert_eq!(
        safe_solver.bcp_stats().2,
        3,
        "len-5 scan should increment once for each checked tail literal"
    );
}

#[test]
fn test_unsafe_bcp_len6_8_saved_pos_wrap_matches_safe() {
    for clause_len in 6..=8 {
        let clause: Vec<i32> = (1..=clause_len as i32).collect();
        let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let safe_clause = safe_solver
            .arena
            .active_indices()
            .next()
            .expect("safe clause");
        let unsafe_clause = unsafe_solver
            .arena
            .active_indices()
            .next()
            .expect("unsafe clause");
        let saved_pos = clause_len - 2;

        for slot in saved_pos..clause_len {
            let decision = Literal::negative(Variable(slot as u32));
            safe_solver.decide(decision);
            unsafe_solver.decide(decision);
            safe_solver.qhead = safe_solver.trail.len();
            unsafe_solver.qhead = unsafe_solver.trail.len();
        }
        safe_solver.arena.set_saved_pos(safe_clause, saved_pos);
        unsafe_solver.arena.set_saved_pos(unsafe_clause, saved_pos);
        safe_solver.set_bcp_telemetry_enabled(true);
        unsafe_solver.set_bcp_telemetry_enabled(true);

        let decision = Literal::negative(Variable(0));
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
        let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

        assert_eq!(
            snapshot(&safe_solver, safe_conflict),
            snapshot(&unsafe_solver, unsafe_conflict),
            "len-{clause_len} safe and unsafe BCP should match"
        );
        assert_eq!(
            safe_solver.arena.saved_pos(safe_clause),
            unsafe_solver.arena.saved_pos(unsafe_clause),
            "len-{clause_len} saved_pos should match"
        );
        assert_eq!(
            safe_solver.arena.saved_pos(safe_clause),
            2,
            "len-{clause_len} replacement should wrap to slot 2"
        );
        assert_eq!(
            safe_solver.bcp_stats(),
            unsafe_solver.bcp_stats(),
            "len-{clause_len} scan telemetry should match"
        );
        assert_eq!(safe_solver.bcp_stats().2, 3);
        assert_eq!(
            safe_solver.bcp_saved_pos_stats(),
            unsafe_solver.bcp_saved_pos_stats(),
            "len-{clause_len} saved-position telemetry should match"
        );
    }
}

#[test]
fn test_unsafe_bcp_len6_8_false_saved_start_skip_matches_safe() {
    for clause_len in 6..=8 {
        let clause: Vec<i32> = (1..=clause_len as i32).collect();
        let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let safe_clause = safe_solver
            .arena
            .active_indices()
            .next()
            .expect("safe clause");
        let unsafe_clause = unsafe_solver
            .arena
            .active_indices()
            .next()
            .expect("unsafe clause");
        let saved_pos = clause_len - 2;
        let replacement_pos = saved_pos + 1;

        safe_solver.arena.set_learned(safe_clause, true);
        unsafe_solver.arena.set_learned(unsafe_clause, true);
        safe_solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);
        unsafe_solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);

        for slot in 2..=saved_pos {
            let decision = Literal::negative(Variable(slot as u32));
            safe_solver.decide(decision);
            unsafe_solver.decide(decision);
            safe_solver.qhead = safe_solver.trail.len();
            unsafe_solver.qhead = unsafe_solver.trail.len();
        }
        safe_solver.arena.set_saved_pos(safe_clause, saved_pos);
        unsafe_solver.arena.set_saved_pos(unsafe_clause, saved_pos);
        safe_solver.set_bcp_telemetry_enabled(true);
        unsafe_solver.set_bcp_telemetry_enabled(true);

        let decision = Literal::negative(Variable(0));
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
        let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

        assert_eq!(
            snapshot(&safe_solver, safe_conflict),
            snapshot(&unsafe_solver, unsafe_conflict),
            "len-{clause_len} false-start skip should preserve safe/unsafe parity"
        );
        assert_eq!(
            safe_solver.arena.literal(safe_clause, 0),
            unsafe_solver.arena.literal(unsafe_clause, 0),
            "len-{clause_len} watched replacement should match"
        );
        assert_eq!(
            safe_solver.arena.literal(safe_clause, 0),
            Literal::positive(Variable(replacement_pos as u32)),
            "len-{clause_len} should skip the known-false saved start and use the next tail"
        );
        assert_eq!(
            safe_solver.arena.saved_pos(safe_clause),
            unsafe_solver.arena.saved_pos(unsafe_clause),
            "len-{clause_len} saved_pos should match"
        );
        assert_eq!(safe_solver.arena.saved_pos(safe_clause), replacement_pos);
        assert_eq!(
            safe_solver.bcp_stats(),
            unsafe_solver.bcp_stats(),
            "len-{clause_len} scan telemetry should match"
        );
        assert_eq!(safe_solver.bcp_stats().2, (replacement_pos - 2) as u64);
        assert_eq!(
            safe_solver.bcp_saved_pos_stats(),
            unsafe_solver.bcp_saved_pos_stats(),
            "len-{clause_len} saved-position telemetry should match"
        );
        assert_eq!(
            safe_solver.bcp_long_scan_stats(),
            unsafe_solver.bcp_long_scan_stats(),
            "len-{clause_len} long-scan telemetry should match"
        );
    }
}

#[test]
fn test_unsafe_bcp_learned_1963_saved_start_hit_matches_safe() {
    for make_saved_start_true in [false, true] {
        let clause_len = 32;
        let saved_pos = 12;
        let clause: Vec<i32> = (1..=clause_len as i32).collect();
        let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let safe_clause = safe_solver
            .arena
            .active_indices()
            .next()
            .expect("safe clause");
        let unsafe_clause = unsafe_solver
            .arena
            .active_indices()
            .next()
            .expect("unsafe clause");

        safe_solver.arena.set_learned(safe_clause, true);
        unsafe_solver.arena.set_learned(unsafe_clause, true);
        safe_solver.set_bcp_telemetry_enabled(true);
        unsafe_solver.set_bcp_telemetry_enabled(true);
        safe_solver.set_bcp_learned_1963_false_saved_pos_reset_enabled(true);
        unsafe_solver.set_bcp_learned_1963_false_saved_pos_reset_enabled(true);

        for slot in 2..saved_pos {
            let decision = Literal::negative(Variable(slot as u32));
            safe_solver.decide(decision);
            unsafe_solver.decide(decision);
            safe_solver.qhead = safe_solver.trail.len();
            unsafe_solver.qhead = unsafe_solver.trail.len();
        }
        if make_saved_start_true {
            let decision = Literal::positive(Variable(saved_pos as u32));
            safe_solver.decide(decision);
            unsafe_solver.decide(decision);
            safe_solver.qhead = safe_solver.trail.len();
            unsafe_solver.qhead = unsafe_solver.trail.len();
        }
        safe_solver.arena.set_saved_pos(safe_clause, saved_pos);
        unsafe_solver.arena.set_saved_pos(unsafe_clause, saved_pos);

        let decision = Literal::negative(Variable(0));
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
        let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

        assert_eq!(
            snapshot(&safe_solver, safe_conflict),
            snapshot(&unsafe_solver, unsafe_conflict),
            "safe and unsafe BCP should match when the sampled 19-63 saved start is non-false"
        );
        assert_eq!(
            safe_solver.arena.saved_pos(safe_clause),
            unsafe_solver.arena.saved_pos(unsafe_clause),
            "saved_pos should match"
        );
        assert_eq!(
            safe_solver.bcp_stats(),
            unsafe_solver.bcp_stats(),
            "scan telemetry should match"
        );
        assert_eq!(safe_solver.bcp_stats().2, 1);
        assert_eq!(
            safe_solver.bcp_saved_pos_stats(),
            unsafe_solver.bcp_saved_pos_stats(),
            "saved-position telemetry should match"
        );
        assert_eq!(
            safe_solver.bcp_long_scan_stats(),
            unsafe_solver.bcp_long_scan_stats(),
            "long-scan telemetry should match"
        );
    }
}

#[test]
fn test_unsafe_bcp_learned_no_replacement_saved_pos_update_matches_safe() {
    for (clause_len, make_conflict, bucket_label, expected_update) in [
        (6usize, false, "6-8", true),
        (17usize, false, "9-17", true),
        (18usize, true, "18", true),
        (32usize, false, "19-63", true),
        (64usize, false, "64+", false),
    ] {
        let clause: Vec<i32> = (1..=clause_len as i32).collect();
        let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let safe_clause = safe_solver
            .arena
            .active_indices()
            .next()
            .expect("safe clause");
        let unsafe_clause = unsafe_solver
            .arena
            .active_indices()
            .next()
            .expect("unsafe clause");
        let saved_pos = if clause_len == 6 { 4 } else { 10 };

        safe_solver.arena.set_learned(safe_clause, true);
        unsafe_solver.arena.set_learned(unsafe_clause, true);
        safe_solver.set_bcp_learned_no_replacement_saved_pos_update_enabled(true);
        unsafe_solver.set_bcp_learned_no_replacement_saved_pos_update_enabled(true);

        let start_false_slot = if make_conflict { 1 } else { 2 };
        for slot in start_false_slot..clause_len {
            let decision = Literal::negative(Variable(slot as u32));
            safe_solver.decide(decision);
            unsafe_solver.decide(decision);
            safe_solver.qhead = safe_solver.trail.len();
            unsafe_solver.qhead = unsafe_solver.trail.len();
        }
        safe_solver.arena.set_saved_pos(safe_clause, saved_pos);
        unsafe_solver.arena.set_saved_pos(unsafe_clause, saved_pos);

        let decision = Literal::negative(Variable(0));
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
        let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

        assert_eq!(
            snapshot(&safe_solver, safe_conflict),
            snapshot(&unsafe_solver, unsafe_conflict),
            "len-{clause_len} no-replacement saved-pos update should preserve safe/unsafe parity"
        );
        assert_eq!(safe_conflict.is_some(), make_conflict);
        assert_eq!(
            safe_solver.arena.saved_pos(safe_clause),
            unsafe_solver.arena.saved_pos(unsafe_clause),
            "len-{clause_len} saved_pos should match"
        );
        assert_eq!(
            safe_solver.arena.saved_pos(safe_clause),
            if expected_update { 2 } else { saved_pos },
            "len-{clause_len} learned no-replacement update should only target 6-63 buckets"
        );
        assert_eq!(
            safe_solver.bcp_saved_pos_stats(),
            unsafe_solver.bcp_saved_pos_stats(),
            "len-{clause_len} saved-position telemetry should match"
        );
        assert_eq!(
            safe_solver.bcp_long_scan_stats(),
            unsafe_solver.bcp_long_scan_stats(),
            "len-{clause_len} long-scan telemetry should match"
        );
        let long_stats = safe_solver.bcp_long_scan_stats();
        let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, bucket_label);
        assert_eq!(
            long_stats.learned_no_replacement_saved_pos_eligible_by_len[bucket],
            u64::from(expected_update)
        );
        assert_eq!(
            long_stats.learned_no_replacement_saved_pos_writes_by_len[bucket],
            u64::from(expected_update)
        );
        assert_eq!(
            long_stats.learned_no_replacement_saved_pos_unit_by_len[bucket],
            u64::from(expected_update && !make_conflict)
        );
        assert_eq!(
            long_stats.learned_no_replacement_saved_pos_conflict_by_len[bucket],
            u64::from(expected_update && make_conflict)
        );
    }
}

#[test]
fn test_unsafe_bcp_learned_no_replacement_scan_pressure_matches_safe() {
    for (clause_len, make_conflict, bucket_label) in [
        (6usize, false, "6-8"),
        (18usize, true, "18"),
        (32usize, false, "19-63"),
        (32usize, true, "19-63"),
    ] {
        let clause: Vec<i32> = (1..=clause_len as i32).collect();
        let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let safe_clause = safe_solver
            .arena
            .active_indices()
            .next()
            .expect("safe clause");
        let unsafe_clause = unsafe_solver
            .arena
            .active_indices()
            .next()
            .expect("unsafe clause");
        let saved_pos = if clause_len == 6 { 4 } else { 10 };

        safe_solver.arena.set_learned(safe_clause, true);
        unsafe_solver.arena.set_learned(unsafe_clause, true);
        safe_solver
            .arena
            .set_lbd(safe_clause, if make_conflict { 25 } else { 5 });
        unsafe_solver
            .arena
            .set_lbd(unsafe_clause, if make_conflict { 25 } else { 5 });
        safe_solver
            .arena
            .set_used(safe_clause, if make_conflict { 0 } else { 3 });
        unsafe_solver
            .arena
            .set_used(unsafe_clause, if make_conflict { 0 } else { 3 });
        safe_solver.set_bcp_learned_no_replacement_scan_pressure_enabled(true);
        unsafe_solver.set_bcp_learned_no_replacement_scan_pressure_enabled(true);
        safe_solver.set_bcp_learned_1963_identity_profile_enabled(true);
        unsafe_solver.set_bcp_learned_1963_identity_profile_enabled(true);

        let start_false_slot = if make_conflict { 1 } else { 2 };
        for slot in start_false_slot..clause_len {
            let decision = Literal::negative(Variable(slot as u32));
            safe_solver.decide(decision);
            unsafe_solver.decide(decision);
            safe_solver.qhead = safe_solver.trail.len();
            unsafe_solver.qhead = unsafe_solver.trail.len();
        }
        safe_solver.arena.set_saved_pos(safe_clause, saved_pos);
        unsafe_solver.arena.set_saved_pos(unsafe_clause, saved_pos);

        let decision = Literal::negative(Variable(0));
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
        let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

        assert_eq!(
            snapshot(&safe_solver, safe_conflict),
            snapshot(&unsafe_solver, unsafe_conflict),
            "len-{clause_len} no-replacement pressure profile should preserve safe/unsafe parity"
        );
        assert_eq!(safe_conflict.is_some(), make_conflict);
        assert_eq!(safe_solver.arena.saved_pos(safe_clause), saved_pos);
        assert_eq!(unsafe_solver.arena.saved_pos(unsafe_clause), saved_pos);
        assert_eq!(
            safe_solver.bcp_long_scan_stats(),
            unsafe_solver.bcp_long_scan_stats(),
            "len-{clause_len} long-scan pressure telemetry should match"
        );
        assert_eq!(
            safe_solver.bcp_learned_1963_identity_stats(4),
            unsafe_solver.bcp_learned_1963_identity_stats(4),
            "len-{clause_len} learned 19-63 identity telemetry should match"
        );

        let long_stats = safe_solver.bcp_long_scan_stats();
        let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, bucket_label);
        assert!(long_stats.learned_no_replacement_scan_pressure_enabled);
        assert_eq!(
            long_stats.learned_no_replacement_scan_pressure_scans_by_len[bucket],
            1
        );
        assert_eq!(
            long_stats.learned_no_replacement_scan_pressure_steps_by_len[bucket],
            // Test builds enable the len-18 false-saved-position reset helper,
            // so the known-false saved slot is intentionally skipped.
            if clause_len == 18 {
                (clause_len - 3) as u64
            } else {
                (clause_len - 2) as u64
            }
        );
        assert_eq!(
            long_stats.learned_no_replacement_scan_pressure_start_false_by_len[bucket],
            1
        );
        assert_eq!(
            long_stats.learned_no_replacement_scan_pressure_wrapped_by_len[bucket],
            1
        );
        assert_eq!(
            long_stats.learned_no_replacement_scan_pressure_unit_by_len[bucket],
            u64::from(!make_conflict)
        );
        assert_eq!(
            long_stats.learned_no_replacement_scan_pressure_conflict_by_len[bucket],
            u64::from(make_conflict)
        );
        if clause_len == 32 {
            let identity = safe_solver.bcp_learned_1963_identity_stats(4);
            assert!(identity.enabled);
            assert_eq!(identity.exact_identity_rows, 1);
            assert_eq!(identity.total_scans, 1);
            assert_eq!(identity.total_scan_steps, (clause_len - 2) as u64);
            if make_conflict {
                assert_eq!(long_stats.learned_1963_fsw_conflict_by_lbd[4], 1);
                assert_eq!(long_stats.learned_1963_fsw_conflict_by_used[0], 1);
                assert_eq!(identity.conflict, 1);
                assert_eq!(identity.rows[0].fsw_conflict_steps, (clause_len - 2) as u64);
                assert_eq!(identity.rows[0].fsw_unit_steps, 0);
            } else {
                assert_eq!(long_stats.learned_1963_fsw_unit_by_lbd[1], 1);
                assert_eq!(long_stats.learned_1963_fsw_unit_by_used[2], 1);
                assert_eq!(identity.unit, 1);
                assert_eq!(identity.rows[0].fsw_unit_steps, (clause_len - 2) as u64);
                assert_eq!(identity.rows[0].fsw_conflict_steps, 0);
            }
            assert_eq!(identity.fsw_steps, (clause_len - 2) as u64);
            assert_eq!(identity.topk_fsw_pressure_share_ppm, 1_000_000);
            assert_eq!(identity.rows[0].fsw_steps, (clause_len - 2) as u64);
            assert_eq!(identity.fsw_rows, identity.rows);
            assert_eq!(long_stats.learned_1963_fsw_repeat_bucket_max, 1);
        }
    }
}

#[test]
fn test_unsafe_bcp_learned_1963_fsw_gent_skip_matches_safe() {
    for (
        case_name,
        expected_saved_pos,
        expected_steps,
        expected_suffix,
        expected_prefix,
        expected_unit,
        expected_conflict,
    ) in [
        ("suffix", 21usize, 1u64, 1u64, 0u64, 0u64, 0u64),
        ("prefix", 2usize, 12u64, 0u64, 1u64, 0u64, 0u64),
        ("unit", 20usize, 29u64, 0u64, 0u64, 1u64, 0u64),
        ("conflict", 20usize, 29u64, 0u64, 0u64, 0u64, 1u64),
    ] {
        let clause_len = 32usize;
        let saved_pos = 20usize;
        let clause: Vec<i32> = (1..=clause_len as i32).collect();
        let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let safe_clause = safe_solver
            .arena
            .active_indices()
            .next()
            .expect("safe clause");
        let unsafe_clause = unsafe_solver
            .arena
            .active_indices()
            .next()
            .expect("unsafe clause");

        safe_solver.arena.set_learned(safe_clause, true);
        unsafe_solver.arena.set_learned(unsafe_clause, true);
        safe_solver.set_bcp_learned_1963_fsw_gent_skip_enabled(true);
        unsafe_solver.set_bcp_learned_1963_fsw_gent_skip_enabled(true);
        safe_solver.set_bcp_telemetry_enabled(true);
        unsafe_solver.set_bcp_telemetry_enabled(true);

        let false_slots: Vec<usize> = match case_name {
            "suffix" => vec![saved_pos],
            "prefix" => (saved_pos..clause_len).collect(),
            "unit" => (2..clause_len).collect(),
            "conflict" => (1..clause_len).collect(),
            _ => unreachable!("test case"),
        };
        for slot in false_slots {
            let decision = Literal::negative(Variable(slot as u32));
            safe_solver.decide(decision);
            unsafe_solver.decide(decision);
            safe_solver.qhead = safe_solver.trail.len();
            unsafe_solver.qhead = unsafe_solver.trail.len();
        }
        safe_solver.arena.set_saved_pos(safe_clause, saved_pos);
        unsafe_solver.arena.set_saved_pos(unsafe_clause, saved_pos);

        let decision = Literal::negative(Variable(0));
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
        let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

        assert_eq!(
            snapshot(&safe_solver, safe_conflict),
            snapshot(&unsafe_solver, unsafe_conflict),
            "{case_name} Gent-order skip should preserve safe/unsafe parity"
        );
        assert_eq!(
            safe_conflict.is_some(),
            expected_conflict == 1,
            "{case_name} Gent-order skip conflict state should match fixture"
        );
        assert_eq!(
            safe_solver.arena.saved_pos(safe_clause),
            unsafe_solver.arena.saved_pos(unsafe_clause),
            "{case_name} saved_pos should match"
        );
        assert_eq!(safe_solver.arena.saved_pos(safe_clause), expected_saved_pos);
        assert_eq!(
            safe_solver.bcp_stats(),
            unsafe_solver.bcp_stats(),
            "{case_name} scan telemetry should match"
        );
        assert_eq!(safe_solver.bcp_stats().2, expected_steps);
        assert_eq!(
            safe_solver.bcp_long_scan_stats(),
            unsafe_solver.bcp_long_scan_stats(),
            "{case_name} long-scan telemetry should match"
        );

        let long_stats = safe_solver.bcp_long_scan_stats();
        assert!(long_stats.learned_1963_fsw_gent_skip_enabled);
        assert_eq!(long_stats.learned_1963_fsw_gent_skip_candidates, 1);
        assert_eq!(long_stats.learned_1963_fsw_gent_skip_applied, 1);
        assert_eq!(
            long_stats.learned_1963_fsw_gent_skip_found_unassigned_suffix,
            expected_suffix
        );
        assert_eq!(
            long_stats.learned_1963_fsw_gent_skip_found_unassigned_prefix,
            expected_prefix
        );
        assert_eq!(
            long_stats.learned_1963_fsw_gent_skip_no_replacement_unit,
            expected_unit
        );
        assert_eq!(
            long_stats.learned_1963_fsw_gent_skip_no_replacement_conflict,
            expected_conflict
        );
    }
}

#[test]
fn test_unsafe_bcp_learned_1963_blocker_cert_elision_matches_safe_minimal() {
    let clause_len = 32usize;
    let saved_pos = 20usize;
    let true_slot = 3usize;
    let clause: Vec<i32> = (1..=clause_len as i32).collect();
    let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
    let safe_clause = safe_solver
        .arena
        .active_indices()
        .next()
        .expect("safe clause");
    let unsafe_clause = unsafe_solver
        .arena
        .active_indices()
        .next()
        .expect("unsafe clause");

    safe_solver.arena.set_learned(safe_clause, true);
    unsafe_solver.arena.set_learned(unsafe_clause, true);
    safe_solver.set_bcp_telemetry_enabled(true);
    unsafe_solver.set_bcp_telemetry_enabled(true);
    enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut safe_solver);
    enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut unsafe_solver);
    stage_bcp_blocker_cert_false_start_wrap(
        &mut safe_solver,
        safe_clause,
        clause_len,
        saved_pos,
        true_slot,
    );
    stage_bcp_blocker_cert_false_start_wrap(
        &mut unsafe_solver,
        unsafe_clause,
        clause_len,
        saved_pos,
        true_slot,
    );
    seed_bcp_learned_1963_blocker_cert_repeats(
        &mut safe_solver,
        safe_clause,
        true_slot,
        Literal::positive(Variable(true_slot as u32)).0,
        BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS - 1,
    );
    seed_bcp_learned_1963_blocker_cert_repeats(
        &mut unsafe_solver,
        unsafe_clause,
        true_slot,
        Literal::positive(Variable(true_slot as u32)).0,
        BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS - 1,
    );

    let first_decision = Literal::negative(Variable(0));
    safe_solver.decide(first_decision);
    unsafe_solver.decide(first_decision);
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();
    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "first blocker-cert scan should preserve safe/unsafe parity"
    );

    safe_solver.arena.set_saved_pos(safe_clause, saved_pos);
    unsafe_solver.arena.set_saved_pos(unsafe_clause, saved_pos);
    let second_decision = Literal::negative(Variable(1));
    safe_solver.decide(second_decision);
    unsafe_solver.decide(second_decision);
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "certified blocker elision should preserve safe/unsafe parity"
    );
    assert_eq!(
        safe_solver.arena.saved_pos(safe_clause),
        unsafe_solver.arena.saved_pos(unsafe_clause),
        "blocker-cert elision saved_pos should match"
    );
    assert_eq!(safe_solver.arena.saved_pos(safe_clause), true_slot);
    assert_eq!(
        safe_solver.bcp_stats(),
        unsafe_solver.bcp_stats(),
        "blocker-cert scan telemetry should match"
    );
    assert_eq!(
        safe_solver.bcp_long_scan_stats(),
        unsafe_solver.bcp_long_scan_stats(),
        "blocker-cert long-scan telemetry should match"
    );

    let stats = safe_solver.bcp_long_scan_stats();
    assert!(stats.learned_1963_blocker_cert_elision_enabled);
    assert_eq!(
        stats.learned_1963_blocker_cert_populates,
        u64::from(BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS)
    );
    assert_eq!(stats.learned_1963_blocker_cert_candidates, 2);
    assert_eq!(stats.learned_1963_blocker_cert_repeat_rejects, 1);
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 1);
    assert_eq!(stats.learned_1963_blocker_cert_shadow_hits, 0);
    assert_eq!(stats.learned_1963_blocker_cert_stale_rejects, 0);
    assert_eq!(stats.learned_1963_blocker_cert_false_rejects, 0);
    assert_eq!(stats.learned_1963_blocker_cert_elided_suffix_slots, 16);
    assert_eq!(stats.learned_1963_blocker_cert_affected_fsw_rows, 1);
    let bucket = bcp_long_bucket_index(&stats.bucket_labels, "19-63");
    assert_eq!(stats.learned_scan_steps_by_len[bucket], 28);
}

#[test]
fn test_unsafe_bcp_learned_1963_blocker_cert_stale_reject_matches_safe() {
    let clause_len = 32usize;
    let saved_pos = 20usize;
    let true_slot = 3usize;
    let clause: Vec<i32> = (1..=clause_len as i32).collect();
    let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
    let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
    let safe_clause = safe_solver
        .arena
        .active_indices()
        .next()
        .expect("safe clause");
    let unsafe_clause = unsafe_solver
        .arena
        .active_indices()
        .next()
        .expect("unsafe clause");

    safe_solver.arena.set_learned(safe_clause, true);
    unsafe_solver.arena.set_learned(unsafe_clause, true);
    safe_solver.set_bcp_telemetry_enabled(true);
    unsafe_solver.set_bcp_telemetry_enabled(true);
    enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut safe_solver);
    enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut unsafe_solver);
    stage_bcp_blocker_cert_false_start_wrap(
        &mut safe_solver,
        safe_clause,
        clause_len,
        saved_pos,
        true_slot,
    );
    stage_bcp_blocker_cert_false_start_wrap(
        &mut unsafe_solver,
        unsafe_clause,
        clause_len,
        saved_pos,
        true_slot,
    );

    let stale_lit_raw = Literal::positive(Variable((true_slot + 1) as u32)).0;
    seed_bcp_learned_1963_blocker_cert_repeats(
        &mut safe_solver,
        safe_clause,
        true_slot,
        stale_lit_raw,
        BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS - 1,
    );
    seed_bcp_learned_1963_blocker_cert_repeats(
        &mut unsafe_solver,
        unsafe_clause,
        true_slot,
        stale_lit_raw,
        BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS - 1,
    );

    let decision = Literal::negative(Variable(0));
    safe_solver.decide(decision);
    unsafe_solver.decide(decision);
    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "stale blocker cert should preserve safe/unsafe propagation parity"
    );
    assert_eq!(
        safe_solver.bcp_stats(),
        unsafe_solver.bcp_stats(),
        "stale blocker cert scan telemetry should match"
    );
    assert_eq!(
        safe_solver.bcp_long_scan_stats(),
        unsafe_solver.bcp_long_scan_stats(),
        "stale blocker cert long-scan telemetry should match"
    );
    let stats = safe_solver.bcp_long_scan_stats();
    assert_eq!(stats.learned_1963_blocker_cert_candidates, 1);
    assert_eq!(stats.learned_1963_blocker_cert_stale_rejects, 1);
    assert_eq!(stats.learned_1963_blocker_cert_false_rejects, 0);
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 0);
    let true_lit_raw = Literal::positive(Variable(true_slot as u32)).0;
    let safe_cert = safe_solver.stats.bcp_learned_1963_blocker_cert(safe_clause);
    let unsafe_cert = unsafe_solver
        .stats
        .bcp_learned_1963_blocker_cert(unsafe_clause);
    assert_eq!(
        safe_cert.map(|cert| (
            cert.position,
            cert.literal_raw,
            cert.repeat_count,
            cert.fsw_seed
        )),
        unsafe_cert.map(|cert| (
            cert.position,
            cert.literal_raw,
            cert.repeat_count,
            cert.fsw_seed
        )),
        "stale reject fallback should leave matching refreshed cert state"
    );
    assert_eq!(
        safe_cert.map(|cert| cert.literal_raw),
        Some(true_lit_raw),
        "stale cert should be replaced by the normal true replacement observation"
    );
}

#[test]
fn test_unsafe_bcp_learned_1963_blocker_cert_false_reject_matches_safe() {
    for demote_false_reject in [false, true] {
        let clause_len = 32usize;
        let saved_pos = 20usize;
        let cert_slot = 3usize;
        let clause: Vec<i32> = (1..=clause_len as i32).collect();
        let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let safe_clause = safe_solver
            .arena
            .active_indices()
            .next()
            .expect("safe clause");
        let unsafe_clause = unsafe_solver
            .arena
            .active_indices()
            .next()
            .expect("unsafe clause");

        safe_solver.arena.set_learned(safe_clause, true);
        unsafe_solver.arena.set_learned(unsafe_clause, true);
        safe_solver.set_bcp_telemetry_enabled(true);
        unsafe_solver.set_bcp_telemetry_enabled(true);
        enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut safe_solver);
        enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut unsafe_solver);
        if demote_false_reject {
            enable_bcp_learned_1963_blocker_cert_false_reject_demote_for_test(&mut safe_solver);
            enable_bcp_learned_1963_blocker_cert_false_reject_demote_for_test(&mut unsafe_solver);
        }

        let false_slot = Literal::negative(Variable(2));
        safe_solver.decide(false_slot);
        unsafe_solver.decide(false_slot);
        safe_solver.qhead = safe_solver.trail.len();
        unsafe_solver.qhead = unsafe_solver.trail.len();
        for slot in saved_pos..clause_len {
            let decision = Literal::negative(Variable(slot as u32));
            safe_solver.decide(decision);
            unsafe_solver.decide(decision);
            safe_solver.qhead = safe_solver.trail.len();
            unsafe_solver.qhead = unsafe_solver.trail.len();
        }
        safe_solver.arena.set_saved_pos(safe_clause, saved_pos);
        unsafe_solver.arena.set_saved_pos(unsafe_clause, saved_pos);

        let cert_lit = Literal::positive(Variable(cert_slot as u32));
        seed_bcp_learned_1963_blocker_cert(&mut safe_solver, safe_clause, cert_slot, cert_lit.0);
        seed_bcp_learned_1963_blocker_cert(
            &mut unsafe_solver,
            unsafe_clause,
            cert_slot,
            cert_lit.0,
        );

        let decision = Literal::negative(Variable(0));
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
        let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

        assert_eq!(
            snapshot(&safe_solver, safe_conflict),
            snapshot(&unsafe_solver, unsafe_conflict),
            "false-reject blocker cert should preserve safe/unsafe propagation parity"
        );
        assert_eq!(
            safe_solver.bcp_stats(),
            unsafe_solver.bcp_stats(),
            "false-reject blocker cert scan telemetry should match"
        );
        assert_eq!(
            safe_solver.bcp_long_scan_stats(),
            unsafe_solver.bcp_long_scan_stats(),
            "false-reject blocker cert long-scan telemetry should match"
        );

        let stats = safe_solver.bcp_long_scan_stats();
        assert_eq!(stats.learned_1963_blocker_cert_candidates, 1);
        assert_eq!(stats.learned_1963_blocker_cert_false_rejects, 1);
        assert_eq!(
            stats.learned_1963_blocker_cert_false_reject_demotions,
            u64::from(demote_false_reject)
        );
        assert_eq!(stats.learned_1963_blocker_cert_stale_rejects, 0);
        assert_eq!(stats.learned_1963_blocker_cert_elisions, 0);
        assert_eq!(
            safe_solver
                .stats
                .bcp_learned_1963_blocker_cert(safe_clause)
                .is_none(),
            demote_false_reject,
            "demotion should control whether the false-reject cert is cleared"
        );
        assert_eq!(
            unsafe_solver
                .stats
                .bcp_learned_1963_blocker_cert(unsafe_clause)
                .is_none(),
            demote_false_reject,
            "unsafe demotion cleanup should match the safe path"
        );
    }
}

#[test]
fn test_unsafe_bcp_learned_1963_blocker_cert_mismatch_demote_matches_safe() {
    for shadow_mode in [false, true] {
        let clause_len = 32usize;
        let saved_pos = 20usize;
        let earlier_slot = 3usize;
        let cert_slot = 4usize;
        let clause: Vec<i32> = (1..=clause_len as i32).collect();
        let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
        let safe_clause = safe_solver
            .arena
            .active_indices()
            .next()
            .expect("safe clause");
        let unsafe_clause = unsafe_solver
            .arena
            .active_indices()
            .next()
            .expect("unsafe clause");

        safe_solver.arena.set_learned(safe_clause, true);
        unsafe_solver.arena.set_learned(unsafe_clause, true);
        safe_solver.set_bcp_telemetry_enabled(true);
        unsafe_solver.set_bcp_telemetry_enabled(true);
        if shadow_mode {
            enable_bcp_learned_1963_blocker_cert_shadow_for_test(&mut safe_solver);
            enable_bcp_learned_1963_blocker_cert_shadow_for_test(&mut unsafe_solver);
        } else {
            enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut safe_solver);
            enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut unsafe_solver);
        }
        enable_bcp_learned_1963_blocker_cert_false_reject_demote_for_test(&mut safe_solver);
        enable_bcp_learned_1963_blocker_cert_false_reject_demote_for_test(&mut unsafe_solver);

        let cert_lit = Literal::positive(Variable(cert_slot as u32));
        safe_solver.decide(cert_lit);
        unsafe_solver.decide(cert_lit);
        safe_solver.qhead = safe_solver.trail.len();
        unsafe_solver.qhead = unsafe_solver.trail.len();
        let false_slot = Literal::negative(Variable(2));
        safe_solver.decide(false_slot);
        unsafe_solver.decide(false_slot);
        safe_solver.qhead = safe_solver.trail.len();
        unsafe_solver.qhead = unsafe_solver.trail.len();
        for slot in saved_pos..clause_len {
            let decision = Literal::negative(Variable(slot as u32));
            safe_solver.decide(decision);
            unsafe_solver.decide(decision);
            safe_solver.qhead = safe_solver.trail.len();
            unsafe_solver.qhead = unsafe_solver.trail.len();
        }
        safe_solver.arena.set_saved_pos(safe_clause, saved_pos);
        unsafe_solver.arena.set_saved_pos(unsafe_clause, saved_pos);
        seed_bcp_learned_1963_blocker_cert(&mut safe_solver, safe_clause, cert_slot, cert_lit.0);
        seed_bcp_learned_1963_blocker_cert(
            &mut unsafe_solver,
            unsafe_clause,
            cert_slot,
            cert_lit.0,
        );

        let decision = Literal::negative(Variable(0));
        safe_solver.decide(decision);
        unsafe_solver.decide(decision);
        let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
        let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

        assert_eq!(
            snapshot(&safe_solver, safe_conflict),
            snapshot(&unsafe_solver, unsafe_conflict),
            "mismatched blocker cert should preserve safe/unsafe propagation parity"
        );
        assert_eq!(
            safe_solver.arena.saved_pos(safe_clause),
            unsafe_solver.arena.saved_pos(unsafe_clause),
            "mismatched blocker cert saved_pos should match"
        );
        assert_eq!(safe_solver.arena.saved_pos(safe_clause), earlier_slot);
        assert_eq!(
            safe_solver.bcp_stats(),
            unsafe_solver.bcp_stats(),
            "mismatched blocker cert scan telemetry should match"
        );
        assert_eq!(
            safe_solver.bcp_long_scan_stats(),
            unsafe_solver.bcp_long_scan_stats(),
            "mismatched blocker cert long-scan telemetry should match"
        );

        let stats = safe_solver.bcp_long_scan_stats();
        assert!(stats.learned_1963_blocker_cert_false_reject_demote_enabled);
        assert_eq!(stats.learned_1963_blocker_cert_candidates, 1);
        assert_eq!(
            stats.learned_1963_blocker_cert_shadow_hits,
            u64::from(shadow_mode)
        );
        assert_eq!(stats.learned_1963_blocker_cert_shadow_mismatches, 1);
        assert_eq!(stats.learned_1963_blocker_cert_mismatch_demotions, 1);
        assert_eq!(stats.learned_1963_blocker_cert_elisions, 0);
        assert_eq!(stats.learned_1963_blocker_cert_false_rejects, 0);
        assert_eq!(stats.learned_1963_blocker_cert_false_reject_demotions, 0);
        assert!(
            safe_solver
                .stats
                .bcp_learned_1963_blocker_cert(safe_clause)
                .is_none(),
            "default-off mismatch demotion should clear the stale-order cert"
        );
        assert!(
            unsafe_solver
                .stats
                .bcp_learned_1963_blocker_cert(unsafe_clause)
                .is_none(),
            "unsafe mismatch demotion should match the safe path"
        );
    }
}

#[test]
fn test_unsafe_bcp_learned_1963_used5_fsw_saved_pos_reset_matches_safe() {
    for telemetry_enabled in [false, true] {
        for make_conflict in [false, true] {
            let clause_len = 32usize;
            let clause: Vec<i32> = (1..=clause_len as i32).collect();
            let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
            let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
            let safe_clause = safe_solver
                .arena
                .active_indices()
                .next()
                .expect("safe clause");
            let unsafe_clause = unsafe_solver
                .arena
                .active_indices()
                .next()
                .expect("unsafe clause");

            safe_solver.arena.set_learned(safe_clause, true);
            unsafe_solver.arena.set_learned(unsafe_clause, true);
            safe_solver.arena.set_used(safe_clause, 5);
            unsafe_solver.arena.set_used(unsafe_clause, 5);
            safe_solver.arena.set_saved_pos(safe_clause, 10);
            unsafe_solver.arena.set_saved_pos(unsafe_clause, 10);
            safe_solver.set_bcp_telemetry_enabled(telemetry_enabled);
            unsafe_solver.set_bcp_telemetry_enabled(telemetry_enabled);
            safe_solver.set_bcp_learned_1963_used5_fsw_saved_pos_reset_enabled(true);
            unsafe_solver.set_bcp_learned_1963_used5_fsw_saved_pos_reset_enabled(true);

            let start_false_slot = if make_conflict { 1 } else { 2 };
            for slot in start_false_slot..clause_len {
                let decision = Literal::negative(Variable(slot as u32));
                safe_solver.decide(decision);
                unsafe_solver.decide(decision);
                safe_solver.qhead = safe_solver.trail.len();
                unsafe_solver.qhead = unsafe_solver.trail.len();
            }
            let decision = Literal::negative(Variable(0));
            safe_solver.decide(decision);
            unsafe_solver.decide(decision);

            let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
            let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

            assert_eq!(
                snapshot(&safe_solver, safe_conflict),
                snapshot(&unsafe_solver, unsafe_conflict),
                "used5 FSW saved-pos reset should preserve safe/unsafe parity"
            );
            assert_eq!(safe_conflict.is_some(), make_conflict);
            let expected_saved_pos = 2;
            assert_eq!(safe_solver.arena.saved_pos(safe_clause), expected_saved_pos);
            assert_eq!(
                unsafe_solver.arena.saved_pos(unsafe_clause),
                expected_saved_pos
            );
            assert_eq!(
                safe_solver.bcp_long_scan_stats(),
                unsafe_solver.bcp_long_scan_stats(),
                "used5 FSW saved-pos reset telemetry should match"
            );

            let long_stats = safe_solver.bcp_long_scan_stats();
            assert!(long_stats.learned_1963_used5_fsw_saved_pos_reset_enabled);
            let counters_collected = cfg!(debug_assertions) || telemetry_enabled;
            let expected_eligible = u64::from(counters_collected);
            assert_eq!(
                long_stats.learned_1963_used5_fsw_saved_pos_reset_eligible,
                expected_eligible
            );
            assert_eq!(
                long_stats.learned_1963_used5_fsw_saved_pos_reset_writes,
                u64::from(counters_collected)
            );
            assert_eq!(
                long_stats.learned_1963_used5_fsw_saved_pos_reset_unit,
                u64::from(counters_collected && !make_conflict)
            );
            assert_eq!(
                long_stats.learned_1963_used5_fsw_saved_pos_reset_conflict,
                u64::from(counters_collected && make_conflict)
            );
        }
    }
}

#[test]
fn test_unsafe_bcp_learned_1963_fsw_conflict_saved_pos_reset_matches_safe() {
    for telemetry_enabled in [false, true] {
        for make_conflict in [false, true] {
            let clause_len = 32usize;
            let clause: Vec<i32> = (1..=clause_len as i32).collect();
            let mut safe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
            let mut unsafe_solver = build_solver(clause_len, std::slice::from_ref(&clause));
            let safe_clause = safe_solver
                .arena
                .active_indices()
                .next()
                .expect("safe clause");
            let unsafe_clause = unsafe_solver
                .arena
                .active_indices()
                .next()
                .expect("unsafe clause");

            safe_solver.arena.set_learned(safe_clause, true);
            unsafe_solver.arena.set_learned(unsafe_clause, true);
            safe_solver.arena.set_saved_pos(safe_clause, 10);
            unsafe_solver.arena.set_saved_pos(unsafe_clause, 10);
            safe_solver.set_bcp_telemetry_enabled(telemetry_enabled);
            unsafe_solver.set_bcp_telemetry_enabled(telemetry_enabled);
            safe_solver.set_bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled(true);
            unsafe_solver.set_bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled(true);

            let start_false_slot = if make_conflict { 1 } else { 2 };
            for slot in start_false_slot..clause_len {
                let decision = Literal::negative(Variable(slot as u32));
                safe_solver.decide(decision);
                unsafe_solver.decide(decision);
                safe_solver.qhead = safe_solver.trail.len();
                unsafe_solver.qhead = unsafe_solver.trail.len();
            }
            let decision = Literal::negative(Variable(0));
            safe_solver.decide(decision);
            unsafe_solver.decide(decision);

            let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
            let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();

            assert_eq!(
                snapshot(&safe_solver, safe_conflict),
                snapshot(&unsafe_solver, unsafe_conflict),
                "FSW conflict-only reset should preserve safe/unsafe parity"
            );
            assert_eq!(safe_conflict.is_some(), make_conflict);
            let expected_saved_pos = if make_conflict { 2 } else { 10 };
            assert_eq!(safe_solver.arena.saved_pos(safe_clause), expected_saved_pos);
            assert_eq!(
                unsafe_solver.arena.saved_pos(unsafe_clause),
                expected_saved_pos
            );
            assert_eq!(
                safe_solver.bcp_long_scan_stats(),
                unsafe_solver.bcp_long_scan_stats(),
                "FSW conflict-only reset telemetry should match"
            );

            let long_stats = safe_solver.bcp_long_scan_stats();
            assert!(long_stats.learned_1963_fsw_conflict_saved_pos_reset_enabled);
            assert_eq!(
                long_stats.learned_1963_fsw_conflict_saved_pos_reset_eligible,
                u64::from(make_conflict)
            );
            assert_eq!(
                long_stats.learned_1963_fsw_conflict_saved_pos_reset_writes,
                u64::from(make_conflict)
            );
            assert_eq!(
                long_stats.learned_1963_fsw_conflict_saved_pos_reset_conflict,
                u64::from(make_conflict)
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Test 6: Mixed binary and long clauses
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_mixed() {
    // Mix of binary and long clauses.
    // Binary: (-1 v 2), (-2 v 3)
    // Long:   (-1 v -3 v -4 v 5), (-5 v -6 v 7)
    let snap = run_bcp_comparison(
        7,
        &[
            vec![-1, 2],
            vec![-2, 3],
            vec![-1, -3, -4, 5],
            vec![-5, -6, 7],
        ],
        &[1, 4, 6], // decide x0=true, x3=true, x5=true
    );
    assert!(snap.conflict.is_none(), "no conflict expected");
    // x0=T(dec), x1=T(prop), x2=T(prop), x3=T(dec), x4=T(prop), x5=T(dec), x6=T(prop)
    assert_eq!(snap.trail.len(), 7, "all 7 variables should be assigned");
}

// ---------------------------------------------------------------------------
// Test 7: Binary conflict after decision
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_binary_conflict() {
    // Formula: (-1 v 2) AND (-2 v 3) AND (-3 v -1)
    // Decide x0=true => BCP: x1=true, x2=true, then (-3 v -1) has
    // both literals false => conflict from binary propagation chain.
    let snap = run_bcp_comparison(3, &[vec![-1, 2], vec![-2, 3], vec![-3, -1]], &[1]);
    assert!(
        snap.conflict.is_some(),
        "binary conflict expected from propagation chain"
    );
}

#[test]
fn test_unsafe_bcp_binary_prefix_continues_after_first_conflict() {
    // watches[-1] has three binary entries. The first conflicts, the second
    // propagates x3, and the third conflicts again. Unsafe BCP must preserve
    // the safe path's CaDiCaL-style behavior of scanning the rest of the
    // binary prefix after the first binary conflict.
    let clauses = &[vec![-1, -2], vec![-1, 3], vec![-1, -4]];
    let mut safe_solver = build_solver(4, clauses);
    let mut unsafe_solver = build_solver(4, clauses);

    for decision in [2, 4] {
        safe_solver.decide(lit(decision));
        safe_solver.qhead = safe_solver.trail.len();
        unsafe_solver.decide(lit(decision));
        unsafe_solver.qhead = unsafe_solver.trail.len();
    }

    safe_solver.decide(lit(1));
    unsafe_solver.decide(lit(1));

    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();
    let snap = snapshot(&safe_solver, safe_conflict);
    assert_eq!(
        snap,
        snapshot(&unsafe_solver, unsafe_conflict),
        "unsafe binary-prefix conflict scan must match safe BCP"
    );
    assert!(safe_conflict.is_some(), "binary conflict expected");
    assert!(
        snap.trail.contains(&lit(3)),
        "binary watcher after first conflict should still propagate"
    );
}

#[test]
fn test_unsafe_bcp_binary_prefix_unit_then_long_suffix_matches_safe() {
    let clauses = &[vec![-1, 3], vec![-1, 2, 4]];
    let mut safe_solver = build_solver(4, clauses);
    let mut unsafe_solver = build_solver(4, clauses);
    let false_lit = lit(-1);
    let replacement_lit = lit(4);

    safe_solver.decide(lit(-2));
    safe_solver.qhead = safe_solver.trail.len();
    unsafe_solver.decide(lit(-2));
    unsafe_solver.qhead = unsafe_solver.trail.len();

    safe_solver.decide(lit(1));
    unsafe_solver.decide(lit(1));

    let safe_conflict = safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    let unsafe_conflict = unsafe_solver.propagate_bcp_unsafe_search();
    assert_eq!(
        snapshot(&safe_solver, safe_conflict),
        snapshot(&unsafe_solver, unsafe_conflict),
        "safe in-place binary-prefix scan should preserve unsafe parity before the deferred long suffix"
    );
    assert!(safe_conflict.is_none(), "no conflict expected");
    assert!(
        safe_solver.trail.contains(&lit(3)),
        "binary prefix should propagate the binary unit"
    );
    assert_eq!(
        safe_solver.watches.len_of(false_lit),
        unsafe_solver.watches.len_of(false_lit),
        "false-literal watch length should match after long-suffix replacement"
    );
    assert_eq!(safe_solver.watches.len_of(false_lit), 1);
    assert_eq!(
        safe_solver.watches.len_of(replacement_lit),
        unsafe_solver.watches.len_of(replacement_lit),
        "replacement watch length should match"
    );
    assert_eq!(safe_solver.watches.len_of(replacement_lit), 1);
}

#[test]
fn test_unsafe_bcp_binary_conflict_preserves_long_suffix() {
    let mut solver = build_solver(
        6,
        &[
            vec![-1, -2], // binary watcher in watches[-1]
            vec![-1, 3, 4],
            vec![-1, 5, 6],
        ],
    );
    let false_lit = lit(-1);
    let before_len = solver.watches.len_of(false_lit);
    assert!(
        before_len >= 3,
        "test requires binary prefix plus long suffix in watches[-1]"
    );
    assert!(
        solver.watches.is_binary(false_lit, 0),
        "first watches[-1] entry should be binary"
    );
    assert!(
        (1..before_len).all(|i| !solver.watches.is_binary(false_lit, i)),
        "remaining watches[-1] entries should be long"
    );
    let before_entries: Vec<(u32, u64)> = (0..before_len)
        .map(|i| {
            (
                solver.watches.blocker_raw(false_lit, i),
                solver.watches.clause_raw(false_lit, i),
            )
        })
        .collect();

    solver.decide(lit(2));
    solver.qhead = solver.trail.len();
    solver.decide(lit(1));

    let conflict = solver.propagate_bcp_unsafe_search();
    assert!(conflict.is_some(), "binary conflict expected");
    solver.watches.debug_assert_binary_first();

    let after_len = solver.watches.len_of(false_lit);
    let after_entries: Vec<(u32, u64)> = (0..after_len)
        .map(|i| {
            (
                solver.watches.blocker_raw(false_lit, i),
                solver.watches.clause_raw(false_lit, i),
            )
        })
        .collect();

    assert_eq!(
        before_entries, after_entries,
        "binary conflict must not truncate or rewrite unvisited long suffix"
    );
}

#[test]
fn test_unsafe_bcp_binary_conflict_skips_mixed_long_suffix_without_rewrite() {
    let mut solver = build_solver(
        6,
        &[
            vec![-1, -2],    // binary watcher in watches[-1]
            vec![-1, 3, 4],  // blocker satisfied if long suffix were scanned
            vec![-1, -5, 6], // blocker false, slow path if scanned
        ],
    );
    let false_lit = lit(-1);
    let before_len = solver.watches.len_of(false_lit);
    assert!(before_len >= 3);
    assert!(solver.watches.is_binary(false_lit, 0));
    assert!((1..before_len).all(|i| !solver.watches.is_binary(false_lit, i)));
    let before_entries: Vec<(u32, u64)> = (0..before_len)
        .map(|i| {
            (
                solver.watches.blocker_raw(false_lit, i),
                solver.watches.clause_raw(false_lit, i),
            )
        })
        .collect();

    for decision in [2, 3, 5] {
        solver.decide(lit(decision));
        solver.qhead = solver.trail.len();
    }
    solver.qhead = solver.trail.len();
    solver.decide(lit(1));

    let conflict = solver.propagate_bcp_unsafe_search();
    assert!(conflict.is_some(), "binary conflict expected");
    solver.watches.debug_assert_binary_first();

    let after_len = solver.watches.len_of(false_lit);
    let after_entries: Vec<(u32, u64)> = (0..after_len)
        .map(|i| {
            (
                solver.watches.blocker_raw(false_lit, i),
                solver.watches.clause_raw(false_lit, i),
            )
        })
        .collect();

    assert_eq!(
        before_entries, after_entries,
        "binary conflict should return before mixed long suffix telemetry/work"
    );
}

// ---------------------------------------------------------------------------
// Test 8: Long clause conflict
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_long_clause_conflict() {
    // Formula with binary chain + long clause that conflicts:
    //   A: (-1 v 2)   B: (-2 v 3)   C: (-3 v 4)   D: (-4 v -1 v -2 v -3)
    // Decide x0=T → chain: x1=T, x2=T, x3=T.
    // Long clause D: ¬x3=F, ¬x0=F, ¬x1=F, ¬x2=F → all false → conflict.
    let snap = run_bcp_comparison(
        4,
        &[
            vec![-1, 2],          // A: binary
            vec![-2, 3],          // B: binary
            vec![-3, 4],          // C: binary
            vec![-4, -1, -2, -3], // D: long clause (conflict target)
        ],
        &[1],
    );
    assert!(
        snap.conflict.is_some(),
        "long clause conflict expected from propagation chain"
    );
}

#[test]
fn test_unsafe_bcp_long_conflict_without_compaction_preserves_watch_list() {
    let mut solver = build_solver(
        5,
        &[
            vec![-1, -2, -3], // conflict when processing watches[-1]
            vec![-1, 4, 5],   // unvisited suffix entry copied unchanged
        ],
    );
    let false_lit = lit(-1);
    let before_len = solver.watches.len_of(false_lit);
    assert_eq!(
        before_len, 2,
        "test requires exactly two long watchers on watches[-1]"
    );
    assert!(
        (0..before_len).all(|i| !solver.watches.is_binary(false_lit, i)),
        "watches[-1] entries should be long"
    );
    let before_entries: Vec<(u32, u64)> = (0..before_len)
        .map(|i| {
            (
                solver.watches.blocker_raw(false_lit, i),
                solver.watches.clause_raw(false_lit, i),
            )
        })
        .collect();

    for decision in [2, 3] {
        solver.decide(lit(decision));
        solver.qhead = solver.trail.len();
    }
    solver.decide(lit(1));

    let conflict = solver.propagate_bcp_unsafe_search();
    assert!(conflict.is_some(), "long-clause conflict expected");
    solver.watches.debug_assert_binary_first();

    let after_len = solver.watches.len_of(false_lit);
    let after_entries: Vec<(u32, u64)> = (0..after_len)
        .map(|i| {
            (
                solver.watches.blocker_raw(false_lit, i),
                solver.watches.clause_raw(false_lit, i),
            )
        })
        .collect();

    assert_eq!(
        before_entries, after_entries,
        "long conflict with no compaction gap must preserve the full watch list"
    );
}

// ---------------------------------------------------------------------------
// Test 9: No propagation (all decisions, no implications)
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_no_propagation() {
    // Independent positive clauses: (1 v 2), (3 v 4)
    // Decide x0=true => satisfies first clause, no propagation.
    let snap = run_bcp_comparison(4, &[vec![1, 2], vec![3, 4]], &[1]);
    assert!(snap.conflict.is_none(), "no conflict expected");
    // Only the decision, no propagations
    assert_eq!(snap.trail.len(), 1, "only the decision should be on trail");
}

// ---------------------------------------------------------------------------
// Test 10: Multiple watch list updates
// ---------------------------------------------------------------------------

#[test]
fn test_unsafe_bcp_matches_safe_multiple_watch_updates() {
    // Several clauses all watching the same literal, forcing multiple
    // watch list operations in a single BCP pass.
    // All clauses start with (1 v ...): falsifying x0 triggers scanning all of them.
    let snap = run_bcp_comparison(
        8,
        &[vec![1, 2, 3], vec![1, 4, 5], vec![1, 6, 7], vec![1, 8, -2]],
        &[-1], // falsify x0 => all four clauses need watch updates
    );
    assert!(snap.conflict.is_none(), "no conflict expected");
}

// ---------------------------------------------------------------------------
// Test 11: Proptest — exhaustive small random formulas
// ---------------------------------------------------------------------------

mod proptest_bcp {
    use super::*;
    use proptest::prelude::*;

    /// Generate a random 3-SAT clause over `num_vars` variables.
    fn random_clause(num_vars: usize) -> impl Strategy<Value = Vec<i32>> {
        let nv = num_vars as i32;
        proptest::collection::vec(
            (1..=nv).prop_flat_map(|v| prop_oneof![Just(v), Just(-v)]),
            2..=5, // clause length 2..5
        )
    }

    /// Generate a random CNF formula.
    fn random_formula(
        num_vars: usize,
        num_clauses: std::ops::Range<usize>,
    ) -> impl Strategy<Value = Vec<Vec<i32>>> {
        proptest::collection::vec(random_clause(num_vars), num_clauses)
    }

    /// Generate a list of decisions (positive or negative literals).
    fn random_decisions(num_vars: usize, max_decisions: usize) -> impl Strategy<Value = Vec<i32>> {
        let nv = num_vars as i32;
        proptest::collection::vec(
            (1..=nv).prop_flat_map(|v| prop_oneof![Just(v), Just(-v)]),
            0..=max_decisions,
        )
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        #[test]
        fn test_unsafe_bcp_exhaustive_small_formulas(
            clauses in random_formula(6, 5..20),
            decisions in random_decisions(6, 4),
        ) {
            let num_vars = 6;

            let mut safe_solver = build_solver(num_vars, &clauses);
            let mut unsafe_solver = build_solver(num_vars, &clauses);

            // Apply decisions one at a time, running BCP after each.
            // Skip decisions for already-assigned variables.
            for &dec in &decisions {
                let decision_lit = lit(dec);
                let var_idx = decision_lit.variable().index();

                // Both solvers must agree on assignment state
                let safe_assigned = safe_solver.var_is_assigned(var_idx);
                let unsafe_assigned = unsafe_solver.var_is_assigned(var_idx);
                prop_assert_eq!(
                    safe_assigned, unsafe_assigned,
                    "assignment state diverged for var {}", var_idx
                );

                if safe_assigned {
                    continue;
                }

                // Check that qhead == trail.len() (BCP completed) before deciding
                if safe_solver.qhead != safe_solver.trail.len() {
                    break; // previous BCP found conflict, stop
                }

                safe_solver.decide(decision_lit);
                unsafe_solver.decide(decision_lit);

                let safe_conflict =
                    safe_solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
                let unsafe_conflict =
                    unsafe_solver.propagate_bcp_unsafe_search();

                let safe_snap = snapshot(&safe_solver, safe_conflict);
                let unsafe_snap = snapshot(&unsafe_solver, unsafe_conflict);

                prop_assert_eq!(
                    safe_snap.trail, unsafe_snap.trail,
                    "trail diverged after deciding {}", dec
                );
                prop_assert_eq!(
                    safe_snap.qhead, unsafe_snap.qhead,
                    "qhead diverged after deciding {}", dec
                );
                prop_assert_eq!(
                    safe_snap.conflict, unsafe_snap.conflict,
                    "conflict result diverged after deciding {}", dec
                );

                // If conflict, stop making decisions
                if safe_conflict.is_some() {
                    break;
                }
            }
        }
    }
}
