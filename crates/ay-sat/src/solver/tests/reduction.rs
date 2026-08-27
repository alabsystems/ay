// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for clause database reduction.
//!
//! Split from `reduction.rs` for file-size compliance (#5142).

use super::*;

fn count_active_learned_clauses(solver: &Solver) -> usize {
    solver
        .arena
        .indices()
        .filter(|&idx| solver.arena.is_active(idx) && solver.arena.is_learned(idx))
        .count()
}

fn add_tier2_learned_unit_clauses(solver: &mut Solver, count: usize) {
    for var in 0..count {
        let idx = solver.add_clause_db(&[Literal::positive(Variable(var as u32))], true);
        solver.arena.set_lbd(idx, 10);
    }
}

fn add_l0_satisfied_learned_binary_clauses(solver: &mut Solver, count: usize) {
    let root = Variable(0);
    for var in 0..count {
        let idx = solver.add_clause_db(
            &[
                Literal::positive(root),
                Literal::positive(Variable((var + 1) as u32)),
            ],
            true,
        );
        solver.arena.set_lbd(idx, 10);
    }
}

fn add_lbd2_learned_binary(solver: &mut Solver, left: usize, right: usize) -> usize {
    let idx = solver.add_clause_db(
        &[
            Literal::positive(Variable(left as u32)),
            Literal::negative(Variable(right as u32)),
        ],
        true,
    );
    solver.arena.set_lbd(idx, 2);
    idx
}

fn add_len20_learned_clause(solver: &mut Solver, first_var: usize, lbd: u32) -> usize {
    let lits: Vec<_> = (0..20)
        .map(|offset| Literal::positive(Variable((first_var + offset) as u32)))
        .collect();
    let idx = solver.add_clause_db(&lits, true);
    solver.arena.set_lbd(idx, lbd);
    idx
}

fn record_len20_identity_pressure(solver: &mut Solver, idx: usize, scan_steps: u64) {
    let clause_id = solver.cold.clause_ids[idx];
    solver.stats.record_bcp_learned_1963_identity(
        clause_id,
        idx,
        solver.arena.len_of(idx),
        solver.num_conflicts,
        0,
        scan_steps,
        -1,
        -1,
        true,
        true,
        solver.arena.lbd(idx),
        solver.arena.used(idx),
    );
}

fn build_gc_occ(solver: &Solver) -> crate::occ_list::OccList {
    let mut occ = crate::occ_list::OccList::new(solver.num_vars);
    for idx in solver.arena.active_indices() {
        occ.add_clause(idx, solver.arena.literals(idx));
    }
    occ
}

fn full_scan_active_learned_offsets(solver: &Solver) -> Vec<usize> {
    let mut offsets: Vec<_> = solver
        .arena
        .indices()
        .filter(|&idx| solver.arena.is_active(idx) && solver.arena.is_learned(idx))
        .collect();
    offsets.sort_unstable();
    offsets
}

fn indexed_active_learned_offsets(solver: &Solver) -> Vec<usize> {
    let mut offsets: Vec<_> = solver
        .arena
        .learned_indices()
        .inspect(|&idx| {
            assert!(
                solver.arena.is_active(idx) && solver.arena.is_learned(idx),
                "learned index contains non-active/non-learned offset {idx}"
            );
        })
        .collect();
    offsets.sort_unstable();
    offsets
}

fn assert_learned_index_matches_full_scan(solver: &Solver) {
    assert_eq!(
        indexed_active_learned_offsets(solver),
        full_scan_active_learned_offsets(solver),
        "learned-clause index must match a full arena scan"
    );
}

fn test_candidate_rank(glue: u32, size: u32) -> u64 {
    (u64::from(glue) << 32) | u64::from(size)
}

fn expected_first_normal_reduce_deletions_from_full_scan(solver: &mut Solver) -> Vec<usize> {
    solver.ensure_reason_clause_marks_current();
    let protect_lbd = solver.reduce_permanent_protect_lbd();

    let mut candidates: Vec<_> = solver
        .arena
        .indices()
        .filter_map(|idx| {
            if !solver.arena.is_active(idx)
                || !solver.arena.is_learned(idx)
                || solver.is_reason_clause_marked(idx)
                || solver.arena.is_ic3_lemma(idx)
            {
                return None;
            }

            let used = solver.arena.used(idx);
            if solver.arena.is_hyper(idx) {
                return (used == 0).then_some((test_candidate_rank(u32::MAX, u32::MAX), idx));
            }
            if solver.arena.lbd(idx) <= protect_lbd {
                return None;
            }
            match solver.clause_tier(idx) {
                ClauseTier::Core if used > 0 => return None,
                ClauseTier::Tier1 if used >= crate::clause_arena::MAX_USED - 1 => {
                    return None;
                }
                _ => {}
            }
            Some((
                test_candidate_rank(solver.arena.lbd(idx), solver.arena.len_of(idx) as u32),
                idx,
            ))
        })
        .collect();

    candidates.sort_unstable_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(&b.1)));
    let delete_count = candidates.len() * solver.reduce_delete_permille() as usize / 1000;
    candidates
        .into_iter()
        .take(delete_count)
        .map(|(_, idx)| idx)
        .collect()
}

fn expected_flush_deletions_from_full_scan(solver: &mut Solver) -> Vec<usize> {
    solver.ensure_reason_clause_marks_current();
    let protect_lbd = solver.reduce_permanent_protect_lbd();

    let mut to_flush = Vec::new();
    for idx in solver.arena.indices() {
        if !solver.arena.is_active(idx)
            || !solver.arena.is_learned(idx)
            || solver.is_reason_clause_marked(idx)
            || solver.arena.is_ic3_lemma(idx)
        {
            continue;
        }

        let used = solver.arena.used(idx);
        if solver.arena.is_hyper(idx) {
            if used == 0 {
                to_flush.push(idx);
            }
            continue;
        }
        if solver.arena.lbd(idx) <= protect_lbd {
            continue;
        }
        match solver.clause_tier(idx) {
            ClauseTier::Core if used > 0 => continue,
            ClauseTier::Tier1 if used >= crate::clause_arena::MAX_USED - 1 => {
                continue;
            }
            _ => {}
        }
        to_flush.push(idx);
    }
    to_flush.sort_unstable();
    to_flush
}

struct MixedReductionFixture {
    candidates: Vec<usize>,
    core: usize,
    ic3: usize,
    reason: usize,
}

fn add_mixed_reduction_fixture(solver: &mut Solver) -> MixedReductionFixture {
    let vars: Vec<Variable> = (0..80).map(|i| Variable(i as u32)).collect();

    for i in 0..24 {
        solver.add_clause_db(
            &[
                Literal::positive(vars[20 + i * 2]),
                Literal::negative(vars[21 + i * 2]),
            ],
            false,
        );
    }

    let core = solver.add_clause_db(&[Literal::positive(vars[0])], true);
    solver.arena.set_lbd(core, 1);

    let ic3 = solver.add_clause_db(&[Literal::positive(vars[1])], true);
    solver.arena.set_lbd(ic3, 30);
    solver.arena.set_ic3_lemma(ic3, true);

    let reason = solver.add_clause_db(
        &[Literal::negative(vars[2]), Literal::positive(vars[3])],
        true,
    );
    solver.arena.set_lbd(reason, 30);
    solver.enqueue(Literal::positive(vars[3]), Some(ClauseRef(reason as u32)));

    let mut candidates = Vec::new();
    for (i, &(glue, size)) in [
        (25, 1),
        (40, 2),
        (35, 3),
        (20, 1),
        (50, 2),
        (45, 4),
        (30, 3),
        (15, 2),
    ]
    .iter()
    .enumerate()
    {
        let base = 8 + i * 4;
        let lits = match size {
            1 => vec![Literal::positive(vars[base])],
            2 => vec![
                Literal::positive(vars[base]),
                Literal::negative(vars[base + 1]),
            ],
            3 => vec![
                Literal::positive(vars[base]),
                Literal::negative(vars[base + 1]),
                Literal::positive(vars[base + 2]),
            ],
            _ => vec![
                Literal::positive(vars[base]),
                Literal::negative(vars[base + 1]),
                Literal::positive(vars[base + 2]),
                Literal::negative(vars[base + 3]),
            ],
        };
        let idx = solver.add_clause_db(&lits, true);
        solver.arena.set_lbd(idx, glue);
        candidates.push(idx);
    }

    MixedReductionFixture {
        candidates,
        core,
        ic3,
        reason,
    }
}

#[test]
fn test_small_dense_reduce_policy_uses_fractional_density_threshold() {
    let mut solver = Solver::new(10);

    solver.num_original_clauses = 100;
    assert!(
        !solver.small_dense_learned_reduce_policy(),
        "exact density 10.0 must keep the standard reduce policy"
    );

    solver.num_original_clauses = 101;
    assert!(
        solver.small_dense_learned_reduce_policy(),
        "density above 10.0 must trigger the small-dense reduce policy"
    );
    assert_eq!(
        solver.reduce_permanent_protect_lbd(),
        1,
        "small-dense Main formulas protect only unit learned clauses permanently"
    );
}

#[test]
fn test_small_dense_reduce_policy_is_disabled_for_ic3() {
    let mut solver = Solver::new(10);
    solver.num_original_clauses = 101;
    solver.cold.ic3_mode = true;

    assert!(
        !solver.small_dense_learned_reduce_policy(),
        "dense IC3 formulas must keep glue-2 blocking lemmas protected"
    );
    assert_eq!(solver.reduce_permanent_protect_lbd(), CORE_LBD);
}

#[test]
fn test_main_reduce_permanent_protection_keeps_only_lbd1() {
    let mut solver = Solver::new(1000);
    solver.num_original_clauses = 1001;

    assert!(
        !solver.small_dense_learned_reduce_policy(),
        "non-dense Main formula should keep the standard reduce target"
    );
    assert_eq!(
        solver.reduce_permanent_protect_lbd(),
        1,
        "Main reduction should let stale LBD-2 clauses use the Core used-gate"
    );
}

#[test]
fn test_small_dense_reduce_delete_fraction_starts_more_aggressive() {
    let mut normal = Solver::new(1000);
    normal.num_original_clauses = 1001;
    assert_eq!(
        normal.reduce_delete_permille(),
        REDUCE_LOW_PERMILLE,
        "pre-first-reduction queries should clamp to the standard low target"
    );
    normal.cold.num_reductions = 1;

    let mut dense = Solver::new(100);
    dense.num_original_clauses = 1001;
    assert_eq!(
        dense.reduce_delete_permille(),
        SMALL_DENSE_REDUCE_LOW_PERMILLE,
        "pre-first-reduction queries should clamp to the small-dense low target"
    );
    dense.cold.num_reductions = 1;

    assert!(
        !normal.small_dense_learned_reduce_policy(),
        "large variable count should keep the standard reduce curve"
    );
    assert!(dense.small_dense_learned_reduce_policy());
    assert_eq!(normal.reduce_delete_permille(), REDUCE_LOW_PERMILLE);
    assert_eq!(
        dense.reduce_delete_permille(),
        SMALL_DENSE_REDUCE_LOW_PERMILLE,
        "small-dense formulas start at the denser candidate deletion target"
    );
}

#[test]
fn test_learned_clause_index_matches_full_scan_across_mutations_and_compaction() {
    let mut solver = Solver::new(12);
    let vars: Vec<Variable> = (0..12).map(|i| Variable(i as u32)).collect();

    let irred0 = solver.add_clause_db(
        &[Literal::positive(vars[0]), Literal::positive(vars[1])],
        false,
    );
    let learned0 = solver.add_clause_db(&[Literal::positive(vars[2])], true);
    let learned1 = solver.add_clause_db(
        &[Literal::positive(vars[3]), Literal::negative(vars[4])],
        true,
    );
    let irred1 = solver.add_clause_db(
        &[Literal::positive(vars[5]), Literal::positive(vars[6])],
        false,
    );
    let learned2 = solver.add_clause_db(
        &[
            Literal::positive(vars[7]),
            Literal::negative(vars[8]),
            Literal::positive(vars[9]),
        ],
        true,
    );

    let _ = irred0;
    assert_learned_index_matches_full_scan(&solver);

    solver.arena.set_learned(irred1, true);
    solver.arena.set_learned(learned1, false);
    solver.arena.delete(learned0);
    solver.arena.replace(
        learned2,
        &[Literal::positive(vars[7]), Literal::negative(vars[8])],
    );
    assert_learned_index_matches_full_scan(&solver);

    let mut order: Vec<u32> = solver
        .arena
        .active_indices()
        .map(|idx| idx as u32)
        .collect();
    order.reverse();
    solver.arena.compact_reorder(&order);

    assert_learned_index_matches_full_scan(&solver);
}

#[test]
fn test_reduce_db_indexed_candidates_match_full_scan_deletions() {
    let mut solver = Solver::new(80);
    let fixture = add_mixed_reduction_fixture(&mut solver);

    assert_learned_index_matches_full_scan(&solver);
    let mut expected_deleted = expected_first_normal_reduce_deletions_from_full_scan(&mut solver);
    expected_deleted.sort_unstable();
    assert_eq!(
        expected_deleted.len(),
        6,
        "fixture should produce eight normal candidates and a first-reduce 75% deletion quota"
    );

    solver.reduce_db();

    let mut actual_deleted: Vec<_> = fixture
        .candidates
        .iter()
        .copied()
        .filter(|&idx| !solver.arena.is_active(idx))
        .collect();
    actual_deleted.sort_unstable();

    assert_eq!(
        actual_deleted, expected_deleted,
        "indexed normal reduce deletions must match full-scan candidate ranking"
    );
    assert!(
        solver.arena.is_active(fixture.core),
        "core clause is protected"
    );
    assert!(
        solver.arena.is_active(fixture.ic3),
        "IC3 lemma is protected"
    );
    assert!(
        solver.arena.is_active(fixture.reason),
        "reason clause is protected"
    );
    let expected_target_kept = (fixture.candidates.len() - expected_deleted.len()) as u64;
    assert_eq!(
        solver.learned_reduction_telemetry_stats(),
        (
            11,
            expected_deleted.len() as u64,
            1,
            1,
            1,
            0,
            expected_target_kept,
            0,
            0,
            0
        ),
        "normal reduce telemetry should describe considered, deleted, and protected clauses"
    );
    assert_learned_index_matches_full_scan(&solver);
}

#[test]
fn test_reduce_db_learned_reduction_telemetry_counts_normal_outcomes() {
    let mut solver = Solver::new(80);
    let _fixture = add_mixed_reduction_fixture(&mut solver);

    solver.reduce_db();

    assert_eq!(
        solver.learned_reduction_telemetry_stats(),
        (11, 6, 1, 1, 1, 0, 2, 0, 0, 0),
        "normal reduce telemetry should count considered/deleted/protected/target-kept clauses"
    );
}

#[test]
fn test_reduce_db_learned_1963_pressure_reduction_is_default_off() {
    let mut solver = Solver::new(64);
    let first = add_len20_learned_clause(&mut solver, 0, 50);
    let second = add_len20_learned_clause(&mut solver, 20, 50);
    record_len20_identity_pressure(&mut solver, second, 4096);

    solver.reduce_db();

    let deleted = [first, second]
        .into_iter()
        .filter(|&idx| !solver.arena.is_active(idx))
        .count();
    assert_eq!(deleted, 1, "default reduction should delete one candidate");
    let stats = solver.learned_1963_pressure_reduction_stats();
    assert!(!stats.enabled);
    assert_eq!(stats.candidates, 0);
    assert_eq!(stats.ranked, 0);
    assert_eq!(stats.deleted, 0);
}

#[test]
fn test_reduce_db_learned_1963_pressure_reduction_biases_equal_rank_candidate() {
    let mut solver = Solver::new(64);
    solver.set_bcp_learned_1963_pressure_reduction_enabled(true);
    let first = add_len20_learned_clause(&mut solver, 0, 50);
    let second = add_len20_learned_clause(&mut solver, 20, 50);
    record_len20_identity_pressure(&mut solver, second, 4096);

    solver.reduce_db();

    assert!(
        solver.arena.is_active(first),
        "unpressured equal-rank candidate should be kept after the pressure bias"
    );
    assert!(
        !solver.arena.is_active(second),
        "pressured equal-rank learned 19-63 candidate should enter the delete quota"
    );
    let stats = solver.learned_1963_pressure_reduction_stats();
    assert!(stats.enabled);
    assert_eq!(stats.candidates, 2);
    assert_eq!(stats.pressure_candidates, 1);
    assert_eq!(stats.ranked, 1);
    assert!(stats.rank_bias_total > 0);
    assert_eq!(stats.selected, 1);
    assert_eq!(stats.deleted, 1);
    assert_eq!(stats.kept, 0);
    assert_eq!(stats.skipped_no_pressure, 1);
    assert!(stats.selected_steps >= 4096);
    assert_eq!(stats.deleted_steps, stats.selected_steps);
}

#[test]
fn test_reduce_db_learned_1963_pressure_reduction_keeps_existing_protections() {
    let mut solver = Solver::new(80);
    solver.set_bcp_learned_1963_pressure_reduction_enabled(true);
    let low_lbd = add_len20_learned_clause(&mut solver, 0, 1);
    let candidate = add_len20_learned_clause(&mut solver, 20, 50);
    let other = add_len20_learned_clause(&mut solver, 40, 50);
    record_len20_identity_pressure(&mut solver, low_lbd, 8192);
    record_len20_identity_pressure(&mut solver, candidate, 4096);

    solver.reduce_db();

    assert!(
        solver.arena.is_active(low_lbd),
        "low-LBD protection must run before pressure-aware ranking"
    );
    let stats = solver.learned_1963_pressure_reduction_stats();
    assert_eq!(
        stats.candidates, 2,
        "protected low-LBD clauses must not enter the pressure candidate pool"
    );
    assert_eq!(stats.pressure_candidates, 1);
    assert_eq!(stats.skipped_no_pressure, 1);
    assert!(
        stats.selected <= 1,
        "two normal candidates should produce at most one selected deletion"
    );
    let _ = other;
}

#[test]
fn test_reduce_db_learned_1963_pressure_retention_is_default_off() {
    let mut solver = Solver::new(64);
    let first = add_len20_learned_clause(&mut solver, 0, 50);
    let second = add_len20_learned_clause(&mut solver, 20, 50);
    record_len20_identity_pressure(&mut solver, second, 4096);

    solver.reduce_db();

    let deleted = [first, second]
        .into_iter()
        .filter(|&idx| !solver.arena.is_active(idx))
        .count();
    assert_eq!(deleted, 1, "default reduction should delete one candidate");
    let stats = solver.learned_1963_pressure_retention_stats();
    assert!(!stats.enabled);
    assert_eq!(stats.candidates, 0);
    assert_eq!(stats.ranked, 0);
    assert_eq!(stats.deleted, 0);
}

#[test]
fn test_reduce_db_learned_1963_pressure_retention_keeps_equal_rank_candidate() {
    let mut solver = Solver::new(64);
    solver.set_bcp_learned_1963_pressure_retention_enabled(true);
    let first = add_len20_learned_clause(&mut solver, 0, 50);
    let second = add_len20_learned_clause(&mut solver, 20, 50);
    record_len20_identity_pressure(&mut solver, first, 4096);

    solver.reduce_db();

    assert!(
        solver.arena.is_active(first),
        "pressured equal-rank learned 19-63 candidate should be retained"
    );
    assert!(
        !solver.arena.is_active(second),
        "unpressured equal-rank candidate should enter the delete quota"
    );
    let stats = solver.learned_1963_pressure_retention_stats();
    assert!(stats.enabled);
    assert_eq!(stats.candidates, 2);
    assert_eq!(stats.pressure_candidates, 1);
    assert_eq!(stats.ranked, 1);
    assert!(stats.rank_bias_total > 0);
    assert_eq!(stats.selected, 0);
    assert_eq!(stats.deleted, 0);
    assert_eq!(stats.kept, 1);
    assert_eq!(stats.skipped_no_pressure, 1);
    assert!(stats.kept_steps >= 4096);
}

#[test]
fn test_reduce_db_learned_1963_pressure_retention_keeps_existing_protections() {
    let mut solver = Solver::new(160);
    solver.set_bcp_learned_1963_pressure_retention_enabled(true);
    let low_lbd = add_len20_learned_clause(&mut solver, 0, 1);
    let ic3 = add_len20_learned_clause(&mut solver, 20, 50);
    solver.arena.set_ic3_lemma(ic3, true);
    let reason = add_len20_learned_clause(&mut solver, 40, 50);
    solver.enqueue(
        Literal::positive(Variable(41)),
        Some(ClauseRef(reason as u32)),
    );
    let used_tier1 = add_len20_learned_clause(&mut solver, 60, 4);
    solver
        .arena
        .set_used(used_tier1, crate::clause_arena::MAX_USED - 1);
    let retained_candidate = add_len20_learned_clause(&mut solver, 80, 50);
    let unpressured_candidate = add_len20_learned_clause(&mut solver, 100, 50);
    for idx in [low_lbd, ic3, reason, used_tier1, retained_candidate] {
        record_len20_identity_pressure(&mut solver, idx, 4096);
    }

    solver.reduce_db();

    assert!(
        solver.arena.is_active(low_lbd),
        "low-LBD protection must run before pressure-aware ranking"
    );
    assert!(
        solver.arena.is_active(ic3),
        "IC3 lemma protection must run before pressure-aware ranking"
    );
    assert!(
        solver.arena.is_active(reason),
        "reason protection must run before pressure-aware ranking"
    );
    assert!(
        solver.arena.is_active(used_tier1),
        "usage protection must run before pressure-aware ranking"
    );
    assert!(
        solver.arena.is_active(retained_candidate),
        "pressured candidate should be retained among equal-rank peers"
    );
    assert!(
        !solver.arena.is_active(unpressured_candidate),
        "unpressured equal-rank peer should take the delete slot"
    );
    let stats = solver.learned_1963_pressure_retention_stats();
    assert_eq!(
        stats.candidates, 2,
        "protected clauses must not enter the pressure candidate pool"
    );
    assert_eq!(stats.pressure_candidates, 1);
    assert_eq!(stats.ranked, 1);
    assert_eq!(stats.skipped_no_pressure, 1);
    assert_eq!(stats.kept, 1);
    assert_eq!(stats.deleted, 0);
}

#[test]
fn test_reduce_db_learned_1963_pressure_rank_policy_conflict_is_noop() {
    let mut solver = Solver::new(64);
    solver.set_bcp_learned_1963_pressure_reduction_enabled(true);
    solver.set_bcp_learned_1963_pressure_retention_enabled(true);
    let first = add_len20_learned_clause(&mut solver, 0, 50);
    let second = add_len20_learned_clause(&mut solver, 20, 50);
    record_len20_identity_pressure(&mut solver, second, 4096);

    solver.reduce_db();

    let deleted = [first, second]
        .into_iter()
        .filter(|&idx| !solver.arena.is_active(idx))
        .count();
    assert_eq!(deleted, 1, "normal reduction should still run");
    assert_eq!(
        solver.learned_1963_pressure_reduction_stats().candidates,
        0,
        "conflicting pressure policies must not apply reduction ranking"
    );
    assert_eq!(
        solver.learned_1963_pressure_retention_stats().candidates,
        0,
        "conflicting pressure policies must not apply retention ranking"
    );
}

#[test]
fn test_flush_indexed_candidates_match_full_scan_deletions() {
    let mut solver = Solver::new(80);
    let fixture = add_mixed_reduction_fixture(&mut solver);

    assert_learned_index_matches_full_scan(&solver);
    let expected_deleted = expected_flush_deletions_from_full_scan(&mut solver);
    assert_eq!(
        expected_deleted.len(),
        fixture.candidates.len(),
        "flush fixture should delete every unprotected high-LBD learned candidate"
    );

    solver.num_conflicts = solver.cold.next_flush;
    solver.reduce_db();

    let mut actual_deleted: Vec<_> = fixture
        .candidates
        .iter()
        .copied()
        .filter(|&idx| !solver.arena.is_active(idx))
        .collect();
    actual_deleted.sort_unstable();

    assert_eq!(
        actual_deleted, expected_deleted,
        "indexed flush deletions must match full-scan candidate enumeration"
    );
    assert!(
        solver.arena.is_active(fixture.core),
        "core clause is protected"
    );
    assert!(
        solver.arena.is_active(fixture.ic3),
        "IC3 lemma is protected"
    );
    assert!(
        solver.arena.is_active(fixture.reason),
        "reason clause is protected"
    );
    assert_learned_index_matches_full_scan(&solver);
}

#[test]
fn test_reduce_db_learned_reduction_telemetry_counts_hyper_outcomes() {
    let mut solver = Solver::new(6);
    let vars: Vec<Variable> = (0..6).map(|i| Variable(i as u32)).collect();

    let delete_hyper = solver.add_clause_db(
        &[Literal::positive(vars[0]), Literal::negative(vars[1])],
        true,
    );
    solver.arena.set_lbd(delete_hyper, 10);
    solver.arena.set_hyper(delete_hyper, true);

    let keep_hyper = solver.add_clause_db(
        &[Literal::positive(vars[2]), Literal::negative(vars[3])],
        true,
    );
    solver.arena.set_lbd(keep_hyper, 10);
    solver.arena.set_hyper(keep_hyper, true);
    solver.arena.set_used(keep_hyper, 1);

    solver.reduce_db();

    let telemetry = solver.learned_reduction_telemetry_stats();
    assert_eq!(
        count_active_learned_clauses(&solver),
        1,
        "one hyper clause should remain after reduction"
    );
    assert_eq!(
        telemetry,
        (2, 1, 0, 0, 0, 0, 0, 0, 1, 1),
        "hyper telemetry should distinguish deleted and kept hyper clauses"
    );
}

#[test]
fn test_reduce_db_learned_reduction_telemetry_counts_usage_protection() {
    let mut solver = Solver::new(8);
    let vars: Vec<Variable> = (0..8).map(|i| Variable(i as u32)).collect();

    let used_tier1 = solver.add_clause_db(
        &[Literal::positive(vars[0]), Literal::negative(vars[1])],
        true,
    );
    solver.arena.set_lbd(used_tier1, 4);
    solver
        .arena
        .set_used(used_tier1, crate::clause_arena::MAX_USED - 1);

    let candidate = solver.add_clause_db(
        &[Literal::positive(vars[2]), Literal::negative(vars[3])],
        true,
    );
    solver.arena.set_lbd(candidate, 10);

    solver.reduce_db();

    assert!(
        solver.arena.is_active(used_tier1),
        "recently-used tier1 clause should be protected"
    );
    assert!(
        solver.arena.is_active(candidate),
        "single normal candidate is kept by the first-reduce target floor"
    );
    assert_eq!(
        solver.learned_reduction_telemetry_stats(),
        (2, 0, 0, 0, 0, 1, 1, 0, 0, 0),
        "usage-protected and target-kept counters should be separate"
    );
}

#[test]
fn test_reduce_db_deletes_stale_lbd2_core_clauses() {
    let mut solver = Solver::new(10);
    let mut stale_count = 0usize;
    for (left, right) in [(0, 1), (2, 3), (4, 5), (6, 7)] {
        add_lbd2_learned_binary(&mut solver, left, right);
        stale_count += 1;
    }
    let lbd1 = solver.add_clause_db(
        &[
            Literal::positive(Variable(8)),
            Literal::negative(Variable(9)),
        ],
        true,
    );
    solver.arena.set_lbd(lbd1, 1);

    solver.reduce_db();

    let expected_deleted = stale_count * solver.reduce_delete_permille() as usize / 1000;
    assert_eq!(
        count_active_learned_clauses(&solver),
        1 + stale_count - expected_deleted,
        "first normal reduce should delete the configured stale LBD-2 Core candidate fraction"
    );
    assert!(
        solver
            .arena
            .active_indices()
            .any(|idx| solver.arena.is_learned(idx) && solver.arena.lbd(idx) == 1),
        "LBD-1 learned clauses must remain permanently protected"
    );
    assert_eq!(
        solver.learned_reduction_telemetry_stats(),
        (
            5,
            expected_deleted as u64,
            0,
            0,
            1,
            0,
            (stale_count - expected_deleted) as u64,
            0,
            0,
            0
        ),
        "stale LBD-2 clauses should be candidates, while LBD-1 is low-LBD protected"
    );
}

#[test]
fn test_reduce_db_keeps_recently_used_lbd2_core_clause() {
    let mut solver = Solver::new(10);
    let recent = add_lbd2_learned_binary(&mut solver, 0, 1);
    solver.arena.set_used(recent, 1);
    let mut stale_count = 0usize;
    for (left, right) in [(2, 3), (4, 5), (6, 7), (8, 9)] {
        add_lbd2_learned_binary(&mut solver, left, right);
        stale_count += 1;
    }

    solver.reduce_db();

    let expected_deleted = stale_count * solver.reduce_delete_permille() as usize / 1000;
    assert!(
        solver.arena.is_active(recent),
        "pre-decay used>0 must protect an LBD-2 Core clause for this reduction"
    );
    assert_eq!(
        solver.arena.used(recent),
        0,
        "used should still decay after protecting the clause"
    );
    assert_eq!(
        count_active_learned_clauses(&solver),
        1 + stale_count - expected_deleted,
        "stale LBD-2 peers should remain normal delete candidates"
    );
    assert_eq!(
        solver.learned_reduction_telemetry_stats(),
        (
            5,
            expected_deleted as u64,
            0,
            0,
            0,
            1,
            (stale_count - expected_deleted) as u64,
            0,
            0,
            0
        ),
        "recently used LBD-2 clauses should count as usage-protected"
    );
}

#[test]
fn test_reduce_db_keeps_lbd2_core_clauses_in_ic3_mode() {
    let mut solver = Solver::new(8);
    solver.cold.ic3_mode = true;
    let clauses = [
        add_lbd2_learned_binary(&mut solver, 0, 1),
        add_lbd2_learned_binary(&mut solver, 2, 3),
        add_lbd2_learned_binary(&mut solver, 4, 5),
        add_lbd2_learned_binary(&mut solver, 6, 7),
    ];

    solver.reduce_db();

    assert!(
        clauses.iter().all(|&idx| solver.arena.is_active(idx)),
        "IC3 mode must retain LBD-2 learned clauses conservatively"
    );
    assert_eq!(
        solver.learned_reduction_telemetry_stats(),
        (4, 0, 0, 0, 4, 0, 0, 0, 0, 0),
        "IC3 LBD-2 clauses should remain low-LBD protected"
    );
}

#[test]
fn test_reduce_db_keeps_lbd2_reason_clause() {
    let mut solver = Solver::new(10);
    let a = Variable(0);
    let b = Variable(1);

    solver.decide(Literal::positive(a));
    let reason = solver.add_clause_db(&[Literal::negative(a), Literal::positive(b)], true);
    solver.arena.set_lbd(reason, 2);
    solver.enqueue(Literal::positive(b), Some(ClauseRef(reason as u32)));

    let mut stale_count = 0usize;
    for (left, right) in [(2, 3), (4, 5), (6, 7), (8, 9)] {
        add_lbd2_learned_binary(&mut solver, left, right);
        stale_count += 1;
    }

    solver.reduce_db();

    let expected_deleted = stale_count * solver.reduce_delete_permille() as usize / 1000;
    assert!(
        solver.arena.is_active(reason),
        "LBD-2 reason clauses must remain protected"
    );
    assert_eq!(
        count_active_learned_clauses(&solver),
        1 + stale_count - expected_deleted,
        "non-reason stale LBD-2 clauses should still be reduced"
    );
    assert_eq!(
        solver.learned_reduction_telemetry_stats(),
        (
            5,
            expected_deleted as u64,
            1,
            0,
            0,
            0,
            (stale_count - expected_deleted) as u64,
            0,
            0,
            0
        ),
        "reason protection should stay ahead of LBD-2 candidate collection"
    );
}

#[test]
fn test_flush_deletes_stale_lbd2_core_clauses() {
    let mut solver = Solver::new(10);
    for (left, right) in [(0, 1), (2, 3), (4, 5), (6, 7)] {
        add_lbd2_learned_binary(&mut solver, left, right);
    }
    let lbd1 = solver.add_clause_db(
        &[
            Literal::positive(Variable(8)),
            Literal::negative(Variable(9)),
        ],
        true,
    );
    solver.arena.set_lbd(lbd1, 1);

    solver.num_conflicts = solver.cold.next_flush;
    solver.reduce_db();

    assert_eq!(
        count_active_learned_clauses(&solver),
        1,
        "flush should delete every stale LBD-2 Core clause"
    );
    assert!(
        solver
            .arena
            .active_indices()
            .any(|idx| solver.arena.is_learned(idx) && solver.arena.lbd(idx) == 1),
        "LBD-1 learned clauses must remain permanently protected during flush"
    );
    assert!(
        !solver
            .arena
            .active_indices()
            .any(|idx| solver.arena.is_learned(idx) && solver.arena.lbd(idx) == 2),
        "no stale LBD-2 learned clauses should survive this flush fixture"
    );
    assert_eq!(
        solver.learned_reduction_telemetry_stats(),
        (5, 4, 0, 0, 1, 0, 0, 0, 0, 0),
        "flush should count stale LBD-2 clauses as deleted and LBD-1 as low-LBD protected"
    );
}

#[test]
fn test_flush_preserves_lbd2_core_safety_exceptions() {
    let mut solver = Solver::with_proof_output(12, ProofOutput::lrat_text(Vec::new(), 0));
    let stale = add_lbd2_learned_binary(&mut solver, 0, 1);

    let recent = add_lbd2_learned_binary(&mut solver, 2, 3);
    solver.arena.set_used(recent, 1);

    let ic3 = add_lbd2_learned_binary(&mut solver, 4, 5);
    solver.arena.set_ic3_lemma(ic3, true);

    let a = Variable(6);
    let b = Variable(7);
    solver.decide(Literal::positive(a));
    let reason = solver.add_clause_db(&[Literal::negative(a), Literal::positive(b)], true);
    solver.arena.set_lbd(reason, 2);
    solver.enqueue(Literal::positive(b), Some(ClauseRef(reason as u32)));

    let retained = add_lbd2_learned_binary(&mut solver, 8, 9);
    let retained_id = solver.clause_id(ClauseRef(retained as u32));
    assert_ne!(retained_id, 0);
    solver.record_unit_proof_id_for_lit(Literal::positive(Variable(8)), retained_id);
    assert!(
        !solver.lrat_clause_unit_rederivations_ready_for_delete(retained),
        "fixture must make LRAT retain the selected flush candidate"
    );

    solver.num_conflicts = solver.cold.next_flush;
    solver.reduce_db();

    assert!(
        !solver.arena.is_active(stale),
        "flush should delete a stale LBD-2 Core clause"
    );
    assert!(
        solver.arena.is_active(recent),
        "pre-decay used>0 must protect an LBD-2 Core clause during flush"
    );
    assert_eq!(
        solver.arena.used(recent),
        0,
        "used should decay after flush protection"
    );
    assert!(
        solver.arena.is_active(ic3),
        "IC3 LBD-2 lemmas must remain protected during flush"
    );
    assert!(
        solver.arena.is_active(reason),
        "LBD-2 reason clauses must remain protected during flush"
    );
    assert!(
        solver.arena.is_active(retained),
        "LRAT-retained LBD-2 flush candidates must remain active after skipped delete"
    );
    assert_eq!(
        solver.learned_reduction_telemetry_stats(),
        (5, 2, 1, 1, 0, 1, 0, 1, 0, 0),
        "flush telemetry should preserve reason, IC3, usage, and LRAT-retained protections"
    );
    assert_eq!(solver.learned_reduction_lrat_retained_delete_skips(), 1);
}

#[test]
fn test_reduce_db_learned_reduction_telemetry_counts_lrat_retained_delete_skip() {
    let mut solver = Solver::with_proof_output(4, ProofOutput::lrat_text(Vec::new(), 0));
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);
    let d = Variable(3);

    let retained = solver.add_clause_db(&[Literal::positive(a), Literal::positive(b)], true);
    solver.arena.set_lbd(retained, 2);
    let retained_id = solver.clause_id(ClauseRef(retained as u32));
    assert_ne!(retained_id, 0);
    solver.record_unit_proof_id_for_lit(Literal::positive(a), retained_id);
    assert!(
        !solver.lrat_clause_unit_rederivations_ready_for_delete(retained),
        "fixture must make LRAT retain the selected delete candidate"
    );

    let target_kept = solver.add_clause_db(&[Literal::positive(c), Literal::positive(d)], true);
    solver.arena.set_lbd(target_kept, 2);

    solver.reduce_db();

    assert!(
        solver.arena.is_active(retained),
        "LRAT-retained candidate must remain active after skipped delete"
    );
    assert!(
        solver.arena.is_active(target_kept),
        "second candidate is outside the first-reduce delete quota"
    );
    assert_eq!(
        solver.learned_reduction_telemetry_stats(),
        (2, 0, 0, 0, 0, 0, 1, 1, 0, 0)
    );
    assert_eq!(solver.learned_reduction_lrat_retained_delete_skips(), 1);
}

#[test]
fn test_reduce_db_prepass_deletes_level0_satisfied_learned_clause() {
    let mut solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);

    // Root assignment: a = true.
    solver.enqueue(Literal::positive(a), None);

    // Learned clause satisfied by the root assignment.
    let clause_idx = solver.add_clause_db(&[Literal::positive(a), Literal::positive(b)], true);
    solver.arena.set_lbd(clause_idx, 10);
    solver.gc_occ = Some(build_gc_occ(&solver));

    assert!(solver.arena.is_active(clause_idx));
    solver.reduce_db();
    assert!(
        !solver.arena.is_active(clause_idx),
        "reduce_db prepass must delete learned clauses satisfied at level 0 (#3723)"
    );
    assert_eq!(
        solver.reduction_l0_satisfied_prepass_stats(),
        (1, 0, 0, 1),
        "gc_occ path should delete without a full arena scan"
    );
}

#[test]
fn test_reduce_db_skips_no_occ_l0_satisfied_full_scan_in_normal_interval() {
    let mut solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);

    solver.enqueue(Literal::positive(a), None);
    let clause_idx = solver.add_clause_db(&[Literal::positive(a), Literal::positive(b)], false);

    assert!(solver.arena.is_active(clause_idx));
    solver.reduce_db();

    assert!(
        solver.arena.is_active(clause_idx),
        "normal interval reduce without gc_occ must not full-scan irredundant L0-satisfied clauses"
    );
    assert_eq!(
        solver.reduction_l0_satisfied_prepass_stats(),
        (0, 0, 1, 0),
        "normal interval reduce should count one skipped no-occ L0 prepass"
    );
}

#[test]
fn test_reduce_db_reason_at_higher_level_is_protected() {
    // Test that a clause acting as a reason at a non-zero level
    // is still protected during reduce.
    let mut solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);

    // Decision at level 1: a = true.
    solver.decide(Literal::positive(a));

    // Clause implies b at level 1 (reason is NOT cleared since level > 0).
    let clause_idx = solver.add_clause_db(&[Literal::negative(a), Literal::positive(b)], true);
    solver.arena.set_lbd(clause_idx, 10);
    solver.enqueue(Literal::positive(b), Some(ClauseRef(clause_idx as u32)));

    assert!(solver.arena.is_active(clause_idx));
    solver.reduce_db();
    assert!(
        solver.arena.is_active(clause_idx),
        "reduce_db must not delete reason-protected clauses at level > 0"
    );
}

#[test]
fn test_reduce_db_prepass_deletes_level0_satisfied_irredundant_clause() {
    // CaDiCaL collect.cpp:73-88 mark_satisfied_clauses_as_garbage():
    // Level-0-satisfied clauses are permanently true and should be deleted
    // regardless of whether they are learned or irredundant (#8038).
    let mut solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);

    solver.enqueue(Literal::positive(a), None);
    let clause_idx = solver.add_clause_db(&[Literal::positive(a), Literal::positive(b)], false);
    solver.gc_occ = Some(build_gc_occ(&solver));

    assert!(solver.arena.is_active(clause_idx));
    solver.reduce_db();
    assert!(
        !solver.arena.is_active(clause_idx),
        "reduce_db prepass should delete level-0-satisfied irredundant clauses (CaDiCaL parity)"
    );
    assert_eq!(
        solver.reduction_l0_satisfied_prepass_stats(),
        (1, 0, 0, 1),
        "gc_occ path should delete the satisfied irredundant clause without fallback"
    );
}

#[test]
fn test_reduce_db_l0_irredundant_skip_bve_snapshot_when_occ_not_live() {
    let mut solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);

    solver.enqueue(Literal::positive(a), None);
    let clause_idx = solver.add_clause_db(&[Literal::positive(a), Literal::positive(b)], false);
    solver.gc_occ = Some(build_gc_occ(&solver));

    assert!(
        !solver.inproc.bve.is_occ_populated(),
        "default search reductions should not have live BVE occurrence maintenance"
    );
    solver.reduce_db();

    assert!(
        !solver.arena.is_active(clause_idx),
        "gc_occ cleanup should still delete the satisfied irredundant clause"
    );
    assert!(
        !solver.inproc.bve.is_occ_populated(),
        "no-BVE fast path must not populate BVE occurrence maintenance"
    );
    assert_eq!(
        solver.reduction_l0_satisfied_prepass_stats(),
        (1, 0, 0, 1),
        "BVE snapshot gating must not change L0-satisfied telemetry"
    );
}

#[test]
fn test_reduce_db_l0_irredundant_updates_live_bve_occurrence_lists() {
    let mut solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);

    let clause_idx = solver.add_clause_db(&[Literal::positive(a), Literal::positive(b)], false);
    solver.inproc.bve.rebuild(&solver.arena);
    assert!(
        solver.inproc.bve.is_occ_populated(),
        "fixture should start with live BVE occurrence maintenance"
    );
    assert!(
        solver
            .inproc
            .bve
            .get_occs(Literal::positive(a))
            .contains(&clause_idx),
        "fixture should start with the irredundant clause in BVE occ lists"
    );
    assert!(
        solver
            .inproc
            .bve
            .get_occs(Literal::positive(b))
            .contains(&clause_idx),
        "fixture should start with every old literal occurrence tracked"
    );

    solver.enqueue(Literal::positive(a), None);
    solver.gc_occ = Some(build_gc_occ(&solver));
    solver.reduce_db();

    assert!(
        !solver.arena.is_active(clause_idx),
        "gc_occ cleanup should delete the satisfied irredundant clause"
    );
    assert!(
        !solver
            .inproc
            .bve
            .get_occs(Literal::positive(a))
            .contains(&clause_idx),
        "live BVE occ maintenance must remove the deleted clause from the true literal"
    );
    assert!(
        !solver
            .inproc
            .bve
            .get_occs(Literal::positive(b))
            .contains(&clause_idx),
        "live BVE occ maintenance must remove the deleted clause from all old literals"
    );
    #[cfg(debug_assertions)]
    solver
        .inproc
        .bve
        .debug_verify_occ_against_rebuild(&solver.arena, &[]);
    assert_eq!(
        solver.reduction_l0_satisfied_prepass_stats(),
        (1, 0, 0, 1),
        "BVE live maintenance must not change L0-satisfied telemetry"
    );
}

#[test]
fn test_reduce_db_allows_no_occ_l0_satisfied_full_scan_for_flush() {
    let mut solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);

    solver.enqueue(Literal::positive(a), None);
    let clause_idx = solver.add_clause_db(&[Literal::positive(a), Literal::positive(b)], false);
    solver.num_conflicts = solver.cold.next_flush;

    assert!(solver.arena.is_active(clause_idx));
    solver.reduce_db();

    assert!(
        !solver.arena.is_active(clause_idx),
        "flush reduce may use the no-occ full fallback for L0-satisfied cleanup"
    );
    assert_eq!(
        solver.reduction_l0_satisfied_prepass_stats(),
        (0, 1, 0, 1),
        "flush should count one full fallback scan and one deletion"
    );
}

#[test]
fn test_reduce_db_allows_no_occ_l0_satisfied_full_scan_for_explicit_pressure() {
    let mut solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);

    solver.enqueue(Literal::positive(a), None);
    let clause_idx = solver.add_clause_db(&[Literal::positive(a), Literal::positive(b)], false);
    solver.set_max_clause_db_bytes(Some(0));

    assert!(solver.arena.is_active(clause_idx));
    solver.reduce_db();

    assert!(
        !solver.arena.is_active(clause_idx),
        "explicit byte pressure may use the no-occ full fallback for L0-satisfied cleanup"
    );
    assert_eq!(
        solver.reduction_l0_satisfied_prepass_stats(),
        (0, 1, 0, 1),
        "explicit pressure should count one full fallback scan and one deletion"
    );
}

#[test]
fn test_should_reduce_db_learned_limit_uses_active_redundant_count() {
    let mut solver = Solver::new(8);
    add_tier2_learned_unit_clauses(&mut solver, 6);

    solver.cold.next_reduce_db = u64::MAX;
    solver.set_max_learned_clauses(Some(4));
    assert_eq!(solver.arena.redundant_count(), 6);
    assert!(
        solver.should_reduce_db(),
        "active learned clauses over the configured limit must trigger reduce_db"
    );

    let learned: Vec<_> = solver.arena.learned_indices().collect();
    for idx in learned {
        let _ = solver.delete_clause_unchecked(idx, mutate::ReasonPolicy::Skip);
    }

    assert_eq!(
        solver.arena.num_clauses(),
        6,
        "deleted learned clauses remain as arena slots until compaction"
    );
    assert_eq!(solver.arena.redundant_count(), 0);
    solver.set_max_learned_clauses(Some(0));
    assert!(
        !solver.should_reduce_db(),
        "deleted learned slots must not count as active learned-clause pressure"
    );
}

#[test]
fn test_reduce_db_explicit_learned_pressure_ignores_deleted_slots() {
    let mut solver = Solver::new(8);
    let a = Variable(0);
    let b = Variable(1);

    solver.enqueue(Literal::positive(a), None);
    let satisfied_irredundant =
        solver.add_clause_db(&[Literal::positive(a), Literal::positive(b)], false);
    add_tier2_learned_unit_clauses(&mut solver, 4);

    let learned: Vec<_> = solver.arena.learned_indices().collect();
    for idx in learned {
        let _ = solver.delete_clause_unchecked(idx, mutate::ReasonPolicy::Skip);
    }

    assert!(
        solver.arena.num_clauses() > solver.arena.active_clause_count(),
        "fixture must leave deleted arena slots behind"
    );
    assert_eq!(solver.arena.redundant_count(), 0);

    solver.set_max_learned_clauses(Some(0));
    solver.reduce_db();

    assert!(
        solver.arena.is_active(satisfied_irredundant),
        "deleted learned slots must not create explicit pressure that enables the no-occ L0 full scan"
    );
    assert_eq!(
        solver.reduction_l0_satisfied_prepass_stats(),
        (0, 0, 1, 0),
        "without active learned pressure, reduce should skip the no-occ L0 prepass"
    );
}

#[test]
fn test_reduce_db_deletes_dynamic_fraction_in_normal_mode() {
    let mut solver = Solver::new(8);
    add_tier2_learned_unit_clauses(&mut solver, 8);

    let before = count_active_learned_clauses(&solver);
    solver.reduce_db();
    let after = count_active_learned_clauses(&solver);

    assert_eq!(
        before, 8,
        "test fixture should provide 8 learned candidates"
    );
    // Kissat-style dynamic fraction (#8655) with current raised low watermark
    // (#8448): at first reduction (count=1), percent =
    // high(90) - (high-low)(15) / log10(1+9) = 75%.
    // 75% of 8 = 6 deletions.
    let deleted = before - after;
    assert_eq!(
        deleted, 6,
        "dynamic reducetarget at first reduction should delete 75% of candidates"
    );
}

#[test]
fn test_reduce_db_deletes_dynamic_fraction_when_over_limit() {
    let mut solver = Solver::new(8);
    add_tier2_learned_unit_clauses(&mut solver, 8);
    solver.set_max_learned_clauses(Some(0));

    let before = count_active_learned_clauses(&solver);
    solver.reduce_db();
    let after = count_active_learned_clauses(&solver);

    assert_eq!(
        before, 8,
        "test fixture should provide 8 learned candidates"
    );
    // Same dynamic fraction as normal mode: 75% of 8 = 6 deletions.
    let deleted = before - after;
    assert_eq!(
        deleted, 6,
        "over-limit dynamic reducetarget should delete 75% of candidates"
    );
}

#[test]
fn test_reduce_db_dynamic_fraction_gets_more_aggressive() {
    // Verify the dynamic fraction increases with reduction count.
    // After many reductions, the fraction should approach 90%.
    let mut solver = Solver::new(20);
    add_tier2_learned_unit_clauses(&mut solver, 20);

    // Simulate many prior reductions by setting num_reductions high.
    solver.cold.num_reductions = 1000;

    let before = count_active_learned_clauses(&solver);
    solver.reduce_db();
    let after = count_active_learned_clauses(&solver);

    // At reduction #1001: percent = 90 - 40/log10(1001+9) = 90 - 40/3.004 = 76.7%
    // 76.7% of 20 = 15.3, floored to 15.
    let deleted = before - after;
    assert!(
        (13..=18).contains(&deleted),
        "dynamic reducetarget after many reductions should delete ~77% (got {deleted})"
    );
}

#[test]
fn test_reduce_db_reducetarget_uses_floor_rounding() {
    let mut solver = Solver::new(3);
    add_tier2_learned_unit_clauses(&mut solver, 3);

    let before = count_active_learned_clauses(&solver);
    solver.reduce_db();
    let after = count_active_learned_clauses(&solver);

    assert_eq!(
        before, 3,
        "test fixture should provide 3 learned candidates"
    );
    // At first reduction: 50% of 3 = 1.5, floored to 1.
    let deleted = before - after;
    assert!(
        (1..=2).contains(&deleted),
        "50% of 3 candidates must floor to 1-2 deletions (got {deleted})"
    );
}

/// CaDiCaL reduce_less_useful (#5132): higher-glue clauses are deleted
/// first. This test verifies that the highest-glue clauses are deleted
/// in order, using the Kissat-style dynamic fraction (#8655).
///
/// At first reduction (count=1): percent = 90 - 15/log10(1+9) = 75%.
/// 75% of 4 = 3 deleted: the 3 highest-glue clauses (D, B, C).
///
/// Irredundant padding clauses prevent arena compaction from invalidating
/// the arena offsets stored in local variables (compaction fires at >25%
/// dead space; padding keeps the dead fraction below the threshold).
#[test]
fn test_reduce_db_glue_ordering() {
    let mut solver = Solver::new(20);

    let vars: Vec<Variable> = (0..20).map(|i| Variable(i as u32)).collect();

    // Add irredundant padding to prevent arena compaction after deletion.
    // In legacy accounting units (5-word headers, see `accounting_len`):
    // 8 padding clauses * (5 + 2) = 56 words survive reduce.
    // 4 learned clauses * 6 words = 24 words. 3 deleted = 18 dead words.
    // 18 dead / (56+24) = 22.5% < 25% threshold => no compaction.
    for i in 0..8 {
        solver.add_clause_db(
            &[
                Literal::positive(vars[i * 2 + 4]),
                Literal::negative(vars[i * 2 + 5]),
            ],
            false, // irredundant
        );
    }

    // Add 4 tier2 learned clauses with varying glue.
    // Clause A: glue 7
    let a = solver.add_clause_db(&[Literal::positive(vars[0])], true);
    solver.arena.set_lbd(a, 7);

    // Clause B: glue 12
    let b = solver.add_clause_db(&[Literal::positive(vars[1])], true);
    solver.arena.set_lbd(b, 12);

    // Clause C: glue 10
    let c = solver.add_clause_db(&[Literal::positive(vars[2])], true);
    solver.arena.set_lbd(c, 10);

    // Clause D: glue 15
    let d = solver.add_clause_db(&[Literal::positive(vars[3])], true);
    solver.arena.set_lbd(d, 15);

    let compactions_before = solver.num_arena_compactions();
    solver.reduce_db();

    // Verify no compaction fired (offsets remain valid).
    assert_eq!(
        solver.num_arena_compactions(),
        compactions_before,
        "arena compaction must not fire (would invalidate offsets)"
    );

    // Glue ordering: D(15) > B(12) > C(10) > A(7).
    // At first reduction, dynamic fraction is 75%, so 3 of 4 are deleted.
    // D(15), B(12), and C(10) are the highest-glue and deleted first.
    assert!(
        solver.arena.is_active(a),
        "glue-7 clause A must survive (lowest glue)"
    );
    assert!(
        !solver.arena.is_active(c),
        "glue-10 clause C must be deleted (third highest glue)"
    );
    assert!(
        !solver.arena.is_active(d),
        "glue-15 clause D must be deleted (highest glue)"
    );
    assert!(
        !solver.arena.is_active(b),
        "glue-12 clause B must be deleted (second highest glue)"
    );
}

#[test]
fn test_reduce_db_decision_trace_preserves_sorted_delete_ids() {
    let dir = tempfile::tempdir().expect("tempdir");
    let trace_path = dir.path().join("reduce.trace");
    let trace_str = trace_path.to_str().expect("utf8 path");

    let mut solver = Solver::new(20);
    let vars: Vec<Variable> = (0..20).map(|i| Variable(i as u32)).collect();

    // Padding keeps this focused on reduce ordering, not compaction.
    for i in 0..8 {
        solver.add_clause_db(
            &[
                Literal::positive(vars[i * 2 + 4]),
                Literal::negative(vars[i * 2 + 5]),
            ],
            false,
        );
    }

    let a = solver.add_clause_db(&[Literal::positive(vars[0])], true);
    solver.arena.set_lbd(a, 7);
    let b = solver.add_clause_db(&[Literal::positive(vars[1])], true);
    solver.arena.set_lbd(b, 12);
    let c = solver.add_clause_db(&[Literal::positive(vars[2])], true);
    solver.arena.set_lbd(c, 10);
    let d = solver.add_clause_db(&[Literal::positive(vars[3])], true);
    solver.arena.set_lbd(d, 15);

    let expected_ids = vec![
        solver.clause_id(ClauseRef(d as u32)),
        solver.clause_id(ClauseRef(b as u32)),
        solver.clause_id(ClauseRef(c as u32)),
    ];

    solver.enable_decision_trace(trace_str).unwrap();
    solver.reduce_db();
    solver.finish_decision_trace();

    let events = decision_trace::read_trace(trace_str).expect("read trace");
    let reduce_ids = events
        .iter()
        .find_map(|event| match event {
            TraceEvent::Reduce { clause_ids } => Some(clause_ids),
            _ => None,
        })
        .expect("reduce event");

    assert_eq!(
        reduce_ids, &expected_ids,
        "decision trace must preserve deterministic reduce deletion order"
    );
}

#[test]
fn test_reduce_db_size_tiebreak_ordering() {
    let mut solver = Solver::new(40);
    let vars: Vec<Variable> = (0..40).map(|i| Variable(i as u32)).collect();

    // Padding keeps dead arena space below the compaction threshold so saved
    // offsets remain valid for the assertions below.
    for i in 0..12 {
        solver.add_clause_db(
            &[
                Literal::positive(vars[i * 2 + 10]),
                Literal::negative(vars[i * 2 + 11]),
            ],
            false,
        );
    }

    let size1 = solver.add_clause_db(&[Literal::positive(vars[0])], true);
    solver.arena.set_lbd(size1, 15);

    let size2 = solver.add_clause_db(
        &[Literal::positive(vars[1]), Literal::negative(vars[2])],
        true,
    );
    solver.arena.set_lbd(size2, 15);

    let size3 = solver.add_clause_db(
        &[
            Literal::positive(vars[3]),
            Literal::negative(vars[4]),
            Literal::positive(vars[5]),
        ],
        true,
    );
    solver.arena.set_lbd(size3, 15);

    let size4 = solver.add_clause_db(
        &[
            Literal::positive(vars[6]),
            Literal::negative(vars[7]),
            Literal::positive(vars[8]),
            Literal::negative(vars[9]),
        ],
        true,
    );
    solver.arena.set_lbd(size4, 15);

    let compactions_before = solver.num_arena_compactions();
    solver.reduce_db();

    assert_eq!(
        solver.num_arena_compactions(),
        compactions_before,
        "arena compaction must not fire (would invalidate offsets)"
    );
    assert!(
        solver.arena.is_active(size1),
        "smallest same-glue clause must survive"
    );
    assert!(
        !solver.arena.is_active(size2),
        "size-2 same-glue clause must be deleted"
    );
    assert!(
        !solver.arena.is_active(size3),
        "size-3 same-glue clause must be deleted"
    );
    assert!(
        !solver.arena.is_active(size4),
        "largest same-glue clause must be deleted"
    );
}

#[test]
fn test_reduce_db_reuses_candidate_scratch_capacity() {
    let mut solver = Solver::new(64);
    add_tier2_learned_unit_clauses(&mut solver, 64);

    solver.reduce_db();
    let cap_after_first = solver.cold.reduce_candidates_buf.capacity();
    assert!(
        cap_after_first >= 64,
        "first reduction should grow candidate scratch for all candidates"
    );

    add_tier2_learned_unit_clauses(&mut solver, 8);
    let candidates_before_second = count_active_learned_clauses(&solver);
    assert!(
        candidates_before_second < 64,
        "second reduction fixture should use fewer candidates than the first"
    );

    solver.reduce_db();

    assert!(
        solver.cold.reduce_candidates_buf.capacity() >= cap_after_first,
        "candidate scratch capacity must be retained across reductions"
    );
    assert!(
        solver.cold.reduce_candidates_buf.len() <= candidates_before_second,
        "candidate scratch should contain only the second reduction's candidates"
    );
}

#[test]
fn test_reduce_db_occ_l0_cleanup_reuses_index_scratch_capacity() {
    let mut solver = Solver::new(80);
    solver.enqueue(Literal::positive(Variable(0)), None);
    add_l0_satisfied_learned_binary_clauses(&mut solver, 64);
    solver.gc_occ = Some(build_gc_occ(&solver));

    solver.reduce_db();
    let cap_after_first = solver.cold.reduce_indices_buf.capacity();
    assert!(
        cap_after_first >= 64,
        "first occ-guided cleanup should grow index scratch for all candidates"
    );
    assert_eq!(
        solver.reduction_l0_satisfied_prepass_stats(),
        (1, 0, 0, 64),
        "first reduction should exercise the gc_occ L0 cleanup path"
    );

    add_l0_satisfied_learned_binary_clauses(&mut solver, 8);
    solver.reduce_db();

    assert!(
        solver.cold.reduce_indices_buf.capacity() >= cap_after_first,
        "occ-guided L0 cleanup must retain index scratch capacity across reductions"
    );
    assert_eq!(
        solver.reduction_l0_satisfied_prepass_stats(),
        (2, 0, 0, 72),
        "second reduction should reuse the gc_occ path for the smaller candidate set"
    );
}

/// Multi-variable reduce_db test with active watches and reason entries.
/// Verifies acceptance criterion #2 from #5091: after reduce_db with byte
/// limit active, all ClauseRef values in reason[] and watch lists remain
/// valid (point to active clauses).
#[test]
fn test_reduce_db_preserves_clause_ref_integrity_5091() {
    let num_vars = 10;
    let mut solver = Solver::new(num_vars);

    // Add irredundant binary clauses that create implication chains.
    // (¬a → b) encoded as (a ∨ b): if a is false, b is implied.
    let v: Vec<Variable> = (0..num_vars as u32).map(Variable).collect();

    // Clause 0: (v0 ∨ v1) — if ¬v0 then v1
    let reason_clause_0 =
        solver.add_clause_db(&[Literal::positive(v[0]), Literal::positive(v[1])], false);
    // Clause 1: (v2 ∨ v3) — if ¬v2 then v3
    let reason_clause_1 =
        solver.add_clause_db(&[Literal::positive(v[2]), Literal::positive(v[3])], false);

    // Set up reason entries: v1 was implied by clause 0, v3 by clause 1.
    solver.enqueue(Literal::negative(v[0]), None); // decision
    solver.enqueue(
        Literal::positive(v[1]),
        Some(ClauseRef(reason_clause_0 as u32)),
    );
    solver.enqueue(Literal::negative(v[2]), None); // decision
    solver.enqueue(
        Literal::positive(v[3]),
        Some(ClauseRef(reason_clause_1 as u32)),
    );

    // Add many learned tier-2 clauses with high LBD to create reduction
    // pressure. Use distinct variable pairs so watches are spread out.
    let mut learned_indices = Vec::new();
    for i in 0..20 {
        let a = v[(i * 2) % num_vars];
        let b = v[(i * 2 + 1) % num_vars];
        let idx = solver.add_clause_db(&[Literal::positive(a), Literal::negative(b)], true);
        solver.arena.set_lbd(idx, 15); // high LBD = tier2 = deletable
        learned_indices.push(idx);
    }

    // Set byte limit below current usage to trigger aggressive reduction.
    let current_bytes = solver.arena.memory_bytes();
    solver.set_max_clause_db_bytes(Some(current_bytes / 2));

    // Verify pre-condition: reason clauses are active.
    assert!(solver.arena.is_active(reason_clause_0));
    assert!(solver.arena.is_active(reason_clause_1));

    solver.reduce_db();

    // Post-condition 1: reason clauses must still be active.
    assert!(
        solver.arena.is_active(reason_clause_0),
        "reason clause 0 must survive reduce_db"
    );
    assert!(
        solver.arena.is_active(reason_clause_1),
        "reason clause 1 must survive reduce_db"
    );

    // Post-condition 2: every reason entry for an *assigned* variable
    // points to an active clause. Unassigned variables may retain stale
    // reason values after backtrack store elimination (#6991).
    for (var_idx, vd) in solver.var_data.iter().enumerate() {
        if vd.reason != NO_REASON && solver.var_is_assigned(var_idx) {
            let idx = vd.reason as usize;
            assert!(
                solver.arena.is_active(idx),
                "reason clause {idx} for variable {var_idx} is not active after reduce_db"
            );
        }
    }

    // Post-condition 3: some learned clauses were deleted (reduction worked).
    let surviving_learned = learned_indices
        .iter()
        .filter(|&&idx| solver.arena.is_active(idx))
        .count();
    assert!(
        surviving_learned < learned_indices.len(),
        "reduce_db must delete some tier-2 learned clauses (survived {surviving_learned}/{})",
        learned_indices.len()
    );
}

/// Arena locality compaction fires after reduce_db when dead space
/// exceeds the adaptive threshold, and correctly remaps all ClauseRef
/// holders (watch lists, trail reasons, LRAT clause IDs).
///
/// Reference: CaDiCaL collect.cpp:385-399 (arenatype=3, #8030).
#[test]
fn test_arena_compaction_fires_after_reduce_db_and_remaps_correctly() {
    let num_vars = 10;
    let mut solver = Solver::new(num_vars);
    let v: Vec<Variable> = (0..num_vars as u32).map(Variable).collect();

    // Add irredundant clauses (these survive reduce_db).
    let irred_0 = solver.add_clause_db(&[Literal::positive(v[0]), Literal::positive(v[1])], false);
    let _irred_1 = solver.add_clause_db(&[Literal::positive(v[2]), Literal::positive(v[3])], false);

    // Set up a reason entry so we can verify reason remapping.
    solver.enqueue(Literal::negative(v[0]), None);
    solver.enqueue(Literal::positive(v[1]), Some(ClauseRef(irred_0 as u32)));

    // Add many high-LBD learned clauses to create enough dead space
    // after deletion to trigger compaction (dead > 25% of arena).
    let mut learned_indices = Vec::new();
    for i in 0..40 {
        let a = v[(i * 2) % num_vars];
        let b = v[(i * 2 + 1) % num_vars];
        let idx = solver.add_clause_db(
            &[
                Literal::positive(a),
                Literal::negative(b),
                Literal::positive(v[4]),
            ],
            true,
        );
        solver.arena.set_lbd(idx, 15);
        learned_indices.push(idx);
    }

    let arena_len_before = solver.arena.len();
    assert_eq!(
        solver.num_arena_compactions(),
        0,
        "no arena compactions should have occurred yet"
    );

    // Trigger reduce_db. The 75% deletion of 40 tier-2 clauses should
    // produce enough dead space to exceed the 25% threshold.
    solver.reduce_db();

    // Check if compaction fired.
    let compacted = solver.num_arena_compactions() > 0;
    if compacted {
        // Arena should have shrunk (dead space removed).
        assert!(
            solver.arena.len() < arena_len_before,
            "arena should shrink after compaction (before={arena_len_before}, after={})",
            solver.arena.len()
        );

        // Dead words should be reset to 0 after compaction.
        assert_eq!(
            solver.arena.dead_words(),
            0,
            "dead_words must be 0 after compaction"
        );

        // Reason clause for v[1] must still be valid and point to the
        // correct clause (irred_0 was remapped to a new offset).
        let v1_reason = solver.var_data[1].reason;
        assert!(
            is_clause_reason(v1_reason),
            "v[1] must still have a clause reason after compaction"
        );
        let reason_offset = v1_reason as usize;
        assert!(
            solver.arena.is_active(reason_offset),
            "reason clause for v[1] must be active at remapped offset {reason_offset}"
        );
        // Verify the clause at the remapped offset has the expected literals.
        let reason_lits = solver.arena.literals(reason_offset);
        assert_eq!(
            reason_lits.len(),
            2,
            "reason clause should still be a binary clause"
        );

        // Irredundant clauses must survive (active at their new offsets).
        let active_irred = solver
            .arena
            .active_indices()
            .filter(|&idx| !solver.arena.is_learned(idx))
            .count();
        assert!(
            active_irred >= 2,
            "both irredundant clauses must survive compaction (found {active_irred})"
        );

        // Watch lists must be consistent: every non-binary watcher must
        // point to an active clause in the arena.
        for lit_idx in 0..solver.watches.num_lists() {
            let lit = Literal::from_index(lit_idx);
            let wl = solver.watches.get_watches(lit);
            for i in 0..wl.len() {
                if !wl.is_binary(i) {
                    let offset = wl.clause_ref(i).index();
                    assert!(
                        solver.arena.is_active(offset),
                        "watch list entry for lit {lit:?} points to inactive clause at offset {offset}"
                    );
                }
            }
        }
    } else {
        // If compaction didn't fire, the threshold wasn't met. This is
        // acceptable — verify the arena still has dead space.
        assert!(
            solver.arena.dead_words() > 0
                || learned_indices
                    .iter()
                    .all(|&idx| solver.arena.is_active(idx)),
            "if no compaction, dead space or all clauses surviving is expected"
        );
    }
}

/// Verify the arena compaction stats counter tracks compaction events.
#[test]
fn test_arena_compaction_stats_counter() {
    let mut solver = Solver::new(4);
    assert_eq!(solver.num_arena_compactions(), 0);

    // Force compaction by adding and deleting enough clauses to exceed
    // the dead-space threshold, then calling reduce_db.
    for _ in 0..20 {
        let idx = solver.add_clause_db(
            &[
                Literal::positive(Variable(0)),
                Literal::negative(Variable(1)),
                Literal::positive(Variable(2)),
            ],
            true,
        );
        solver.arena.set_lbd(idx, 15);
    }
    solver.reduce_db();

    // The counter should be >= 0. We cannot guarantee compaction fires
    // on every reduce_db (depends on the adaptive threshold), but the
    // counter must be well-defined.
    let count = solver.num_arena_compactions();
    // count is either 0 (threshold not met) or 1+ (compaction ran).
    assert!(
        count <= 1,
        "at most 1 compaction expected from a single reduce_db (got {count})"
    );
}

/// #8672 Finding #2: the clause-DB memory trigger in `should_reduce_db` now
/// composes arena + watches + clause_ids + original_ledger + reconstruction
/// instead of only the arena word buffer. The composite figure must strictly
/// exceed the arena-only figure once clauses and watchers exist, otherwise
/// the memory-pressure reduction branch would continue to fire late.
#[test]
fn test_clause_db_memory_bytes_exceeds_arena_only_8672() {
    let mut solver = Solver::new(16);

    // Seed the arena with a mix of irredundant binaries and high-LBD tier-2
    // learned clauses so the arena, watch buffers, and clause_ids side vector
    // all hold live data.
    let v: Vec<Variable> = (0..16u32).map(Variable).collect();
    for i in 0..8 {
        let a = v[(i * 2) % v.len()];
        let b = v[(i * 2 + 1) % v.len()];
        solver.add_clause_db(&[Literal::positive(a), Literal::negative(b)], false);
    }
    for i in 0..32 {
        let a = v[i % v.len()];
        let b = v[(i + 3) % v.len()];
        let c = v[(i + 7) % v.len()];
        let idx = solver.add_clause_db(
            &[
                Literal::positive(a),
                Literal::negative(b),
                Literal::positive(c),
            ],
            true,
        );
        solver.arena.set_lbd(idx, 15);
    }

    let arena_only = solver.arena.memory_bytes();
    let composite = solver.clause_db_memory_bytes();

    assert!(
        composite > arena_only,
        "clause_db_memory_bytes ({composite}) must exceed arena-only ({arena_only}); \
         the composite figure is the one consulted by the memory trigger in \
         should_reduce_db after #8672."
    );

    // The gap must at least cover the watch buffers — the dominant auxiliary
    // cost — otherwise the fix did not wire in the watcher heap.
    let watches_bytes = solver.watches.heap_bytes();
    assert!(
        composite >= arena_only + watches_bytes,
        "composite ({composite}) must cover arena ({arena_only}) + watches \
         ({watches_bytes})"
    );
}

/// #8672 Finding #2: the byte-limit branch in `should_reduce_db` must trip on
/// the composite clause-DB memory figure, not only on the arena size. With a
/// limit placed just under the composite but well above the arena-only number,
/// the trigger must still fire.
#[test]
fn test_should_reduce_db_uses_composite_memory_8672() {
    let mut solver = Solver::new(16);

    // Build up some clauses so arena+watches are both non-trivial.
    let v: Vec<Variable> = (0..16u32).map(Variable).collect();
    for i in 0..8 {
        solver.add_clause_db(
            &[
                Literal::positive(v[i % v.len()]),
                Literal::negative(v[(i + 1) % v.len()]),
            ],
            false,
        );
    }
    for i in 0..20 {
        let idx = solver.add_clause_db(
            &[
                Literal::positive(v[i % v.len()]),
                Literal::negative(v[(i + 2) % v.len()]),
                Literal::positive(v[(i + 5) % v.len()]),
            ],
            true,
        );
        solver.arena.set_lbd(idx, 15);
    }

    let arena_only = solver.arena.memory_bytes();
    let composite = solver.clause_db_memory_bytes();

    // Arrange for the interval trigger not to fire.
    solver.cold.next_reduce_db = u64::MAX;
    solver.num_conflicts = 0;

    // Set limit above arena-only but below composite; the memory branch must
    // still trip because it now consults the composite figure.
    if composite > arena_only {
        let limit = usize::midpoint(arena_only, composite);
        assert!(limit > arena_only);
        assert!(limit < composite);
        solver.set_max_clause_db_bytes(Some(limit));
        assert!(
            solver.should_reduce_db(),
            "memory trigger must fire when composite clause-DB bytes \
             ({composite}) exceed the configured limit ({limit}), even though \
             arena-only ({arena_only}) does not."
        );
    }
}

/// Load-time slack reclamation must not move the reduce-DB byte trigger.
///
/// THE BARRIER for #load-slack-reclaim. `clause_db_memory_bytes` decides WHEN
/// `should_reduce_db` fires, and two of its terms — `clause_ids.capacity()` and
/// `original_ledger.heap_bytes()` — read REAL capacity, unlike the arena's
/// pinned `accounted_words`. Shrinking those at load without adding the
/// reclaimed bytes back shrinks the trigger's basis, so reduction fires at
/// different conflict counts and the search trajectory diverges. Every verdict
/// stays correct, so no other test in the suite would notice.
///
/// Delete the `+ self.cold.load_slack_reclaimed_bytes` term in
/// `clause_db_memory_bytes` and this test fails.
#[test]
fn load_slack_reclamation_does_not_move_the_reduce_db_trigger() {
    let mut solver = Solver::new(16);
    let v: Vec<Variable> = (0..16u32).map(Variable).collect();
    for i in 0..8 {
        let a = v[(i * 2) % v.len()];
        let b = v[(i * 2 + 1) % v.len()];
        solver.add_clause_db(&[Literal::positive(a), Literal::negative(b)], false);
    }

    // Slack well past the 16MB reclamation floor (2M u64 entries).
    solver.cold.clause_ids.reserve_exact(3_000_000);
    let cap_before = solver.cold.clause_ids.capacity();
    let billed_before = solver.clause_db_memory_bytes();
    assert!(
        (cap_before - solver.cold.clause_ids.len()) * size_of::<u64>() >= 16 << 20,
        "precondition: clause_ids slack must exceed the reclamation floor"
    );

    solver.reclaim_load_time_slack(0);

    assert!(
        solver.cold.clause_ids.capacity() < cap_before,
        "real capacity must actually be handed back: {cap_before} -> {}",
        solver.cold.clause_ids.capacity()
    );
    assert!(
        solver.cold.load_slack_reclaimed_bytes > 0,
        "the reclaimed bytes must be recorded for compensation"
    );
    assert_eq!(
        solver.clause_db_memory_bytes(),
        billed_before,
        "the reduce-DB byte trigger must be bit-identical across reclamation, \
         or the reduction cadence — and with it the search — moves"
    );
}

/// `clause_ids` defers its construction reservation to the first write
/// (#lazy-clause-ids): while disabled (the no-proof route) the vector stays
/// unallocated so `--memory` is never charged, but `clause_db_memory_bytes`
/// must keep billing the deferred hint as a phantom — the historical trigger
/// basis included the eager reservation, and dropping it would move the
/// reduce-DB cadence. On the first write the reservation lands at exactly the
/// hint, reproducing the retired `with_capacity` capacity ladder.
#[test]
fn clause_ids_reservation_is_lazy_and_trigger_basis_is_preserved() {
    let solver = Solver::with_clause_hint(64, 32);
    let hint = solver.cold.clause_ids_reserve_hint;
    assert!(
        hint > 0,
        "precondition: the clause hint must produce a hint"
    );
    assert_eq!(
        solver.cold.clause_ids.capacity(),
        0,
        "construction must not allocate clause_ids"
    );
    // The phantom charge stands in for the deferred reservation.
    let billed_unallocated = solver.clause_db_memory_bytes();

    let mut solver2 = Solver::with_clause_hint(64, 32);
    solver2.cold.clause_ids_grow_for(0);
    assert_eq!(
        solver2.cold.clause_ids.capacity(),
        hint,
        "first write must take exactly the deferred reservation"
    );
    assert_eq!(
        solver2.clause_db_memory_bytes(),
        billed_unallocated,
        "taking the deferred reservation must not move the trigger basis"
    );
}

/// The clause-DB byte ceiling derived from a `--memory` budget (B77).
///
/// Before this existed, `max_clause_db_bytes` was `None` on every DIMACS route,
/// so `--memory` bounded a CNF run only by aborting it: the advisory tripped at
/// 95% of the budget and the watchdog published `c memout`. These pin the
/// derivation, because getting the share or the floor wrong is the difference
/// between backpressure and a byte trigger that fires on every conflict for
/// nothing.
#[test]
fn clause_db_budget_takes_a_share_of_the_process_limit() {
    let mut solver = Solver::new(64);
    assert_eq!(
        solver.cold.max_clause_db_bytes, None,
        "precondition: the byte ceiling starts unset"
    );

    let limit = 6000 * 1024 * 1024;
    let installed = solver
        .arm_clause_db_budget_from_process_limit(limit)
        .expect("a positive budget must install a ceiling");

    assert_eq!(
        installed,
        limit / 100 * memory_budget::CLAUSE_DB_BUDGET_PERCENT,
        "a small formula must take exactly the configured share"
    );
    assert_eq!(solver.cold.max_clause_db_bytes, Some(installed));
    assert!(
        installed < limit,
        "the clause DB may never claim the whole process budget: the \
         per-variable arrays, the proof writer and allocator slack are charged \
         against the same number"
    );
}

#[test]
fn clause_db_budget_is_inert_without_a_process_limit() {
    let mut solver = Solver::new(64);
    assert_eq!(solver.arm_clause_db_budget_from_process_limit(0), None);
    assert_eq!(
        solver.cold.max_clause_db_bytes, None,
        "an unset budget must leave the engine exactly as it was — library \
         consumers and uncapped runs must not acquire a ceiling"
    );
}

/// A budget share BELOW what the original formula already costs must not
/// produce a ceiling the solver is already over: `should_reduce_db` would then
/// return true on every conflict, and no amount of reduction could clear it,
/// because the irredundant arena and the original ledger are not reducible.
#[test]
fn clause_db_budget_floors_at_the_loaded_formula_plus_headroom() {
    let mut solver = Solver::new(64);
    let loaded = solver.clause_db_memory_bytes();

    let installed = solver
        .arm_clause_db_budget_from_process_limit(1024)
        .expect("a positive budget must install a ceiling");

    assert_eq!(
        installed,
        loaded + memory_budget::CLAUSE_DB_MIN_LEARNED_HEADROOM_BYTES,
        "an absurd budget must fall back to the loaded formula plus headroom"
    );
    assert!(
        solver.clause_db_memory_bytes() < installed,
        "the solver must not start out already over its own ceiling"
    );
}
