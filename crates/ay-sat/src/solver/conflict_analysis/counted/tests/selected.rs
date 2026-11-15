// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn root_fixture() -> (Solver, ClauseRef) {
    let mut s = Solver::new(4);
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    for clause in [
        vec![pos(0)],
        vec![neg(1), pos(2), neg(0)],
        vec![neg(1), pos(3), neg(0)],
        vec![neg(2), neg(3), neg(0)],
    ] {
        assert!(s.add_clause(clause));
    }
    s.initialize_watches();
    assert!(s.process_initial_clauses().is_none());
    assert!(s.search_propagate().is_none());
    assert_eq!(s.lit_val(pos(0)), 1);
    assert_eq!(s.var_data[0].level, 0);
    s.decide(pos(1));
    let reference = s.search_propagate().unwrap();
    assert_eq!(s.var_data[0].level, 0);
    (s, reference)
}

#[test]
fn selected_traced_root_unit_augmentation_matches_ordinary_without_detaching_trace() {
    let (mut expected, reference) = root_fixture();
    let expected_result = ordinary(&mut expected, reference).unwrap();
    let expected_trace = format!("{:?}", expected.clause_trace());
    let (mut s, reference) = root_fixture();
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut s, &owner);
    assert_eq!(run(&mut s, reference).unwrap().unwrap(), expected_result);
    assert!(s.cold.lrat_enabled && s.has_live_clause_trace());
    assert_eq!(format!("{:?}", s.clause_trace()), expected_trace);
    assert!(s.stats.lrat_materialize_calls > 0);
    assert!(s.stats.lrat_unit_chain_hints > 0);
    assert_eq!(s.stats.lrat_unit_chain_missing_hints, 0);
    assert!(owner.usage().unwrap().work_admitted > 100);
    clean(&s);
}

#[test]
fn selected_traced_removal_snapshot_is_refused_without_turning_off_lrat() {
    let (mut s, reference, _) = fixture(2, Reasons::Long);
    s.set_shrink_enabled(false); // Exercise the existing selected recursive route.
    let trace = format!("{:?}", s.clause_trace());
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut s, &owner);
    assert_eq!(
        run(&mut s, reference),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert!(s.cold.lrat_enabled && s.has_live_clause_trace());
    assert_eq!(format!("{:?}", s.clause_trace()), trace);
    assert_eq!(s.stats.lrat_original_learned_snapshot_copies, 0);
    clean(&s);
}

fn otfs_fixture() -> (Solver, ClauseRef) {
    let mut s = Solver::new(6);
    for clause in [
        vec![neg(1), pos(2), neg(0)],
        vec![neg(2), pos(3), neg(0)],
        vec![neg(1), pos(4), neg(0)],
        vec![neg(4), pos(5), neg(0)],
        vec![neg(3), neg(5), neg(0)],
    ] {
        assert!(s.add_clause(clause));
    }
    s.initialize_watches();
    s.decide(pos(0));
    assert!(s.search_propagate().is_none());
    s.decide(pos(1));
    let reference = s.search_propagate().unwrap();
    (s, reference)
}

#[test]
fn actually_selected_otfs_is_refused_before_arena_watch_or_trace_mutation() {
    let (mut expected, reference) = otfs_fixture();
    assert!(ordinary(&mut expected, reference).is_some());
    assert!(
        expected.stats.otfs_strengthened > 0,
        "must exercise real selected OTFS"
    );
    let (mut s, reference) = otfs_fixture();
    let before = clauses(&s);
    let trace = format!("{:?}", s.clause_trace());
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut s, &owner);
    assert_eq!(
        run(&mut s, reference),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert!(s.stats.otfs_candidates > 0);
    assert_eq!(s.stats.otfs_strengthened, 0);
    assert_eq!(clauses(&s), before);
    assert_eq!(format!("{:?}", s.clause_trace()), trace);
    assert!(owner.usage().unwrap().refusal.is_some());
    clean(&s);
}

#[test]
fn proof_and_ic3_states_are_explicit_refusals_without_reconfiguring_solver() {
    for mutate in [
        (|s: &mut Solver| s.cold.ic3_mode = true) as fn(&mut Solver),
        |s| s.cold.clause_trace = None,
        |s| s.cold.internal_lrat_enabled = true,
        |s| s.mark_veripb_hints_active_for_test(),
    ] {
        let (mut s, reference, _) = fixture(1, Reasons::Long);
        mutate(&mut s);
        let before = clauses(&s);
        let flags = (
            s.cold.ic3_mode,
            s.cold.lrat_enabled,
            s.cold.internal_lrat_enabled,
        );
        attach(&mut s, &test_owner(100_000_000, 100_000_000));
        assert_eq!(
            run(&mut s, reference),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(
            (
                s.cold.ic3_mode,
                s.cold.lrat_enabled,
                s.cold.internal_lrat_enabled
            ),
            flags
        );
        assert_eq!(clauses(&s), before);
    }
}

#[test]
fn real_clause_bump_preserves_glue_wrap_exact_growth_tiers_and_two_stage_score() {
    use crate::solver::conflict_analysis_minimize::admitted::Ordinary;
    for two_stage in [false, true] {
        let (mut expected, reference, _) = fixture(2, Reasons::Long);
        let index = reference.0 as usize;
        expected.arena.set_learned(index, true);
        expected.arena.set_lbd(index, 7);
        expected.glue_stamp.clear();
        expected.glue_stamp_counter = u32::MAX;
        expected.two_stage_clause_management = two_stage;
        let (mut actual, actual_reference, _) = fixture(2, Reasons::Long);
        assert_eq!(actual_reference, reference);
        actual.arena.set_learned(index, true);
        actual.arena.set_lbd(index, 7);
        actual.glue_stamp.clear();
        actual.glue_stamp_counter = u32::MAX;
        actual.two_stage_clause_management = two_stage;
        expected.bump_clause_admitted(reference, &Ordinary).unwrap();
        let owner = test_owner(100_000_000, 100_000_000);
        side_effects::prepare_bump(&mut actual, reference, &owner).unwrap();
        assert_eq!(actual.arena.lbd(index), expected.arena.lbd(index));
        assert_eq!(
            actual.arena.two_stage_score(index),
            expected.arena.two_stage_score(index)
        );
        assert_eq!(actual.glue_stamp, expected.glue_stamp);
        assert_eq!(actual.glue_stamp.capacity(), expected.glue_stamp.capacity());
        assert_eq!(actual.glue_stamp_counter, expected.glue_stamp_counter);
        assert_eq!(actual.tiers.tier_usage, expected.tiers.tier_usage);
        assert_eq!(actual.tiers.tier_bump_total, expected.tiers.tier_bump_total);
        assert!(owner.usage().unwrap().work_admitted > 0);
    }
}

#[test]
fn learned_clause_glue_early_exit_does_not_grow_for_unvisited_levels() {
    use crate::solver::conflict_analysis_minimize::admitted::Ordinary;
    let mut expected = Solver::new(20);
    let index = expected.add_clause_db(&[neg(0), neg(1), neg(2)], true);
    for (var, level) in [(0, 1), (1, 15), (2, 19)] {
        expected.var_data[var].level = level;
        expected.vals[pos(var as u32).index()] = 1;
        expected.vals[neg(var as u32).index()] = -1;
    }
    expected.arena.set_lbd(index, 1);
    expected.glue_stamp.clear();
    let mut actual = Solver::new(20);
    assert_eq!(actual.add_clause_db(&[neg(0), neg(1), neg(2)], true), index);
    for (var, level) in [(0, 1), (1, 15), (2, 19)] {
        actual.var_data[var].level = level;
        actual.vals[pos(var as u32).index()] = 1;
        actual.vals[neg(var as u32).index()] = -1;
    }
    actual.arena.set_lbd(index, 1);
    actual.glue_stamp.clear();
    expected
        .bump_clause_admitted(ClauseRef(index as u32), &Ordinary)
        .unwrap();
    let owner = test_owner(100_000_000, 100_000_000);
    side_effects::prepare_bump(&mut actual, ClauseRef(index as u32), &owner).unwrap();
    assert_eq!(actual.glue_stamp, expected.glue_stamp);
    assert_eq!(actual.glue_stamp.len(), 2);
    assert_eq!(actual.glue_stamp.capacity(), expected.glue_stamp.capacity());
}

#[cfg(all(feature = "jit", target_arch = "aarch64"))]
#[test]
fn native_output_layout_mismatch_refuses_before_any_native_application() {
    let (mut s, reference, _) = fixture(1, Reasons::Long);
    s.compile_conflict_processor();
    assert!(s.standard_native_available());
    let capacity = s.jit_conflict_output.capacity();
    s.jit_conflict_output.resize(capacity + 1);
    attach(&mut s, &test_owner(100_000_000, 100_000_000));
    assert_eq!(
        run(&mut s, reference),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(s.stats.sat_conflict_analysis_native_applications, 0);
    clean(&s);
}

#[test]
fn sampled_relevance_otfs_branch_b_observes_seen_before_retirement() {
    for stable in [false, true] {
        let mut observed = Vec::new();
        for num_conflicts in [1023, 1024] {
            let (mut s, reference) = otfs_fixture();
            s.stable_mode = stable;
            s.num_conflicts = num_conflicts;
            let result = ordinary(&mut s, reference).expect("real OTFS branch B result");
            assert_eq!(s.stats.otfs_branch_b, 1);
            assert!(s.stats.otfs_strengthened > 0);
            assert!(s.var_data.iter().all(|data| !data.is_seen()));
            let (focused, stable_counts) = s.sampled_decision_relevance();
            let (active, inactive) = if stable {
                (stable_counts, focused)
            } else {
                (focused, stable_counts)
            };
            assert_eq!(inactive, (0, 0, 0));
            assert_eq!(
                active,
                if num_conflicts == 1024 {
                    (1, 2, 2)
                } else {
                    (0, 0, 0)
                }
            );
            let (focused_sources, stable_sources) = s.sampled_decision_sources();
            let (split, inactive_split) = if stable {
                (stable_sources, focused_sources)
            } else {
                (focused_sources, stable_sources)
            };
            assert_eq!(inactive_split, (0, 0, 0, 0));
            assert_eq!(split.0 + split.2, active.1);
            assert_eq!(split.1 + split.3, active.2);
            assert!(split.1 <= split.0 && split.3 <= split.2);
            observed.push((result, clauses(&s)));
        }
        assert_eq!(observed[0], observed[1]);
    }
}
