// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for forward subsumption and self-subsumption.

use super::*;
use crate::test_util::lit;

#[test]
fn test_subsumption_basic() {
    let mut subsumer = Subsumer::new(5);

    let c = vec![lit(0, true), lit(1, true)];
    let d = vec![lit(0, true), lit(1, true), lit(2, true)];

    subsumer.mark_clause(&d);
    let check = subsumer.subsume_check(&c);
    subsumer.unmark_clause(&d);
    assert_eq!(check, i32::MIN);

    subsumer.mark_clause(&c);
    let check = subsumer.subsume_check(&d);
    subsumer.unmark_clause(&c);
    assert_eq!(check, 0);
}

#[test]
fn test_subsumption_polarity() {
    let mut subsumer = Subsumer::new(5);

    // C = {0, ¬1} checked against D = {0, 1, 2}: one opposite polarity = strengthening
    let c = vec![lit(0, true), lit(1, false)];
    let d = vec![lit(0, true), lit(1, true), lit(2, true)];

    subsumer.mark_clause(&d);
    let check = subsumer.subsume_check(&c);
    subsumer.unmark_clause(&d);
    assert_ne!(check, i32::MIN);
    assert_ne!(check, 0);
}

#[test]
fn test_ordered_watch_pair_prefers_rarer_literal() {
    let mut subsumer = Subsumer::new(4);
    subsumer.noccs.resize(8, 0);
    subsumer.noccs[lit(0, true).index()] = 9;
    subsumer.noccs[lit(1, true).index()] = 3;

    let (first, second) = subsumer.ordered_watch_pair(lit(0, true), lit(1, true));
    assert_eq!(first, lit(1, true));
    assert_eq!(second, lit(0, true));
}

#[test]
fn test_pick_connection_literal_breaks_size_ties_with_higher_noccs() {
    let mut subsumer = Subsumer::new(4);
    subsumer.occs.resize_with(8, Vec::new);
    subsumer.noccs.resize(8, 0);

    let a = lit(0, true);
    let b = lit(1, true);
    let c = lit(2, true);
    subsumer.noccs[a.index()] = 3;
    subsumer.noccs[b.index()] = 7;
    subsumer.noccs[c.index()] = 5;

    let chosen = subsumer.pick_connection_literal(&[a, b, c], false);
    assert_eq!(chosen, b);
}

#[test]
fn test_self_subsumption_via_check() {
    let mut subsumer = Subsumer::new(5);

    let c = vec![lit(0, true), lit(1, true)];
    let d = vec![lit(0, false), lit(1, true), lit(2, true)];

    subsumer.mark_clause(&d);
    let check = subsumer.subsume_check(&c);
    subsumer.unmark_clause(&d);
    assert!(check != 0 && check != i32::MIN);
}

#[test]
fn test_run_subsumption_forward() {
    let mut subsumer = Subsumer::new(5);
    subsumer.check_limit = 0;

    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(2, true), lit(3, true)], false);
    let c2_off = clauses.add(&[lit(0, true), lit(1, true), lit(4, true)], false);
    let c3_off = clauses.add(&[lit(0, false), lit(1, true), lit(4, true)], false);

    let freeze_counts = vec![0u32; 5];
    let all_dirty = vec![true; 5];
    let vals = vec![0i8; 10];

    let result = subsumer.run_forward_subsumption(
        &mut clauses,
        &freeze_counts,
        &all_dirty,
        &vals,
        KeptThresholds::all_inclusive(),
    );

    assert!(
        result.subsumed.iter().any(|&(sub, _)| sub == c2_off),
        "C2 should be subsumed, got: {:?}",
        result.subsumed
    );

    let strengthened_c3 = result
        .strengthened
        .iter()
        .find(|(idx, _, _)| *idx == c3_off);
    assert!(
        strengthened_c3.is_some(),
        "C3 should be strengthened, got: {:?}",
        result.strengthened
    );
    if let Some((_, new_lits, _)) = strengthened_c3 {
        assert_eq!(new_lits.len(), 2);
        assert!(new_lits.contains(&lit(1, true)));
        assert!(new_lits.contains(&lit(4, true)));
    }
}

#[test]
fn test_clause_subsumed_by_existing_finds_subsumer() {
    let mut subsumer = Subsumer::new(5);

    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(2, true), lit(3, true)], false);

    subsumer.rebuild(&clauses);

    assert_eq!(
        subsumer
            .clause_subsumed_by_existing(&[lit(0, true), lit(1, true), lit(4, true)], &clauses,),
        Some(c0)
    );
    assert_eq!(
        subsumer.clause_subsumed_by_existing(&[lit(0, true), lit(4, true)], &clauses),
        None
    );
}

#[test]
fn test_clause_subsumed_by_existing_ignores_dead_stale_occurrence() {
    let mut subsumer = Subsumer::new(5);

    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, true), lit(1, true)], false);
    subsumer.rebuild(&clauses);

    clauses.set_pending_garbage(c0, true);

    assert_eq!(
        subsumer.clause_subsumed_by_existing(&[lit(0, true), lit(1, true), lit(4, true)], &clauses),
        None,
        "stale occurrence entries for dead clauses must not subsume new clauses"
    );
}

#[test]
fn test_forward_subsumption_skips_dead_candidate_and_subsumer() {
    let mut subsumer = Subsumer::new(5);
    subsumer.check_limit = 0;

    let mut clauses = ClauseArena::new();
    let dead_subsumer = clauses.add(&[lit(0, true), lit(1, true)], false);
    let live_candidate = clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    let dead_candidate = clauses.add(&[lit(2, true), lit(3, true), lit(4, true)], false);
    clauses.set_pending_garbage(dead_subsumer, true);
    clauses.set_pending_garbage(dead_candidate, true);

    let freeze_counts = vec![0u32; 5];
    let all_dirty = vec![true; 5];
    let vals = vec![0i8; 10];

    let result = subsumer.run_forward_subsumption(
        &mut clauses,
        &freeze_counts,
        &all_dirty,
        &vals,
        KeptThresholds::all_inclusive(),
    );

    assert_eq!(
        result.candidates_scheduled, 1,
        "only the live candidate should be scheduled"
    );
    assert!(
        result.subsumed.is_empty(),
        "dead subsumer must not subsume live candidate {live_candidate}, got {:?}",
        result.subsumed
    );
    assert!(
        result.strengthened.is_empty(),
        "dead candidates/subsumers must not produce strengthening"
    );
}

#[test]
fn test_backward_compat_run_subsumption() {
    let mut subsumer = Subsumer::new(5);
    subsumer.check_limit = 0;

    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    let c1_off = clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);

    let freeze_counts = vec![0u32; 5];
    let num_clauses = clauses.num_clauses();
    let result = subsumer.run_subsumption(&mut clauses, &freeze_counts, 0, num_clauses);

    assert!(result.subsumed.iter().any(|&(sub, _)| sub == c1_off));
}

#[test]
fn test_incremental_dirty_bits() {
    let mut subsumer = Subsumer::new(5);
    subsumer.check_limit = 0;

    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(1, true), lit(4, true)], false);

    let freeze_counts = vec![0u32; 5];
    let mut dirty = vec![false; 5];
    dirty[0] = true; // only var 0 is dirty
    let vals = vec![0i8; 10];

    let result = subsumer.run_forward_subsumption(
        &mut clauses,
        &freeze_counts,
        &dirty,
        &vals,
        KeptThresholds::all_inclusive(),
    );

    assert_eq!(result.subsumed.len(), 0);
    assert_eq!(result.strengthened.len(), 0);
}

#[test]
fn test_dirty_unit_subsumer_strengthens_binary_with_one_dirty_var() {
    let mut subsumer = Subsumer::new(2);
    subsumer.check_limit = 0;

    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true)], false);
    let binary = clauses.add(&[lit(0, false), lit(1, true)], false);

    let freeze_counts = vec![0u32; 2];
    let mut dirty = vec![false; 2];
    dirty[0] = true;
    let vals = vec![0i8; 4];

    let result = subsumer.run_forward_subsumption(
        &mut clauses,
        &freeze_counts,
        &dirty,
        &vals,
        KeptThresholds::all_inclusive(),
    );

    let strengthened = result
        .strengthened
        .iter()
        .find(|(idx, _, _)| *idx == binary)
        .expect("unit subsumer should strengthen binary clause");
    assert_eq!(strengthened.1, vec![lit(1, true)]);
}

#[test]
fn test_opposing_dirty_units_strengthen_to_empty() {
    let mut subsumer = Subsumer::new(1);
    subsumer.check_limit = 0;

    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true)], false);
    clauses.add(&[lit(0, false)], false);

    let freeze_counts = vec![0u32; 1];
    let dirty = vec![true; 1];
    let vals = vec![0i8; 2];

    let result = subsumer.run_forward_subsumption(
        &mut clauses,
        &freeze_counts,
        &dirty,
        &vals,
        KeptThresholds::all_inclusive(),
    );

    assert!(
        result
            .strengthened
            .iter()
            .any(|(_, new_lits, _)| new_lits.is_empty()),
        "opposing unit clauses should derive an empty strengthening, got: {:?}",
        result.strengthened
    );
}

#[test]
fn test_forward_subsumption_reports_round_diagnostics() {
    let mut subsumer = Subsumer::new(5);
    subsumer.check_limit = 0;

    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);

    let freeze_counts = vec![0u32; 5];
    let all_dirty = vec![true; 5];
    let vals = vec![0i8; 10];

    let result = subsumer.run_forward_subsumption(
        &mut clauses,
        &freeze_counts,
        &all_dirty,
        &vals,
        KeptThresholds::all_inclusive(),
    );

    assert_eq!(result.candidates_scheduled, 2);
    assert!(result.checks_performed > 0);
    assert!(result.completed);

    let stats = subsumer.stats();
    assert_eq!(stats.rounds, 1);
    assert_eq!(stats.completed_rounds, 1);
    assert_eq!(stats.candidates_scheduled, 2);
}

#[test]
fn test_fixed_literal_skipped() {
    let mut subsumer = Subsumer::new(5);
    subsumer.check_limit = 0;

    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);

    let freeze_counts = vec![0u32; 5];
    let all_dirty = vec![true; 5];
    let mut vals = vec![0i8; 10];
    vals[lit(0, true).index()] = 1;

    let result = subsumer.run_forward_subsumption(
        &mut clauses,
        &freeze_counts,
        &all_dirty,
        &vals,
        KeptThresholds::all_inclusive(),
    );

    assert_eq!(result.subsumed.len(), 0);
}

/// Verify KeptThresholds filtering: learned clauses with LBD above tier2
/// and exceeding keptglue/keptsize are skipped by the subsumption schedule.
/// Exercises the CaDiCaL likely_to_be_kept_clause gate (d52c37e7d).
#[test]
fn test_kept_thresholds_filters_unlikely_learned() {
    let mut subsumer = Subsumer::new(5);
    subsumer.check_limit = 0;

    let mut clauses = ClauseArena::new();
    // C0: irredundant subsuming clause {0, 1}
    clauses.add(&[lit(0, true), lit(1, true)], false);
    // C1: learned, LBD=10, size=3 — should be filtered by thresholds
    let c1 = clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], true);
    clauses.set_lbd(c1, 10);

    let freeze_counts = vec![0u32; 5];
    let all_dirty = vec![true; 5];
    let vals = vec![0i8; 10];

    // With restrictive thresholds: tier2_lbd=6, keptglue=8, keptsize=5.
    // C1 has LBD=10 > tier2_lbd=6, and LBD=10 > keptglue=8 → skipped.
    let kept = KeptThresholds {
        tier2_lbd: 6,
        kept_glue: 8,
        kept_size: 5,
        irredundant_only: false,
    };
    let result =
        subsumer.run_forward_subsumption(&mut clauses, &freeze_counts, &all_dirty, &vals, kept);

    // C1 should NOT be subsumed because it was filtered out of the schedule.
    assert!(
        result.subsumed.is_empty(),
        "high-LBD learned clause should be skipped by KeptThresholds, got: {:?}",
        result.subsumed
    );

    // Same clauses with all_inclusive: C1 SHOULD be subsumed.
    let result2 = subsumer.run_forward_subsumption(
        &mut clauses,
        &freeze_counts,
        &all_dirty,
        &vals,
        KeptThresholds::all_inclusive(),
    );
    assert!(
        result2.subsumed.iter().any(|&(sub, _)| sub == c1),
        "with all_inclusive, C1 should be subsumed by C0, got: {:?}",
        result2.subsumed
    );
}

/// Verify that a learned clause within keptglue/keptsize thresholds is
/// still scheduled for subsumption even though its LBD exceeds tier2.
#[test]
fn test_kept_thresholds_passes_within_bounds() {
    let mut subsumer = Subsumer::new(5);
    subsumer.check_limit = 0;

    let mut clauses = ClauseArena::new();
    // C0: irredundant subsuming clause {0, 1}
    clauses.add(&[lit(0, true), lit(1, true)], false);
    // C1: learned, LBD=7, size=3 — within keptglue=8 AND keptsize=5
    let c1 = clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], true);
    clauses.set_lbd(c1, 7);

    let freeze_counts = vec![0u32; 5];
    let all_dirty = vec![true; 5];
    let vals = vec![0i8; 10];

    // tier2_lbd=6 so LBD 7 is tier3, but keptglue=8, keptsize=5
    // means glue(7) <= keptglue(8) AND size(3) <= keptsize(5) → kept.
    let kept = KeptThresholds {
        tier2_lbd: 6,
        kept_glue: 8,
        kept_size: 5,
        irredundant_only: false,
    };
    let result =
        subsumer.run_forward_subsumption(&mut clauses, &freeze_counts, &all_dirty, &vals, kept);

    assert!(
        result.subsumed.iter().any(|&(sub, _)| sub == c1),
        "tier3 learned clause within keptglue/keptsize should still be subsumed, got: {:?}",
        result.subsumed
    );
}

/// `--sat-subsume-kissat` (`irredundant_only`): a learned ternary clause is
/// neither subsumed nor a subsumer; a learned binary still subsumes, since
/// Kissat's binaries are all irredundant.
#[test]
fn test_irredundant_only_skips_learned_non_binary_clauses() {
    let kissat = KeptThresholds {
        irredundant_only: true,
        ..KeptThresholds::all_inclusive()
    };
    let freeze_counts = vec![0u32; 6];
    let all_dirty = vec![true; 6];
    let vals = vec![0i8; 12];

    // Learned ternary {0,1,2} would subsume irredundant {0,1,2,3}.
    let mut subsumer = Subsumer::new(6);
    subsumer.check_limit = 0;
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], true);
    let target = clauses.add(
        &[lit(0, true), lit(1, true), lit(2, true), lit(3, true)],
        false,
    );
    let result =
        subsumer.run_forward_subsumption(&mut clauses, &freeze_counts, &all_dirty, &vals, kissat);
    assert_eq!(
        result.subsumed.len(),
        0,
        "learned ternary subsumer: {:?}",
        result.subsumed
    );
    let mut subsumer = Subsumer::new(6);
    subsumer.check_limit = 0;
    let result = subsumer.run_forward_subsumption(
        &mut clauses,
        &freeze_counts,
        &all_dirty,
        &vals,
        KeptThresholds::all_inclusive(),
    );
    assert!(result.subsumed.iter().any(|&(sub, _)| sub == target));

    // A learned binary {4,5} still subsumes irredundant {4,5,0}.
    let mut subsumer = Subsumer::new(6);
    subsumer.check_limit = 0;
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(4, true), lit(5, true)], true);
    let target = clauses.add(&[lit(4, true), lit(5, true), lit(0, true)], false);
    let result =
        subsumer.run_forward_subsumption(&mut clauses, &freeze_counts, &all_dirty, &vals, kissat);
    assert!(
        result.subsumed.iter().any(|&(sub, _)| sub == target),
        "{:?}",
        result.subsumed
    );
}

/// Independent reimplementation of the legacy length-group candidate
/// generation (Cartesian product over length groups, a-major, diagonal
/// skipped, 200k pair cap), returning detected (subsumed, subsumer)
/// arena pairs in legacy order. The production prepass must match this
/// exactly while checking only occurrence-plausible pairs.
#[cfg(feature = "jit")]
fn legacy_simd_prepass_reference(clauses: &ClauseArena, vals: &[i8]) -> Vec<(usize, usize)> {
    let mut clause_data: Vec<(usize, usize)> = Vec::new();
    for idx in clauses.indices() {
        if clauses.is_dead(idx) || clauses.is_empty_clause(idx) {
            continue;
        }
        let lits = clauses.literals(idx);
        if lits.len() < 2 || lits.len() > 20 {
            continue;
        }
        let has_fixed = lits.iter().any(|lit| {
            let li = lit.index();
            li < vals.len() && vals[li] != 0
        });
        if has_fixed {
            continue;
        }
        clause_data.push((idx, lits.len()));
    }
    if clause_data.len() < 500 {
        return Vec::new();
    }
    clause_data.sort_unstable_by_key(|&(_, len)| len);
    let n = clause_data.len();
    let mut groups: Vec<(usize, usize, usize)> = Vec::new();
    let mut group_start = 0;
    while group_start < n {
        let group_len = clause_data[group_start].1;
        let mut group_end = group_start + 1;
        while group_end < n && clause_data[group_end].1 == group_len {
            group_end += 1;
        }
        groups.push((group_len, group_start, group_end));
        group_start = group_end;
    }
    let mut out = Vec::new();
    let mut checked = 0usize;
    'legacy: for (gi, &(_, a_start, a_end)) in groups.iter().enumerate() {
        for &(_, b_start, b_end) in &groups[gi..] {
            for a in a_start..a_end {
                for b in b_start..b_end {
                    if a == b {
                        continue;
                    }
                    let a_lits = clauses.literals(clause_data[a].0);
                    let b_lits = clauses.literals(clause_data[b].0);
                    if a_lits.iter().all(|l| b_lits.contains(l)) {
                        out.push((clause_data[b].0, clause_data[a].0));
                    }
                    checked += 1;
                    if checked >= 200_000 {
                        break 'legacy;
                    }
                }
            }
        }
    }
    out
}

/// Occurrence-indexed candidate generation must reproduce the legacy
/// length-group generation's detections exactly (same pairs, same
/// order) on an under-cap database with planted subsumptions, including
/// a duplicate pair (equal-length subsumption in both directions).
#[cfg(feature = "jit")]
#[test]
fn simd_prepass_matches_legacy_generation() {
    let mut clauses = ClauseArena::new();
    // Planted clauses on low variables.
    let subsumer = clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    let subsumed = clauses.add(
        &[
            lit(0, true),
            lit(1, true),
            lit(2, true),
            lit(3, true),
            lit(4, true),
        ],
        false,
    );
    clauses.add(&[lit(5, true), lit(6, true)], false);
    clauses.add(
        &[lit(5, true), lit(6, true), lit(7, true), lit(8, true)],
        false,
    );
    clauses.add(&[lit(20, true), lit(21, true), lit(22, true)], false);
    clauses.add(&[lit(20, true), lit(21, true), lit(22, true)], false);
    // Near miss: shares literals with the subsumer but is not a superset.
    clauses.add(&[lit(0, true), lit(1, true), lit(9, true)], false);
    // Pad past the 500-clause threshold with clauses spread over all
    // lengths 2..=20 on disjoint variables, keeping the legacy pair
    // count under the 200k cap.
    let mut var = 100u32;
    for len in 2..=20u32 {
        for _ in 0..27 {
            let lits: Vec<_> = (0..len).map(|k| lit(var + k, true)).collect();
            clauses.add(&lits, false);
            var += len;
        }
    }
    let vals = vec![0i8; 2 * (var as usize + 1)];
    let result = simd_prepass::simd_subsume_prepass(&clauses, &vals);
    let expected = legacy_simd_prepass_reference(&clauses, &vals);
    assert!(
        expected.contains(&(subsumed, subsumer)),
        "reference itself must find the planted pair"
    );
    assert_eq!(result.pairs, expected);
}

/// Over the pair cap, the prepass still matches the capped legacy
/// generation, but checks only occurrence-plausible pairs: 600 disjoint
/// binary clauses make the legacy generation spend its whole 200k cap
/// inside the binary group, while the occurrence index admits almost
/// none of those pairs.
#[cfg(feature = "jit")]
#[test]
fn simd_prepass_over_cap_checks_only_plausible_pairs() {
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(
        &[
            lit(0, true),
            lit(1, true),
            lit(2, true),
            lit(3, true),
            lit(4, true),
        ],
        false,
    );
    for i in 0..600u32 {
        let v = 10 + 2 * i;
        clauses.add(&[lit(v, true), lit(v + 1, true)], false);
    }
    let vals = vec![0i8; 2500];
    let result = simd_prepass::simd_subsume_prepass(&clauses, &vals);
    let expected = legacy_simd_prepass_reference(&clauses, &vals);
    assert_eq!(result.pairs, expected);
    assert!(
        result.pairs_checked < 50_000,
        "occurrence-indexed generation must stay far below the pair cap, got {}",
        result.pairs_checked
    );
}
