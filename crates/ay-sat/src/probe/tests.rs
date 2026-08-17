// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::analysis::{
    failed_literal_dominator, failed_literal_dominator_forced_only, find_failed_literal_uip,
    hyper_binary_resolve, probe_dominator, DominatorFailure,
};
use super::*;
use crate::solver::{VarData, NO_REASON};
use crate::watched::ClauseRef;

/// Build a VarData vec from separate trail_pos/level/reason arrays (test helper).
fn make_var_data(trail_pos: &[usize], level: &[u32], reason: &[Option<ClauseRef>]) -> Vec<VarData> {
    let n = trail_pos.len().max(level.len()).max(reason.len());
    (0..n)
        .map(|i| VarData {
            level: level.get(i).copied().unwrap_or(0),
            trail_pos: trail_pos.get(i).map(|&tp| tp as u32).unwrap_or(u32::MAX),
            reason: reason
                .get(i)
                .and_then(|r| r.map(|cr| cr.0))
                .unwrap_or(NO_REASON),
            flags: 0,
            _pad: [0; 3],
        })
        .collect()
}

#[test]
fn test_prober_new() {
    let prober = Prober::new(10);
    assert_eq!(prober.num_vars, 10);
    assert!(prober.probes.is_empty());
    assert_eq!(prober.stats.rounds, 0);
}

#[test]
fn test_count_binary_occurrences() {
    let mut prober = Prober::new(3);
    let vals = vec![0i8; 6]; // 3 vars * 2

    // Create clauses: (x0 v x1), (¬x0 v x2)
    let mut clauses = ClauseArena::new();
    clauses.add(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    clauses.add(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    prober.count_binary_occurrences(&clauses, &vals);

    // x0 appears once positive, once negative
    assert_eq!(prober.bin_occs[Literal::positive(Variable(0)).index()], 1);
    assert_eq!(prober.bin_occs[Literal::negative(Variable(0)).index()], 1);
    // x1 appears once positive
    assert_eq!(prober.bin_occs[Literal::positive(Variable(1)).index()], 1);
    assert_eq!(prober.bin_occs[Literal::negative(Variable(1)).index()], 0);
    // x2 appears once positive
    assert_eq!(prober.bin_occs[Literal::positive(Variable(2)).index()], 1);
    assert_eq!(prober.bin_occs[Literal::negative(Variable(2)).index()], 0);
}

#[test]
fn test_generate_probes_root_detection() {
    let mut prober = Prober::new(3);
    let vals = vec![0i8; 6]; // 3 vars * 2

    // Create binary clauses where x1 is a root (appears only negated)
    // (x0 v ¬x1), (x2 v ¬x1)
    let mut clauses = ClauseArena::new();
    clauses.add(
        &[
            Literal::positive(Variable(0)),
            Literal::negative(Variable(1)),
        ],
        false,
    );
    clauses.add(
        &[
            Literal::positive(Variable(2)),
            Literal::negative(Variable(1)),
        ],
        false,
    );

    prober.generate_probes(&clauses, &vals, 0);

    // Binary clauses (x0 v !x1), (x2 v !x1):
    //   !x1 appears in binary clauses (neg_occs=2), x1 does not (pos_occs=0)
    //     → probe pos_x1 (to falsify !x1 and exercise !x1→x0, !x1→x2 chain)
    //   x0 appears in binary clauses (pos_occs=1), !x0 does not (neg_occs=0)
    //     → probe neg_x0 (to falsify x0 and exercise x0→!x1 chain)
    //   x2 appears in binary clauses (pos_occs=1), !x2 does not (neg_occs=0)
    //     → probe neg_x2 (to falsify x2 and exercise x2→!x1 chain)
    assert!(!prober.probes.is_empty());

    // x1 (positive) should be a probe: deciding x1=TRUE falsifies !x1,
    // triggering propagation from {x0, !x1} and {x2, !x1}.
    let mut found_pos_x1 = false;
    for probe in &prober.probes {
        if *probe == Literal::positive(Variable(1)) {
            found_pos_x1 = true;
        }
    }
    assert!(
        found_pos_x1,
        "x1 should be a probe candidate (neg_occs > 0, pos_occs == 0)"
    );
}

#[test]
fn test_probe_stats() {
    let mut prober = Prober::new(5);

    prober.record_probed();
    prober.record_probed();
    prober.record_failed();
    prober.record_round();

    assert_eq!(prober.stats.probed, 2);
    assert_eq!(prober.stats.failed, 1);
    assert_eq!(prober.stats.units_derived, 1);
    assert_eq!(prober.stats.rounds, 1);
}

#[test]
fn test_mark_probed() {
    let mut prober = Prober::new(3);
    let lit = Literal::positive(Variable(1));

    assert!(prober.propfixed[lit.index()] < 0);

    prober.mark_probed(lit, 5);
    assert_eq!(prober.propfixed[lit.index()], 5);

    // Should skip probing if current_fixed hasn't changed
    let vals = vec![0i8; 6]; // 3 vars * 2
    let mut clauses = ClauseArena::new();
    clauses.add(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );

    prober.generate_probes(&clauses, &vals, 5);
    // lit should not be in probes because propfixed[lit] >= current_fixed
    assert!(
        !prober.probes.contains(&lit),
        "Already probed literal should be skipped"
    );
}

#[test]
fn test_probe_dominator_same_literal() {
    // Two identical literals should return that literal as dominator
    let a = Literal::positive(Variable(0));
    let trail: Vec<Literal> = vec![a];
    let var_data = make_var_data(&[0], &[1], &[None]);
    let clauses = ClauseArena::new();

    let probe_parent: Vec<Option<Literal>> = vec![None]; // decision literal
    let result = probe_dominator(a, a, &trail, &var_data, &probe_parent, &clauses);
    assert_eq!(result, Some(a));
}

#[test]
fn test_find_failed_literal_uip_single_level1_literal() {
    let conflict_clause = vec![Literal::positive(Variable(0))];
    let trail = vec![Literal::positive(Variable(0))];
    let var_data = make_var_data(&[0], &[1], &[None]);
    let clauses = ClauseArena::new();
    let mut scratch = Vec::new();

    let forced =
        find_failed_literal_uip(&conflict_clause, &trail, &var_data, &clauses, &mut scratch);
    assert_eq!(forced.forced, Some(Literal::negative(Variable(0))));
    assert!(scratch.len() >= var_data.len());
}

#[test]
fn test_find_failed_literal_uip_reuses_scratch_buffer() {
    let mut clauses = ClauseArena::new();
    let reason_idx = clauses.add(
        &[
            Literal::negative(Variable(1)),
            Literal::positive(Variable(2)),
        ],
        false,
    );
    let conflict_clause = vec![
        Literal::negative(Variable(1)),
        Literal::negative(Variable(2)),
    ];
    let trail = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ];
    let var_data = make_var_data(
        &[0, 1, 2],
        &[1, 1, 1],
        &[None, None, Some(ClauseRef(reason_idx as u32))],
    );
    let mut scratch = vec![true; 8];
    let capacity_before = scratch.capacity();

    let forced1 =
        find_failed_literal_uip(&conflict_clause, &trail, &var_data, &clauses, &mut scratch);
    assert_eq!(forced1.forced, Some(Literal::negative(Variable(1))));

    // Re-run with the same scratch to ensure stable behavior without
    // requiring capacity growth in steady state.
    let forced2 =
        find_failed_literal_uip(&conflict_clause, &trail, &var_data, &clauses, &mut scratch);
    assert_eq!(forced2.forced, Some(Literal::negative(Variable(1))));
    assert_eq!(scratch.capacity(), capacity_before);
}

#[test]
fn test_failed_literal_dominator_tracks_parent_chain() {
    let d = Literal::positive(Variable(0));
    let a = Literal::positive(Variable(1));
    let b = Literal::positive(Variable(2));
    let conflict_clause = vec![a.negated(), b.negated()];
    let trail = vec![d, a, b];
    let var_data = make_var_data(&[0, 1, 2], &[1, 1, 1], &[None, None, None]);
    let probe_parent = vec![None, Some(d), Some(a)];
    let clauses = ClauseArena::new();

    let result = failed_literal_dominator(
        &conflict_clause,
        d,
        &trail,
        &var_data,
        &probe_parent,
        &clauses,
    );

    assert_eq!(result.forced, Some(a.negated()));
    assert_eq!(result.parent_chain, vec![d]);
    assert_eq!(result.failure, None);
}

#[test]
fn test_failed_literal_dominator_forced_only_matches_full_result() {
    let d = Literal::positive(Variable(0));
    let a = Literal::positive(Variable(1));
    let b = Literal::positive(Variable(2));
    let conflict_clause = vec![a.negated(), b.negated()];
    let trail = vec![d, a, b];
    let var_data = make_var_data(&[0, 1, 2], &[1, 1, 1], &[None, None, None]);
    let probe_parent = vec![None, Some(d), Some(a)];
    let clauses = ClauseArena::new();

    let full = failed_literal_dominator(
        &conflict_clause,
        d,
        &trail,
        &var_data,
        &probe_parent,
        &clauses,
    );
    let forced_only = failed_literal_dominator_forced_only(
        &conflict_clause,
        d,
        &trail,
        &var_data,
        &probe_parent,
        &clauses,
    );

    assert_eq!(forced_only.forced, full.forced);
    assert_eq!(forced_only.failure, full.failure);
    assert!(
        forced_only.parent_chain.is_empty(),
        "forced-only path must not build parent chain"
    );
}

mod dominator_failures;
#[test]
fn test_probe_dominator_decision_literal() {
    // When one literal is the decision (no parent), it should be the dominator
    let d = Literal::positive(Variable(0)); // decision
    let a = Literal::positive(Variable(1)); // implied by d

    // Build trail: d at pos 0, a at pos 1
    let trail = vec![d, a];

    // d has no reason (decision), a has binary reason (d, ¬a) => a is implied by d
    let mut clauses = ClauseArena::new();
    let clause_idx = clauses.add(&[a, d.negated()], false) as u32;
    let var_data = make_var_data(&[0, 1], &[1, 1], &[None, Some(ClauseRef(clause_idx))]);
    // probe_parent: d is decision (None), a's parent is d
    let probe_parent: Vec<Option<Literal>> = vec![None, Some(d)];

    // dominator(d, a) should be d (the decision)
    let result = probe_dominator(d, a, &trail, &var_data, &probe_parent, &clauses);
    assert_eq!(result, Some(d));
}

#[test]
fn test_probe_dominator_missing_parent_metadata_returns_none() {
    let d = Literal::positive(Variable(0)); // decision
    let a = Literal::positive(Variable(1)); // implied by d, but parent metadata missing

    let trail = vec![d, a];

    let mut clauses = ClauseArena::new();
    let clause_idx = clauses.add(&[a, d.negated()], false) as u32;
    let var_data = make_var_data(&[0, 1], &[1, 1], &[None, Some(ClauseRef(clause_idx))]);

    // Missing parent metadata for `a`: this must not be reinterpreted as root.
    let probe_parent: Vec<Option<Literal>> = vec![None, None];

    let result = probe_dominator(d, a, &trail, &var_data, &probe_parent, &clauses);
    assert_eq!(result, None);
}

#[test]
fn test_hyper_binary_resolve_trivial_clause() {
    // Clauses with <= 2 literals should not produce HBR
    let lits = vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ];
    let trail: Vec<Literal> = vec![];
    let var_data: Vec<VarData> = vec![];
    let probe_parent: Vec<Option<Literal>> = vec![];
    let clauses = ClauseArena::new();

    let result = hyper_binary_resolve(&lits, &trail, &var_data, &probe_parent, &clauses, false);
    assert!(result.binary_clause.is_none());
}

#[test]
fn test_hyper_binary_resolve_all_level0() {
    // If all false literals (except unit) are at level 0, should not produce HBR
    let unit = Literal::positive(Variable(0));
    let false1 = Literal::negative(Variable(1));
    let false2 = Literal::negative(Variable(2));
    let lits = vec![unit, false1, false2];

    let trail: Vec<Literal> = vec![];
    let var_data = make_var_data(&[0, 0, 0], &[0, 0, 0], &[None, None, None]);
    let probe_parent: Vec<Option<Literal>> = vec![None, None, None];
    let clauses = ClauseArena::new();

    let result = hyper_binary_resolve(&lits, &trail, &var_data, &probe_parent, &clauses, false);
    // Level check for lits[1] should fail (not level 1)
    assert!(result.binary_clause.is_none());
}

#[test]
fn test_hyper_binary_resolve_carries_dominator_without_binary_emission() {
    let unit = Literal::positive(Variable(0));
    let lit1 = Literal::negative(Variable(1));
    let lit2 = Literal::negative(Variable(2));
    let lits = vec![unit, lit1, lit2];

    // Only lits[1] is at level 1. Remaining false literals are level 0, so
    // HBR must not emit a binary clause but should still carry dominator.
    let trail = vec![lit1.negated()];
    let var_data = make_var_data(
        &[usize::MAX, 0, usize::MAX],
        &[0, 1, 0],
        &[None, None, None],
    );
    let probe_parent: Vec<Option<Literal>> = vec![None, None, None];
    let clauses = ClauseArena::new();

    let result = hyper_binary_resolve(&lits, &trail, &var_data, &probe_parent, &clauses, false);

    assert!(
        result.binary_clause.is_none(),
        "no binary clause should be emitted when no non-root level-1 literal remains"
    );
    assert_eq!(
        result.dominator,
        Some(lit1.negated()),
        "dominator must carry through for probe_parent assignment"
    );
}

#[test]
fn test_record_hbr() {
    let mut prober = Prober::new(5);
    assert_eq!(prober.stats.hbrs, 0);
    assert_eq!(prober.stats.hbr_subs, 0);
    assert_eq!(prober.stats.hbr_subsumed_deleted, 0);

    prober.record_hbr(5, false, false);
    assert_eq!(prober.stats.hbrs, 1);
    assert_eq!(prober.stats.hbr_sizes, 5);
    assert_eq!(prober.stats.hbr_redundant, 0);
    assert_eq!(prober.stats.hbr_subs, 0);
    assert_eq!(prober.stats.hbr_subsumed_deleted, 0);

    prober.record_hbr(3, true, false);
    assert_eq!(prober.stats.hbrs, 2);
    assert_eq!(prober.stats.hbr_sizes, 8);
    assert_eq!(prober.stats.hbr_redundant, 1);
    assert_eq!(prober.stats.hbr_subs, 0);
    assert_eq!(prober.stats.hbr_subsumed_deleted, 0);

    prober.record_hbr(4, false, true);
    assert_eq!(prober.stats.hbrs, 3);
    assert_eq!(prober.stats.hbr_sizes, 12);
    assert_eq!(prober.stats.hbr_subs, 1);
    assert_eq!(prober.stats.hbr_subsumed_deleted, 0);

    prober.record_hbr_subsumed_deletion();
    assert_eq!(prober.stats.hbr_subsumed_deleted, 1);
}

/// (#8478) When a conflict clause contains a literal whose variable index
/// exceeds var_data.len() (e.g., from a pre-compaction clause referencing
/// eliminated variables), find_failed_literal_uip must not panic. It should
/// skip the OOB literal and still find the UIP among in-bounds literals.
#[test]
fn test_find_failed_literal_uip_skips_oob_conflict_literal() {
    // var_data has 3 variables (indices 0..2).
    // Conflict clause includes Variable(5), which is OOB.
    let in_bounds_lit = Literal::positive(Variable(0));
    let oob_lit = Literal::positive(Variable(5)); // exceeds var_data.len()
    let conflict_clause = vec![in_bounds_lit, oob_lit];
    let trail = vec![in_bounds_lit];
    let var_data = make_var_data(&[0], &[1], &[None]);
    let clauses = ClauseArena::new();
    let mut scratch = Vec::new();

    // Must not panic: OOB literal should be skipped.
    let result =
        find_failed_literal_uip(&conflict_clause, &trail, &var_data, &clauses, &mut scratch);
    // The in-bounds literal at level 1 is the UIP.
    assert_eq!(result.forced, Some(in_bounds_lit.negated()));
}

/// (#8478) When a reason clause contains an OOB literal, the UIP extraction
/// must skip it rather than panic on var_data or seen array access.
#[test]
fn test_find_failed_literal_uip_skips_oob_reason_literal() {
    // Setup: conflict has two level-1 literals (v1, v2). v2's reason clause
    // mentions Variable(10), which exceeds var_data.len().
    let d = Literal::positive(Variable(0)); // decision
    let a = Literal::positive(Variable(1)); // implied
    let b = Literal::positive(Variable(2)); // implied

    let mut clauses = ClauseArena::new();
    // Reason for b: (b, -a, OOB_literal)
    let oob_lit = Literal::negative(Variable(10));
    let reason_idx = clauses.add(&[b, a.negated(), oob_lit], false);

    let conflict_clause = vec![a.negated(), b.negated()];
    let trail = vec![d, a, b];
    let var_data = make_var_data(
        &[0, 1, 2],
        &[1, 1, 1],
        &[None, None, Some(ClauseRef(reason_idx as u32))],
    );
    let mut scratch = Vec::new();

    // Must not panic: OOB reason literal should be skipped.
    let result =
        find_failed_literal_uip(&conflict_clause, &trail, &var_data, &clauses, &mut scratch);
    // UIP should be found (either a or d depending on resolution).
    assert!(result.forced.is_some());
}
