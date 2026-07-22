// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for Bounded Variable Elimination (BVE).

use super::*;
use crate::lit_marks::LitMarks;
use crate::test_util::lit;

fn assign_root(vals: &mut [i8], lit: Literal) {
    vals[lit.index()] = 1;
    vals[lit.negated().index()] = -1;
}

#[test]
fn test_bve_occurrence_list() {
    let mut occ = BVEOccList::new(5);

    let clause1 = vec![lit(0, true), lit(1, false)];
    let clause2 = vec![lit(0, true), lit(2, true)];

    occ.add_clause(0, &clause1);
    occ.add_clause(1, &clause2);

    // lit(0, true) appears in both clauses
    assert_eq!(occ.count(lit(0, true)), 2);
    assert!(occ.get(lit(0, true)).contains(&0));
    assert!(occ.get(lit(0, true)).contains(&1));

    // lit(1, false) appears only in clause 0
    assert_eq!(occ.count(lit(1, false)), 1);
    assert!(occ.get(lit(1, false)).contains(&0));
}

#[test]
fn test_bve_resolve_basic() {
    let mut bve = BVE::new(5);

    // C1 = {x0, x1}, C2 = {~x0, x2}
    // Resolvent on x0 should be {x1, x2}
    let c1 = vec![lit(0, true), lit(1, true)];
    let c2 = vec![lit(0, false), lit(2, true)];

    let result = bve.resolve(&c1, &c2, Variable(0));
    assert!(result.is_some());

    let resolvent = result.unwrap();
    assert_eq!(resolvent.len(), 2);
    assert!(resolvent.contains(&lit(1, true)));
    assert!(resolvent.contains(&lit(2, true)));
}

#[test]
fn test_bve_resolve_tautology() {
    let mut bve = BVE::new(5);

    // C1 = {x0, x1}, C2 = {~x0, ~x1}
    // Resolvent on x0 would be {x1, ~x1} - tautology
    let c1 = vec![lit(0, true), lit(1, true)];
    let c2 = vec![lit(0, false), lit(1, false)];

    let result = bve.resolve(&c1, &c2, Variable(0));
    assert!(result.is_none());
}

#[test]
fn test_bve_resolve_duplicates() {
    let mut bve = BVE::new(5);

    // C1 = {x0, x1, x2}, C2 = {~x0, x1, x3}
    // Resolvent on x0 should be {x1, x2, x3} (x1 appears once)
    let c1 = vec![lit(0, true), lit(1, true), lit(2, true)];
    let c2 = vec![lit(0, false), lit(1, true), lit(3, true)];

    let result = bve.resolve(&c1, &c2, Variable(0));
    assert!(result.is_some());

    let resolvent = result.unwrap();
    assert_eq!(resolvent.len(), 3);
    assert!(resolvent.contains(&lit(1, true)));
    assert!(resolvent.contains(&lit(2, true)));
    assert!(resolvent.contains(&lit(3, true)));
}

#[test]
fn test_bve_pure_literal() {
    let mut bve = BVE::new(5);

    // Clauses: {x0, x1}, {x0, x2}
    // x0 appears only positively - it's pure
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);

    bve.rebuild(&clauses);

    // x0 appears only positively (pure literal). The reconstruction
    // completeness guard (#8179) correctly rejects pure literals because
    // they lack one polarity in the witness, making conditional autarky
    // unsound. Pure literals are handled instead via unit propagation.
    let result = bve.try_eliminate(Variable(0), &clauses);
    assert!(
        !result.eliminated,
        "pure literals should be rejected by reconstruction completeness guard"
    );
}

#[test]
fn test_bve_bounded_check() {
    let mut bve = BVE::new(5);

    // Simple case: x0 appears in 2 clauses, elimination should be bounded
    // C0 = {x0, x1}, C1 = {~x0, x2}
    // Resolvent = {x1, x2} - one new clause vs two removed
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(2, true)], false);

    bve.rebuild(&clauses);

    let result = bve.try_eliminate(Variable(0), &clauses);
    assert!(result.eliminated);
    assert_eq!(result.to_delete.len(), 2);
    assert_eq!(result.resolvents.len(), 1);
}

#[test]
fn test_bve_rebuild_skips_garbage_clause_with_removed_variable() {
    let mut bve = BVE::new(3);
    let mut clauses = ClauseArena::new();
    let clause_idx = clauses.add(&[lit(0, true), lit(1, true)], false);

    bve.mark_removed_external(0);
    clauses.mark_garbage_keep_data(clause_idx);

    bve.rebuild(&clauses);

    assert!(bve.get_occs(lit(0, true)).is_empty());
    assert!(bve.get_occs(lit(1, true)).is_empty());
}

/// CaDiCaL fastelim product shortcut (elimfast.cpp:85-88, :239):
/// When pos * neg <= budget, the clause-count bound is trivially satisfied.
/// This test verifies that elimination succeeds for a 2×2 configuration
/// where all 4 resolvents are non-tautological (product 4 <= budget 4).
#[test]
fn test_bve_product_shortcut_accepts_small_product() {
    let mut bve = BVE::new(8);

    // x0 has 2 positive and 2 negative occurrences.
    // All variables are distinct, so all 4 resolvents are non-tautological.
    // product = 2 * 2 = 4, clauses_removed = 4, budget = 4 + 0 = 4.
    // 4 <= 4 → product shortcut fires, clause-count early-abort skipped.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(3, true)], false);
    clauses.add(&[lit(0, false), lit(4, true)], false);

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);
    assert!(
        result.eliminated,
        "product shortcut should allow elimination"
    );
    assert_eq!(result.resolvents.len(), 4);
    assert_eq!(result.to_delete.len(), 4);
}

#[test]
fn test_bve_records_self_subsuming_parent_strengthening() {
    let mut bve = BVE::new(6);

    // C0: (x0 v x1 v x2)
    // C1: (~x0 v x1)     -> resolve(C0, C1) = (x1 v x2), subsumes C0
    // C2: (~x0 v x3)     -> resolve(C0, C2) = (x1 v x2 v x3) (kept as resolvent)
    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(3, true)], false);

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(result.eliminated, "x0 should remain eliminable");
    assert!(
        result.strengthened.iter().any(|s| s.clause_idx == c0
            && s.new_lits.len() == 2
            && s.new_lits.contains(&lit(1, true))
            && s.new_lits.contains(&lit(2, true))),
        "expected parent clause to be scheduled for in-place strengthening"
    );
    assert!(
        result.resolvents.iter().any(|(r, _, _, _)| r.len() == 3
            && r.contains(&lit(1, true))
            && r.contains(&lit(2, true))
            && r.contains(&lit(3, true))),
        "expected non-subsuming resolvent to remain in add list"
    );
}

#[test]
fn test_bve_double_otfs_strengthens_one_garbage_collects_other() {
    // CaDiCaL elim.cpp:413-424: When both parent clauses are subsumed by
    // the resolvent (they differ only in the pivot), strengthen one parent
    // and garbage-collect the other. The resolvent is NOT added.
    let mut bve = BVE::new(4);

    // C0: (x0 v x1 v x2) — positive occurrence
    // C1: (~x0 v x1 v x2) — negative occurrence
    // Resolvent: (x1 v x2) — subsumes BOTH parents
    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    let c1 = clauses.add(&[lit(0, false), lit(1, true), lit(2, true)], false);

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(result.eliminated, "x0 should be eliminable");
    // Only ONE parent should be strengthened (the positive one).
    assert_eq!(
        result.strengthened.len(),
        1,
        "double OTFS should strengthen exactly one parent"
    );
    assert_eq!(
        result.strengthened[0].clause_idx, c0,
        "positive parent should be the strengthened one"
    );
    assert_eq!(
        result.strengthened[0].new_lits.len(),
        2,
        "strengthened clause should have pivot removed"
    );
    // No resolvents should be added (the resolvent was used for OTFS).
    assert!(
        result.resolvents.is_empty(),
        "double OTFS should not add any resolvents"
    );
    // Both original clauses should be in to_delete.
    assert_eq!(result.to_delete.len(), 2);
    assert!(result.to_delete.contains(&c0));
    assert!(result.to_delete.contains(&c1));
    // Stats should record the double OTFS.
    assert_eq!(bve.stats().double_otfs, 1);
}

#[test]
fn test_bve_elimination_records_witness_entries_per_clause() {
    let mut bve = BVE::new(4);
    let mut clauses = ClauseArena::new();
    let c_pos = clauses.add(&[lit(0, true), lit(1, true)], false);
    let c_neg = clauses.add(&[lit(0, false), lit(2, true)], false);

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(result.eliminated);
    assert_eq!(result.witness_entries.len(), 2);
    assert!(
        result
            .witness_entries
            .iter()
            .any(|e| e.clause_idx == c_pos && e.witness == lit(0, true)),
        "positive occurrence must keep +pivot witness"
    );
    assert!(
        result
            .witness_entries
            .iter()
            .any(|e| e.clause_idx == c_neg && e.witness == lit(0, false)),
        "negative occurrence must keep -pivot witness"
    );
}

#[test]
fn test_bve_elimination_prunes_root_level_false_literals_from_resolvent() {
    // CaDiCaL elim.cpp:302-303: root-false literals are PRUNED from
    // resolvents. The pruned_vars vec tracks them for LRAT hint generation.
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(3, true), lit(4, true)], false);

    bve.rebuild(&clauses);

    let mut marks = LitMarks::new(5);
    let mut vals = vec![0i8; 10];
    assign_root(&mut vals, lit(1, false));
    assign_root(&mut vals, lit(3, false));

    let result = bve.try_eliminate_with_gate_with_marks(
        Variable(0),
        &clauses,
        None,
        false,
        &mut marks,
        &vals,
        u64::MAX,
    );

    assert!(
        result.eliminated,
        "elimination should be bounded with root-false literals pruned"
    );
    assert_eq!(result.resolvents.len(), 1, "expected one live resolvent");

    let (resolvent, _pos_ante, _neg_ante, pruned_vars) = &result.resolvents[0];
    // CaDiCaL: root-false literals are PRUNED from the resolvent
    assert_eq!(
        resolvent.len(),
        2,
        "root-false literals should be pruned from resolvent"
    );
    assert!(resolvent.contains(&lit(2, true)));
    assert!(resolvent.contains(&lit(4, true)));
    assert_eq!(
        pruned_vars,
        &vec![1, 3],
        "root-false literals should be tracked for LRAT hints"
    );
    assert_eq!(bve.stats().root_literals_pruned, 2);
}

#[test]
fn test_bve_elimination_skips_positive_parent_satisfied_at_root_level() {
    let mut bve = BVE::new(4);
    let mut clauses = ClauseArena::new();
    let satisfied_pos = clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(3, true)], false);

    bve.rebuild(&clauses);

    let mut marks = LitMarks::new(4);
    let mut vals = vec![0i8; 8];
    assign_root(&mut vals, lit(1, true));

    let result = bve.try_eliminate_with_gate_with_marks(
        Variable(0),
        &clauses,
        None,
        false,
        &mut marks,
        &vals,
        u64::MAX,
    );

    assert!(result.eliminated);
    assert_eq!(
        result.satisfied_parents,
        vec![satisfied_pos],
        "the root-satisfied positive parent should be skipped and marked for GC"
    );
    assert_eq!(
        result.resolvents.len(),
        1,
        "only the unsatisfied pair should resolve"
    );
    assert_eq!(bve.stats().root_satisfied_parents, 1);
}

#[test]
fn test_bve_elimination_skips_negative_parent_satisfied_at_root_level() {
    let mut bve = BVE::new(4);
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(2, true)], false);
    let satisfied_neg = clauses.add(&[lit(0, false), lit(1, true)], false);

    bve.rebuild(&clauses);

    let mut marks = LitMarks::new(4);
    let mut vals = vec![0i8; 8];
    assign_root(&mut vals, lit(1, true));

    let result = bve.try_eliminate_with_gate_with_marks(
        Variable(0),
        &clauses,
        None,
        false,
        &mut marks,
        &vals,
        u64::MAX,
    );

    assert!(result.eliminated);
    assert_eq!(
        result.satisfied_parents,
        vec![satisfied_neg],
        "the root-satisfied negative parent should be skipped and marked for GC"
    );
    assert!(
        result.resolvents.is_empty(),
        "no live resolvent should remain when the only pair is root-satisfied"
    );
    assert_eq!(bve.stats().root_satisfied_parents, 1);
}

#[test]
fn test_bve_elimination_dedups_dual_polarity_clause_entry() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();
    let c_taut = clauses.add(&[lit(0, true), lit(0, false), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(3, true)], false);

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(result.eliminated);
    assert_eq!(
        result.witness_entries.len(),
        result.to_delete.len(),
        "each deleted clause should have exactly one witness entry"
    );
    assert_eq!(
        result
            .witness_entries
            .iter()
            .filter(|e| e.clause_idx == c_taut)
            .count(),
        1,
        "dual-polarity clause should be recorded once"
    );
}

#[test]
fn test_bve_not_bounded() {
    let mut bve = BVE::new(12);

    // x0 appears in 5 positive and 5 negative clauses, yielding up to
    // 25 resolvents while only 10 clauses are removed.
    // Default growth_bound=0, so budget = 10 + 0 = 10. 25 > 10 => not bounded.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(3, true)], false);
    clauses.add(&[lit(0, true), lit(4, true)], false);
    clauses.add(&[lit(0, true), lit(5, true)], false);
    clauses.add(&[lit(0, false), lit(6, true)], false);
    clauses.add(&[lit(0, false), lit(7, true)], false);
    clauses.add(&[lit(0, false), lit(8, true)], false);
    clauses.add(&[lit(0, false), lit(9, true)], false);
    clauses.add(&[lit(0, false), lit(10, true)], false);

    bve.rebuild(&clauses);

    let result = bve.try_eliminate(Variable(0), &clauses);
    // Should not be eliminated because bounded-growth check rejects it.
    assert!(!result.eliminated);
}

#[test]
fn test_bve_run_elimination() {
    let mut bve = BVE::new(5);

    // Simple formula where x0 can be eliminated
    // x0 appears in both polarities (good candidate)
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(2, true)], false);
    clauses.add(&[lit(1, true), lit(2, false)], false); // Independent

    bve.rebuild(&clauses);

    // Verify x0 is eliminable BEFORE run_elimination modifies the arena.
    // After elimination, clauses containing x0 are deleted so the occ
    // lists no longer have both polarities — the completeness guard would
    // reject a post-hoc check.
    let mut bve_check = BVE::new(5);
    bve_check.rebuild(&clauses);
    let pre_result = bve_check.try_eliminate(Variable(0), &clauses);
    assert!(
        pre_result.eliminated,
        "x0 should be eliminable on fresh arena"
    );

    let vals = vec![0i8; 10]; // 5 vars × 2 literals, all unassigned
    let frozen: &[u32] = &[];
    let results = bve.run_elimination(&mut clauses, &vals, frozen, 1);

    // Some variable should be eliminated
    assert!(!results.is_empty());
    assert!(results.iter().any(|r| r.eliminated));
}

#[test]
fn test_bve_skip_assigned() {
    let mut bve = BVE::new(5);

    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(2, true)], false);

    bve.rebuild(&clauses);

    // x0 is assigned (positive)
    let mut vals = vec![0i8; 10]; // 5 vars × 2 literals
    vals[0] = 1; // var 0 positive literal = true
    vals[1] = -1; // var 0 negative literal = false

    let frozen: &[u32] = &[];
    let candidate = bve.find_elimination_candidate(&vals, frozen);
    // Should not select x0 since it's assigned
    assert!(candidate.is_none() || candidate.unwrap() != Variable(0));
}

/// Test that a frozen variable survives BVE round (#1479)
#[test]
fn test_bve_skip_frozen() {
    // Use exactly 3 variables to avoid extra variables with score 0
    let mut bve = BVE::new(3);

    // Set up clauses where x0 has the best score (score = pos_count * neg_count)
    // x0: pos=1, neg=1 -> score=1 (best)
    // x1: pos=2, neg=1 -> score=2
    // x2: pos=1, neg=2 -> score=2
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false); // x0+, x1+
    clauses.add(&[lit(0, false), lit(2, true)], false); // x0-, x2+
    clauses.add(&[lit(1, true), lit(2, false)], false); // x1+, x2-
    clauses.add(&[lit(1, false), lit(2, false)], false); // x1-, x2-

    bve.rebuild(&clauses);

    let vals = vec![0i8; 6]; // 3 vars × 2 literals, all unassigned

    // Without freezing, x0 should be the best candidate (score 1 vs 2 for x1, x2)
    let frozen_empty: &[u32] = &[];
    let candidate = bve.find_elimination_candidate(&vals, frozen_empty);
    assert_eq!(
        candidate,
        Some(Variable(0)),
        "x0 should be candidate when not frozen (score 1 < 2)"
    );

    // With x0 frozen, it should not be selected
    let frozen = vec![1u32, 0, 0]; // x0 has freeze count 1
    let candidate = bve.find_elimination_candidate(&vals, &frozen);
    assert!(
        candidate.is_none() || candidate.unwrap() != Variable(0),
        "frozen x0 should not be selected"
    );

    // Verify x0 survives a full BVE round when frozen
    let results = bve.run_elimination(&mut clauses, &vals, &frozen, 1);
    // x0 should not be in the eliminated list
    assert!(
        !results
            .iter()
            .any(|r| r.eliminated && r.variable == Variable(0)),
        "frozen variable should not be eliminated"
    );
}

#[test]
fn test_bve_gate_defined_variable_gets_schedule_credit() {
    let mut bve = BVE::new(5);

    let mut clauses = ClauseArena::new();
    // x0: ordinary 1×2 candidate → raw score 5.
    clauses.add(&[lit(0, true), lit(4, true)], false);
    clauses.add(&[lit(0, false), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(3, true)], false);

    // x1 = x2 ∧ x3:
    //   (x1 v ~x2 v ~x3), (~x1 v x2), (~x1 v x3)
    // Raw score is also 5, but restricted resolution skips the gate×gate
    // pairs so the scheduler should prefer x1 over the smaller-index tie.
    clauses.add(&[lit(1, true), lit(2, false), lit(3, false)], false);
    clauses.add(&[lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(1, false), lit(3, true)], false);

    bve.rebuild(&clauses);

    let vals = vec![0i8; 10];
    let mut frozen = vec![0u32; 5];
    frozen[2] = 1;
    frozen[3] = 1;
    frozen[4] = 1;

    assert_eq!(
        bve.find_elimination_candidate(&vals, &frozen),
        Some(Variable(1)),
        "gate-defined variable should outrank same-base non-gate candidate",
    );
}

#[test]
fn test_next_candidate_rechecks_frozen_after_schedule_build() {
    let mut bve = BVE::new(1);
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true)], false);
    clauses.add(&[lit(0, false)], false);

    bve.rebuild(&clauses);

    let vals = vec![0i8; 2]; // 1 var × 2 literals, unassigned
    let mut frozen = vec![0u32];
    bve.build_schedule(&vals, &frozen);
    assert_eq!(bve.schedule.len(), 1, "expected one prebuilt candidate");

    // Freeze after schedule construction; next_candidate must re-check
    // runtime eligibility and skip the frozen variable.
    frozen[0] = 1;
    assert_eq!(
        bve.next_candidate(&clauses, &vals, &frozen),
        None,
        "frozen variable should be rejected even when already scheduled"
    );
}

/// Test that an unfrozen variable can be eliminated (#1480)
#[test]
fn test_bve_unfrozen_can_eliminate() {
    let mut bve = BVE::new(5);

    // x0 and x1 are eliminable, x2 and x3 are frozen (so x1's clauses
    // won't be removed by eliminating x2/x3). x1 has clauses involving
    // frozen variables x2 and x3, ensuring x1 is still a candidate after
    // any other eliminations.
    let mut clauses = ClauseArena::new();
    // x0: (x0 ∨ x2), (¬x0 ∨ x3)
    clauses.add(&[lit(0, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(3, true)], false);
    // x1: (x1 ∨ x2), (¬x1 ∨ x3)
    clauses.add(&[lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(1, false), lit(3, true)], false);

    bve.rebuild(&clauses);

    let vals = vec![0i8; 10]; // 5 vars × 2 literals, all unassigned

    // Freeze x0, x2, x3 — only x1 and x4 are unfrozen
    let frozen = vec![1u32, 0, 1, 1, 0]; // x0,x2,x3 frozen; x1,x4 unfrozen

    // x1 should still be eliminable
    let results = bve.run_elimination(&mut clauses, &vals, &frozen, 10);

    // x1 should be eliminated specifically (not just "some variable")
    assert!(
        results
            .iter()
            .any(|r| r.eliminated && r.variable == Variable(1)),
        "x1 should be eliminated (unfrozen)"
    );
    assert!(
        !results
            .iter()
            .any(|r| r.eliminated && r.variable == Variable(0)),
        "x0 should NOT be eliminated (frozen)"
    );
}

/// Test nested freeze (count > 1) still protects variable
#[test]
fn test_bve_nested_freeze() {
    // Use exactly 3 variables to avoid extra variables with score 0
    let mut bve = BVE::new(3);

    // Set up clauses where x0 has the best score (score = pos_count * neg_count)
    // Same setup as test_bve_skip_frozen to ensure x0 is preferred when unfrozen
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false); // x0+, x1+
    clauses.add(&[lit(0, false), lit(2, true)], false); // x0-, x2+
    clauses.add(&[lit(1, true), lit(2, false)], false); // x1+, x2-
    clauses.add(&[lit(1, false), lit(2, false)], false); // x1-, x2-

    bve.rebuild(&clauses);

    let vals = vec![0i8; 6]; // 3 vars × 2 literals, all unassigned

    // x0 is frozen twice (nested freeze)
    let frozen = vec![2u32, 0, 0];
    let candidate = bve.find_elimination_candidate(&vals, &frozen);
    assert!(
        candidate.is_none() || candidate.unwrap() != Variable(0),
        "nested frozen x0 should not be selected"
    );

    // x0 melted once (still frozen with count 1)
    let frozen_once = vec![1u32, 0, 0];
    let candidate = bve.find_elimination_candidate(&vals, &frozen_once);
    assert!(
        candidate.is_none() || candidate.unwrap() != Variable(0),
        "partially melted x0 should still not be selected"
    );

    // x0 fully melted (count 0)
    let frozen_none = vec![0u32, 0, 0];
    let candidate = bve.find_elimination_candidate(&vals, &frozen_none);
    assert_eq!(
        candidate,
        Some(Variable(0)),
        "fully melted x0 should be eliminable (score 1 < 2)"
    );
}

#[test]
fn test_bve_stats() {
    let mut bve = BVE::new(5);

    // Create a formula where only x0 can be eliminated
    // x0 appears in both polarities, x1 and x2 also appear in both
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(2, true)], false);
    clauses.add(&[lit(1, false), lit(2, false)], false); // Makes x1, x2 also balanced

    bve.rebuild(&clauses);

    let vals = vec![0i8; 10]; // 5 vars × 2 literals, all unassigned
    let frozen: &[u32] = &[];
    let _ = bve.run_elimination(&mut clauses, &vals, frozen, 1);

    let stats = bve.stats();
    // At least one variable should be eliminated
    assert!(
        stats.vars_eliminated >= 1,
        "At least one var should be eliminated"
    );
    assert!(
        stats.clauses_removed >= 2,
        "At least 2 clauses should be removed"
    );
    assert_eq!(stats.rounds, 1, "Should run 1 round");
}

#[test]
fn test_bve_restricted_resolution_gate_vs_non_gate() {
    let mut bve = BVE::new(4);

    // x0 <-> x1 (gate clauses), plus two non-gate clauses containing x0:
    // (x0 v ~x1) (gate)
    // (~x0 v x1) (gate)
    // (x0 v x2) (non-gate)
    // (~x0 v x3) (non-gate)
    let mut clauses = ClauseArena::new();
    let g0 = clauses.add(&[lit(0, true), lit(1, false)], false);
    let g1 = clauses.add(&[lit(0, false), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(3, true)], false);

    bve.rebuild(&clauses);

    let result = bve.try_eliminate_with_gate(Variable(0), &clauses, Some(&[g0, g1]), false);
    assert!(result.eliminated);

    // Restricted resolution produces cross-resolvents (gate × non-gate):
    //   (x0, ~x1) × (~x0, x3) → (~x1, x3)
    //   (~x0, x1) × (x0, x2)  → (x1, x2)
    //
    // CaDiCaL elim.cpp:501: non-gate × non-gate pairs are NEVER resolved
    // when a gate exists. The gate + gate×non-gate resolvents are
    // equisatisfiable with the original formula.
    let mut has_x1_x2 = false;
    let mut has_not_x1_x3 = false;
    let mut has_x2_x3 = false;

    for (r, _, _, _) in &result.resolvents {
        if r.len() == 2 && r.contains(&lit(1, true)) && r.contains(&lit(2, true)) {
            has_x1_x2 = true;
        }
        if r.len() == 2 && r.contains(&lit(1, false)) && r.contains(&lit(3, true)) {
            has_not_x1_x3 = true;
        }
        if r.len() == 2 && r.contains(&lit(2, true)) && r.contains(&lit(3, true)) {
            has_x2_x3 = true;
        }
    }

    assert!(has_x1_x2, "cross-resolvent (x1, x2) must be produced");
    assert!(has_not_x1_x3, "cross-resolvent (~x1, x3) must be produced");
    assert!(
        has_x2_x3,
        "full-resolution fallback must produce non-gate×non-gate resolvent (x2, x3)"
    );
}

#[test]
fn test_bve_restricted_resolution_optionally_resolves_gate_pairs() {
    let mut clauses = ClauseArena::new();
    let g0 = clauses.add(&[lit(0, true), lit(1, true)], false);
    let g1 = clauses.add(&[lit(0, false), lit(2, true)], false);

    let mut bve_without_gate_pairs = BVE::new(3);
    bve_without_gate_pairs.rebuild(&clauses);
    let without_gate_pairs = bve_without_gate_pairs.try_eliminate_with_gate(
        Variable(0),
        &clauses,
        Some(&[g0, g1]),
        false,
    );
    assert!(without_gate_pairs.eliminated);
    assert!(
        without_gate_pairs.resolvents.is_empty(),
        "restricted resolution should skip gate×gate pairs by default"
    );

    let mut bve_with_gate_pairs = BVE::new(3);
    bve_with_gate_pairs.rebuild(&clauses);
    let with_gate_pairs =
        bve_with_gate_pairs.try_eliminate_with_gate(Variable(0), &clauses, Some(&[g0, g1]), true);
    assert!(with_gate_pairs.eliminated);
    assert_eq!(with_gate_pairs.resolvents.len(), 1);

    let (resolvent, _pos_ante, _neg_ante, _pruned_vars) = &with_gate_pairs.resolvents[0];
    assert_eq!(resolvent.len(), 2);
    assert!(resolvent.contains(&lit(1, true)));
    assert!(resolvent.contains(&lit(2, true)));
}

#[test]
fn test_bve_gate_resolution_with_subsumption_adds_fewer_resolvents_than_naive() {
    let mut clauses = ClauseArena::new();
    let g0 = clauses.add(&[lit(0, true), lit(1, false)], false);
    let g1 = clauses.add(&[lit(0, false), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(3, true)], false);
    clauses.add(&[lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(1, false), lit(3, true)], false);

    let mut naive = BVE::new(4);
    naive.rebuild(&clauses);
    let naive_result = naive.try_eliminate(Variable(0), &clauses);
    assert!(naive_result.eliminated);
    assert_eq!(
        naive_result.resolvents.len(),
        3,
        "full resolution should keep all 3 non-tautological resolvents",
    );

    let mut gated = BVE::new(4);
    gated.rebuild(&clauses);
    let gated_result = gated.try_eliminate_with_gate(Variable(0), &clauses, Some(&[g0, g1]), false);
    assert!(gated_result.eliminated);
    // SOUNDNESS CLAMP (inc1): x0 has non-gate clauses on both polarity sides, so
    // gate restriction is unsound for reconstruction → fall back to FULL
    // resolution. The gated result therefore matches naive full resolution.
    // (Gate restriction's resolvent savings are kept only for pure-gate vars.)
    assert_eq!(
        gated_result.resolvents.len(),
        naive_result.resolvents.len(),
        "mixed-gate variable falls back to full resolution (== naive)",
    );
}

#[test]
fn test_bve_mark_failed_does_not_blacklist() {
    let mut bve = BVE::new(2);

    bve.mark_failed(Variable(1));

    assert!(
        !bve.is_eliminated(Variable(1)),
        "failed elimination must not permanently blacklist a variable"
    );
}

#[test]
fn test_resolvent_budget_fastelim_uses_min_bound() {
    let mut bve = BVE::new(2);
    bve.set_growth_bound(8);

    // CaDiCaL fastelim: bound = min(fastelimbound, pos+neg).
    // elimfast.cpp:71-79: resolvent count is capped at the bound.
    // When clauses_removed < growth_bound, budget = clauses_removed.
    // When clauses_removed > growth_bound, budget = growth_bound (caps resolvents).
    assert_eq!(bve.resolvent_budget(3), 3);
    assert_eq!(bve.resolvent_budget(12), 8);
}

#[test]
fn test_additive_fastelim_lever_uses_additive_budget_in_pass1() {
    // Lever AY_AB_BVE_ADDITIVE_FASTELIM: Pass-1 fastelim adopts kissat's
    // additive budget removed+bound; Pass-0 quick stays no-growth (min).
    let mut bve = BVE::new(2);
    assert!(!bve.is_additive_fastelim(), "default OFF");
    bve.set_additive_fastelim(true);
    bve.set_growth_bound(16);

    // Pass 1 (fastelim, NOT quick): additive removed+bound.
    assert_eq!(bve.resolvent_budget(3), 3 + 16, "additive: 3 + 16");
    assert_eq!(bve.resolvent_budget(12), 12 + 16, "additive: 12 + 16");

    // Pass 0 (quick) must stay no-growth even with the lever ON, so the
    // free-elimination pre-pass is unaffected.
    bve.set_quick_elim_mode(true);
    assert_eq!(bve.resolvent_budget(3), 3, "quick stays min: min(3,16)=3");
    assert_eq!(
        bve.resolvent_budget(30),
        16,
        "quick stays min: min(30,16)=16"
    );
    bve.set_quick_elim_mode(false);

    // Lever OFF restores CaDiCaL no-growth min in Pass 1.
    bve.set_additive_fastelim(false);
    assert_eq!(bve.resolvent_budget(30), 16, "lever OFF: min(30,16)=16");
}

#[test]
fn test_additive_fastelim_band_gated_default_by_num_vars() {
    // Banded default (wf_e2bdf6e1): with no AY_AB_BVE_ADDITIVE_FASTELIM
    // override, additive is ACTIVE only above the 200K band edge
    // (= PREPROCESS_EXPENSIVE_MAX_VARS). Below/at the edge stays CaDiCaL
    // no-growth baseline (6f354fbe 48K regression sentinel); above it captures
    // the ebbda8d9 723K UNKNOWN -> cake_lpr-VERIFIED UNSAT flip.
    //
    // NOTE: like the sibling lever test, this assumes the process env leaves
    // AY_AB_BVE_ADDITIVE_FASTELIM / AY_BVE_ADDITIVE_MIN_VARS unset (as the
    // suite is run under the gate harness).
    assert!(
        !BVE::new(48_032).is_additive_fastelim(),
        "6f354fbe 48K sentinel below band: baseline (no-growth)"
    );
    assert!(
        !BVE::new(200_000).is_additive_fastelim(),
        "exactly at the 200K edge stays baseline (strict >)"
    );
    assert!(
        BVE::new(200_001).is_additive_fastelim(),
        "one var above the edge: additive active"
    );
    assert!(
        BVE::new(723_395).is_additive_fastelim(),
        "ebbda8d9 723K above band: additive active (captures the flip)"
    );
}

#[test]
fn test_increment_growth_bound_switches_to_additive_budget() {
    let mut bve = BVE::new(2);
    bve.set_growth_bound(8);
    // Fastelim: budget = min(clauses_removed, growth_bound)
    assert_eq!(bve.resolvent_budget(12), 8);

    // First increment from fastelim mode resets to 0 (CaDiCaL: elimboundmin=0).
    // This prevents the fastelim bound (8) from leaking into inprocessing (#7178).
    bve.increment_growth_bound();
    assert_eq!(bve.growth_bound, 0);
    // Inprocessing: budget = clauses_removed + growth_bound = 12 + 0 = 12
    assert_eq!(bve.resolvent_budget(12), 12);

    // Second increment (already in additive mode): 0 -> 1.
    bve.increment_growth_bound();
    assert_eq!(bve.growth_bound, 1);
    assert_eq!(bve.resolvent_budget(12), 13);

    // Third increment doubles the adaptive inprocessing bound: 1 -> 2.
    bve.increment_growth_bound();
    assert_eq!(bve.growth_bound, 2);
    assert_eq!(bve.resolvent_budget(12), 14);
}

/// Verify that re-calling `set_growth_bound(8)` after `increment_growth_bound()`
/// restores fastelim semantics. This is the preprocessing multi-round path:
/// each preprocessing round calls `set_growth_bound(8)`, a successful BVE
/// round calls `increment_growth_bound()` (which resets to additive bound 0),
/// and the next preprocessing round must re-enable fastelim via
/// `set_growth_bound(8)`.
#[test]
fn test_set_growth_bound_after_increment_restores_fastelim() {
    let mut bve = BVE::new(2);

    // Round 1: preprocessing sets fastelim bound
    bve.set_growth_bound(8);
    // Fastelim: budget = min(clauses_removed, growth_bound)
    assert_eq!(bve.resolvent_budget(5), 5, "fastelim: min(5,8)=5");
    assert_eq!(bve.resolvent_budget(12), 8, "fastelim: min(12,8)=8");

    // After successful BVE round, increment resets to additive bound 0 (#7178).
    bve.increment_growth_bound();
    assert_eq!(bve.growth_bound, 0);
    assert_eq!(bve.resolvent_budget(5), 5, "additive: 5 + 0 = 5");

    // Round 2: preprocessing re-sets fastelim bound
    bve.set_growth_bound(8);
    assert_eq!(bve.growth_bound, 8, "growth_bound reset to 8");
    assert_eq!(bve.resolvent_budget(5), 5, "fastelim restored: min(5,8)=5");
    assert_eq!(
        bve.resolvent_budget(12),
        8,
        "fastelim restored: min(12,8)=8"
    );
}

#[test]
fn test_bve_global_clause_growth_limit_rejects_more_than_ten_percent_growth() {
    // The 10% per-elimination growth guard only activates on formulas with
    // >= 100 active clauses. For smaller formulas, the resolvent budget
    // (clauses_removed + growth_bound) is the sole control.
    //
    // Build a 105-clause formula where eliminating variable 0 would produce
    // net growth > 10% of active clauses (> 10 clauses).
    // Variable 0: 2 positive x 15 negative = 30 resolvents, 17 deleted = +13 growth.
    // 13 * 10 = 130 > 105 => rejected by 10% guard.
    let num_vars = 200;
    let mut bve = BVE::new(num_vars);
    // Set a large growth bound so the resolvent budget doesn't reject first.
    bve.set_growth_bound(16);
    bve.increment_growth_bound(); // fastelim -> additive, reset to 0
    for _ in 0..5 {
        bve.increment_growth_bound(); // 0->1->2->4->8->16
    }

    let mut clauses = ClauseArena::new();
    // 2 positive occurrences of variable 0
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);
    // 15 negative occurrences of variable 0 (vars 3..17)
    for i in 0..15 {
        clauses.add(&[lit(0, false), lit(3 + i, true)], false);
    }
    // Padding: 88 clauses not involving variable 0 (vars 100..199).
    for i in 0..88 {
        clauses.add(
            &[lit(100 + i, true), lit(100 + (i + 1) % 100, false)],
            false,
        );
    }

    let active = clauses.active_clause_count();
    assert!(
        active >= 100,
        "need >= 100 active clauses for 10% guard to activate, got {active}"
    );

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(
        !result.eliminated,
        "2x15 elimination would grow the {active}-clause formula by 13 (+12%), so it must be skipped",
    );
}

/// Verify that reset_growth_bound_for_inprocessing() restores fresh
/// inprocessing state after preprocessing fastelim.
///
/// CaDiCaL keeps fastelimbound (8) and elimbound (starts at 0) as
/// separate values. AY uses one growth_bound field. Calling
/// increment_growth_bound() while in fastelim mode transitions to
/// inprocessing by resetting bound to 0, preventing the pos+neg+8
/// resolvent bloat described in #7178.
#[test]
fn test_reset_growth_bound_for_inprocessing_after_fastelim() {
    let mut bve = BVE::new(2);

    // Preprocessing: fastelim mode with bound=8
    bve.set_growth_bound(8);
    assert!(bve.is_fastelim_mode());
    assert_eq!(bve.growth_bound(), 8);

    // Successful preprocessing round → increment transitions to inprocessing
    // by resetting bound to 0 (CaDiCaL: fastelim→elim transition).
    bve.increment_growth_bound();
    assert_eq!(bve.growth_bound(), 0, "fastelim→inprocessing resets to 0");
    assert!(!bve.is_fastelim_mode());

    // First inprocessing round: strict budget (pos+neg+0 = pos+neg)
    assert_eq!(bve.resolvent_budget(10), 10, "additive: 10 + 0 = 10");

    // After successful inprocessing round: 0 -> 1
    bve.increment_growth_bound();
    assert_eq!(bve.growth_bound(), 1);
    assert_eq!(bve.resolvent_budget(10), 11, "additive: 10 + 1 = 11");

    // Next round doubles the bound: 1 -> 2.
    bve.increment_growth_bound();
    assert_eq!(bve.growth_bound(), 2);
    assert_eq!(bve.resolvent_budget(10), 12, "additive: 10 + 2 = 12");
}

/// Verify that a variable which fails bounded elimination in one round
/// becomes eligible again in the next round after `rebuild()`.
///
/// CaDiCaL drains its schedule exactly once per round (elim.cpp), so
/// within-round retry doesn't apply. The `schedule_built` guard
/// (#3506) prevents infinite schedule rebuilds within a round. Retry
/// happens across rounds because `mark_failed` is a no-op (#3464) and
/// `rebuild()` constructs a fresh schedule.
#[test]
fn test_bve_retries_failed_candidate_after_neighbor_elimination() {
    let mut bve = BVE::new(11);
    let mut clauses = ClauseArena::new();

    // x0: 3 positive × 2 negative = up to 6 resolvents for 5 clauses.
    // With growth_bound=0, 6 > 5+0 → fails bounded check. Score = 3×2 = 6.
    clauses.add(&[lit(0, true), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(3, true)], false);
    clauses.add(&[lit(0, true), lit(4, true)], false);
    clauses.add(&[lit(0, false), lit(5, true)], false);
    clauses.add(&[lit(0, false), lit(6, true)], false);

    // x1/x7: high-score neighbor candidates with tautological resolvents.
    // Score = 3×3 = 9 (> 6, so x0 comes first in the schedule).
    // All 9 resolvents are tautological (contain x7 and ~x7), so bounded
    // check passes: 0 actual resolvents ≤ 6+0.
    clauses.add(&[lit(1, true), lit(7, true)], false);
    clauses.add(&[lit(1, true), lit(7, true), lit(8, true)], false);
    clauses.add(&[lit(1, true), lit(7, true), lit(9, true)], false);
    clauses.add(&[lit(1, false), lit(7, false)], false);
    clauses.add(&[lit(1, false), lit(7, false), lit(8, true)], false);
    clauses.add(&[lit(1, false), lit(7, false), lit(10, true)], false);

    bve.rebuild(&clauses);
    let vals = vec![0i8; 22]; // 11 vars × 2 literals, all unassigned

    // Freeze auxiliary variables (x2-x6, x8-x10) to prevent pure elimination
    // from destroying x0's clauses before x0 is tried. This isolates the
    // retry-across-rounds behavior being tested.
    let mut frozen = vec![0u32; 11];
    for &v in &[2, 3, 4, 5, 6, 8, 9, 10] {
        frozen[v] = 1;
    }

    // Round 1: x0 has the lowest score (6) among non-frozen candidates.
    let cand = bve
        .next_candidate(&clauses, &vals, &frozen)
        .expect("expected BVE candidate");
    assert_eq!(cand, Variable(0), "x0 should be first candidate (score 6)");
    let result = bve.try_eliminate(cand, &clauses);
    assert!(
        !result.eliminated,
        "x0 should fail bounded check (3×2=6 > 5+0)"
    );
    bve.mark_failed(cand);

    // Neighbor succeeds (all resolvents are tautological).
    let neighbor = bve
        .next_candidate(&clauses, &vals, &frozen)
        .expect("expected fallback candidate after x0 failure");
    assert_ne!(
        neighbor,
        Variable(0),
        "expected a different neighbor candidate after x0 failure"
    );
    let neighbor_result = bve.try_eliminate(neighbor, &clauses);
    assert!(
        neighbor_result.eliminated,
        "neighbor elimination should succeed (all resolvents tautological)"
    );
    bve.update_occs_after_elimination(&neighbor_result.to_delete, &clauses);
    for &idx in &neighbor_result.to_delete {
        clauses.delete(idx);
    }

    // Round 2: rebuild constructs a fresh schedule. Previously failed x0
    // becomes eligible again.
    bve.rebuild(&clauses);

    let mut found_x0 = false;
    while let Some(cand) = bve.next_candidate(&clauses, &vals, &frozen) {
        if cand == Variable(0) {
            found_x0 = true;
            break;
        }
        let r = bve.try_eliminate(cand, &clauses);
        if r.eliminated {
            bve.update_occs_after_elimination(&r.to_delete, &clauses);
            for &idx in &r.to_delete {
                clauses.delete(idx);
            }
        } else {
            bve.mark_failed(cand);
        }
    }
    assert!(
        found_x0,
        "failed variable x0 should reappear after rebuild (cross-round retry)"
    );
}

/// Double OTFS (CaDiCaL elim.cpp:413-424): when the resolvent subsumes
/// BOTH antecedent clauses, strengthen one and let the other be deleted.
/// Both parents are identical except for the pivot polarity.
#[test]
fn test_bve_double_otfs_strengthens_one_deletes_other() {
    let mut bve = BVE::new(4);

    // C0: ( x0 v x1 v x2)  — pos occurrence of x0
    // C1: (~x0 v x1 v x2)  — neg occurrence of x0
    // Resolvent: (x1 v x2), which subsumes BOTH C0 and C1.
    //
    // Expected (CaDiCaL double OTFS):
    //   - Strengthen C0 → (x1 v x2) (remove pivot x0)
    //   - C1 is NOT strengthened (will be garbage-collected via to_delete)
    //   - No resolvent added to the result
    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    let c1 = clauses.add(&[lit(0, false), lit(1, true), lit(2, true)], false);

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(result.eliminated, "x0 should be eliminable");

    // Only ONE parent should be strengthened (the positive one).
    assert_eq!(
        result.strengthened.len(),
        1,
        "double OTFS should strengthen exactly one parent, got: {:?}",
        result.strengthened,
    );
    assert_eq!(
        result.strengthened[0].clause_idx, c0,
        "positive parent should be the strengthened one"
    );
    assert_eq!(
        result.strengthened[0].new_lits.len(),
        2,
        "strengthened clause should have pivot removed"
    );

    // The negative parent (c1) should NOT be in strengthened — it will be
    // deleted via to_delete.
    assert!(
        !result.strengthened.iter().any(|s| s.clause_idx == c1),
        "negative parent should NOT be strengthened in double OTFS"
    );
    assert!(
        result.to_delete.contains(&c1),
        "negative parent should be in to_delete list"
    );

    // No resolvents should be added (the resolvent was consumed by OTFS).
    assert!(
        result.resolvents.is_empty(),
        "double OTFS should not produce any counted resolvents"
    );
}

// ---- Signature-based BVE filtering tests (issue #7922) ----

/// When two clauses share no non-pivot variables, the 64-bit signature filter
/// guarantees no tautological resolvent. The fast path should be used.
#[test]
fn test_sig_fast_path_used_for_non_overlapping_clauses() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();

    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(2, true)], false);

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(result.eliminated, "x0 should be eliminable");
    assert_eq!(result.resolvents.len(), 1, "one resolvent expected");
    assert!(
        bve.stats().sig_fast_path >= 1,
        "signature fast path should fire for non-overlapping clauses, got {}",
        bve.stats().sig_fast_path
    );
}

/// When two clauses share a variable in opposite polarity (other than the
/// pivot), the full mark-based path should be used for that pair.
#[test]
fn test_sig_slow_path_used_for_overlapping_clauses() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();

    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(1, false)], false);
    clauses.add(&[lit(0, false), lit(2, true)], false);

    bve.rebuild(&clauses);

    let before = bve.stats().sig_fast_path;
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(result.eliminated, "x0 should be eliminable");
    assert_eq!(
        bve.stats().sig_fast_path - before,
        1,
        "only the non-tautological pair should use the fast path"
    );
    assert!(
        bve.stats().tautologies_skipped >= 1,
        "tautological pair should be detected"
    );
}

/// Verify resolve_without_tautology_checks produces same resolvent as full
/// resolution for non-tautological cases.
#[test]
fn test_resolve_without_tautology_checks_matches_full_resolution() {
    let mut bve = BVE::new(6);

    let c0 = vec![lit(0, true), lit(1, true), lit(3, true)];
    let c1 = vec![lit(0, false), lit(2, true), lit(4, true)];

    let full_result = bve.resolve(&c0, &c1, Variable(0));
    assert!(full_result.is_some(), "should produce a resolvent");

    let resolvent = full_result.unwrap();
    assert_eq!(resolvent.len(), 4, "resolvent should have 4 literals");
    assert!(resolvent.contains(&lit(1, true)));
    assert!(resolvent.contains(&lit(3, true)));
    assert!(resolvent.contains(&lit(2, true)));
    assert!(resolvent.contains(&lit(4, true)));
}

/// Shared same-polarity variables produce correct resolvent without duplication.
#[test]
fn test_resolve_without_tautology_checks_handles_shared_same_polarity() {
    let mut bve = BVE::new(5);

    let c0 = vec![lit(0, true), lit(1, true), lit(2, true)];
    let c1 = vec![lit(0, false), lit(1, true), lit(3, true)];

    let result = bve.resolve(&c0, &c1, Variable(0));
    assert!(result.is_some(), "should produce a resolvent");

    let resolvent = result.unwrap();
    assert_eq!(
        resolvent.len(),
        3,
        "resolvent should have 3 literals (no dup)"
    );
    assert!(resolvent.contains(&lit(1, true)));
    assert!(resolvent.contains(&lit(2, true)));
    assert!(resolvent.contains(&lit(3, true)));
}

/// Signature popcount is bounded by 64 bits.
#[test]
fn test_sig_popcount_bounded() {
    use crate::clause::compute_clause_signature;

    let many_pos_lits: Vec<Literal> = (0..40).map(|i| lit(i, true)).collect();
    let many_neg_lits: Vec<Literal> = (40..80).map(|i| lit(i, true)).collect();

    let sig_pos = compute_clause_signature(&many_pos_lits);
    let sig_neg = compute_clause_signature(&many_neg_lits);
    let combined = sig_pos | sig_neg;

    assert!(combined.count_ones() <= 64);
    assert!(
        combined.count_ones() >= 30,
        "80 variables should produce high popcount, got {}",
        combined.count_ones()
    );
}

// ========================================================================
// Soundness regression sweep after BVE restricted resolution fix (#7903)
// ========================================================================

// ---- Binary-clause-only patterns ----

/// BVE on a formula consisting entirely of binary clauses.
/// Variable x0 appears in 2 binary clauses (one pos, one neg).
/// Resolvent is a single binary clause: {x1, x2}.
/// Soundness: the resolvent must contain exactly {x1, x2}
/// and no reference to the eliminated variable x0.
#[test]
fn test_bve_soundness_binary_clauses_only_simple() {
    let mut bve = BVE::new(4);
    let mut clauses = ClauseArena::new();
    // (x0 v x1), (~x0 v x2)
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(2, true)], false);

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(
        result.eliminated,
        "x0 should be eliminable from binary-only formula"
    );
    assert_eq!(
        result.to_delete.len(),
        2,
        "both binary parents must be deleted"
    );
    assert_eq!(result.resolvents.len(), 1, "one resolvent expected");

    let (resolvent, _, _, _) = &result.resolvents[0];
    assert_eq!(resolvent.len(), 2, "resolvent should be binary");
    assert!(
        resolvent.contains(&lit(1, true)),
        "resolvent must contain x1"
    );
    assert!(
        resolvent.contains(&lit(2, true)),
        "resolvent must contain x2"
    );
    assert!(
        resolvent.iter().all(|l| l.variable() != Variable(0)),
        "resolvent must not contain eliminated variable x0"
    );
}

/// BVE with multiple binary clauses per polarity.
/// x0 has 2 positive and 2 negative binary clauses = 4 resolvents.
/// All variables are distinct, so no tautologies.
#[test]
fn test_bve_soundness_binary_clauses_multiple_occurrences() {
    let mut bve = BVE::new(6);
    let mut clauses = ClauseArena::new();
    // Positive: (x0 v x1), (x0 v x2)
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);
    // Negative: (~x0 v x3), (~x0 v x4)
    clauses.add(&[lit(0, false), lit(3, true)], false);
    clauses.add(&[lit(0, false), lit(4, true)], false);

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(
        result.eliminated,
        "x0 should be eliminable (4 resolvents <= 4 removed)"
    );
    assert_eq!(result.to_delete.len(), 4);
    assert_eq!(
        result.resolvents.len(),
        4,
        "2x2 = 4 non-tautological resolvents"
    );

    // Verify no resolvent contains x0
    for (resolvent, _, _, _) in &result.resolvents {
        assert!(
            resolvent.iter().all(|l| l.variable() != Variable(0)),
            "resolvent must not reference eliminated variable x0: {resolvent:?}"
        );
        assert_eq!(resolvent.len(), 2, "each resolvent should be binary");
    }

    // Verify all expected resolvents exist: {x1,x3}, {x1,x4}, {x2,x3}, {x2,x4}
    let expected = [
        (lit(1, true), lit(3, true)),
        (lit(1, true), lit(4, true)),
        (lit(2, true), lit(3, true)),
        (lit(2, true), lit(4, true)),
    ];
    for (a, b) in &expected {
        assert!(
            result
                .resolvents
                .iter()
                .any(|(r, _, _, _)| r.contains(a) && r.contains(b)),
            "expected resolvent ({a:?}, {b:?}) not found"
        );
    }
}

/// Binary clauses where one resolution pair is tautological.
/// (x0 v x1), (~x0 v ~x1) -- resolvent would be {x1, ~x1} = tautology
/// (x0 v x2), (~x0 v x3)
/// Tautological pair is skipped; non-tautological resolvents kept.
#[test]
fn test_bve_soundness_binary_with_tautological_pair() {
    let mut bve = BVE::new(4);
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(1, false)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(3, true)], false);

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(result.eliminated, "x0 should be eliminable");
    assert_eq!(result.to_delete.len(), 4);

    // 2 pos x 2 neg = 4 pairs, but (x0,x1) x (~x0,~x1) is tautological
    assert!(
        bve.stats().tautologies_skipped >= 1,
        "at least one tautological resolvent should be skipped"
    );
    // All produced resolvents must not contain x0
    for (resolvent, _, _, _) in &result.resolvents {
        assert!(
            resolvent.iter().all(|l| l.variable() != Variable(0)),
            "resolvent must not reference eliminated variable: {resolvent:?}"
        );
    }
}

// ---- Ternary clause patterns ----

/// BVE with ternary clauses only.
/// (x0 v x1 v x2), (~x0 v x3 v x4)
/// Resolvent: {x1, x2, x3, x4} -- a 4-literal clause.
#[test]
fn test_bve_soundness_ternary_clauses_only() {
    let mut bve = BVE::new(6);
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(3, true), lit(4, true)], false);

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(
        result.eliminated,
        "x0 should be eliminable from ternary-only formula"
    );
    assert_eq!(result.to_delete.len(), 2);
    assert_eq!(result.resolvents.len(), 1);

    let (resolvent, _, _, _) = &result.resolvents[0];
    assert_eq!(
        resolvent.len(),
        4,
        "resolvent of two ternary clauses should have 4 literals"
    );
    assert!(resolvent.contains(&lit(1, true)));
    assert!(resolvent.contains(&lit(2, true)));
    assert!(resolvent.contains(&lit(3, true)));
    assert!(resolvent.contains(&lit(4, true)));
    assert!(
        resolvent.iter().all(|l| l.variable() != Variable(0)),
        "resolvent must not contain eliminated variable"
    );
}

/// BVE with ternary clauses sharing a non-pivot variable.
/// (x0 v x1 v x2), (~x0 v x1 v x3)
/// Resolvent: {x1, x2, x3} (x1 appears once, deduplicated).
#[test]
fn test_bve_soundness_ternary_shared_variable() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(3, true)], false);

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(result.eliminated);
    assert_eq!(result.resolvents.len(), 1);

    let (resolvent, _, _, _) = &result.resolvents[0];
    assert_eq!(
        resolvent.len(),
        3,
        "shared variable x1 must be deduplicated"
    );
    assert!(resolvent.contains(&lit(1, true)));
    assert!(resolvent.contains(&lit(2, true)));
    assert!(resolvent.contains(&lit(3, true)));
}

/// BVE with multiple ternary clauses per polarity.
/// 2 positive ternary x 2 negative ternary = 4 resolvents.
/// All non-pivot variables distinct => no tautologies, no deduplication.
#[test]
fn test_bve_soundness_ternary_multiple_per_polarity() {
    let mut bve = BVE::new(10);
    let mut clauses = ClauseArena::new();
    // Positive: (x0 v x1 v x2), (x0 v x3 v x4)
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(3, true), lit(4, true)], false);
    // Negative: (~x0 v x5 v x6), (~x0 v x7 v x8)
    clauses.add(&[lit(0, false), lit(5, true), lit(6, true)], false);
    clauses.add(&[lit(0, false), lit(7, true), lit(8, true)], false);

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(
        result.eliminated,
        "x0 should be eliminable (4 resolvents <= 4 removed)"
    );
    assert_eq!(result.to_delete.len(), 4);
    assert_eq!(result.resolvents.len(), 4, "2x2 = 4 resolvents expected");

    for (resolvent, _, _, _) in &result.resolvents {
        assert_eq!(resolvent.len(), 4, "each resolvent should have 4 literals");
        assert!(
            resolvent.iter().all(|l| l.variable() != Variable(0)),
            "resolvent must not reference eliminated variable"
        );
    }
}

// ---- Gate detection: success vs failure ----

/// Gate detection succeeds: x0 = AND(x1, x2) encoded as:
///   (x0 v ~x1 v ~x2), (~x0 v x1), (~x0 v x2)
/// Plus a non-gate clause (x0 v x3).
/// Restricted resolution skips gate x gate pairs and produces only
/// gate x non-gate cross resolvents.
#[test]
fn test_bve_soundness_gate_detection_succeeds_and_gate() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();
    // Gate clauses for x0 = AND(x1, x2):
    let g0 = clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    let g1 = clauses.add(&[lit(0, false), lit(1, true)], false);
    let g2 = clauses.add(&[lit(0, false), lit(2, true)], false);
    // Non-gate clause:
    clauses.add(&[lit(0, true), lit(3, true)], false);

    bve.rebuild(&clauses);
    let result = bve.try_eliminate_with_gate(
        Variable(0),
        &clauses,
        Some(&[g0, g1, g2]),
        false, // skip gate x gate pairs
    );

    assert!(result.eliminated, "gate-detected x0 should be eliminable");
    assert_eq!(
        result.to_delete.len(),
        4,
        "all 4 clauses containing x0 deleted"
    );

    // All resolvents must not contain x0
    for (resolvent, _, _, _) in &result.resolvents {
        assert!(
            resolvent.iter().all(|l| l.variable() != Variable(0)),
            "resolvent must not reference eliminated variable: {resolvent:?}"
        );
    }

    // Cross-resolvents: gate x non-gate only.
    // g1=(~x0, x1) x (x0, x3) => (x1, x3)
    // g2=(~x0, x2) x (x0, x3) => (x2, x3)
    let mut has_x1_x3 = false;
    let mut has_x2_x3 = false;
    for (r, _, _, _) in &result.resolvents {
        if r.contains(&lit(1, true)) && r.contains(&lit(3, true)) {
            has_x1_x3 = true;
        }
        if r.contains(&lit(2, true)) && r.contains(&lit(3, true)) {
            has_x2_x3 = true;
        }
    }
    assert!(has_x1_x3, "cross-resolvent (x1, x3) must be produced");
    assert!(has_x2_x3, "cross-resolvent (x2, x3) must be produced");
}

/// Gate detection fails (no gate structure): BVE falls back to full resolution.
/// Compare resolvent count between gated and non-gated elimination.
#[test]
fn test_bve_soundness_gate_detection_fails_full_resolution() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();
    // No gate structure: x0 in assorted clauses, no functional definition
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(3, true)], false);
    clauses.add(&[lit(0, false), lit(4, true)], false);

    bve.rebuild(&clauses);
    // No gate clauses provided => full resolution
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(
        result.eliminated,
        "x0 should be eliminable with full resolution"
    );
    assert_eq!(result.to_delete.len(), 4);
    assert_eq!(
        result.resolvents.len(),
        4,
        "full resolution: 2x2 = 4 resolvents (no gate skip)"
    );

    for (resolvent, _, _, _) in &result.resolvents {
        assert!(
            resolvent.iter().all(|l| l.variable() != Variable(0)),
            "resolvent must not contain eliminated variable"
        );
    }
}

/// Gate detected on equivalence x0 <-> x1, with non-gate clauses on both
/// sides. The has_incomplete_gate safety produces non-gate x non-gate
/// resolvents as well as cross resolvents.
#[test]
fn test_bve_soundness_gate_equivalence_restricted_resolution() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();
    // Equivalence gate: x0 <-> x1
    let g0 = clauses.add(&[lit(0, true), lit(1, false)], false);
    let g1 = clauses.add(&[lit(0, false), lit(1, true)], false);
    // Non-gate clauses on BOTH polarity sides:
    clauses.add(&[lit(0, true), lit(2, true)], false); // pos non-gate
    clauses.add(&[lit(0, false), lit(3, true)], false); // neg non-gate

    bve.rebuild(&clauses);
    let result = bve.try_eliminate_with_gate(Variable(0), &clauses, Some(&[g0, g1]), false);

    assert!(
        result.eliminated,
        "equivalence-gated x0 should be eliminable"
    );
    assert_eq!(result.to_delete.len(), 4);

    // CaDiCaL restricted resolution: only gate × non-gate pairs resolved.
    // Non-gate × non-gate pairs are NEVER resolved when a gate exists.
    // Cross resolvents:
    //   (x0, ~x1) x (~x0, x3) → (~x1, x3)
    //   (~x0, x1) x (x0, x2) → (x1, x2)
    // Gate × gate: tautology, skipped.
    // Non-gate × non-gate: (x0, x2) x (~x0, x3) → (x2, x3) — SKIPPED.
    let has_ng_ng = result
        .resolvents
        .iter()
        .any(|(r, _, _, _)| r.contains(&lit(2, true)) && r.contains(&lit(3, true)));
    // SOUNDNESS CLAMP (inc1): non-gate clauses on both polarity sides → gate-only
    // witnessing would be unsound for reconstruction, so the eliminator falls
    // back to FULL resolution, which DOES produce the non-gate × non-gate
    // resolvent (x2 ∨ x3) and witnesses every deleted clause.
    assert!(
        has_ng_ng,
        "full-resolution fallback must produce the non-gate × non-gate resolvent (x2 ∨ x3)"
    );
    assert_eq!(
        result.witness_entries.len(),
        result.to_delete.len(),
        "fallback must witness every deleted clause"
    );

    for (resolvent, _, _, _) in &result.resolvents {
        assert!(
            resolvent.iter().all(|l| l.variable() != Variable(0)),
            "resolvent must not contain eliminated variable: {resolvent:?}"
        );
    }
}

/// Gate with resolve_gate_pairs=true: gate x gate resolvents are produced.
/// Compare against resolve_gate_pairs=false to confirm the difference.
#[test]
fn test_bve_soundness_gate_with_resolve_gate_pairs_flag() {
    let mut clauses = ClauseArena::new();
    // x0 = AND(x1, x2):
    //   (x0 v ~x1 v ~x2), (~x0 v x1), (~x0 v x2)
    let g0 = clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    let g1 = clauses.add(&[lit(0, false), lit(1, true)], false);
    let g2 = clauses.add(&[lit(0, false), lit(2, true)], false);

    // Without gate pairs: gate x gate pairs skipped
    let mut bve_no_gp = BVE::new(4);
    bve_no_gp.rebuild(&clauses);
    let result_no_gp =
        bve_no_gp.try_eliminate_with_gate(Variable(0), &clauses, Some(&[g0, g1, g2]), false);
    assert!(result_no_gp.eliminated);

    // With gate pairs: gate x gate pairs included
    let mut bve_gp = BVE::new(4);
    bve_gp.rebuild(&clauses);
    let result_gp =
        bve_gp.try_eliminate_with_gate(Variable(0), &clauses, Some(&[g0, g1, g2]), true);
    assert!(result_gp.eliminated);

    // With gate pairs should produce >= as many resolvents
    assert!(
        result_gp.resolvents.len() >= result_no_gp.resolvents.len(),
        "resolve_gate_pairs=true should produce at least as many resolvents: {} vs {}",
        result_gp.resolvents.len(),
        result_no_gp.resolvents.len(),
    );

    // All resolvents must be sound (no eliminated variable)
    for (resolvent, _, _, _) in result_gp
        .resolvents
        .iter()
        .chain(result_no_gp.resolvents.iter())
    {
        assert!(
            resolvent.iter().all(|l| l.variable() != Variable(0)),
            "resolvent must not contain eliminated variable"
        );
    }
}

// ---- 10% growth limit boundary tests ----

/// Just under the 10% growth limit: elimination should succeed.
/// Formula: 100 active clauses. Eliminate x0 with net growth = 4
/// (4% of 100). growth * 10 = 40, active = 100. 40 <= 100 => pass.
#[test]
fn test_bve_soundness_ten_percent_growth_just_under_limit() {
    let num_vars = 200;
    let mut bve = BVE::new(num_vars);
    // Set additive growth bound high enough that the resolvent budget
    // does not reject before the 10% guard.
    bve.set_growth_bound(16);
    bve.increment_growth_bound(); // fastelim -> additive, reset to 0
    for _ in 0..5 {
        bve.increment_growth_bound(); // 0->1->2->4->8->16
    }

    let mut clauses = ClauseArena::new();
    // x0: 2 pos x 6 neg = 12 resolvents, 8 removed. growth = 4.
    // 4 * 10 = 40 <= 100. Passes 10% guard.
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);
    for i in 0..6 {
        clauses.add(&[lit(0, false), lit(10 + i, true)], false);
    }
    // Padding: 92 clauses not involving x0
    for i in 0..92 {
        clauses.add(
            &[lit(100 + i, true), lit(100 + (i + 1) % 100, false)],
            false,
        );
    }

    let active = clauses.active_clause_count();
    assert!(active >= 100, "need >= 100 active clauses, got {active}");

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(
        result.eliminated,
        "growth={} on {active}-clause formula should be within 10% limit",
        result
            .resolvents
            .len()
            .saturating_sub(result.to_delete.len()),
    );
    for (resolvent, _, _, _) in &result.resolvents {
        assert!(
            resolvent.iter().all(|l| l.variable() != Variable(0)),
            "resolvent must not contain eliminated variable"
        );
    }
}

/// Exactly at the 10% growth limit boundary: growth * 10 == active_before.
/// The guard is `growth * 10 > active_before`, so equality passes.
#[test]
fn test_bve_soundness_ten_percent_growth_at_exact_boundary() {
    let num_vars = 200;
    let mut bve = BVE::new(num_vars);
    bve.set_growth_bound(16);
    bve.increment_growth_bound();
    for _ in 0..5 {
        bve.increment_growth_bound();
    }

    let mut clauses = ClauseArena::new();
    // Target: active_before = 100, growth = 10 (exactly 10%).
    // growth * 10 = 100 = active_before => NOT greater than => passes.
    // 2 pos x 12 neg = 24 resolvents, 14 deleted. growth = 10. Exact!
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);
    for i in 0..12 {
        clauses.add(&[lit(0, false), lit(10 + i, true)], false);
    }
    // Padding to reach exactly 100 active clauses: 100 - 14 = 86
    for i in 0..86 {
        clauses.add(
            &[lit(100 + i, true), lit(100 + (i + 1) % 100, false)],
            false,
        );
    }

    let active = clauses.active_clause_count();
    assert_eq!(active, 100, "need exactly 100 active clauses, got {active}");

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    // growth = 24 - 14 = 10. growth * 10 = 100 = active_before.
    // Guard is `>`, not `>=`, so this should PASS.
    assert!(
        result.eliminated,
        "growth=10 on 100-clause formula is exactly 10% and should be accepted \
         (guard uses strict >)"
    );
}

/// Just over the 10% growth limit: elimination must be rejected.
/// We construct a formula where net clause growth exceeds 10% of active clauses.
#[test]
fn test_bve_soundness_ten_percent_growth_just_over_limit() {
    let num_vars = 200;
    let mut bve = BVE::new(num_vars);
    bve.set_growth_bound(16);
    bve.increment_growth_bound();
    for _ in 0..5 {
        bve.increment_growth_bound();
    }

    let mut clauses = ClauseArena::new();
    // Target: active_before = 100, growth = 11 (11% > 10%).
    // growth * 10 = 110 > 100 => rejected.
    // 2 pos x 13 neg = 26 resolvents, 15 deleted. growth = 11.
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);
    for i in 0..13 {
        clauses.add(&[lit(0, false), lit(10 + i, true)], false);
    }
    // Padding: 100 - 15 = 85 clauses
    for i in 0..85 {
        clauses.add(
            &[lit(100 + i, true), lit(100 + (i + 1) % 100, false)],
            false,
        );
    }

    let active = clauses.active_clause_count();
    assert_eq!(active, 100, "need exactly 100 active clauses, got {active}");

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(
        !result.eliminated,
        "growth=11 on 100-clause formula exceeds 10% and must be rejected"
    );
}

/// The 10% guard only activates on formulas with >= 100 active clauses.
/// On a small formula (< 100 clauses), growth is controlled only by the
/// resolvent budget (clauses_removed + growth_bound).
#[test]
fn test_bve_soundness_ten_percent_guard_inactive_on_small_formula() {
    let num_vars = 30;
    let mut bve = BVE::new(num_vars);
    // Additive growth bound large enough to accept the resolvents.
    bve.set_growth_bound(16);
    bve.increment_growth_bound();
    for _ in 0..5 {
        bve.increment_growth_bound();
    }

    let mut clauses = ClauseArena::new();
    // x0: 2 pos x 8 neg = 16 resolvents, 10 deleted. growth = 6.
    // On a 20-clause formula: 6 * 10 = 60 > 20. Would fail 10% guard.
    // But with < 100 clauses, the 10% guard does not activate.
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);
    for i in 0..8 {
        clauses.add(&[lit(0, false), lit(10 + i, true)], false);
    }
    // 10 padding clauses -> total = 20 (well under 100)
    for i in 0..10 {
        clauses.add(&[lit(20 + i, true), lit(20 + (i + 1) % 10, false)], false);
    }

    let active = clauses.active_clause_count();
    assert!(
        active < 100,
        "formula must have < 100 clauses for this test, got {active}"
    );

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    // Resolvent budget: 10 (deleted) + 16 (growth_bound) = 26. 16 <= 26. Passes.
    assert!(
        result.eliminated,
        "small formula should skip 10% guard; resolvent budget should accept"
    );
    for (resolvent, _, _, _) in &result.resolvents {
        assert!(
            resolvent.iter().all(|l| l.variable() != Variable(0)),
            "resolvent must not contain eliminated variable"
        );
    }
}

// ---- Mixed clause width regression ----

/// Mix of binary and ternary clauses: verifies resolution produces correct
/// resolvent widths and no variable leakage.
#[test]
fn test_bve_soundness_mixed_binary_and_ternary() {
    let mut bve = BVE::new(7);
    let mut clauses = ClauseArena::new();
    // Binary positive: (x0 v x1)
    clauses.add(&[lit(0, true), lit(1, true)], false);
    // Ternary positive: (x0 v x2 v x3)
    clauses.add(&[lit(0, true), lit(2, true), lit(3, true)], false);
    // Binary negative: (~x0 v x4)
    clauses.add(&[lit(0, false), lit(4, true)], false);
    // Ternary negative: (~x0 v x5 v x6)
    clauses.add(&[lit(0, false), lit(5, true), lit(6, true)], false);

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(
        result.eliminated,
        "x0 should be eliminable (4 resolvents <= 4 removed)"
    );
    assert_eq!(result.to_delete.len(), 4);
    assert_eq!(result.resolvents.len(), 4, "2x2 = 4 resolvents");

    // Expected resolvent sizes:
    // (x0,x1) x (~x0,x4) => {x1,x4} (2 lits)
    // (x0,x1) x (~x0,x5,x6) => {x1,x5,x6} (3 lits)
    // (x0,x2,x3) x (~x0,x4) => {x2,x3,x4} (3 lits)
    // (x0,x2,x3) x (~x0,x5,x6) => {x2,x3,x5,x6} (4 lits)
    let mut sizes: Vec<usize> = result
        .resolvents
        .iter()
        .map(|(r, _, _, _)| r.len())
        .collect();
    sizes.sort_unstable();
    assert_eq!(
        sizes,
        vec![2, 3, 3, 4],
        "resolvent size distribution should match expected"
    );

    for (resolvent, _, _, _) in &result.resolvents {
        assert!(
            resolvent.iter().all(|l| l.variable() != Variable(0)),
            "resolvent must not contain eliminated variable"
        );
    }
}

/// Empty resolvent detection: (x0) and (~x0) produce the empty resolvent.
/// This signals UNSAT.
#[test]
fn test_bve_soundness_unit_clauses_produce_empty_resolvent() {
    let mut bve = BVE::new(2);
    let mut clauses = ClauseArena::new();
    // Unit positive: (x0)
    clauses.add(&[lit(0, true)], false);
    // Unit negative: (~x0)
    clauses.add(&[lit(0, false)], false);

    bve.rebuild(&clauses);
    let result = bve.try_eliminate(Variable(0), &clauses);

    assert!(
        result.eliminated,
        "x0 should be eliminated (produces empty resolvent)"
    );
    assert_eq!(result.resolvents.len(), 1, "one resolvent (empty clause)");
    let (resolvent, _, _, _) = &result.resolvents[0];
    assert!(
        resolvent.is_empty(),
        "resolvent of unit clauses should be the empty clause"
    );
}

/// Verify that gated BVE and non-gated BVE on the same formula both produce
/// resolvents with no reference to the eliminated variable. This is the core
/// soundness invariant regardless of gate optimization.
#[test]
fn test_bve_soundness_gated_vs_ungated_both_sound() {
    let mut clauses = ClauseArena::new();
    // x0 <-> x1 (equivalence gate)
    let g0 = clauses.add(&[lit(0, true), lit(1, false)], false);
    let g1 = clauses.add(&[lit(0, false), lit(1, true)], false);
    // Non-gate clauses
    clauses.add(&[lit(0, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(3, true)], false);
    clauses.add(&[lit(0, true), lit(4, true)], false);

    // Gated BVE
    let mut bve_gated = BVE::new(6);
    bve_gated.rebuild(&clauses);
    let result_gated =
        bve_gated.try_eliminate_with_gate(Variable(0), &clauses, Some(&[g0, g1]), false);
    assert!(result_gated.eliminated);

    // Non-gated BVE (full resolution)
    let mut bve_full = BVE::new(6);
    bve_full.rebuild(&clauses);
    let result_full = bve_full.try_eliminate(Variable(0), &clauses);
    assert!(result_full.eliminated);

    // Soundness invariant: no resolvent in either result references x0
    for (resolvent, _, _, _) in result_gated
        .resolvents
        .iter()
        .chain(result_full.resolvents.iter())
    {
        assert!(
            resolvent.iter().all(|l| l.variable() != Variable(0)),
            "resolvent must not contain eliminated variable: {resolvent:?}"
        );
    }

    // The gated version should produce resolvents that are a subset of or
    // equivalent to the full version (possibly with OTFS optimizations).
    assert!(
        result_gated.resolvents.len()
            <= result_full.resolvents.len() + result_gated.strengthened.len(),
        "gated BVE should not produce MORE resolvents than full BVE \
         (gated={}, full={}, gated_otfs={})",
        result_gated.resolvents.len(),
        result_full.resolvents.len(),
        result_gated.strengthened.len(),
    );
}

/// Regression for #7916: restricted resolution on XOR gate with single-side
/// non-gate clauses must still produce all cross-resolvents. The bug was that
/// same-round backward subsumption could delete an irredundant clause subsumed
/// by a fresh resolvent, and that resolvent could itself be deleted by a later
/// elimination, losing the original constraint.
///
/// This test verifies that for an XOR gate y = a XOR b with an extra non-gate
/// clause on only one polarity side, restricted resolution produces exactly the
/// gate x non-gate cross-resolvents.
#[test]
fn test_bve_restricted_resolution_xor_gate_single_side_non_gate() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();

    // XOR gate y = a XOR b encoded as:
    //   (y, a, b)       -- positive, gate
    //   (y, ~a, ~b)     -- positive, gate
    //   (~y, ~a, b)     -- negative, gate
    //   (~y, a, ~b)     -- negative, gate
    let g0 = clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    let g1 = clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    let g2 = clauses.add(&[lit(0, false), lit(1, false), lit(2, true)], false);
    let g3 = clauses.add(&[lit(0, false), lit(1, true), lit(2, false)], false);

    // Non-gate clause on positive side only: (y, c, d)
    clauses.add(&[lit(0, true), lit(3, true), lit(4, true)], false);

    bve.rebuild(&clauses);

    let gate_defs = [g0, g1, g2, g3];
    let result = bve.try_eliminate_with_gate(Variable(0), &clauses, Some(&gate_defs), false);
    assert!(result.eliminated, "XOR gate variable should be eliminated");

    // Cross-resolvents: non-gate positive x gate negative
    //   (y, c, d) x (~y, ~a, b) -> (c, d, ~a, b)
    //   (y, c, d) x (~y, a, ~b) -> (c, d, a, ~b)
    // Gate x gate pairs are skipped (tautological for structural XOR).
    // No non-gate negative clauses, so no non-gate x non-gate.
    assert_eq!(
        result.resolvents.len(),
        2,
        "expected exactly 2 cross-resolvents (non-gate-pos x gate-neg)"
    );

    let mut found_cd_notab = false;
    let mut found_cd_anotb = false;
    for (r, _, _, _) in &result.resolvents {
        let has_c = r.contains(&lit(3, true));
        let has_d = r.contains(&lit(4, true));
        if has_c && has_d && r.contains(&lit(1, false)) && r.contains(&lit(2, true)) {
            found_cd_notab = true;
        }
        if has_c && has_d && r.contains(&lit(1, true)) && r.contains(&lit(2, false)) {
            found_cd_anotb = true;
        }
    }
    assert!(found_cd_notab, "resolvent (c, d, ~a, b) must be produced");
    assert!(found_cd_anotb, "resolvent (c, d, a, ~b) must be produced");
}

/// CaDiCaL elim.cpp:628: for complete structural gates, only gate clauses
/// are pushed as witness entries. Non-gate clauses are omitted because the
/// gate fully defines the variable; the resolvents (gate x non-gate) encode
/// the non-gate constraints without the pivot. All clauses are still deleted.
///
/// Regression note: the previous version pushed ALL clauses (#7916) which
/// Verify that ALL clauses (gate and non-gate) are pushed to the
/// reconstruction stack for gated elimination (#8223).
///
/// Previously, only gate-defining clauses were pushed, matching
/// CaDiCaL's `if (!substitute || c->gate)` filter. However, AY's
/// gate detection may differ from CaDiCaL's, causing non-gate
/// clauses to be deleted without reconstruction entries. Pushing
/// all clauses is safe and prevents model corruption.
#[test]
fn test_bve_witness_entries_include_all_clauses_for_gated_elimination() {
    let mut bve = BVE::new(4);
    let mut clauses = ClauseArena::new();

    // AND gate: y = a AND b
    //   (-y, a)       -- negative, gate
    //   (-y, b)       -- negative, gate
    //   (y, -a, -b)   -- positive, gate
    let g0 = clauses.add(&[lit(0, false), lit(1, true)], false);
    let g1 = clauses.add(&[lit(0, false), lit(2, true)], false);
    let g2 = clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);

    // Non-gate positive clause: (y, c) — only on positive side
    let _ng = clauses.add(&[lit(0, true), lit(3, true)], false);

    bve.rebuild(&clauses);

    let gate_defs = [g0, g1, g2];
    let result = bve.try_eliminate_with_gate(Variable(0), &clauses, Some(&gate_defs), false);
    assert!(result.eliminated);

    // SOUNDNESS CLAMP (inc1): a non-gate clause is present, so gate-only
    // witnessing is unsound for reconstruction → full-resolution fallback
    // witnesses ALL 4 deleted clauses (gate AND non-gate). The prior #8482
    // gate-only behavior was the source of the braun/barrel FINALIZE_SAT_FAIL.
    assert_eq!(
        result.witness_entries.len(),
        4,
        "non-gate present → all deleted clauses witnessed (full-resolution fallback)"
    );

    // All 4 clauses should be in to_delete (gate and non-gate).
    assert_eq!(
        result.to_delete.len(),
        4,
        "all clauses containing the eliminated variable must be deleted"
    );
}

/// SOUNDNESS CLAMP (inc1, supersedes the old #8482 gate-only-witness behavior):
/// when non-gate clauses are present (here on BOTH polarity sides), gate-only
/// witnessing would drop their pivot constraint and break reconstruction
/// (braun-9/13, barrel6 FINALIZE_SAT_FAIL). The eliminator falls back to full
/// resolution + FULL witnessing, so every deleted clause is witnessed.
#[test]
fn test_bve_witness_entries_full_when_nongate_present() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();

    // AND gate: y = a AND b
    let g0 = clauses.add(&[lit(0, false), lit(1, true)], false);
    let g1 = clauses.add(&[lit(0, false), lit(2, true)], false);
    let g2 = clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);

    // Non-gate clauses on BOTH sides
    let _ng_pos = clauses.add(&[lit(0, true), lit(3, true)], false);
    let _ng_neg = clauses.add(&[lit(0, false), lit(4, true)], false);

    bve.rebuild(&clauses);
    bve.set_growth_bound(10); // Allow growth for 5 clauses

    let gate_defs = [g0, g1, g2];
    let result = bve.try_eliminate_with_gate(Variable(0), &clauses, Some(&gate_defs), false);
    assert!(result.eliminated);

    // All 5 clauses (3 gate + 2 non-gate) deleted, and ALL 5 witnessed
    // (full-resolution fallback, no gate-only filtering).
    assert_eq!(result.to_delete.len(), 5);
    assert_eq!(
        result.witness_entries.len(),
        5,
        "non-gate present → full witnessing of every deleted clause"
    );
}

// ========================================================================
// Backward subsumption tests (issue #5049)
// ========================================================================

/// Basic backward subsumption: resolvent (a, b) subsumes existing clause (a, b, c).
#[test]
fn test_backward_subsumption_basic() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();

    // Existing clause: (a, b, c) — should be subsumed
    let c0 = clauses.add(&[lit(1, true), lit(2, true), lit(3, true)], false);
    // Resolvent: (a, b) — subsumes c0
    let r0 = clauses.add(&[lit(1, true), lit(2, true)], false);

    bve.rebuild(&clauses);

    let mut marks = LitMarks::new(5);
    let vals = vec![0i8; 10];

    let result = bve.backward_subsume_resolvents(&clauses, &[r0], &mut marks, &vals);

    assert_eq!(result.subsumed.len(), 1, "c0 should be subsumed by r0");
    assert_eq!(result.subsumed[0], c0);
    assert!(result.strengthened.is_empty());
    assert!(result.units.is_empty());
    assert_eq!(bve.stats().backward_subsumed, 1);
}

/// Backward self-subsumption: resolvent (a, b) and existing clause (a, ~b, c)
/// should strengthen the existing clause by removing ~b, yielding (a, c).
///
/// The "best" literal (fewest occ-list entries) must be one whose occ list
/// contains the candidate clause. Here, literal `a` appears in both clauses,
/// so backward subsumption scans occs(a) and finds the candidate.
#[test]
fn test_backward_self_subsumption() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();

    // Existing clause: (a, ~b, c) — should be strengthened
    let c0 = clauses.add(&[lit(1, true), lit(2, false), lit(3, true)], false);
    // Additional clause with lit(2,true) so that occs(b) is not the smallest.
    // Without this, occs(b)=1 < occs(a)=2 and "best" picks b, missing c0
    // because c0 has ~b not b.
    let _filler = clauses.add(&[lit(2, true), lit(4, true)], false);
    // Resolvent: (a, b) — self-subsumes c0 (b vs ~b)
    let r0 = clauses.add(&[lit(1, true), lit(2, true)], false);

    bve.rebuild(&clauses);

    let mut marks = LitMarks::new(5);
    let vals = vec![0i8; 10];

    let result = bve.backward_subsume_resolvents(&clauses, &[r0], &mut marks, &vals);

    assert!(
        result.subsumed.is_empty(),
        "should not be a pure subsumption"
    );
    assert_eq!(result.strengthened.len(), 1, "c0 should be strengthened");
    assert_eq!(result.strengthened[0].0, c0);
    assert_eq!(
        result.strengthened[0].1,
        lit(2, false),
        "~b should be removed"
    );
    assert!(result.units.is_empty());
    assert_eq!(bve.stats().backward_strengthened, 1);
}

/// Hyper-unary resolution: resolvent (a, b) and existing clause (a, ~b)
/// should derive unit `a`.
#[test]
fn test_backward_hyper_unary_resolution() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();

    // Existing clause: (a, ~b)
    clauses.add(&[lit(1, true), lit(2, false)], false);
    // Resolvent: (a, b) — complementary pair with the existing clause
    let r0 = clauses.add(&[lit(1, true), lit(2, true)], false);
    // Filler clause containing `b` so that occs(b) >= occs(a), making `a`
    // the "best" literal. Without this, the algorithm picks `b` as best
    // (smallest occ count) and its occ list doesn't contain the existing
    // clause (which has ~b, not b).
    clauses.add(&[lit(2, true), lit(4, true)], false);

    bve.rebuild(&clauses);

    let mut marks = LitMarks::new(5);
    let vals = vec![0i8; 10];

    let result = bve.backward_subsume_resolvents(&clauses, &[r0], &mut marks, &vals);

    assert!(result.subsumed.is_empty());
    // Hyper-unary resolution: complementary pair (a, b) and (a, ~b) with
    // d_active == active_size and exactly one non-negated active literal
    // triggers direct unit derivation of `a` (CaDiCaL backward.cpp:119-148).
    assert!(
        result.strengthened.is_empty(),
        "unit path, not strengthening"
    );
    assert_eq!(result.units.len(), 1, "should derive unit `a`");
    assert_eq!(result.units[0], lit(1, true), "unit should be literal `a`");
    assert_eq!(bve.stats().backward_units, 1);
    assert_eq!(bve.stats().backward_strengthened, 0);
}

/// No subsumption when the resolvent is larger than the candidate.
#[test]
fn test_backward_no_subsumption_resolvent_larger() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();

    // Existing clause: (a, b) — shorter than the resolvent
    clauses.add(&[lit(1, true), lit(2, true)], false);
    // Resolvent: (a, b, c) — cannot subsume the shorter clause
    let r0 = clauses.add(&[lit(1, true), lit(2, true), lit(3, true)], false);

    bve.rebuild(&clauses);

    let mut marks = LitMarks::new(5);
    let vals = vec![0i8; 10];

    let result = bve.backward_subsume_resolvents(&clauses, &[r0], &mut marks, &vals);

    assert!(
        result.subsumed.is_empty(),
        "shorter clause should not be subsumed"
    );
    assert!(result.strengthened.is_empty());
    assert!(result.units.is_empty());
}

/// The resolvent should not subsume itself.
#[test]
fn test_backward_does_not_subsume_self() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();

    // Resolvent: (a, b)
    let r0 = clauses.add(&[lit(1, true), lit(2, true)], false);
    // Identical clause: (a, b) — but it IS r0 itself
    // We add another to give the occ list something to scan
    let _c1 = clauses.add(&[lit(1, true), lit(3, true)], false);

    bve.rebuild(&clauses);

    let mut marks = LitMarks::new(5);
    let vals = vec![0i8; 10];

    let result = bve.backward_subsume_resolvents(&clauses, &[r0], &mut marks, &vals);

    // r0 should not appear in subsumed (it's the resolvent itself)
    assert!(
        !result.subsumed.contains(&r0),
        "resolvent must not subsume itself"
    );
}

/// Root-level-false literals are ignored during backward subsumption.
#[test]
fn test_backward_subsumption_with_root_level_false() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();

    // Existing clause: (a, b, c) — c is false at root level, so effectively (a, b)
    let c0 = clauses.add(&[lit(1, true), lit(2, true), lit(3, true)], false);
    // Resolvent: (a, b)
    let r0 = clauses.add(&[lit(1, true), lit(2, true)], false);

    bve.rebuild(&clauses);

    let mut marks = LitMarks::new(5);
    let mut vals = vec![0i8; 10];
    // Mark lit(3, true) as false at root level
    assign_root(&mut vals, lit(3, false));

    let result = bve.backward_subsume_resolvents(&clauses, &[r0], &mut marks, &vals);

    // Even though c0 has 3 literals, with lit(3) false it's effectively (a, b),
    // so r0=(a,b) subsumes c0.
    assert_eq!(
        result.subsumed.len(),
        1,
        "c0 should be subsumed (root-false lit ignored)"
    );
    assert_eq!(result.subsumed[0], c0);
}

/// Multiple resolvents processed in batch.
#[test]
fn test_backward_multiple_resolvents() {
    let mut bve = BVE::new(6);
    let mut clauses = ClauseArena::new();

    // Existing clauses that may be subsumed
    let c0 = clauses.add(&[lit(1, true), lit(2, true), lit(3, true)], false);
    let c1 = clauses.add(&[lit(4, true), lit(5, true), lit(3, true)], false);

    // Resolvents
    let r0 = clauses.add(&[lit(1, true), lit(2, true)], false);
    let r1 = clauses.add(&[lit(4, true), lit(5, true)], false);

    bve.rebuild(&clauses);

    let mut marks = LitMarks::new(6);
    let vals = vec![0i8; 12];

    let result = bve.backward_subsume_resolvents(&clauses, &[r0, r1], &mut marks, &vals);

    assert_eq!(
        result.subsumed.len(),
        2,
        "both c0 and c1 should be subsumed"
    );
    assert!(result.subsumed.contains(&c0));
    assert!(result.subsumed.contains(&c1));
}

/// Two negated literals in candidate: not a subsumption or self-subsumption.
#[test]
fn test_backward_two_negated_skips() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();

    // Existing clause: (~a, ~b, c) — has two literals negated relative to resolvent
    clauses.add(&[lit(1, false), lit(2, false), lit(3, true)], false);
    // Resolvent: (a, b)
    let r0 = clauses.add(&[lit(1, true), lit(2, true)], false);

    bve.rebuild(&clauses);

    let mut marks = LitMarks::new(5);
    let vals = vec![0i8; 10];

    let result = bve.backward_subsume_resolvents(&clauses, &[r0], &mut marks, &vals);

    assert!(result.subsumed.is_empty());
    assert!(result.strengthened.is_empty());
    assert!(result.units.is_empty());
}

/// Satisfied candidate (at root level) is collected for deletion (#8007).
/// CaDiCaL backward.cpp:107-110 marks satisfied candidates as garbage.
#[test]
fn test_backward_satisfied_candidate_collected() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();

    // Existing clause: (c, a, b) where c is true at root level.
    // The satisfied literal c is placed FIRST so the scan encounters it
    // before all of R's literals match (which would cause an early break
    // via `found == active_size` before reaching c).
    let c0 = clauses.add(&[lit(3, true), lit(1, true), lit(2, true)], false);
    // Resolvent: (a, b)
    let r0 = clauses.add(&[lit(1, true), lit(2, true)], false);

    bve.rebuild(&clauses);

    let mut marks = LitMarks::new(5);
    let mut vals = vec![0i8; 10];
    // Mark lit(3, true) as true at root level -> c0 is satisfied
    assign_root(&mut vals, lit(3, true));

    let result = bve.backward_subsume_resolvents(&clauses, &[r0], &mut marks, &vals);

    // Satisfied candidate should be collected for deletion, not subsumed
    assert!(
        result.subsumed.is_empty(),
        "satisfied clause should not be subsumed"
    );
    assert_eq!(
        result.satisfied,
        vec![c0],
        "satisfied candidate should be collected for deletion"
    );
}

/// Test that BVE effort budget exhaustion prevents elimination (#8195).
///
/// CaDiCaL's incremental effort charging (elim.cpp:888) aborts a variable's
/// elimination when the global resolution budget is exhausted mid-variable.
/// This test verifies AY's implementation: passing a small `remaining_budget`
/// causes `check_bounded_elimination_with_marks` to return not-eliminable
/// before all resolution pairs are tried.
#[test]
fn test_bve_effort_budget_exhaustion_prevents_elimination() {
    // Create a variable x0 with 3 positive and 3 negative occurrences.
    // Full resolution requires 3*3 = 9 resolution attempts.
    // With a budget of 2, only 2 attempts should be made before aborting.
    let num_vars = 8;
    let mut bve = BVE::new(num_vars);
    let mut clauses = ClauseArena::new();

    // 3 positive occurrences of x0
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(3, true)], false);

    // 3 negative occurrences of x0
    clauses.add(&[lit(0, false), lit(4, true)], false);
    clauses.add(&[lit(0, false), lit(5, true)], false);
    clauses.add(&[lit(0, false), lit(6, true)], false);

    bve.rebuild(&clauses);

    let mut marks = LitMarks::new(num_vars);
    let vals = vec![0i8; num_vars * 2];

    // With unlimited budget, elimination should succeed (9 resolvents <= 6+0 budget
    // is false, but let's check).
    let result_unlimited = bve.try_eliminate_with_gate_with_marks(
        Variable(0),
        &clauses,
        None,
        false,
        &mut marks,
        &vals,
        u64::MAX,
    );
    // 9 resolvents vs budget of 6 (pos+neg+growth_bound=6+0=6): too many.
    // The clause-count bound rejects this, not the effort budget.
    // So this variable is not eliminable even with unlimited budget.
    // Let's use a formula where elimination IS bounded but budget is too small.

    // Reset and use a simpler formula: 2 pos, 2 neg = 4 pairs, all non-tautological.
    // clauses_removed = 4, budget = 4+0 = 4. 4 resolvents <= 4: bounded.
    let _ = result_unlimited;
    let mut bve2 = BVE::new(num_vars);
    let mut clauses2 = ClauseArena::new();

    // 2 positive occurrences
    clauses2.add(&[lit(0, true), lit(1, true)], false);
    clauses2.add(&[lit(0, true), lit(2, true)], false);

    // 2 negative occurrences
    clauses2.add(&[lit(0, false), lit(3, true)], false);
    clauses2.add(&[lit(0, false), lit(4, true)], false);

    bve2.rebuild(&clauses2);

    // First verify unlimited budget succeeds
    let result_ok = bve2.try_eliminate_with_gate_with_marks(
        Variable(0),
        &clauses2,
        None,
        false,
        &mut marks,
        &vals,
        u64::MAX,
    );
    assert!(
        result_ok.eliminated,
        "with unlimited budget, 2x2 elimination should succeed"
    );
    assert_eq!(
        result_ok.resolution_attempts, 4,
        "2x2 resolution should produce 4 attempts"
    );

    // Now reset and try with a budget of 1 (less than the 4 needed)
    let mut bve3 = BVE::new(num_vars);
    let mut clauses3 = ClauseArena::new();

    clauses3.add(&[lit(0, true), lit(1, true)], false);
    clauses3.add(&[lit(0, true), lit(2, true)], false);
    clauses3.add(&[lit(0, false), lit(3, true)], false);
    clauses3.add(&[lit(0, false), lit(4, true)], false);

    bve3.rebuild(&clauses3);

    let result_exhausted = bve3.try_eliminate_with_gate_with_marks(
        Variable(0),
        &clauses3,
        None,
        false,
        &mut marks,
        &vals,
        1, // budget of 1: only 1 resolution attempt before exhaustion
    );

    assert!(
        !result_exhausted.eliminated,
        "budget exhaustion must prevent elimination"
    );
    assert_eq!(
        result_exhausted.resolution_attempts, 1,
        "only 1 resolution attempt should be made before budget exhaustion"
    );

    // Budget of 0: should immediately abort with 0 attempts
    let mut bve4 = BVE::new(num_vars);
    let mut clauses4 = ClauseArena::new();

    clauses4.add(&[lit(0, true), lit(1, true)], false);
    clauses4.add(&[lit(0, true), lit(2, true)], false);
    clauses4.add(&[lit(0, false), lit(3, true)], false);
    clauses4.add(&[lit(0, false), lit(4, true)], false);

    bve4.rebuild(&clauses4);

    let result_zero = bve4.try_eliminate_with_gate_with_marks(
        Variable(0),
        &clauses4,
        None,
        false,
        &mut marks,
        &vals,
        0, // budget of 0: immediate exhaustion
    );

    assert!(
        !result_zero.eliminated,
        "zero budget must prevent elimination"
    );
    assert_eq!(
        result_zero.resolution_attempts, 0,
        "zero budget should produce 0 resolution attempts"
    );
}

/// Test that budget exhaustion tracks resolution_attempts correctly for
/// gated elimination (#8195).
#[test]
fn test_bve_effort_budget_exhaustion_with_gate() {
    let num_vars = 8;
    let mut bve = BVE::new(num_vars);
    let mut clauses = ClauseArena::new();

    // Gate definition for x0: x0 <=> (x1 AND x2)
    // Positive gate clause: (~x0, x1) and (~x0, x2) - these define x0
    // Negative side clause: (x0, ~x1, ~x2)
    let g0 = clauses.add(&[lit(0, false), lit(1, true)], false);
    let g1 = clauses.add(&[lit(0, false), lit(2, true)], false);
    let _ng = clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);

    // Non-gate clauses
    clauses.add(&[lit(0, true), lit(3, true)], false);
    clauses.add(&[lit(0, false), lit(4, true)], false);

    bve.rebuild(&clauses);

    let mut marks = LitMarks::new(num_vars);
    let vals = vec![0i8; num_vars * 2];

    // With budget of 1, gated resolution should abort early
    let result = bve.try_eliminate_with_gate_with_marks(
        Variable(0),
        &clauses,
        Some(&[g0, g1]),
        false,
        &mut marks,
        &vals,
        1,
    );

    assert!(
        !result.eliminated,
        "budget of 1 should prevent gated elimination"
    );
    assert!(
        result.resolution_attempts <= 1,
        "at most 1 resolution attempt with budget of 1"
    );
}

// ==================== Quick elimination (fast_elim) tests ====================

/// Verify that `quick_eliminate_candidates()` filters variables with tight
/// occurrence and clause-size limits (Pass 0 pre-pass, #8242).
#[test]
fn test_fast_elim_quick_candidates_filtering() {
    use crate::bve::fast_eliminate::{QUICK_ELIM_CLS_LIMIT, QUICK_ELIM_OCC_LIMIT};

    // Use 30 variables so we have headroom for the big-clause test.
    let num_vars = 30;
    let mut arena = ClauseArena::new();

    // Clause: (x0, x1, x2) — positive occurrence of x0
    arena.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    // Clause: (x0, x3, x4) — positive occurrence of x0
    arena.add(&[lit(0, true), lit(3, true), lit(4, true)], false);
    // Clause: (~x0, x1, x3) — negative occurrence of x0
    arena.add(&[lit(0, false), lit(1, true), lit(3, true)], false);

    // Add 6 clauses with x5 positive to exceed QUICK_ELIM_OCC_LIMIT=5.
    // Also give x5 one negative occurrence so it's not pure.
    for i in 0..6 {
        arena.add(&[lit(5, true), lit(6 + i, true)], false);
    }
    arena.add(&[lit(5, false), lit(7, true)], false);

    // Add a clause for x8 that exceeds QUICK_ELIM_CLS_LIMIT=20.
    let mut big_lits = vec![lit(8, true)];
    for i in 9..=(9 + QUICK_ELIM_CLS_LIMIT) {
        big_lits.push(lit(i as u32, true));
    }
    arena.add(&big_lits, false);
    // Give x8 a negative occurrence so it's not pure.
    arena.add(&[lit(8, false), lit(9, true)], false);

    let mut bve = BVE::new(num_vars);
    let vals = vec![0i8; num_vars * 2];
    bve.rebuild_with_vals(&arena, &vals);
    let frozen = vec![0u32; num_vars];
    let candidates = bve.quick_eliminate_candidates(&arena, &vals, &frozen);

    // x0 has 2 pos + 1 neg = 3 total, all small clauses → should be a candidate.
    assert!(
        candidates.contains(&Variable(0)),
        "x0 should be in quick_eliminate_candidates (2 pos, 1 neg, all small clauses)"
    );

    // x5 has 6 positive occurrences, exceeding QUICK_ELIM_OCC_LIMIT=5 → excluded.
    assert!(
        !candidates.contains(&Variable(5)),
        "x5 should be excluded: 6 positive occurrences exceeds limit of {QUICK_ELIM_OCC_LIMIT}",
    );

    // x8 appears in a clause of size QUICK_ELIM_CLS_LIMIT+1 → excluded.
    assert!(
        !candidates.contains(&Variable(8)),
        "x8 should be excluded: clause size {} exceeds limit of {}",
        QUICK_ELIM_CLS_LIMIT + 1,
        QUICK_ELIM_CLS_LIMIT,
    );
}

#[test]
fn test_fast_elim_mode_toggle() {
    let mut bve = BVE::new(4);
    assert!(!bve.is_quick_elim_mode(), "should start as false");
    bve.set_quick_elim_mode(true);
    assert!(bve.is_quick_elim_mode(), "should be true after set");
    bve.set_quick_elim_mode(false);
    assert!(!bve.is_quick_elim_mode(), "should be false after clear");
}

#[test]
fn test_fast_elim_stats_fields() {
    let mut bve = BVE::new(4);
    assert_eq!(bve.stats().fast_elim_vars, 0);
    assert_eq!(bve.stats().fast_elim_clauses, 0);
    bve.stats_mut().fast_elim_vars = 42;
    bve.stats_mut().fast_elim_clauses = 7;
    assert_eq!(bve.stats().fast_elim_vars, 42);
    assert_eq!(bve.stats().fast_elim_clauses, 7);
}

#[test]
fn test_bve_refresh_incremental_uses_consistent_saved_occ_state() {
    let mut arena = ClauseArena::new();
    let c0 = arena.add(&[lit(0, true), lit(1, true)], false);
    let c1 = arena.add(&[lit(0, false), lit(2, true)], false);
    let vals = vec![0i8; 6];
    let mut bve = BVE::new(3);

    bve.rebuild_with_vals(&arena, &vals);

    assert!(bve.is_occ_populated());
    assert!(
        bve.refresh_incremental(&arena, &vals),
        "consistent saved occurrence state should refresh incrementally"
    );
    assert!(bve.get_occs(lit(0, true)).contains(&c0));
    assert!(bve.get_occs(lit(0, false)).contains(&c1));
}

#[test]
fn test_bve_refresh_incremental_epoch_reuses_validated_saved_occ_state() {
    let mut arena = ClauseArena::new();
    let c0 = arena.add(&[lit(0, true), lit(1, true)], false);
    let c1 = arena.add(&[lit(0, false), lit(2, true)], false);
    let vals = vec![0i8; 6];
    let mut bve = BVE::new(3);

    bve.rebuild_with_vals_at_epoch(&arena, &vals, 7);

    assert_eq!(bve.occ_consistency_epoch, Some(7));
    assert!(
        bve.refresh_incremental_at_epoch(&arena, &vals, 7),
        "same clause-DB epoch should reuse the already-validated saved state"
    );
    assert_eq!(bve.occ_consistency_epoch, Some(7));
    assert!(bve.get_occs(lit(0, true)).contains(&c0));
    assert!(bve.get_occs(lit(0, false)).contains(&c1));
}

#[test]
fn test_bve_occ_saved_state_round_end_default_drops_live_marker() {
    let mut arena = ClauseArena::new();
    arena.add(&[lit(0, true), lit(1, true)], false);
    let vals = vec![0i8; 4];
    let mut bve = BVE::new(2);

    assert!(
        !bve.occ_saved_state_reuse_enabled(),
        "cross-round occurrence saved-state reuse must be default-off"
    );
    bve.rebuild_with_vals_at_epoch(&arena, &vals, 61);
    assert!(bve.is_occ_populated());

    bve.finish_occ_saved_state_round();

    assert!(
        !bve.is_occ_populated(),
        "default-off round finalizer should stop later mutation hooks"
    );
    assert_eq!(bve.stats().occ_saved_state_round_end_drops, 1);
    assert_eq!(bve.stats().occ_saved_state_round_end_retains, 0);
}

#[test]
fn test_bve_occ_saved_state_reuse_candidate_retains_and_delta_validates_next_round() {
    let mut arena = ClauseArena::new();
    let c0 = arena.add(&[lit(0, true), lit(1, true)], false);
    let c1 = arena.add(&[lit(0, false), lit(2, true)], false);
    let vals = vec![0i8; 6];
    let mut bve = BVE::new(3);

    bve.set_occ_saved_state_reuse_enabled_for_tests(true);
    bve.set_occ_delta_validation_enabled_for_tests(true);
    bve.rebuild_with_vals_at_epoch(&arena, &vals, 71);
    bve.finish_occ_saved_state_round();

    assert!(bve.is_occ_populated());
    assert_eq!(bve.stats().occ_saved_state_round_end_drops, 0);
    assert_eq!(bve.stats().occ_saved_state_round_end_retains, 1);

    let old_lits = arena.literals(c0).to_vec();
    let new_lits = vec![lit(0, true)];
    bve.occ_replace_clause(c0, &old_lits, &new_lits);
    arena.replace(c0, &new_lits);

    assert!(
        bve.refresh_incremental_at_epoch(&arena, &vals, 72),
        "retained occurrence state should be reused and validated by the touched delta"
    );
    assert_eq!(bve.occ_consistency_epoch, Some(72));
    assert_eq!(bve.stats().occ_delta_validated_refreshes, 1);
    assert_eq!(bve.stats().occ_delta_validation_fallbacks, 0);
    assert!(bve.get_occs(lit(0, true)).contains(&c0));
    assert!(!bve.get_occs(lit(1, true)).contains(&c0));
    assert!(bve.get_occs(lit(0, false)).contains(&c1));
}

#[test]
fn test_bve_refresh_incremental_falls_back_on_stale_extra_occ_entry() {
    let mut arena = ClauseArena::new();
    let c0 = arena.add(&[lit(0, true), lit(1, true)], false);
    let c1 = arena.add(&[lit(2, true), lit(3, true)], false);
    let vals = vec![0i8; 8];
    let mut bve = BVE::new(4);

    bve.rebuild_with_vals(&arena, &vals);
    bve.occ_add_clause(c1, &[lit(0, true)]);

    assert!(
        !bve.refresh_incremental(&arena, &vals),
        "stale live occurrence entry must fail closed to a full rebuild"
    );
    assert!(bve.get_occs(lit(0, true)).contains(&c0));
    assert!(
        !bve.get_occs(lit(0, true)).contains(&c1),
        "fallback rebuild should remove stale occurrence entries"
    );
}

#[test]
fn test_bve_refresh_incremental_epoch_falls_back_after_mutation_epoch_changes() {
    let mut arena = ClauseArena::new();
    let c0 = arena.add(&[lit(0, true), lit(1, true)], false);
    let c1 = arena.add(&[lit(2, true), lit(3, true)], false);
    let vals = vec![0i8; 8];
    let mut bve = BVE::new(4);

    bve.rebuild_with_vals_at_epoch(&arena, &vals, 11);
    bve.occ_add_clause(c1, &[lit(0, true)]);

    assert!(
        !bve.refresh_incremental_at_epoch(&arena, &vals, 12),
        "changed clause-DB epoch must force validation and fail closed"
    );
    assert_eq!(bve.occ_consistency_epoch, Some(12));
    assert!(bve.get_occs(lit(0, true)).contains(&c0));
    assert!(
        !bve.get_occs(lit(0, true)).contains(&c1),
        "epoch-triggered fallback rebuild should remove stale occurrence entries"
    );
}

#[test]
fn test_bve_occ_delta_disabled_keeps_full_validation_gate() {
    let mut arena = ClauseArena::new();
    let c0 = arena.add(&[lit(0, true), lit(1, true)], false);
    let c1 = arena.add(&[lit(0, false), lit(2, true)], false);
    let vals = vec![0i8; 6];
    let mut bve = BVE::new(3);

    assert!(
        !bve.occ_delta_validation_enabled(),
        "occ-delta validation must be default-off"
    );
    bve.rebuild_with_vals_at_epoch(&arena, &vals, 13);

    let old_lits = arena.literals(c0).to_vec();
    let new_lits = vec![lit(0, true)];
    bve.occ_replace_clause(c0, &old_lits, &new_lits);
    arena.replace(c0, &new_lits);

    assert!(
        bve.refresh_incremental_at_epoch(&arena, &vals, 14),
        "hooked replacement should still pass through the existing full validation gate"
    );
    assert_eq!(bve.occ_consistency_epoch, Some(14));
    assert_eq!(bve.stats().occ_delta_validated_refreshes, 0);
    assert_eq!(bve.stats().occ_delta_validation_fallbacks, 0);
    assert_eq!(bve.stats().occ_delta_touched_clauses, 0);
    assert_eq!(bve.stats().occ_delta_touched_lits, 0);
    assert!(bve.get_occs(lit(0, true)).contains(&c0));
    assert!(!bve.get_occs(lit(1, true)).contains(&c0));
    assert!(bve.get_occs(lit(0, false)).contains(&c1));
}

#[test]
fn test_bve_occ_delta_validates_touched_replace_after_epoch_change() {
    let mut arena = ClauseArena::new();
    let c0 = arena.add(&[lit(0, true), lit(1, true)], false);
    let c1 = arena.add(&[lit(0, false), lit(2, true)], false);
    let vals = vec![0i8; 6];
    let mut bve = BVE::new(3);

    bve.set_occ_delta_validation_enabled_for_tests(true);
    bve.rebuild_with_vals_at_epoch(&arena, &vals, 21);

    let old_lits = arena.literals(c0).to_vec();
    let new_lits = vec![lit(0, true)];
    bve.occ_replace_clause(c0, &old_lits, &new_lits);
    arena.replace(c0, &new_lits);

    assert!(
        bve.refresh_incremental_at_epoch(&arena, &vals, 22),
        "certified touched replace should validate without full rebuild"
    );
    assert_eq!(bve.occ_consistency_epoch, Some(22));
    assert_eq!(bve.stats().occ_delta_validated_refreshes, 1);
    assert_eq!(bve.stats().occ_delta_validation_fallbacks, 0);
    assert_eq!(bve.stats().occ_delta_touched_clauses, 1);
    assert_eq!(bve.stats().occ_delta_touched_lits, 2);
    assert!(bve.get_occs(lit(0, true)).contains(&c0));
    assert!(!bve.get_occs(lit(1, true)).contains(&c0));
    assert!(bve.get_occs(lit(0, false)).contains(&c1));
}

#[test]
fn test_bve_occ_delta_validates_touched_remove_after_epoch_change() {
    let mut arena = ClauseArena::new();
    let c0 = arena.add(&[lit(0, true), lit(1, true)], false);
    let c1 = arena.add(&[lit(0, false), lit(2, true)], false);
    let vals = vec![0i8; 6];
    let mut bve = BVE::new(3);

    bve.set_occ_delta_validation_enabled(true);
    bve.rebuild_with_vals_at_epoch(&arena, &vals, 23);

    let removed_lits = arena.literals(c1).to_vec();
    bve.occ_remove_clause(c1, &removed_lits);
    arena.delete(c1);

    assert!(
        bve.refresh_incremental_at_epoch(&arena, &vals, 24),
        "certified touched remove should validate without full rebuild"
    );
    assert_eq!(bve.occ_consistency_epoch, Some(24));
    assert_eq!(bve.stats().occ_delta_validated_refreshes, 1);
    assert_eq!(bve.stats().occ_delta_validation_fallbacks, 0);
    assert!(bve.get_occs(lit(0, true)).contains(&c0));
    assert!(!bve.get_occs(lit(0, false)).contains(&c1));
    assert!(!bve.get_occs(lit(2, true)).contains(&c1));
}

#[test]
fn test_bve_occ_delta_validates_same_epoch_hooked_add() {
    let mut arena = ClauseArena::new();
    let c0 = arena.add(&[lit(0, true), lit(1, true)], false);
    let vals = vec![0i8; 6];
    let mut bve = BVE::new(3);

    bve.set_occ_delta_validation_enabled_for_tests(true);
    bve.rebuild_with_vals_at_epoch(&arena, &vals, 31);

    let c1 = arena.add(&[lit(0, false), lit(2, true)], false);
    let c1_lits = arena.literals(c1).to_vec();
    bve.occ_add_new_irredundant(c1, &c1_lits);

    assert!(
        bve.refresh_incremental_at_epoch(&arena, &vals, 31),
        "same-epoch hooked mutation should validate its touched region"
    );
    assert_eq!(bve.occ_consistency_epoch, Some(31));
    assert_eq!(bve.stats().occ_delta_validated_refreshes, 1);
    assert_eq!(bve.stats().occ_epoch_fastpath_refreshes, 0);
    assert!(bve.get_occs(lit(0, true)).contains(&c0));
    assert!(bve.get_occs(lit(0, false)).contains(&c1));
    assert!(bve.get_occs(lit(2, true)).contains(&c1));
}

#[test]
fn test_bve_occ_delta_missing_touched_entry_falls_back() {
    let mut arena = ClauseArena::new();
    let c0 = arena.add(&[lit(0, true), lit(1, true)], false);
    let vals = vec![0i8; 6];
    let mut bve = BVE::new(3);

    bve.set_occ_delta_validation_enabled_for_tests(true);
    bve.rebuild_with_vals_at_epoch(&arena, &vals, 41);

    let c1 = arena.add(&[lit(0, false), lit(2, true)], false);
    let c1_lits = arena.literals(c1).to_vec();
    bve.occ_add_new_irredundant(c1, &c1_lits);
    bve.occ.remove_clause(c1, &[lit(0, false)]);

    assert!(
        !bve.refresh_incremental_at_epoch(&arena, &vals, 42),
        "missing touched occurrence must fail closed to full rebuild"
    );
    assert_eq!(bve.occ_consistency_epoch, Some(42));
    assert_eq!(bve.stats().occ_delta_validated_refreshes, 0);
    assert_eq!(bve.stats().occ_delta_validation_fallbacks, 1);
    assert!(bve.stats().occ_delta_missing_entries > 0);
    assert!(bve.get_occs(lit(0, true)).contains(&c0));
    assert!(
        bve.get_occs(lit(0, false)).contains(&c1),
        "fallback rebuild should restore the missing occurrence"
    );
}

#[test]
fn test_bve_occ_delta_live_learned_entry_falls_back() {
    let mut arena = ClauseArena::new();
    let c0 = arena.add(&[lit(0, true), lit(1, true)], false);
    let vals = vec![0i8; 6];
    let mut bve = BVE::new(3);

    bve.set_occ_delta_validation_enabled(true);
    bve.rebuild_with_vals_at_epoch(&arena, &vals, 43);

    let learned = arena.add(&[lit(0, false), lit(2, true)], true);
    let learned_lits = arena.literals(learned).to_vec();
    bve.occ_add_clause(learned, &learned_lits);

    assert!(
        !bve.refresh_incremental_at_epoch(&arena, &vals, 44),
        "live learned occurrence entries must fail closed to full rebuild"
    );
    assert_eq!(bve.occ_consistency_epoch, Some(44));
    assert_eq!(bve.stats().occ_delta_validated_refreshes, 0);
    assert_eq!(bve.stats().occ_delta_validation_fallbacks, 1);
    assert!(bve.stats().occ_delta_live_learned_entries > 0);
    assert!(bve.get_occs(lit(0, true)).contains(&c0));
    assert!(
        !bve.get_occs(lit(0, false)).contains(&learned),
        "fallback rebuild should remove learned occurrence entries"
    );
}

#[test]
fn test_bve_occ_delta_oversize_falls_back_to_full_gate() {
    let mut arena = ClauseArena::new();
    let c0 = arena.add(&[lit(0, true), lit(1, true)], false);
    let c1 = arena.add(&[lit(0, false), lit(2, true)], false);
    let vals = vec![0i8; 6];
    let mut bve = BVE::new(3);

    bve.set_occ_delta_validation_enabled_for_tests(true);
    bve.set_occ_delta_limits_for_tests(0, 0, 0);
    bve.rebuild_with_vals_at_epoch(&arena, &vals, 51);

    let old_lits = arena.literals(c0).to_vec();
    let new_lits = vec![lit(0, true)];
    bve.occ_replace_clause(c0, &old_lits, &new_lits);
    arena.replace(c0, &new_lits);

    assert!(
        bve.refresh_incremental_at_epoch(&arena, &vals, 52),
        "oversize certified delta should use the existing full validation gate"
    );
    assert_eq!(bve.occ_consistency_epoch, Some(52));
    assert_eq!(bve.stats().occ_delta_validated_refreshes, 0);
    assert_eq!(bve.stats().occ_delta_oversize_fallbacks, 1);
    assert!(bve.get_occs(lit(0, true)).contains(&c0));
    assert!(!bve.get_occs(lit(1, true)).contains(&c0));
    assert!(bve.get_occs(lit(0, false)).contains(&c1));
}

/// Regression for #8398: BVE with CaDiCaL-style fastelim bound (8) must
/// reject variables with many non-tautological resolvents on dense binary
/// instances. A variable with 6 pos + 6 neg binary occurrences produces
/// up to 36 resolution pairs; even if many are tautological, 9+ non-
/// tautological resolvents exceed the fastelimbound=8 budget.
///
/// This test constructs a clique-like structure where variable x0 appears
/// in many binary clauses and verifies that fastelim rejects elimination.
#[test]
fn test_fastelim_bound_rejects_dense_binary_variable() {
    // 12 auxiliary variables + 1 pivot = 13 total
    let mut bve = BVE::new(13);
    let mut clauses = ClauseArena::new();

    // Create 6 positive binary clauses: (x0 v a_i) for i in 1..=6
    for i in 1..=6u32 {
        clauses.add(&[lit(0, true), lit(i, true)], false);
    }
    // Create 6 negative binary clauses: (~x0 v b_j) for j in 7..=12
    for j in 7..=12u32 {
        clauses.add(&[lit(0, false), lit(j, true)], false);
    }

    bve.rebuild(&clauses);

    // Fastelim bound = 8 (CaDiCaL fastelimbound default).
    // Budget = min(pos+neg, growth_bound) = min(12, 8) = 8.
    // Resolution produces 36 pairs, all non-tautological since the
    // auxiliary variables are disjoint. resolvents(36) > budget(8) → reject.
    bve.set_growth_bound(8);
    let result = bve.try_eliminate(Variable(0), &clauses);
    assert!(
        !result.eliminated,
        "fastelim bound=8 must reject x0: 36 non-tautological \
         resolvents from 6*6 binary pairs exceeds budget 8"
    );

    // Verify that a looser bound (16, the old Kissat-style value) would
    // also reject this variable since 36 > min(12, 16) = 12.
    bve.set_growth_bound(16);
    let result = bve.try_eliminate(Variable(0), &clauses);
    assert!(
        !result.eliminated,
        "even with bound=16, 36 resolvents > budget min(12,16)=12"
    );
}

/// Verify that CaDiCaL-style fastelim bound=8 accepts variables where
/// elimination is profitable (few non-tautological resolvents).
#[test]
fn test_fastelim_bound_accepts_low_resolvent_variable() {
    let mut bve = BVE::new(5);
    let mut clauses = ClauseArena::new();

    // 2 positive occurrences: (x0 v a), (x0 v b)
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, true), lit(2, true)], false);
    // 2 negative occurrences: (~x0 v c), (~x0 v d)
    clauses.add(&[lit(0, false), lit(3, true)], false);
    clauses.add(&[lit(0, false), lit(4, true)], false);

    bve.rebuild(&clauses);

    // Fastelim bound = 8. Budget = min(4, 8) = 4.
    // Resolution produces 4 resolvents, all non-tautological.
    // resolvents(4) <= budget(4) → accept.
    bve.set_growth_bound(8);
    let result = bve.try_eliminate(Variable(0), &clauses);
    assert!(
        result.eliminated,
        "fastelim bound=8 must accept x0: 4 resolvents <= budget 4"
    );
    assert_eq!(result.resolvents.len(), 4);
}

// ---------------------------------------------------------------------------
// GPU finalize path (#8349): satisfied-parent witness exclusion parity.
// ---------------------------------------------------------------------------

/// Satisfied parents must be deleted but NOT pushed as reconstruction
/// witnesses (#8356/#8397) — GPU-path parity with the CPU path.
#[cfg(feature = "gpu")]
#[test]
fn test_gpu_finalize_excludes_satisfied_parents_from_witnesses() {
    let mut bve = BVE::new(5);

    // c0 = {x0, x1}, c1 = {x0, x2} (root-satisfied parent), c2 = {~x0, x3}
    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, true), lit(1, true)], false);
    let c1 = clauses.add(&[lit(0, true), lit(2, true)], false);
    let c2 = clauses.add(&[lit(0, false), lit(3, true)], false);
    bve.rebuild(&clauses);

    // GPU resolution produced one resolvent from (c0, c2) and classified
    // c1 as a root-satisfied parent (its resolvents were never generated).
    let resolvents = vec![(vec![lit(1, true), lit(3, true)], c0, c2, Vec::new())];
    let result = bve.finalize_elimination_from_resolution(
        Variable(0),
        &clauses,
        true,
        resolvents,
        Vec::new(),
        vec![c1],
        2,
    );

    assert!(result.eliminated);
    assert!(result.to_delete.contains(&c0));
    assert!(
        result.to_delete.contains(&c1),
        "satisfied parent must still be deleted"
    );
    assert!(result.to_delete.contains(&c2));
    assert!(
        !result.witness_entries.iter().any(|e| e.clause_idx == c1),
        "satisfied parent must NOT be a reconstruction witness (#8397)"
    );
    assert!(result.witness_entries.iter().any(|e| e.clause_idx == c0));
    assert!(result.witness_entries.iter().any(|e| e.clause_idx == c2));
}

/// One-sided witnesses are allowed when the missing polarity consists
/// entirely of root-satisfied parents (#8397 exception), matching the CPU
/// path in try_eliminate_with_gate_with_marks.
#[cfg(feature = "gpu")]
#[test]
fn test_gpu_finalize_allows_one_sided_when_missing_side_all_satisfied() {
    let mut bve = BVE::new(5);

    // c0 = {x0, x1} is the only positive clause and is root-satisfied.
    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, true), lit(1, true)], false);
    let c1 = clauses.add(&[lit(0, false), lit(2, true)], false);
    bve.rebuild(&clauses);

    let result = bve.finalize_elimination_from_resolution(
        Variable(0),
        &clauses,
        true,
        Vec::new(),
        Vec::new(),
        vec![c0],
        1,
    );

    assert!(
        result.eliminated,
        "missing polarity fully satisfied: elimination stays valid"
    );
    assert!(
        !result.witness_entries.iter().any(|e| e.clause_idx == c0),
        "satisfied parent must NOT be witnessed"
    );
    assert!(result.witness_entries.iter().any(|e| e.clause_idx == c1));
}

/// A genuinely one-sided variable (pure literal, no satisfied parents on
/// the missing side) must still be rejected by the reconstruction
/// completeness guard (#8179) on the GPU finalize path.
#[cfg(feature = "gpu")]
#[test]
fn test_gpu_finalize_rejects_pure_literal_one_sided_witnesses() {
    let mut bve = BVE::new(5);

    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    bve.rebuild(&clauses);

    let result = bve.finalize_elimination_from_resolution(
        Variable(0),
        &clauses,
        true,
        Vec::new(),
        Vec::new(),
        Vec::new(),
        0,
    );

    assert!(
        !result.eliminated,
        "pure literal must be rejected by the completeness guard"
    );
}
