// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::literal::Variable;

fn vd(levels: &[u32]) -> Vec<VarData> {
    levels
        .iter()
        .map(|&l| VarData {
            level: l,
            ..VarData::UNASSIGNED
        })
        .collect()
}

/// Verify that seen marking is idempotent and can be cleared
#[kani::proof]
#[kani::unwind(5)]
fn proof_seen_marking_idempotent() {
    const NUM_VARS: usize = 4;
    let mut analyzer = ConflictAnalyzer::new(NUM_VARS);
    let mut var_data = vd(&[0; NUM_VARS]);
    let var_idx: usize = kani::any();
    kani::assume(var_idx < NUM_VARS);

    // Initially not seen
    assert!(!analyzer.is_seen(var_idx, &var_data));

    // Mark seen
    analyzer.mark_seen(var_idx, &mut var_data);
    assert!(analyzer.is_seen(var_idx, &var_data));

    // Mark again (idempotent)
    analyzer.mark_seen(var_idx, &mut var_data);
    assert!(analyzer.is_seen(var_idx, &var_data));

    // Unmark
    analyzer.unmark_seen(var_idx, &mut var_data);
    assert!(!analyzer.is_seen(var_idx, &var_data));

    // Clear clears all
    analyzer.mark_seen(var_idx, &mut var_data);
    analyzer.clear(&mut var_data);
    assert!(!analyzer.is_seen(var_idx, &var_data));
}

/// Concrete regression harness: backtrack level for fixed learned clauses.
#[kani::proof]
fn test_backtrack_level_concrete() {
    const NUM_VARS: usize = 4;
    let mut analyzer = ConflictAnalyzer::new(NUM_VARS);

    // Fixed levels for tractability
    let var_data = vd(&[1, 3, 2, 4]);

    // Empty learned clause -> backtrack level is 0
    assert_eq!(analyzer.compute_backtrack_level(&var_data), 0);

    // Add literal at level 1
    analyzer.add_to_learned(Literal::positive(Variable(0)));
    assert_eq!(analyzer.compute_backtrack_level(&var_data), 1);

    // Add literal at level 3 -> max is now 3
    analyzer.add_to_learned(Literal::positive(Variable(1)));
    assert_eq!(analyzer.compute_backtrack_level(&var_data), 3);
}

/// Concrete harness: LBD follows CaDiCaL convention (distinct_levels - 1).
#[kani::proof]
fn test_lbd_cadical_convention_concrete() {
    const NUM_VARS: usize = 4;
    let mut analyzer = ConflictAnalyzer::new(NUM_VARS);

    // Levels: var0=3 (conflict), var1=1, var2=2, var3=1
    let var_data = vd(&[3, 1, 2, 1]);

    // Unit clause: asserting literal only, no learned → 1 distinct level → glue = 0
    analyzer.set_asserting_literal(Literal::positive(Variable(0)));
    assert_eq!(analyzer.compute_lbd(&var_data), 0);

    // Binary clause: asserting at level 3 + learned at level 1 → 2 distinct → glue = 1
    analyzer.add_to_learned(Literal::negative(Variable(1)));
    assert_eq!(analyzer.compute_lbd(&var_data), 1);

    // Ternary clause: + learned at level 2 → 3 distinct → glue = 2
    analyzer.add_to_learned(Literal::positive(Variable(2)));
    assert_eq!(analyzer.compute_lbd(&var_data), 2);

    // Duplicate level: + learned at level 1 (same as var1) → still 3 distinct → glue = 2
    analyzer.add_to_learned(Literal::negative(Variable(3)));
    assert_eq!(analyzer.compute_lbd(&var_data), 2);
}

/// Verify that learned clause has asserting literal first
#[kani::proof]
fn proof_asserting_literal_first_in_result() {
    const NUM_VARS: usize = 4;
    let mut analyzer = ConflictAnalyzer::new(NUM_VARS);

    // Set asserting literal
    let asserting_lit = Literal::positive(Variable(0));
    analyzer.set_asserting_literal(asserting_lit);

    // Add some other literals
    analyzer.add_to_learned(Literal::negative(Variable(1)));
    analyzer.add_to_learned(Literal::positive(Variable(2)));

    let result = analyzer.get_result(1, 2);

    // Asserting literal should be first
    assert!(!result.learned_clause.is_empty());
    assert_eq!(result.learned_clause[0], asserting_lit);
}

/// Verify reorder_for_watches doesn't crash and preserves clause length
#[kani::proof]
fn proof_reorder_preserves_length() {
    // Small clause for verification
    let mut clause = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ];
    let original_len = clause.len();

    let var_data = vd(&[3, 1, 2]);
    let backtrack_level: u32 = kani::any();
    kani::assume(backtrack_level <= 3);

    reorder_for_watches(&mut clause, &var_data, backtrack_level);

    // Length preserved
    assert_eq!(clause.len(), original_len);
}

// ========================================================================
// Concrete conflict-result regression harnesses.
// These checks validate ConflictAnalyzer result assembly on fixed states and
// do NOT execute the full Solver::analyze_conflict() resolution loop.
// ========================================================================

/// Concrete regression harness: hand-built learned clause has single
/// conflict-level literal.
#[kani::proof]
fn test_1uip_single_literal_at_conflict_level_concrete() {
    const NUM_VARS: usize = 4;
    let mut analyzer = ConflictAnalyzer::new(NUM_VARS);

    // Conflict level
    let conflict_level: u32 = 3;

    // Levels for each variable: only var 0 is at conflict level
    // Other variables are at lower levels (1 and 2)
    let levels: [u32; NUM_VARS] = [3, 1, 2, 1];

    // Asserting literal (UIP) is var 0 at conflict level
    let asserting_lit = Literal::positive(Variable(0));
    analyzer.set_asserting_literal(asserting_lit);

    // Other literals in learned clause are at lower levels
    analyzer.add_to_learned(Literal::negative(Variable(1))); // level 1
    analyzer.add_to_learned(Literal::positive(Variable(2))); // level 2

    let result = analyzer.get_result(2, 2); // backtrack to level 2

    // Count how many literals are at conflict level
    let count_at_conflict = result
        .learned_clause
        .iter()
        .filter(|lit| levels[lit.variable().index()] == conflict_level)
        .count();

    // 1UIP property: exactly one literal at conflict level
    assert_eq!(count_at_conflict, 1);

    // That literal should be the asserting literal (first position)
    assert_eq!(result.learned_clause[0], asserting_lit);
}

/// Concrete regression harness: backtrack level is second-highest level.
#[kani::proof]
fn test_backtrack_level_is_second_highest_concrete() {
    const NUM_VARS: usize = 4;
    let mut analyzer = ConflictAnalyzer::new(NUM_VARS);

    // Levels: var 0 at level 5 (conflict), var 1 at level 3, var 2 at level 2
    let var_data = vd(&[5, 3, 2, 1]);

    // Asserting literal at conflict level 5
    analyzer.set_asserting_literal(Literal::positive(Variable(0)));

    // Other literals at lower levels
    analyzer.add_to_learned(Literal::negative(Variable(1))); // level 3
    analyzer.add_to_learned(Literal::positive(Variable(2))); // level 2

    let backtrack_level = analyzer.compute_backtrack_level(&var_data);

    // Backtrack level should be the second-highest: 3
    // (Asserting literal is at 5, next highest is 3)
    assert_eq!(backtrack_level, 3);
}

/// Verify learned clause is non-empty when asserting literal is set
#[kani::proof]
fn proof_learned_clause_non_empty_with_asserting() {
    const NUM_VARS: usize = 4;
    let mut analyzer = ConflictAnalyzer::new(NUM_VARS);

    // Set any asserting literal
    let var_idx: u32 = kani::any();
    kani::assume(var_idx < NUM_VARS as u32);
    let polarity: bool = kani::any();
    let asserting_lit = if polarity {
        Literal::positive(Variable(var_idx))
    } else {
        Literal::negative(Variable(var_idx))
    };

    analyzer.set_asserting_literal(asserting_lit);

    let result = analyzer.get_result(0, 1);

    // Learned clause must have at least the asserting literal
    assert!(!result.learned_clause.is_empty());
    assert_eq!(result.learned_clause[0], asserting_lit);
}

/// Verify analyzer reset clears all state
#[kani::proof]
#[kani::unwind(5)]
fn proof_clear_resets_all_state() {
    const NUM_VARS: usize = 4;
    let mut analyzer = ConflictAnalyzer::new(NUM_VARS);
    let mut var_data = vd(&[0; NUM_VARS]);

    // Mark a symbolic variable as seen (CBMC explores all NUM_VARS values)
    let v0: usize = kani::any();
    kani::assume(v0 < NUM_VARS);

    analyzer.mark_seen(v0, &mut var_data);
    // Also mark a concrete variable to test multi-mark clearing
    analyzer.mark_seen(1, &mut var_data);
    analyzer.set_asserting_literal(Literal::positive(Variable(0)));
    analyzer.add_to_learned(Literal::negative(Variable(1)));

    // Clear
    analyzer.clear(&mut var_data);

    // Verify all state is reset — symbolic v0 must be cleared for ALL values
    assert!(!analyzer.is_seen(v0, &var_data));
    assert!(!analyzer.is_seen(1, &var_data));
    assert!(analyzer.asserting_lit.is_none());
    assert!(analyzer.learned.is_empty());
}

// ========================================================================
// Gap 4: Conflict analysis structural invariants
// ========================================================================

/// Verify reorder_for_watches places the literal at backtrack_level at position 1.
///
/// Invariant: After reorder_for_watches, clause[1] must be at the backtrack
/// level (when such a literal exists in the clause). This is required by the
/// 2WL scheme: the second watched literal must be the one at the backtrack
/// level so that after backtracking, the clause becomes unit with clause[0]
/// (the asserting literal) becoming the only unassigned watched literal.
#[kani::proof]
fn proof_reorder_places_backtrack_level_at_pos1() {
    const NUM_VARS: usize = 4;
    // Clause: asserting lit (level 5) at [0], then lits at levels 3, 1, 2
    let mut clause = vec![
        Literal::positive(Variable(0)), // level 5 (asserting, stays at [0])
        Literal::positive(Variable(1)), // level 3
        Literal::positive(Variable(2)), // level 1
        Literal::positive(Variable(3)), // level 2
    ];

    let var_data = vd(&[5, 3, 1, 2]);
    let backtrack_level: u32 = 3; // second-highest level

    reorder_for_watches(&mut clause, &var_data, backtrack_level);

    // clause[0] must be preserved (asserting literal)
    assert_eq!(clause[0], Literal::positive(Variable(0)));

    // clause[1] must be the literal at backtrack_level (level 3 = var 1)
    assert_eq!(
        var_data[clause[1].variable().index()].level,
        backtrack_level,
        "clause[1] must be at the backtrack level after reorder"
    );
}

/// Verify reorder_for_watches preserves all literals (no duplicates or drops).
///
/// Invariant: Reorder is a permutation — every literal before the reorder
/// must appear exactly once after it.
#[kani::proof]
fn proof_reorder_preserves_literals() {
    const NUM_VARS: usize = 3;
    let lit0 = Literal::positive(Variable(0));
    let lit1 = Literal::negative(Variable(1));
    let lit2 = Literal::positive(Variable(2));
    let mut clause = vec![lit0, lit1, lit2];

    let var_data = vd(&[3, 1, 2]);
    let backtrack_level: u32 = kani::any();
    kani::assume(backtrack_level <= 3);

    reorder_for_watches(&mut clause, &var_data, backtrack_level);

    // All original literals must still be present
    assert!(clause.contains(&lit0), "lit0 must be preserved");
    assert!(clause.contains(&lit1), "lit1 must be preserved");
    assert!(clause.contains(&lit2), "lit2 must be preserved");
    assert_eq!(clause.len(), 3, "clause length must be preserved");
}

/// Verify compute_backtrack_level is always strictly less than the asserting level.
///
/// Invariant: The backtrack level (second-highest level among non-asserting
/// literals) must be strictly less than the asserting literal's level.
/// If the learned clause is unit (only the asserting literal), the
/// backtrack level is 0.
#[kani::proof]
fn proof_backtrack_level_below_conflict_level() {
    const NUM_VARS: usize = 4;
    let mut analyzer = ConflictAnalyzer::new(NUM_VARS);

    // Asserting literal at level 4
    let asserting_var = 0usize;
    let conflict_level: u32 = 4;
    let var_data = vd(&[conflict_level, 1, 2, 3]);

    analyzer.set_asserting_literal(Literal::positive(Variable(asserting_var as u32)));

    // Symbolically add 0-3 learned literals (at levels below conflict_level)
    let add0: bool = kani::any();
    let add1: bool = kani::any();
    let add2: bool = kani::any();

    if add0 {
        analyzer.add_to_learned(Literal::negative(Variable(1))); // level 1
    }
    if add1 {
        analyzer.add_to_learned(Literal::positive(Variable(2))); // level 2
    }
    if add2 {
        analyzer.add_to_learned(Literal::negative(Variable(3))); // level 3
    }

    let bt_level = analyzer.compute_backtrack_level(&var_data);

    // Backtrack level must be strictly below the conflict level
    assert!(
        bt_level < conflict_level,
        "Backtrack level ({bt_level}) must be < conflict level ({conflict_level})"
    );
}

/// Verify LBD is bounded by clause size minus 1.
///
/// Invariant: LBD (glue) < clause_size for all non-trivial clauses.
/// CaDiCaL analyze.cpp:1199 asserts this invariant.
#[kani::proof]
fn proof_lbd_bounded_by_clause_size() {
    const NUM_VARS: usize = 4;
    let mut analyzer = ConflictAnalyzer::new(NUM_VARS);

    // Each variable at a distinct level to maximize LBD
    let var_data = vd(&[4, 1, 2, 3]);

    // Set asserting literal (always present)
    analyzer.set_asserting_literal(Literal::positive(Variable(0)));

    // Symbolically add 0 to 3 learned literals
    let add1: bool = kani::any();
    let add2: bool = kani::any();
    let add3: bool = kani::any();

    let mut clause_size: u32 = 1; // asserting literal always present
    if add1 {
        analyzer.add_to_learned(Literal::negative(Variable(1)));
        clause_size += 1;
    }
    if add2 {
        analyzer.add_to_learned(Literal::positive(Variable(2)));
        clause_size += 1;
    }
    if add3 {
        analyzer.add_to_learned(Literal::negative(Variable(3)));
        clause_size += 1;
    }

    let lbd = analyzer.compute_lbd(&var_data);

    // CaDiCaL invariant: glue < clause_size
    assert!(
        lbd < clause_size,
        "LBD ({lbd}) must be < clause_size ({clause_size})"
    );
}

/// Verify rollback_analyzed restores seen marks correctly.
///
/// Invariant: After rollback_analyzed(saved_size), variables added after
/// saved_size have their seen marks cleared, and variables added before
/// saved_size retain their seen marks.
#[kani::proof]
#[kani::unwind(5)]
fn proof_rollback_analyzed_correctness() {
    const NUM_VARS: usize = 4;
    let mut analyzer = ConflictAnalyzer::new(NUM_VARS);
    let mut var_data = vd(&[0; NUM_VARS]);

    // Mark variables 0 and 1 as seen
    analyzer.mark_seen(0, &mut var_data);
    analyzer.mark_seen(1, &mut var_data);
    let saved_size = analyzer.analyzed_vars().len();

    // Mark additional variables 2 and 3
    analyzer.mark_seen(2, &mut var_data);
    analyzer.mark_seen(3, &mut var_data);

    // Verify all 4 are seen
    assert!(analyzer.is_seen(0, &var_data));
    assert!(analyzer.is_seen(1, &var_data));
    assert!(analyzer.is_seen(2, &var_data));
    assert!(analyzer.is_seen(3, &var_data));

    // Rollback to saved_size
    analyzer.rollback_analyzed(saved_size, &mut var_data);

    // Variables 0 and 1 (before saved_size) should still be seen
    assert!(
        analyzer.is_seen(0, &var_data),
        "var 0 should retain seen mark"
    );
    assert!(
        analyzer.is_seen(1, &var_data),
        "var 1 should retain seen mark"
    );

    // Variables 2 and 3 (after saved_size) should be cleared
    assert!(
        !analyzer.is_seen(2, &var_data),
        "var 2 should be cleared by rollback"
    );
    assert!(
        !analyzer.is_seen(3, &var_data),
        "var 3 should be cleared by rollback"
    );

    // analyzed_vars length should be back to saved_size
    assert_eq!(analyzer.analyzed_vars().len(), saved_size);
}

#[test]
fn test_returned_buffers_restore_conflict_analyzer_capacity() {
    let mut analyzer = ConflictAnalyzer::new(4);
    analyzer.set_asserting_literal(Literal::positive(Variable(0)));
    analyzer.add_to_learned(Literal::negative(Variable(1)));
    analyzer.add_to_learned(Literal::positive(Variable(2)));
    analyzer.add_to_chain(11);
    analyzer.add_to_chain(17);

    let result = analyzer.get_result(1, 2);
    let learned_cap = result.learned_clause.capacity();
    let chain_cap = result.resolution_chain.capacity();

    analyzer.return_learned_buf(result.learned_clause);
    analyzer.return_chain_buf(result.resolution_chain);

    assert!(analyzer.learned.is_empty());
    assert!(analyzer.resolution_chain.is_empty());
    assert_eq!(analyzer.learned.capacity(), learned_cap);
    assert_eq!(analyzer.resolution_chain.capacity(), chain_cap);
}
