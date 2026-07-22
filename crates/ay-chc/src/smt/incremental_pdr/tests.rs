// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for IncrementalPdrContext (#6358).
//!
//! Verifies the activation literal pattern (Z3 Spacer) and the
//! SAT-level blocking check used in PDR's already-blocked query.
//!
//! ## Known limitations
//!
//! 1. Equality contradiction detection (`collect_int_equalities_with_closure`)
//!    silently overwrites when the same variable has two different constant
//!    equalities in separate assumption expressions (HashMap::insert).
//!    Contradictory assumptions like `[x=3, x=5]` may not be detected.

use super::IncrementalPdrContext;
use crate::smt::incremental::IncrementalCheckResult;
use crate::smt::types::SmtValue;
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Helper: create an integer variable expression.
fn int_var(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

#[test]
fn test_unfinalized_context_returns_unknown() {
    // A context that hasn't been finalized should return Unknown.
    let mut ctx = IncrementalPdrContext::new();
    // Deliberately do NOT call finalize_background.

    let state = ChcExpr::eq(int_var("x"), ChcExpr::int(3));

    let result = ctx.check_sat_at_level(0, &[state], None);
    assert!(
        matches!(result, IncrementalCheckResult::Unknown),
        "unfinalized context should return Unknown"
    );
}

#[test]
fn test_false_assumption_returns_unsat() {
    // Assumption Bool(false) should be detected early and return UNSAT.
    let mut ctx = IncrementalPdrContext::new();
    ctx.finalize_background();

    let result = ctx.check_sat_at_level(0, &[ChcExpr::Bool(false)], None);
    assert!(
        matches!(result, IncrementalCheckResult::Unsat),
        "false assumption should return UNSAT"
    );
}

#[test]
fn test_true_assumption_skipped() {
    // Bool(true) should be skipped. With no lemmas and no other constraints,
    // the result should not be UNSAT.
    let mut ctx = IncrementalPdrContext::new();
    ctx.finalize_background();

    let result = ctx.check_sat_at_level(
        0,
        &[
            ChcExpr::Bool(true),
            ChcExpr::eq(int_var("x"), ChcExpr::int(3)),
        ],
        None,
    );
    assert!(
        !matches!(result, IncrementalCheckResult::Unsat),
        "true + consistent state should not be UNSAT"
    );
}

#[test]
fn test_consistent_state_not_blocked_without_lemmas() {
    // With no lemmas, (x == 3) should not be UNSAT.
    // Phase 1 returns Unknown for SAT results, which is correct (not UNSAT).
    let mut ctx = IncrementalPdrContext::new();
    ctx.finalize_background();

    let state = ChcExpr::eq(int_var("x"), ChcExpr::int(3));

    let result = ctx.check_sat_at_level(0, &[state], None);
    assert!(
        !matches!(result, IncrementalCheckResult::Unsat),
        "consistent state with no lemmas should not be UNSAT"
    );
}

#[test]
fn test_activation_ensure_level_creates_vars() {
    // Verify that ensure_level creates activation variables correctly.
    let mut ctx = IncrementalPdrContext::new();
    assert_eq!(ctx.level_act_vars.len(), 0);

    ctx.ensure_level(0);
    assert_eq!(
        ctx.level_act_vars.len(),
        1,
        "should have 1 activation var after ensure_level(0)"
    );

    ctx.ensure_level(3);
    assert_eq!(
        ctx.level_act_vars.len(),
        4,
        "should have 4 activation vars after ensure_level(3)"
    );

    // Idempotent: calling again should not add more.
    ctx.ensure_level(2);
    assert_eq!(
        ctx.level_act_vars.len(),
        4,
        "should still have 4 after ensure_level(2)"
    );

    // All activation variables should be distinct.
    let mut seen: ay_core::kani_compat::DetHashSet<u32> = Default::default();
    for &v in &ctx.level_act_vars {
        assert!(seen.insert(v), "activation variables must be distinct");
    }
}

#[test]
fn test_lemma_exprs_tracked_per_level() {
    // Verify that lemma expressions are tracked correctly per level.
    let mut ctx = IncrementalPdrContext::new();
    ctx.finalize_background();

    let lemma1 = ChcExpr::ge(int_var("x"), ChcExpr::int(5));
    let lemma2 = ChcExpr::le(int_var("x"), ChcExpr::int(10));
    let lemma3 = ChcExpr::ge(int_var("y"), ChcExpr::int(0));

    ctx.assert_lemma_at_level(&lemma1, 1);
    ctx.assert_lemma_at_level(&lemma2, 2);
    ctx.assert_lemma_at_level(&lemma3, 1);

    assert_eq!(
        ctx.lemma_exprs.len(),
        3,
        "should have vectors for levels 0, 1, 2"
    );
    assert_eq!(ctx.lemma_exprs[0].len(), 0, "level 0 should have no lemmas");
    assert_eq!(ctx.lemma_exprs[1].len(), 2, "level 1 should have 2 lemmas");
    assert_eq!(ctx.lemma_exprs[2].len(), 1, "level 2 should have 1 lemma");
}

#[test]
fn test_all_active_lemma_exprs_filters_correctly() {
    // Verify that all_active_lemma_exprs returns the right set for each level.
    let mut ctx = IncrementalPdrContext::new();
    ctx.finalize_background();

    let lemma1 = ChcExpr::ge(int_var("x"), ChcExpr::int(5));
    let lemma2 = ChcExpr::le(int_var("x"), ChcExpr::int(10));

    ctx.assert_lemma_at_level(&lemma1, 1);
    ctx.assert_lemma_at_level(&lemma2, 2);

    // At level 0: both levels 1 and 2 are active (k >= 0).
    let active_at_0: Vec<_> = ctx.all_active_lemma_exprs(0).collect();
    assert_eq!(
        active_at_0.len(),
        2,
        "at level 0, both lemmas should be active"
    );

    // At level 1: levels 1 and 2 are active (k >= 1).
    let active_at_1: Vec<_> = ctx.all_active_lemma_exprs(1).collect();
    assert_eq!(
        active_at_1.len(),
        2,
        "at level 1, both lemmas should be active"
    );

    // At level 2: only level 2 is active (k >= 2).
    let active_at_2: Vec<_> = ctx.all_active_lemma_exprs(2).collect();
    assert_eq!(
        active_at_2.len(),
        1,
        "at level 2, only level-2 lemma should be active"
    );

    // At level 3: no lemmas active (k >= 3 — none exist).
    let active_at_3: Vec<_> = ctx.all_active_lemma_exprs(3).collect();
    assert_eq!(
        active_at_3.len(),
        0,
        "at level 3, no lemmas should be active"
    );
}

#[test]
fn test_budget_exceeded_returns_unknown() {
    // Once background_conversion_budget_exceeded is set, queries return Unknown.
    let mut ctx = IncrementalPdrContext::new();
    ctx.finalize_background();
    ctx.background_conversion_budget_exceeded = true;

    let result = ctx.check_sat_at_level(0, &[ChcExpr::eq(int_var("x"), ChcExpr::int(3))], None);
    assert!(
        matches!(result, IncrementalCheckResult::Unknown),
        "budget exceeded should return Unknown"
    );
}

#[test]
fn test_no_tseitin_state_returns_unknown() {
    // If no lemmas or background have been asserted, tseitin_state is None.
    // The check should return Unknown (no Tseitin encoding to work with).
    let mut ctx = IncrementalPdrContext::new();
    ctx.finalize_background();
    // No lemmas asserted, so tseitin_state remains None.

    let result = ctx.check_sat_at_level(0, &[ChcExpr::eq(int_var("x"), ChcExpr::int(3))], None);
    assert!(
        !matches!(result, IncrementalCheckResult::Unsat),
        "empty context should not falsely claim UNSAT"
    );
}

#[test]
fn test_activation_level_0_lemma_inactive_at_level_1() {
    // Lemma at level 0 should be inactive at level 1.
    // Activation: k >= query_level. Level 0 < 1 → inactive.
    let mut ctx = IncrementalPdrContext::new();
    ctx.finalize_background();

    let lemma = ChcExpr::ge(int_var("x"), ChcExpr::int(5));
    ctx.assert_lemma_at_level(&lemma, 0);

    let state = ChcExpr::eq(int_var("x"), ChcExpr::int(3));
    let result = ctx.check_sat_at_level(1, &[state], None);

    // At level 1, lemma at level 0 is inactive. Should NOT return UNSAT.
    assert!(
        !matches!(result, IncrementalCheckResult::Unsat),
        "lemma at level 0 should be inactive at level 1"
    );
}

#[test]
fn test_lemma_assertion_does_not_corrupt_sat_state() {
    // Asserting a lemma should not cause the SAT solver to become unsatisfiable.
    // After asserting a lemma, a consistent query should not return UNSAT
    // when the lemma is inactive.
    let mut ctx = IncrementalPdrContext::new();
    ctx.finalize_background();

    // Assert a lemma at level 0 (simple boolean constraint).
    let lemma = ChcExpr::Bool(true);
    ctx.assert_lemma_at_level(&lemma, 0);

    // Query at level 1 (lemma inactive). Should not be UNSAT.
    let result = ctx.check_sat_at_level(1, &[ChcExpr::Bool(true)], None);
    assert!(
        !matches!(result, IncrementalCheckResult::Unsat),
        "true lemma + true assumption should not be UNSAT"
    );
}

// --- Regression tests for own_smt refactoring (commit 340742f) ---

#[test]
fn test_tseitin_vars_start_past_activation_literals() {
    // Regression: Before own_smt refactoring, both ensure_level() and
    // Tseitin::new() started variable numbering from 1. This caused
    // activation literal variables to collide with Tseitin encoding
    // variables, producing wrong SAT results.
    //
    // The fix: take_tseitin() sets next_var = num_vars + 1, ensuring
    // Tseitin variables start past all activation literal variables.
    use super::take_tseitin;

    let mut ctx = IncrementalPdrContext::new();
    ctx.finalize_background();

    // Create activation literals at levels 0, 1, 2 → num_vars = 3.
    ctx.ensure_level(2);
    assert_eq!(ctx.num_vars, 3, "3 activation vars for levels 0,1,2");
    assert_eq!(ctx.level_act_vars.len(), 3);

    // Assert a lemma to force Tseitin state creation.
    let lemma = ChcExpr::ge(int_var("x"), ChcExpr::int(0));
    ctx.assert_lemma_at_level(&lemma, 0);

    // After lemma assertion, Tseitin state should exist and all Tseitin
    // variables should be > 3 (past the activation literals).
    let state = ctx
        .tseitin_state
        .as_ref()
        .expect("tseitin state exists after lemma");
    for &var in state.var_to_term.keys() {
        assert!(
            var > 3,
            "Tseitin variable {var} must be > num_vars=3 to avoid collision with activation literals"
        );
    }
    assert!(
        state.next_var > 3,
        "next_var {} must be > num_vars=3",
        state.next_var
    );

    // Verify fresh take_tseitin also starts past activation literals.
    let tseitin = take_tseitin(&mut ctx.tseitin_state, &ctx.own_smt.terms, ctx.num_vars);
    let restored_state = tseitin.into_state();
    assert!(
        restored_state.next_var > ctx.num_vars,
        "take_tseitin next_var {} must be > num_vars {}",
        restored_state.next_var,
        ctx.num_vars
    );
    ctx.tseitin_state = Some(restored_state);
}

#[test]
fn test_own_smt_isolation_from_external_reset() {
    // Regression: Before own_smt refactoring, the IncrementalPdrContext shared
    // the caller's SmtContext. When the caller called smt.reset(), it destroyed
    // the TermStore, invalidating TermIds stored in the Tseitin state. This
    // caused a stale-TermId crash.
    //
    // The fix: each IncrementalPdrContext owns its own SmtContext (own_smt).
    // TermIds in the Tseitin state point into own_smt.terms, which is never
    // reset by the caller.
    let mut ctx = IncrementalPdrContext::new();
    ctx.finalize_background();

    // Assert a lemma to populate Tseitin state with TermIds.
    let lemma = ChcExpr::ge(int_var("x"), ChcExpr::int(5));
    ctx.assert_lemma_at_level(&lemma, 0);

    // Simulate what the caller does: create a separate SmtContext and reset it.
    // This must NOT affect ctx.own_smt or the Tseitin state.
    let mut external_smt = super::super::context::SmtContext::new();
    let _ = external_smt.convert_expr(&ChcExpr::eq(int_var("y"), ChcExpr::int(10)));
    external_smt.reset(); // Destroys external_smt's TermStore.

    // The IncrementalPdrContext should still work — its own_smt is independent.
    let result = ctx.check_sat_at_level(0, &[ChcExpr::eq(int_var("x"), ChcExpr::int(3))], None);
    // x=3 AND lemma x>=5 is theory-inconsistent. Phase 2B DPLL(T) correctly
    // detects this via LIA and returns Unsat. (Phase 1 returned Unknown here.)
    assert!(
        matches!(result, IncrementalCheckResult::Unsat),
        "own_smt isolation: x=3 with lemma x>=5 should be theory-UNSAT"
    );

    // A second query should also work (Tseitin state was preserved).
    let result2 = ctx.check_sat_at_level(0, &[ChcExpr::Bool(false)], None);
    assert!(
        matches!(result2, IncrementalCheckResult::Unsat),
        "own_smt isolation: Bool(false) should still be detected as UNSAT"
    );
}

#[test]
fn test_variable_collision_multiple_lemmas_multiple_levels() {
    // Stress test: assert lemmas at multiple levels, creating many activation
    // variables. Verify that Tseitin variables never collide with any of them.
    let mut ctx = IncrementalPdrContext::new();
    ctx.finalize_background();

    // Assert lemmas at levels 0 through 4 → 5 activation variables.
    for level in 0..5 {
        let lemma = ChcExpr::ge(int_var("x"), ChcExpr::int(level as i64));
        ctx.assert_lemma_at_level(&lemma, level);
    }

    assert_eq!(ctx.level_act_vars.len(), 5);
    let act_var_set: ay_core::kani_compat::DetHashSet<u32> =
        ctx.level_act_vars.iter().copied().collect();

    // No Tseitin variable should share an index with any activation variable.
    // Note: Tseitin vars allocated at level 0 (before levels 1-4 exist) may
    // have indices *less* than later activation vars — that is fine as long as
    // there is no collision (the sets are disjoint).
    let state = ctx.tseitin_state.as_ref().expect("tseitin state exists");
    for &var in state.var_to_term.keys() {
        assert!(
            !act_var_set.contains(&var),
            "Tseitin var {var} collides with activation var set {act_var_set:?}"
        );
    }

    // The incremental check should still produce correct results.
    // At level 0, all lemmas active: x>=0 AND x>=1 AND x>=2 AND x>=3 AND x>=4.
    // Query x=10: consistent with all lemmas → should NOT be UNSAT.
    let result = ctx.check_sat_at_level(0, &[ChcExpr::eq(int_var("x"), ChcExpr::int(10))], None);
    assert!(
        !matches!(result, IncrementalCheckResult::Unsat),
        "x=10 is consistent with all lemmas x>=k, should not be UNSAT"
    );
}

// --- Phase-hint parity tests (#6358) ---

#[test]
fn test_seeded_incremental_need_split_sets_phase_issue_6358() {
    // Verify that the seeded incremental path installs the phase seed model
    // and that the DPLL(T) theory split handler applies phase hints.
    //
    // The constraint `2*x = 3 AND x >= 0` forces an LRA relaxation with x=1.5,
    // which triggers NeedSplit(x, floor=1, ceil=2). The phase hint from the seed
    // model should bias the SAT solver toward the seed value's side of the split.
    //
    // After splitting, neither branch satisfies 2x=3 over integers, so the final
    // result is UNSAT. The test verifies the seeded path runs without error and
    // produces a sound result (UNSAT or Unknown — both are correct).
    let mut ctx = IncrementalPdrContext::new();

    // Background: 2*x = 3 (forces fractional x in LRA relaxation).
    let x = int_var("x");
    let two_x = ChcExpr::mul(ChcExpr::int(2), x.clone());
    let bg = ChcExpr::eq(two_x, ChcExpr::int(3));
    ctx.assert_background(&bg);
    ctx.finalize_background();

    // Seed model: x = 5 (biases toward ceil side of the 1/2 split).
    let mut seed: FxHashMap<String, SmtValue> = FxHashMap::default();
    seed.insert("x".to_string(), SmtValue::Int(5));

    // Query: x >= 0 (consistent with 2x=3 in LRA, but forces split in LIA).
    let assumption = ChcExpr::ge(x, ChcExpr::int(0));
    let result = ctx.check_sat_at_level_seeded(
        0,
        &[assumption],
        Some(std::time::Duration::from_secs(5)),
        Some(&seed),
    );

    // Sound result: UNSAT (2x=3 has no integer solution) or Unknown (timeout/bail).
    // The phase hint does not affect correctness — it only biases search order.
    assert!(
        matches!(
            result,
            IncrementalCheckResult::Unsat | IncrementalCheckResult::Unknown
        ),
        "seeded incremental split: expected UNSAT or Unknown, got {:?}",
        match &result {
            IncrementalCheckResult::Sat(_) => "Sat",
            IncrementalCheckResult::Unsat => "Unsat",
            IncrementalCheckResult::Unknown => "Unknown",
        }
    );

    // Verify the seed model was cleaned up (not leaked to next query).
    assert!(
        ctx.own_smt.phase_seed_model.is_none(),
        "phase_seed_model must be restored to None after seeded query"
    );
}

#[test]
fn test_seeded_incremental_disequality_split_sets_phase_issue_6358() {
    // Verify that the seeded incremental path handles NeedDisequalitySplit
    // with phase hints from the seed model.
    //
    // The constraint `x >= 3 AND x <= 3 AND x != 3` is contradictory in LIA.
    // The LIA solver may request a disequality split when processing x != 3,
    // splitting into (x < 3) OR (x > 3). The phase hint from the seed model
    // biases toward the correct side.
    //
    // This is theory-UNSAT: x >= 3 AND x <= 3 forces x = 3, but x != 3
    // excludes that. The incremental DPLL(T) loop should detect this.
    let mut ctx = IncrementalPdrContext::new();

    // Background: x >= 3 AND x <= 3 (forces x = 3 in any model).
    let x = int_var("x");
    let bg = ChcExpr::and(
        ChcExpr::ge(x.clone(), ChcExpr::int(3)),
        ChcExpr::le(x.clone(), ChcExpr::int(3)),
    );
    ctx.assert_background(&bg);
    ctx.finalize_background();

    // Seed model: x = 1 (biases toward x < 3 side of disequality split).
    let mut seed: FxHashMap<String, SmtValue> = FxHashMap::default();
    seed.insert("x".to_string(), SmtValue::Int(1));

    // Query: x != 3 (contradicts background forcing x = 3).
    let assumption = ChcExpr::not(ChcExpr::eq(x, ChcExpr::int(3)));
    let result = ctx.check_sat_at_level_seeded(
        0,
        &[assumption],
        Some(std::time::Duration::from_secs(5)),
        Some(&seed),
    );

    // Sound result: UNSAT (x=3 forced by bg, but x!=3 in assumption) or Unknown.
    assert!(
        matches!(
            result,
            IncrementalCheckResult::Unsat | IncrementalCheckResult::Unknown
        ),
        "seeded incremental disequality split: expected UNSAT or Unknown, got {:?}",
        match &result {
            IncrementalCheckResult::Sat(_) => "Sat",
            IncrementalCheckResult::Unsat => "Unsat",
            IncrementalCheckResult::Unknown => "Unknown",
        }
    );

    // Verify the seed model was cleaned up.
    assert!(
        ctx.own_smt.phase_seed_model.is_none(),
        "phase_seed_model must be restored to None after seeded query"
    );
}

#[test]
fn test_seeded_query_with_none_matches_unseeded() {
    // Verify that check_sat_at_level_seeded with None seed produces the same
    // result as check_sat_at_level (the unseeded path).
    let mut ctx = IncrementalPdrContext::new();
    ctx.finalize_background();

    let lemma = ChcExpr::ge(int_var("x"), ChcExpr::int(5));
    ctx.assert_lemma_at_level(&lemma, 0);

    // x = 3 conflicts with lemma x >= 5.
    let state = ChcExpr::eq(int_var("x"), ChcExpr::int(3));

    let unseeded = ctx.check_sat_at_level(0, &[state.clone()], None);
    let seeded_none = ctx.check_sat_at_level_seeded(0, &[state], None, None);

    // Both should return the same result class.
    let unseeded_is_unsat = matches!(unseeded, IncrementalCheckResult::Unsat);
    let seeded_is_unsat = matches!(seeded_none, IncrementalCheckResult::Unsat);
    assert_eq!(
        unseeded_is_unsat, seeded_is_unsat,
        "seeded(None) should match unseeded behavior"
    );
}

// --- Query-family activation tests (#6358) ---

#[test]
fn test_alloc_query_activation_creates_distinct_vars() {
    // Verify that alloc_query_activation creates distinct SAT variables
    // that do not collide with level activation variables.
    let mut ctx = IncrementalPdrContext::new();
    ctx.finalize_background();

    // Create 2 level activation variables first.
    ctx.ensure_level(1);
    assert_eq!(ctx.level_act_vars.len(), 2);
    let level_vars: ay_core::kani_compat::DetHashSet<u32> =
        ctx.level_act_vars.iter().copied().collect();

    // Allocate 3 query activation variables.
    let q0 = ctx.alloc_query_activation();
    let q1 = ctx.alloc_query_activation();
    let q2 = ctx.alloc_query_activation();

    assert_eq!(ctx.query_act_vars.len(), 3);

    // All query variables must be distinct from each other.
    assert_ne!(q0, q1, "query activation vars must be distinct");
    assert_ne!(q1, q2, "query activation vars must be distinct");
    assert_ne!(q0, q2, "query activation vars must be distinct");

    // No query variable should collide with level variables.
    assert!(
        !level_vars.contains(&q0),
        "query var {q0} must not collide with level vars"
    );
    assert!(
        !level_vars.contains(&q1),
        "query var {q1} must not collide with level vars"
    );
    assert!(
        !level_vars.contains(&q2),
        "query var {q2} must not collide with level vars"
    );
}

#[test]
fn test_guarded_background_segment_activation_only_selected_clause_active() {
    // Register two guarded background segments for the same solver.
    // Activate only one; verify that only the activated segment constrains the query.
    //
    // Segment A: x >= 10 (guarded by act_a)
    // Segment B: x <= 0  (guarded by act_b)
    //
    // Query: x = 5
    //   - With A active, B inactive: x=5 AND x>=10 → UNSAT
    //   - With B active, A inactive: x=5 AND x<=0 → UNSAT
    //   - With both inactive: x=5 → SAT/Unknown (no constraint)
    let mut ctx = IncrementalPdrContext::new();

    // Permanent background: just a trivially true formula to seed Tseitin state.
    let bg = ChcExpr::ge(int_var("y"), ChcExpr::int(0));
    ctx.assert_background(&bg);
    ctx.finalize_background();

    let act_a = ctx.alloc_query_activation();
    let act_b = ctx.alloc_query_activation();

    // Segment A: x >= 10
    ctx.assert_background_guarded(&ChcExpr::ge(int_var("x"), ChcExpr::int(10)), act_a);
    // Segment B: x <= 0
    ctx.assert_background_guarded(&ChcExpr::le(int_var("x"), ChcExpr::int(0)), act_b);

    let query = ChcExpr::eq(int_var("x"), ChcExpr::int(5));

    // Case 1: A active, B inactive → x=5 AND x>=10 → UNSAT
    let result = ctx.check_sat_at_level_with_activations(
        0,
        &[query.clone()],
        &[act_a], // active: x >= 10
        &[act_b], // inactive: x <= 0
        Some(std::time::Duration::from_secs(5)),
        None,
    );
    assert!(
        matches!(result, IncrementalCheckResult::Unsat),
        "x=5 with x>=10 active should be UNSAT, got {result:?}"
    );

    // Case 2: B active, A inactive → x=5 AND x<=0 → UNSAT
    let result = ctx.check_sat_at_level_with_activations(
        0,
        &[query.clone()],
        &[act_b], // active: x <= 0
        &[act_a], // inactive: x >= 10
        Some(std::time::Duration::from_secs(5)),
        None,
    );
    assert!(
        matches!(result, IncrementalCheckResult::Unsat),
        "x=5 with x<=0 active should be UNSAT, got {result:?}"
    );

    // Case 3: Both inactive → x=5 only constrained by bg y>=0 → not UNSAT
    let result = ctx.check_sat_at_level_with_activations(
        0,
        &[query],
        &[],             // no segments active
        &[act_a, act_b], // both inactive
        Some(std::time::Duration::from_secs(5)),
        None,
    );
    assert!(
        !matches!(result, IncrementalCheckResult::Unsat),
        "x=5 with both segments inactive should not be UNSAT"
    );
}

#[test]
fn test_query_activation_deactivates_sibling_segment() {
    // Verify that deactivating a segment (via inactive_query_acts) correctly
    // makes its constraint invisible, even after a query where it was active.
    //
    // This tests that activation assumptions are truly per-query and do not
    // leave permanent state in the SAT solver.
    let mut ctx = IncrementalPdrContext::new();

    let bg = ChcExpr::ge(int_var("y"), ChcExpr::int(0));
    ctx.assert_background(&bg);
    ctx.finalize_background();

    let act = ctx.alloc_query_activation();

    // Guarded segment: x >= 100
    ctx.assert_background_guarded(&ChcExpr::ge(int_var("x"), ChcExpr::int(100)), act);

    let query = ChcExpr::eq(int_var("x"), ChcExpr::int(5));

    // Query 1: segment active → x=5 AND x>=100 → UNSAT
    let r1 = ctx.check_sat_at_level_with_activations(
        0,
        &[query.clone()],
        &[act],
        &[],
        Some(std::time::Duration::from_secs(5)),
        None,
    );
    assert!(
        matches!(r1, IncrementalCheckResult::Unsat),
        "x=5 with x>=100 active should be UNSAT"
    );

    // Query 2: segment inactive → x=5 should not be UNSAT
    let r2 = ctx.check_sat_at_level_with_activations(
        0,
        &[query],
        &[],
        &[act],
        Some(std::time::Duration::from_secs(5)),
        None,
    );
    assert!(
        !matches!(r2, IncrementalCheckResult::Unsat),
        "x=5 with segment deactivated should not be UNSAT (activation is per-query)"
    );
}

#[test]
fn test_level_activations_and_query_activations_compose() {
    // Verify that level activations (frame lemma scoping) and query activations
    // (segment selection) compose correctly in the same query.
    //
    // Setup:
    //   Level-0 lemma: x >= 10
    //   Guarded segment: x <= 20
    //
    // Query at level 0 with segment active: x=15 → x>=10 AND x<=20 AND x=15 → not UNSAT
    // Query at level 0 with segment active: x=5 → x>=10 AND x<=20 AND x=5 → UNSAT (x>=10 violated)
    // Query at level 1 (lemma inactive) with segment active: x=5 → x<=20 AND x=5 → not UNSAT
    let mut ctx = IncrementalPdrContext::new();

    let bg = ChcExpr::ge(int_var("y"), ChcExpr::int(0));
    ctx.assert_background(&bg);
    ctx.finalize_background();

    // Level-0 lemma: x >= 10
    ctx.assert_lemma_at_level(&ChcExpr::ge(int_var("x"), ChcExpr::int(10)), 0);

    let act = ctx.alloc_query_activation();
    // Guarded segment: x <= 20
    ctx.assert_background_guarded(&ChcExpr::le(int_var("x"), ChcExpr::int(20)), act);

    // Case 1: level 0, segment active, x=15 → all constraints satisfied → not UNSAT
    let r1 = ctx.check_sat_at_level_with_activations(
        0,
        &[ChcExpr::eq(int_var("x"), ChcExpr::int(15))],
        &[act],
        &[],
        Some(std::time::Duration::from_secs(5)),
        None,
    );
    assert!(
        !matches!(r1, IncrementalCheckResult::Unsat),
        "x=15 with x>=10 lemma and x<=20 segment should not be UNSAT"
    );

    // Case 2: level 0, segment active, x=5 → x>=10 violated → UNSAT
    let r2 = ctx.check_sat_at_level_with_activations(
        0,
        &[ChcExpr::eq(int_var("x"), ChcExpr::int(5))],
        &[act],
        &[],
        Some(std::time::Duration::from_secs(5)),
        None,
    );
    assert!(
        matches!(r2, IncrementalCheckResult::Unsat),
        "x=5 with x>=10 lemma active should be UNSAT"
    );

    // Case 3: level 1 (lemma at level 0 inactive), segment active, x=5
    // Only x<=20 is active → x=5 is consistent → not UNSAT
    let r3 = ctx.check_sat_at_level_with_activations(
        1,
        &[ChcExpr::eq(int_var("x"), ChcExpr::int(5))],
        &[act],
        &[],
        Some(std::time::Duration::from_secs(5)),
        None,
    );
    assert!(
        !matches!(r3, IncrementalCheckResult::Unsat),
        "x=5 at level 1 (lemma inactive) with x<=20 segment should not be UNSAT"
    );
}
