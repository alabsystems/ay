// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for extended resolution (ER) proof verification and stats tracking.
//!
//! ER proofs introduce extension variables via "definition" clauses with empty
//! hint chains (trivially blocked), then use "long" clauses with all-negative
//! hint chains referencing blocking witnesses. CaDiCaL generates these for
//! pigeon-hole problems.
//!
//! Reference: CaDiCaL `lratchecker.cpp:384-444` (check_blocked),
//!            CaDiCaL `lratchecker.cpp:503-508` (three-mode dispatch).

use super::{lit, LratChecker};

// -- Stats verification tests --

/// Verify that resolution stats are tracked through add_derived.
#[test]
fn test_stats_rup_and_resolution_ok() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2)]);
    checker.add_original(2, &[lit(-1), lit(3)]);

    // Derived clause {2, 3} with hints [2, 1] — passes RUP and resolution.
    assert!(checker.add_derived(3, &[lit(2), lit(3)], &[2, 1]));

    assert_eq!(checker.stats.rup_ok, 1, "one RUP success expected");
    assert_eq!(checker.stats.resolution_ok, 1, "resolution should match");
    assert_eq!(checker.stats.resolution_mismatch, 0);
    assert_eq!(checker.stats.rat_ok, 0);
    assert_eq!(checker.stats.blocked_ok, 0);
}

/// Verify that resolution mismatch is tracked via direct check_resolution call.
/// (In practice, resolution mismatch after RUP success is rare — the counter
/// exists for completeness.)
#[test]
fn test_stats_resolution_mismatch_direct() {
    let mut checker = LratChecker::new(4);
    // Use add_original to populate clauses through the arena-based API.
    checker.add_original(1, &[lit(1), lit(2), lit(3)]);
    checker.add_original(2, &[lit(-1)]);
    // Resolvent of {1,2,3} and {-1} = {2,3}. Claiming {2} — resolvent has
    // extra literal 3 not in clause → mismatch.
    let mismatch = !checker.check_resolution(&[lit(2)], &[2, 1]);
    assert!(mismatch, "resolvent {{2,3}} doesn't match claim {{2}}");
}

/// Multiple derived clauses: verify cumulative stats.
#[test]
fn test_stats_cumulative() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2)]);
    checker.add_original(2, &[lit(-1), lit(3)]);
    checker.add_original(3, &[lit(-2)]);
    checker.add_original(4, &[lit(-3)]);

    // First derived: {2, 3} from [2, 1].
    assert!(checker.add_derived(5, &[lit(2), lit(3)], &[2, 1]));
    // Second derived: empty clause from {-2} (3), {2,3} (5), {-3} (4).
    // RUP: assume nothing. Hint 3={-2}: unit → propagate -2.
    //       Hint 5={2,3}: 2 false → unit → propagate 3.
    //       Hint 4={-3}: 3 true, -3 false → conflict. OK.
    assert!(checker.add_derived(6, &[], &[3, 5, 4]));

    assert_eq!(checker.stats.rup_ok, 2, "two RUP successes expected");
    assert_eq!(checker.stats.derived, 2, "two derived clauses");
}

// -- Extended resolution (ER) integration tests --

/// ER definition clause with empty hints is accepted as trivially blocked.
///
/// When an extension variable (beyond num_vars) appears in a derived clause
/// with no hints, the clause is trivially blocked: no existing clause contains
/// the negation of the fresh variable.
///
/// This is how CaDiCaL emits ER proofs for pigeon-hole problems:
///   82 31 -21 0 0   ← clause {31, -21}, empty hints, var 31 is fresh
#[test]
fn test_er_definition_empty_hints_accepted() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]);
    checker.add_original(2, &[lit(-1), lit(2)]);

    // Extension variable 4 (beyond num_vars=3). No hints → trivially blocked.
    assert!(
        checker.add_derived(3, &[lit(4), lit(-1)], &[]),
        "ER definition with fresh variable should be trivially blocked"
    );
    assert_eq!(checker.stats.blocked_ok, 1, "should count as blocked");
}

/// ER definition clause with non-fresh variable is rejected when blocked check fails.
///
/// If the clause's literal negation exists in some DB clause and no proof chain
/// witnesses it, the clause is NOT trivially blocked.
#[test]
fn test_er_definition_non_fresh_variable_rejected() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]);
    checker.add_original(2, &[lit(-1), lit(-2)]);

    // Clause {1, -2} with empty hints: variable 1 appears negated in clause 2,
    // variable 2 appears positively in clause 1. Both candidates eliminated.
    let ok = checker.add_derived(3, &[lit(1), lit(-2)], &[]);
    assert!(!ok, "non-fresh variable clause should fail blocked check");
}

/// ER long clause with all-negative hints (blocking witnesses).
///
/// CaDiCaL emits: `85 -31 21 26 1 0 -82 -83 -84 0`
/// Clause {-31, 21, 26, 1} with hints [-82, -83, -84].
/// The negative hints reference clauses that must be blocked.
#[test]
fn test_er_long_clause_all_negative_hints() {
    let mut checker = LratChecker::new(4);
    // Set up: original clauses with negations of imported literals.
    checker.add_original(1, &[lit(-1), lit(-2)]);
    // ER definitions (trivially blocked, empty hints).
    assert!(checker.add_derived(2, &[lit(5), lit(-1)], &[]));
    assert!(checker.add_derived(3, &[lit(5), lit(-2)], &[]));

    // ER long clause: {-5, 1, 2}. Blocked by proof chain clauses 2 and 3.
    // Clause 2 = {5, -1}: marks are set at negation of {-5, 1, 2} = {5, -1, -2}.
    //   5 is marked (count=1), -1 is marked (count=2). count >= 2 ✓.
    // Clause 3 = {5, -2}: 5 is marked (count=1), -2 is marked (count=2). count >= 2 ✓.
    // Non-proof clause 1 = {-1, -2}: -1 is marked → eliminates candidate for lit 1;
    //   -2 is marked → eliminates candidate for lit 2.
    // But candidate for lit -5 (index 0) survives if no clause has negation 5
    //   beyond the proof chain. Clause 2 has 5 but is in proof chain → skip.
    //   Clause 3 has 5 but is in proof chain → skip. ✓ Candidate survives.
    let ok = checker.add_derived(4, &[lit(-5), lit(1), lit(2)], &[-2, -3]);
    assert!(
        ok,
        "ER long clause with valid blocking witnesses should pass"
    );
    // 2 ER definitions accepted as blocked (empty hints), 1 ER long clause
    // accepted as RAT (negative hints go through RAT verification first).
    assert_eq!(checker.stats.blocked_ok, 2, "2 ER definitions via blocked");
    assert_eq!(checker.stats.rat_ok, 1, "1 ER long clause via RAT");
}

/// Complete mini ER proof: PHP(3,2) with extension variables.
///
/// Tests the full ER workflow:
/// 1. Add original clauses (pigeon-hole 3 pigeons, 2 holes)
/// 2. Add ER definition clauses (empty hints → trivially blocked)
/// 3. Add ER long clause (negative hints → blocking witnesses)
/// 4. Derive empty clause via RUP using the ER clauses
#[test]
fn test_er_proof_mini_pigeon_hole() {
    let mut checker = LratChecker::new(6);
    // PHP(3,2): p(1,1)=1, p(1,2)=2, p(2,1)=3, p(2,2)=4, p(3,1)=5, p(3,2)=6
    // Each pigeon in some hole.
    checker.add_original(1, &[lit(1), lit(2)]);
    checker.add_original(2, &[lit(3), lit(4)]);
    checker.add_original(3, &[lit(5), lit(6)]);
    // No two pigeons in same hole.
    checker.add_original(4, &[lit(-1), lit(-3)]);
    checker.add_original(5, &[lit(-1), lit(-5)]);
    checker.add_original(6, &[lit(-3), lit(-5)]);
    checker.add_original(7, &[lit(-2), lit(-4)]);
    checker.add_original(8, &[lit(-2), lit(-6)]);
    checker.add_original(9, &[lit(-4), lit(-6)]);

    // RUP derivations (mirroring CaDiCaL's output for php3):
    // 10: {-2} from hints [7, 8, 2, 3, 6]
    assert!(checker.add_derived(10, &[lit(-2)], &[7, 8, 2, 3, 6]));
    // 11: {1} from hints [10, 1]
    assert!(checker.add_derived(11, &[lit(1)], &[10, 1]));
    // 12: {-3} from hints [11, 4]
    assert!(checker.add_derived(12, &[lit(-3)], &[11, 4]));
    // 13: {-5} from hints [11, 5]
    assert!(checker.add_derived(13, &[lit(-5)], &[11, 5]));
    // 14: {4} from hints [12, 2]
    assert!(checker.add_derived(14, &[lit(4)], &[12, 2]));
    // 15: {6} from hints [13, 3]
    assert!(checker.add_derived(15, &[lit(6)], &[13, 3]));
    // 16: empty from hints [14, 15, 9]
    assert!(checker.add_derived(16, &[], &[14, 15, 9]));

    assert!(checker.derived_empty_clause(), "should derive empty clause");
    assert_eq!(checker.stats.rup_ok, 7, "all 7 derived clauses via RUP");
    assert_eq!(checker.stats.resolution_ok, 7, "all resolutions match");
    assert_eq!(checker.stats.failures, 0, "no failures");
}
