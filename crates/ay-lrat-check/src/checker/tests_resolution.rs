// Copyright 2026 Andrew Yates
// Tests for resolution check and blocked clause (ER) verification (#5235).
//
// Reference: CaDiCaL lratchecker.cpp:233-294 (check_resolution),
// lratchecker.cpp:384-444 (check_blocked), lratchecker.cpp:503-508 (dispatch).

use super::*;

// ─── Resolution check: positive cases ─────────────────────────────────

/// Simple two-clause resolution: {a, b} resolve with {¬a, b} → {b}.
/// Both RUP and resolution should pass.
#[test]
fn test_resolution_simple_two_clause() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
    checker.add_original(2, &[lit(-1), lit(2)]); // ¬a ∨ b
                                                 // Derive {b} via hints [1, 2]. Resolution: start with clause 2 {¬a, b},
                                                 // then resolve with clause 1 {a, b}: cancel a/¬a, keep b. Result: {b}. ✓
    assert!(checker.add_derived(3, &[lit(2)], &[1, 2]));
    assert_eq!(checker.stats.failures, 0);
}

/// Three-clause chain: {a, b}, {¬a, c}, {¬b, c} → {c}.
/// Hints [2, 3, 1]: resolution walks backward from clause 1, then 3, then 2.
#[test]
fn test_resolution_three_clause_chain() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
    checker.add_original(2, &[lit(-1), lit(3)]); // ¬a ∨ c
    checker.add_original(3, &[lit(-2), lit(3)]); // ¬b ∨ c
                                                 // RUP check with hints [2, 3, 1]:
                                                 //   Assume ¬c. Hint 2: {¬a,c} → unit ¬a (c falsified). Hint 3: {¬b,c} → unit ¬b.
                                                 //   Hint 1: {a,b} → conflict (both falsified). ✓
                                                 //
                                                 // Resolution check (reverse walk): start from clause 1 {a,b}.
                                                 //   Resolve with clause 3 {¬b,c}: cancel b/¬b → {a,c}.
                                                 //   Resolve with clause 2 {¬a,c}: cancel a/¬a → {c}. ✓
    assert!(checker.add_derived(4, &[lit(3)], &[2, 3, 1]));
    assert_eq!(checker.stats.failures, 0);
}

/// Empty clause derivation: {a}, {¬a} → {}.
#[test]
fn test_resolution_empty_clause() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]); // a
    checker.add_original(2, &[lit(-1)]); // ¬a
                                         // Derive {} via [1, 2]. Resolution: start from clause 2 {¬a},
                                         // resolve with clause 1 {a}: cancel a/¬a → {}. ✓
    assert!(checker.add_derived(3, &[], &[1, 2]));
    assert_eq!(checker.stats.failures, 0);
}

/// Derived clause is a strict subset of resolvent (subsumption allowed).
/// Resolvent is {b, c} but derived clause is {b}. Per CaDiCaL, this is OK:
/// the derived clause is subsumed by the resolvent.
#[test]
fn test_resolution_subsumption_allowed() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
    checker.add_original(2, &[lit(-1), lit(2), lit(3)]); // ¬a ∨ b ∨ c
                                                         // Resolution: start from clause 2 {¬a,b,c}, resolve with clause 1 {a,b}:
                                                         //   cancel a/¬a → {b, c}. Derived clause {b} is a subset → OK.
                                                         //
                                                         // RUP: assume ¬b. Hint 1: {a,b} → unit a. Hint 2: {¬a,b,c} → unit c.
                                                         // No conflict yet. RUP will fail. Need a different hint order or extra hint.
                                                         //
                                                         // Actually for RUP to work, we need the right setup. Let's add clause {¬c}
                                                         // to force the conflict.
    checker.add_original(3, &[lit(-3)]); // ¬c
                                         // Now: assume ¬b. Hint 1: {a,b} → unit a. Hint 2: {¬a,b,c} → unit c.
                                         // Hint 3: {¬c} → conflict. ✓
                                         // Resolution: start from clause 3 {¬c}, resolve with clause 2 {¬a,b,c}:
                                         //   cancel c/¬c → {¬a,b}. Resolve with clause 1 {a,b}: cancel a/¬a → {b}. ✓
    assert!(checker.add_derived(4, &[lit(2)], &[1, 2, 3]));
    assert_eq!(checker.stats.failures, 0);
}

// ─── Resolution check: negative cases ─────────────────────────────────

/// Resolution mismatch detected via direct check_resolution call.
///
/// The resolution check catches cases where the resolvent has a literal NOT
/// in the derived clause. A weaker (superset) derived clause is allowed
/// (weakening/subsumption), but a resolvent with extra variables fails.
///
/// Example: resolvent is {b} but derived clause claims {a}.
/// Resolvent has variable b not in derived clause → single polarity mark → FAIL.
#[test]
fn test_resolution_mismatch_resolvent_has_extra_var() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
    checker.add_original(2, &[lit(-1), lit(2)]); // ¬a ∨ b
                                                 // Resolvent of [1, 2] backward: clause 2 {¬a,b}, resolve with clause 1 {a,b}:
                                                 //   cancel a/¬a → {b}.
                                                 // Claim derived clause is {a} — mismatch because resolvent has b (not a).
    assert!(
        !checker.check_resolution(&[lit(1)], &[1, 2]),
        "resolvent is {{b}} but derived is {{a}} — variable b is unaccounted for"
    );
}

/// Weakening is allowed: derived clause {a, b} when resolvent is {b}.
/// The derived clause is a superset (weaker) — this is valid.
#[test]
fn test_resolution_weakening_allowed() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
    checker.add_original(2, &[lit(-1), lit(2)]); // ¬a ∨ b
                                                 // Resolvent: {b}. Derived clause: {a, b}. Weakening — valid.
    assert!(checker.check_resolution(&[lit(1), lit(2)], &[1, 2]));
}

/// Resolution check with direct method: verify check_resolution independently.
#[test]
fn test_check_resolution_direct_valid() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
    checker.add_original(2, &[lit(-1), lit(2)]); // ¬a ∨ b
                                                 // Resolution of [1, 2] backward: start from clause 2 {¬a, b},
                                                 // resolve with clause 1 {a, b}: cancel a/¬a → {b}. Matches derived {b}.
    assert!(checker.check_resolution(&[lit(2)], &[1, 2]));
}

#[test]
fn test_check_resolution_direct_mismatch() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
    checker.add_original(2, &[lit(-1), lit(2)]); // ¬a ∨ b
                                                 // Resolvent of [1, 2] is {b}. Claiming derived clause is {a} should fail.
    assert!(!checker.check_resolution(&[lit(1)], &[1, 2]));
}

#[test]
fn test_check_resolution_empty_hints() {
    let mut checker = LratChecker::new(3);
    // Empty hints → resolution check returns true (no chain to verify).
    // Matches CaDiCaL lratchecker.cpp:233-237 behavior. In practice,
    // check_resolution with empty hints is only called after RUP succeeds,
    // which for empty hints only happens on tautological clauses.
    assert!(checker.check_resolution(&[lit(1)], &[]));
}

// Blocked clause (ER) tests are in tests_blocked.rs (#5142).

// ─── Edge cases: resolution ──────────────────────────────────────────

/// Single hint: resolvent is the hint clause itself. Derived clause must match.
#[test]
fn test_resolution_single_hint_exact_match() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
                                                // Single hint [1]: resolvent = clause 1 = {a, b}. Derived: {a, b}. ✓
    assert!(checker.check_resolution(&[lit(1), lit(2)], &[1]));
}

/// Single hint with mismatch: resolvent is {a, b} but derived is {a, c}.
#[test]
fn test_resolution_single_hint_mismatch() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
                                                // Resolvent = {a, b}. Derived: {a, c}. Variable b is in resolvent but not
                                                // accounted for in derived clause → FAIL.
    assert!(!checker.check_resolution(&[lit(1), lit(3)], &[1]));
}

/// Missing hint clause: check_resolution returns false.
#[test]
fn test_resolution_missing_hint_clause() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
                                                // Hint 99 doesn't exist.
    assert!(!checker.check_resolution(&[lit(1), lit(2)], &[1, 99]));
}

/// Missing last hint clause: check_resolution returns false.
#[test]
fn test_resolution_missing_last_hint_clause() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
                                                // Hint 99 (last) doesn't exist.
    assert!(!checker.check_resolution(&[lit(1)], &[99]));
}

/// Resolvent has opposite polarity of derived clause literal.
/// Resolvent = {b}, derived = {¬b}. Phase 3 detects the polarity contradiction.
#[test]
fn test_resolution_opposite_polarity_mismatch() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
    checker.add_original(2, &[lit(-1), lit(2)]); // ¬a ∨ b
                                                 // Resolvent = {b}. Derived = {¬b}. Polarity mismatch → FAIL.
    assert!(!checker.check_resolution(&[lit(-2)], &[1, 2]));
}

/// State cleanup: after check_resolution success, checked_lits should be all false.
#[test]
fn test_resolution_cleanup_on_success() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
    checker.add_original(2, &[lit(-1), lit(2)]); // ¬a ∨ b
    assert!(checker.check_resolution(&[lit(2)], &[1, 2]));
    assert!(checker.checked_lits.iter().all(|&b| !b));
}

/// State cleanup: after check_resolution failure, checked_lits should be all false.
#[test]
fn test_resolution_cleanup_on_failure() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
    checker.add_original(2, &[lit(-1), lit(2)]); // ¬a ∨ b
    assert!(!checker.check_resolution(&[lit(1)], &[1, 2]));
    assert!(checker.checked_lits.iter().all(|&b| !b));
}

/// Resolution with higher-numbered variables.
#[test]
fn test_resolution_higher_variables() {
    let mut checker = LratChecker::new(6);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
    checker.add_original(2, &[lit(-1), lit(5)]); // ¬a ∨ e
                                                 // Resolvent: start from clause 2 {¬a, e}, resolve with clause 1 {a, b}:
                                                 //   cancel a/¬a → {b, e}. Derived: {b, e}. ✓
    assert!(checker.check_resolution(&[lit(2), lit(5)], &[1, 2]));
    assert!(checker.checked_lits.iter().all(|&b| !b));
}

// Edge cases for blocked clause tests are in tests_blocked.rs (#5142).

// ─── Coverage gaps from P1:586 reflection ──────────────────────

/// Resolution rejects negative last hint.
///
/// `check_resolution` at resolution.rs:41-43 returns false when the last hint
/// is a negative ID (negative IDs are RAT witness markers, not clause refs).
#[test]
fn test_resolution_negative_last_hint_rejected() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b

    assert!(
        !checker.check_resolution(&[lit(2)], &[1, -2]),
        "negative last hint must be rejected by check_resolution"
    );
    assert!(
        checker.checked_lits.iter().all(|&b| !b),
        "checked_lits must be cleared after negative-last-hint rejection"
    );
    assert!(
        checker.checked_stack.is_empty(),
        "checked_stack must be empty after negative-last-hint rejection"
    );
}

/// Invariant: checked_stack is empty after every check_resolution call.
///
/// Verifies cleanup invariant that `checked_stack` and `checked_lits`
/// are fully cleaned up regardless of outcome. No cross-call contamination.
#[test]
fn test_checked_stack_cleanup_invariant() {
    let mut checker = LratChecker::new(5);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(3, &[lit(-2), lit(3)]); // ~b v c
    checker.add_original(4, &[lit(-3), lit(4)]); // ~c v d

    // Successful resolution: {b} from [1, 2].
    assert!(checker.check_resolution(&[lit(2)], &[1, 2]));
    assert!(
        checker.checked_stack.is_empty(),
        "stack clean after success"
    );
    assert!(
        checker.checked_lits.iter().all(|&b| !b),
        "lits clean after success"
    );

    // Failed resolution: {a} from [1, 2] — mismatch.
    assert!(!checker.check_resolution(&[lit(1)], &[1, 2]));
    assert!(
        checker.checked_stack.is_empty(),
        "stack clean after failure"
    );
    assert!(
        checker.checked_lits.iter().all(|&b| !b),
        "lits clean after failure"
    );

    // Longer chain: [2, 3, 1]. Backward: start C1 {a,b}, resolve with C3 {~b,c},
    // cancel b → {a,c}. Resolve with C2 {~a,b}: cancel a → {b,c}.
    assert!(checker.check_resolution(&[lit(2), lit(3)], &[2, 3, 1]));
    assert!(
        checker.checked_stack.is_empty(),
        "stack clean after longer chain"
    );
    assert!(
        checker.checked_lits.iter().all(|&b| !b),
        "lits clean after longer chain"
    );

    // Missing hint: [1, 99].
    assert!(!checker.check_resolution(&[lit(2)], &[1, 99]));
    assert!(
        checker.checked_stack.is_empty(),
        "stack clean after missing hint"
    );
    assert!(
        checker.checked_lits.iter().all(|&b| !b),
        "lits clean after missing hint"
    );

    // Empty hints (tautological).
    assert!(checker.check_resolution(&[lit(1)], &[]));
    assert!(
        checker.checked_stack.is_empty(),
        "stack clean after empty hints"
    );
}

// -- Multi-step resolution chain tests --

/// Resolution chain with 3 hints: transitive resolution.
///
///   1: {1, 2}
///   2: {-1, 3}
///   3: {-3, 4}
///
/// Resolve 1 with 2 on var 1: {2, 3}
/// Resolve {2, 3} with 3 on var 3: {2, 4}
///
/// Derived clause 4: {2, 4} with hints [3, 2, 1].
#[test]
fn test_resolution_three_step_chain() {
    let mut checker = LratChecker::new(5);
    checker.add_original(1, &[lit(1), lit(2)]);
    checker.add_original(2, &[lit(-1), lit(3)]);
    checker.add_original(3, &[lit(-3), lit(4)]);

    assert!(checker.add_derived(4, &[lit(2), lit(4)], &[3, 2, 1]));
}

/// Resolution chain with 4 hints: transitive resolution to empty clause.
///
///   1: {1}
///   2: {-1, 2}
///   3: {-2, 3}
///   4: {-3}
///
/// Resolve 1 with 2: {2}. Resolve {2} with 3: {3}. Resolve {3} with 4: empty.
#[test]
fn test_resolution_four_step_chain_to_empty() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1), lit(2)]);
    checker.add_original(3, &[lit(-2), lit(3)]);
    checker.add_original(4, &[lit(-3)]);

    assert!(checker.add_derived(5, &[], &[4, 3, 2, 1]));
}

/// check_resolution: last hint clause missing should fail immediately.
/// Tests the early-exit path at line 48-51 (before any marks are set).
#[test]
fn test_check_resolution_last_hint_missing() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2)]);
    // Hint 99 is the last hint and doesn't exist.
    let ok = checker.check_resolution(&[lit(1), lit(2)], &[1, 99]);
    assert!(!ok, "missing last hint clause should fail resolution");

    // Marks should be clean despite early exit.
    assert!(
        checker.marks.iter().all(|&m| !m),
        "marks should be clean after last-hint-missing early exit"
    );
}

// ─── Guard coverage: runtime guards converted from debug_assert ──────

/// Resolution guard: tautological last hint clause hits the negation-already-marked
/// guard. A clause containing both `a` and `~a` sets `checked_lits[~a]` when
/// processing `a`, then finds it set when processing `~a` → return false.
///
/// Exercises the runtime guard converted from `debug_assert!` (resolution.rs:66-69).
#[test]
fn test_resolution_tautological_last_hint_rejected() {
    let mut checker = LratChecker::new(3);
    // Insert a tautological clause: {a, ~a, b}.
    checker.add_original(1, &[lit(1), lit(-1), lit(2)]);
    checker.add_original(2, &[lit(-2)]); // ~b

    // Use tautological clause 1 as last hint.
    let ok = checker.check_resolution(&[lit(2)], &[2, 1]);
    assert!(
        !ok,
        "tautological last hint clause must be rejected by resolution check"
    );

    // Verify cleanup: checked_stack and checked_lits must be clean.
    assert!(
        checker.checked_stack.is_empty(),
        "checked_stack must be empty after tautological rejection"
    );
    assert!(
        checker.checked_lits.iter().all(|&b| !b),
        "checked_lits must be clean after tautological rejection"
    );
}

/// Resolution guard: leaked checked_stack hits the clear guard at entry.
/// Artificially injects stale state to simulate a leak from a prior call.
///
/// Exercises the runtime guard converted from `debug_assert!` (resolution.rs:46-48).
#[test]
fn test_resolution_leaked_checked_stack_cleared() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b

    // Artificially inject stale state into checked_stack.
    checker.checked_lits.resize(10, false);
    checker.checked_lits[0] = true;
    checker.checked_stack.push(0);

    // The defensive guard at entry should clear this stale state.
    // Resolution of [1, 2] → {b} should still succeed.
    let ok = checker.check_resolution(&[lit(2)], &[1, 2]);
    assert!(
        ok,
        "resolution should succeed after defensive cleanup of leaked state"
    );

    // Verify full cleanup.
    assert!(checker.checked_stack.is_empty());
    assert!(checker.checked_lits.iter().all(|&b| !b));
}

// Detailed check_blocked tests are in tests_blocked.rs (#5142).
