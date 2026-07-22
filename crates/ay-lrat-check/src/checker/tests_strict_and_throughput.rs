// Copyright 2026 Andrew Yates
// Strict resolution checking and robustness tests for the LRAT proof checker.
// Extracted from tests.rs (#5305).

use super::*;
use crate::lrat_parser::LratStep;

// -- Strict mode / resolution checking --

#[test]
fn test_valid_hints_pass_strict_mode() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]); // a
    checker.add_original(2, &[lit(-1)]); // ~a

    let steps = vec![LratStep::Add {
        id: 3,
        clause: vec![],
        hints: vec![1, 2],
    }];

    assert!(checker.verify_proof(&steps));
    assert_eq!(checker.stats.failures, 0);
}

#[test]
fn test_reject_non_unit_hint_with_satisfied_literal() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2), lit(3)]); // a v b v c
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(3, &[lit(-2)]); // ~b

    // Valid derivation of (~a): assume a.
    assert!(checker.add_derived(4, &[lit(-1)], &[3, 2]));
    assert_eq!(checker.stats.failures, 0);

    // Now try with hint 1 prepended: (a v b v c) under assumption a.
    // Three non-falsified literals → non-unit → MUST fail.
    let mut checker2 = LratChecker::new(4);
    checker2.add_original(1, &[lit(1), lit(2), lit(3)]);
    checker2.add_original(2, &[lit(-1), lit(2)]);
    checker2.add_original(3, &[lit(-2)]);
    assert!(
        !checker2.add_derived(4, &[lit(-1)], &[1, 3, 2]),
        "Non-unit hint clause (satisfied + unassigned) must be rejected"
    );
    assert_eq!(checker2.stats.failures, 1);
}

#[test]
fn test_satisfied_unit_hint_accepted() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(3, &[lit(1), lit(-2)]); // a v ~b
    checker.add_original(4, &[lit(-1), lit(-2)]); // ~a v ~b

    assert!(checker.add_derived(5, &[lit(2)], &[1, 2]));
    assert!(checker.add_derived(6, &[], &[5, 3, 4]));
    assert_eq!(checker.stats.failures, 0);
}

/// Test that a redundant SatisfiedUnit hint is accepted (RUP valid) but
/// tracked as a resolution mismatch (informational).
///
/// Standard LRAT requires only RUP. The resolution mismatch is tracked
/// for proof quality diagnostics but does not cause rejection.
#[test]
fn test_satisfied_unit_hint_accepted_resolution_mismatch_tracked() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]); // (a) — unit
    checker.add_original(2, &[lit(1)]); // (a) — same, different ID
    checker.add_original(3, &[lit(-1), lit(2)]); // ~a v b

    // Derive (b) with hints [1, 2, 3]:
    //   RUP ok. Resolution mismatch (hint 2 is redundant). Accepted.
    let ok = checker.add_derived(4, &[lit(2)], &[1, 2, 3]);
    assert!(ok, "RUP-valid clause accepted despite redundant hint");
    assert_eq!(checker.stats.rup_ok, 1);
    assert_eq!(checker.stats.resolution_mismatch, 1);
    assert_eq!(checker.stats.failures, 0);
}

/// Test that the SatisfiedUnit path works with a non-redundant chain.
///
/// Minimal hints [1, 3] derive (b) correctly through both RUP and resolution.
#[test]
fn test_satisfied_unit_hint_is_noop_minimal_chain() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]); // (a) — unit
    checker.add_original(3, &[lit(-1), lit(2)]); // ~a v b

    // Derive (b) with minimal hints [1, 3]:
    //   Assume ~b. Hint 1=(a): propagate a. Hint 3=(~a v b): conflict.
    //   Resolution: resolve {a} and {~a, b} → {b}. Matches clause.
    assert!(
        checker.add_derived(4, &[lit(2)], &[1, 3]),
        "minimal chain should pass both RUP and resolution"
    );
    assert_eq!(checker.stats.failures, 0);
    assert_eq!(checker.stats.rup_ok, 1);
    assert_eq!(checker.stats.resolution_ok, 1);
}

/// Verify `seen_hints` HashSet has no stale data across sequential `add_derived` calls.
///
/// If `seen_hints` retained entries from a previous call, the second derivation
/// would falsely reject a hint ID that appeared in a prior derivation as a
/// "duplicate" even though it's the first appearance in the new derivation.
#[test]
fn test_seen_hints_no_stale_state_across_calls() {
    // Formula: (a | b), (~a | b), (~b | c), (~b | ~c)
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2)]); // a | b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a | b
    checker.add_original(3, &[lit(-2), lit(3)]); // ~b | c
    checker.add_original(4, &[lit(-2), lit(-3)]); // ~b | ~c

    // First derivation: derive (b) using hints [1, 2].
    // RUP: assume ~b → hint 1 (a|b): forces a → hint 2 (~a|b): conflict.
    assert!(checker.add_derived(5, &[lit(2)], &[1, 2]));
    assert_eq!(checker.stats.failures, 0);

    // Second derivation: derive empty clause using hints [5, 3, 4].
    // RUP: (no negated lits) → hint 5 (b): propagate b=true →
    //   hint 3 (~b|c): forces c → hint 4 (~b|~c): conflict.
    assert!(checker.add_derived(6, &[], &[5, 3, 4]));
    assert_eq!(checker.stats.failures, 0);

    // The real correctness proof: both derivations above succeeded, meaning
    // hint IDs from the first call (1, 2) did not interfere with the second
    // call's hint IDs (5, 3, 4). If seen_hints were stale, and a future
    // derivation reused hint ID 1, it would be rejected as duplicate.
    // Test this: derive a new clause using hint 1 again.
    // Derive (a | c) using hints [1, 3].
    // RUP: assume ~a, ~c → hint 1 (a|b): forces b →
    //   hint 3 (~b|c): forces c → conflict with ~c.
    assert!(
        checker.add_derived(7, &[lit(1), lit(3)], &[1, 3]),
        "hint ID 1 must not be rejected as duplicate from a prior derivation"
    );
    assert_eq!(checker.stats.failures, 0);
}

// -- Robustness tests for malformed proofs (#5314) --

#[test]
fn test_duplicate_literal_in_clause_no_panic() {
    // Malformed proof: clause with duplicate literal [a, a].
    // Previously triggered assert! on double-assignment in assign().
    // Should return false (invalid) without panicking.
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1)]); // ~a
                                         // Derive (a, a) — duplicate literal, but must not panic.
                                         // The RUP check will assume ~a twice. Second assign is a no-op.
                                         // Valid derivation: ~a propagates via clause 2, then clause 1 gives b.
                                         // But we're deriving (a, a) which is not implied — should fail gracefully.
    let result = checker.add_derived(3, &[lit(1), lit(1)], &[1, 2]);
    // Whether it passes or fails, it must not panic.
    let _ = result;
}

#[test]
fn test_duplicate_literal_negation_no_panic() {
    // Clause with both a literal and its negation: [a, ~a].
    // Tautological clause, trivially true. Must not panic.
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]);
    // Derive (a, ~a) — tautological. In verify_chain, assume ~a then ~(~a)=a.
    // Second assumption sees value(a) = Some(true) → returns true (trivially satisfied).
    let result = checker.add_derived(2, &[lit(1), lit(-1)], &[]);
    assert!(result, "tautological clause should be accepted");
}
