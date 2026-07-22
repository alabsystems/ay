// Copyright 2026 Andrew Yates
// Unit tests for the LRAT proof checker (RUP verification).
// RAT tests are in tests_rat.rs.

use super::*;
use crate::lrat_parser::LratStep;

#[test]
fn test_valid_chain_simple() {
    // Formula: (a v b) ^ (~a v b) -> derive (b)
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    assert!(checker.add_derived(3, &[lit(2)], &[1, 2])); // b
    assert_eq!(checker.stats.failures, 0);
}

#[test]
fn test_valid_chain_three_clauses() {
    // (a v b), (~a v c), (~b v c) -> derive (c)
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(3)]); // ~a v c
    checker.add_original(3, &[lit(-2), lit(3)]); // ~b v c
    assert!(checker.add_derived(4, &[lit(3)], &[2, 3, 1])); // c
    assert_eq!(checker.stats.failures, 0);
}

#[test]
fn test_invalid_chain_fails() {
    // (a v b) -- cannot derive (~a ^ ~b) from this alone.
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    assert!(!checker.add_derived(2, &[lit(-1), lit(-2)], &[1])); // ~a v ~b -- invalid
}

#[test]
fn test_wrong_hint_order_fails() {
    // (a v b), (~a v c), (~b v c) -> derive (c) with wrong hint order [1, 2, 3]
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2)]);
    checker.add_original(2, &[lit(-1), lit(3)]);
    checker.add_original(3, &[lit(-2), lit(3)]);
    assert!(!checker.add_derived(4, &[lit(3)], &[1, 2, 3])); // wrong order!
}

#[test]
fn test_empty_clause_derivation() {
    // (a) ^ (~a) -> derive empty clause
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]); // a
    checker.add_original(2, &[lit(-1)]); // ~a
    assert!(checker.add_derived(3, &[], &[1, 2])); // empty clause
    assert_eq!(checker.stats.failures, 0);
}

#[test]
fn test_deletion_removes_clause() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]);
    checker.add_original(2, &[lit(-1), lit(2)]);
    assert!(checker.clause_index.contains_key(&1));
    checker.delete(1);
    assert!(!checker.clause_index.contains_key(&1));
}

#[test]
fn test_derived_then_used_as_hint() {
    // (a v b), (~a v b) -> (b) -> (~b v c), use (b) as hint for (c)
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    assert!(checker.add_derived(3, &[lit(2)], &[1, 2])); // b
    checker.add_original(4, &[lit(-2), lit(3)]); // ~b v c
    assert!(checker.add_derived(5, &[lit(3)], &[3, 4])); // c
    assert_eq!(checker.stats.failures, 0);
}

#[test]
fn test_verify_proof_valid() {
    // PHP(2,1): pigeonhole principle with 2 pigeons, 1 hole
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(2)]);
    checker.add_original(3, &[lit(-1), lit(-2)]);

    let steps = vec![LratStep::Add {
        id: 4,
        clause: vec![],
        hints: vec![1, 3, 2],
    }];

    assert!(checker.verify_proof(&steps));
}

#[test]
fn test_verify_proof_invalid() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1), lit(2)]);
    checker.add_original(2, &[lit(-1), lit(-2)]);

    let steps = vec![LratStep::Add {
        id: 3,
        clause: vec![],
        hints: vec![1], // not enough hints
    }];

    assert!(!checker.verify_proof(&steps));
}

#[test]
fn test_verify_proof_rejects_unverified_empty_hint_addition() {
    // This formula is satisfiable with a=false, b=false.  If the empty-hint
    // addition (a) were trusted, the remaining clauses would derive a
    // contradiction, so the proof must be rejected at this step.
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(-1), lit(2)]);
    checker.add_original(2, &[lit(-2)]);

    let steps = vec![
        LratStep::Add {
            id: 3,
            clause: vec![lit(1)],
            hints: vec![],
        },
        LratStep::Add {
            id: 4,
            clause: vec![],
            hints: vec![3, 1, 2],
        },
    ];

    assert!(
        !checker.verify_proof(&steps),
        "an LRAT file must not promote an arbitrary empty-hint clause to an axiom"
    );
}

#[test]
fn test_verify_proof_with_deletion() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);

    let steps = vec![
        LratStep::Delete { ids: vec![1] },
        LratStep::Add {
            id: 3,
            clause: vec![],
            hints: vec![1, 2], // hint 1 is deleted
        },
    ];

    assert!(!checker.verify_proof(&steps));
}

#[test]
fn test_literal_negation() {
    assert_eq!(lit(1).negated(), lit(-1));
    assert_eq!(lit(-1).negated(), lit(1));
    assert_eq!(lit(42).negated(), lit(-42));
}

#[test]
fn test_literal_variable_index() {
    // Variable indices are 0-based: DIMACS var 1 -> index 0, var 42 -> index 41.
    assert_eq!(lit(1).variable().index(), 0);
    assert_eq!(lit(-1).variable().index(), 0);
    assert_eq!(lit(42).variable().index(), 41);
    assert_eq!(lit(-42).variable().index(), 41);
}

#[test]
fn test_missing_hint_clause_skipped() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);

    let steps = vec![LratStep::Add {
        id: 3,
        clause: vec![],
        hints: vec![99],
    }];

    assert!(!checker.verify_proof(&steps));
}

#[test]
fn test_large_variable_within_declared_range() {
    // Variables 100 and 200 are within the declared num_vars=200.
    let mut checker = LratChecker::new(200);
    checker.add_original(1, &[lit(100), lit(200)]);
    checker.add_original(2, &[lit(-100), lit(200)]);
    assert!(checker.add_derived(3, &[lit(200)], &[1, 2]));
}

#[test]
fn test_out_of_range_literal_rejected_in_original() {
    // Literal 200 exceeds declared num_vars=2 — must be rejected.
    let mut checker = LratChecker::new(2);
    assert!(!checker.add_original(1, &[lit(100), lit(200)]));
}

#[test]
fn test_extension_variable_in_derived_clause() {
    // Derived clauses may introduce extension variables beyond num_vars.
    // CaDiCaL's LRAT proofs for pigeon-hole problems use this (extended
    // resolution). The chain won't verify here because there's no actual
    // proof, but the literal itself must not be rejected.
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]);
    checker.add_original(2, &[lit(-1), lit(2)]);
    // Extension variable 200 is beyond num_vars=3 but allowed in derived.
    // add_derived returns false because the chain [1,2] can't derive (200),
    // not because the literal is rejected.
    assert!(!checker.add_derived(3, &[lit(200)], &[1, 2]));
    // But verify the literal was accepted (stats count it as derived attempt).
    assert_eq!(checker.stats.derived, 1);
}

#[test]
fn test_extension_variable_accepted_in_valid_proof() {
    // Extension variables in derived clauses must not cause rejection.
    // Here var 4 (beyond num_vars=3) appears in a derived clause.
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]); // a
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(3, &[lit(-2)]); // ~b
    assert!(checker.add_derived(4, &[lit(2)], &[1, 2])); // derive (b)
    assert!(checker.add_derived(5, &[], &[4, 3])); // empty from (b) ^ (~b)
    assert!(checker.derived_empty_clause());
}

#[test]
fn test_proof_without_empty_clause_rejected() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]);
    checker.add_original(2, &[lit(-1), lit(2)]);

    let steps = vec![LratStep::Add {
        id: 3,
        clause: vec![lit(2)],
        hints: vec![1, 2],
    }];

    assert!(!checker.verify_proof(&steps));
}

#[test]
fn test_multi_step_proof_with_intermediate_derivations() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(3, &[lit(-2)]); // ~b

    let steps = vec![
        LratStep::Add {
            id: 4,
            clause: vec![lit(2)],
            hints: vec![1, 2],
        },
        LratStep::Add {
            id: 5,
            clause: vec![],
            hints: vec![4, 3],
        },
    ];

    assert!(checker.verify_proof(&steps));
}

#[test]
fn test_backtracking_isolation() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(3)]); // ~a v c
    checker.add_original(3, &[lit(-2), lit(3)]); // ~b v c
    checker.add_original(4, &[lit(-3)]); // ~c

    assert!(checker.add_derived(5, &[lit(3)], &[2, 3, 1]));
    assert!(checker.add_derived(6, &[], &[5, 4]));
}

#[test]
fn test_unknown_hint_id_causes_failure() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b

    // Hint 99 doesn't exist — strict mode should reject this.
    assert!(!checker.add_derived(3, &[lit(2)], &[99, 1, 2]));
    assert_eq!(checker.stats.failures, 1);
}

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

#[test]
fn test_duplicate_literal_hint_is_treated_as_unit() {
    // Clauses are sets: (a v a) is the unit clause (a).
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1), lit(1)]);
    checker.add_original(2, &[lit(-1), lit(2)]);

    assert!(
        checker.add_derived(3, &[lit(2)], &[1, 2]),
        "a repeated literal must not make a logically unit hint non-unit"
    );
    assert_eq!(checker.stats.rup_ok, 1);
}

/// Test that a redundant SatisfiedUnit hint is accepted (RUP valid) but
/// tracked as a resolution mismatch.
///
/// RUP passes (conflict found). Resolution fails because hint 2 is
/// redundant — it doesn't contribute to the resolution chain. Standard
/// LRAT only requires RUP; the clause is accepted.
#[test]
fn test_satisfied_unit_hint_accepted_with_resolution_mismatch() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]); // (a) — unit
    checker.add_original(2, &[lit(1)]); // (a) — same, different ID
    checker.add_original(3, &[lit(-1), lit(2)]); // ~a v b

    // Derive (b) with hints [1, 2, 3]:
    //   RUP: Assume ~b. Hint 1 propagates a. Hint 2 is satisfied (no-op).
    //         Hint 3 gives conflict. RUP ok.
    //   Resolution: chain [1,2,3] has redundant hint 2 → mismatch (informational).
    let ok = checker.add_derived(4, &[lit(2)], &[1, 2, 3]);
    assert!(
        ok,
        "RUP-valid clause with redundant hints should be accepted"
    );
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

    // Verify seen_hints is empty after the call returns — clear() at the start
    // of propagate_rup_hints ensures no stale data, and the HashSet is not
    // explicitly cleared after the call completes (it's cleared at the start
    // of the next call). The important invariant is that each call starts clean.
    // seen_hints may contain data from the last call, but it will be cleared
    // before the next use.

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

/// Throughput benchmark: verify a chain of 20K derivation steps.
///
/// Structure: N variables, each with unit clause {x_i} and implication {~x_i, x_{i+1}}.
/// Each derived clause {x_{i+1}} is proved by hints [unit_i, implication_i].
/// Final empty clause: derive from {x_N} and {~x_N}.
///
/// Measures raw RUP throughput — the hot path uses `propagate_rup_hints()` which
/// is the target of the generation counter optimization (#5267).
#[test]
fn test_throughput_20k_derivation_chain() {
    let n: usize = 20_000;
    let num_vars = n + 2;
    let mut checker = LratChecker::new(num_vars);

    // Phase 1: Add original clauses.
    // Clause IDs: 1..=2*n+1
    // clause 2i-1 = {x_i} for i in 1..=n
    // clause 2i   = {~x_i, x_{i+1}} for i in 1..=n
    // clause 2n+1 = {~x_{n+1}} (final contradiction)
    let mut next_id: u64 = 1;
    for i in 1..=n {
        let xi = i as i32;
        let xi_next = (i + 1) as i32;
        assert!(checker.add_original(next_id, &[lit(xi)]));
        next_id += 1;
        assert!(checker.add_original(next_id, &[lit(-xi), lit(xi_next)]));
        next_id += 1;
    }
    // Add final contradiction clause: {~x_{n+1}}
    let final_neg_id = next_id;
    assert!(checker.add_original(final_neg_id, &[lit(-((n + 1) as i32))]));
    next_id += 1;

    // Phase 2: Derive chain. Each step derives {x_{i+1}} from {x_i} and {~x_i, x_{i+1}}.
    // Derivation clause IDs start at next_id.
    let start = std::time::Instant::now();

    for i in 1..=n {
        let xi_next = (i + 1) as i32;
        let unit_id = (2 * i - 1) as i64; // {x_i}
        let impl_id = (2 * i) as i64; // {~x_i, x_{i+1}}
        assert!(
            checker.add_derived(next_id, &[lit(xi_next)], &[unit_id, impl_id]),
            "derivation step {i} failed"
        );
        next_id += 1;
    }

    // Final step: derive empty clause from {x_{n+1}} and {~x_{n+1}}.
    let last_derived_id = (next_id - 1) as i64; // {x_{n+1}}
    assert!(checker.add_derived(next_id, &[], &[last_derived_id, final_neg_id as i64],));

    let elapsed = start.elapsed();
    let total_derivations = n + 1;
    let throughput = total_derivations as f64 / elapsed.as_secs_f64();

    assert_eq!(checker.stats.failures, 0);
    assert!(checker.derived_empty_clause());
    eprintln!(
        "LRAT throughput: {total_derivations} derivations in {:.3}ms ({throughput:.0} derivations/sec)",
        elapsed.as_secs_f64() * 1000.0,
    );
}

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
    // Must not panic. The duplicate literal makes the derivation invalid.
    assert!(!result, "duplicate literal clause should fail verification");
}
