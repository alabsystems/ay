// Copyright 2026 Andrew Yates
// Algorithm audit: boundary condition regression tests for LRAT checker.

use super::*;

// ─── Algorithm audit: boundary condition regression tests ────────────

/// Algorithm audit finding #8: `negate(i32::MIN)` overflow -- now structurally
/// eliminated by the `Literal` type migration.
///
/// With the old `type Lit = i32`, `negate(i32::MIN)` was `-i32::MIN` which
/// overflows (panic in debug, wrap to i32::MIN in release = silent corruption).
///
/// With `Literal`, negation is `self.0 ^ 1` -- a bitwise toggle of polarity.
/// Overflow is structurally impossible. `Literal::from_dimacs(i32::MIN)`
/// actually succeeds (it represents variable 2_147_483_647, the maximum).
///
/// This test verifies the literal conversion and negation at the type level.
/// The previous version created `LratChecker::new(u32::MAX as usize)` which
/// allocated ~220GB of memory and took 500+ seconds to initialize via swapping.
/// The Literal encoding correctness is type-level, not checker-level.
#[test]
fn test_i32_min_literal_accepted_after_type_migration() {
    // Verify i32::MIN converts to a valid Literal (variable MAX_VAR, negative polarity).
    let l = lit(i32::MIN);
    assert!(!l.is_positive(), "i32::MIN should be a negative literal");
    assert_eq!(
        l.variable().id(),
        Literal::MAX_VAR,
        "i32::MIN should map to variable MAX_VAR"
    );
    // Verify negation is bitwise XOR, not arithmetic — no overflow possible.
    let neg = l.negated();
    assert!(
        neg.is_positive(),
        "negated i32::MIN literal should be positive"
    );
    assert_eq!(
        neg.variable().id(),
        Literal::MAX_VAR,
        "negation preserves variable"
    );
    // Double negation is identity.
    assert_eq!(l.negated().negated(), l);
    // Verify the literal works in a small checker (the encoding is correct
    // regardless of checker size — we use a small checker to test add_original
    // with a normal literal, proving the checker API works).
    let mut checker = LratChecker::new(3);
    assert!(
        checker.add_original(1, &[lit(1), lit(-2)]),
        "small checker accepts normal literals"
    );
}

/// Verify that `Literal::from_dimacs(0)` panics -- 0 is a DIMACS clause
/// terminator, not a valid literal.
#[test]
#[should_panic(expected = "DIMACS literal 0 is a clause terminator")]
fn test_from_dimacs_zero_panics() {
    let _ = Literal::from_dimacs(0);
}

/// Algorithm audit finding #1: literal 0 is a DIMACS terminator, not a variable.
///
/// With the `Literal` type, `Literal::from_dimacs(0)` panics at construction
/// time, so invalid literals cannot reach the checker API at all. This is
/// a stronger guarantee than the old runtime `valid_dimacs_lit()` check.
#[test]
fn test_valid_literals_accepted_in_original() {
    let mut checker = LratChecker::new(3);
    assert!(checker.add_original(1, &[lit(1), lit(2)]));
}

#[test]
fn test_valid_literals_accepted_in_derived() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    assert!(checker.add_derived(3, &[], &[1, 2]));
}

/// Clause ID 0 is the LRAT list terminator and cannot identify a clause.
#[test]
fn test_clause_id_zero_rejected() {
    let mut checker = LratChecker::new(2);
    assert!(!checker.add_original(0, &[lit(1), lit(2)]));
}

/// Algorithm audit: `Literal::negated()` is a bitwise XOR, not arithmetic
/// negation. This eliminates the entire class of overflow bugs that existed
/// with the old `negate(lit: i32) -> i32` approach.
#[test]
fn test_negated_normal_values() {
    assert_eq!(lit(1).negated(), lit(-1));
    assert_eq!(lit(-1).negated(), lit(1));
    assert_eq!(lit(42).negated(), lit(-42));
    assert_eq!(lit(-42).negated(), lit(42));
    assert_eq!(lit(i32::MAX).negated(), lit(-i32::MAX));
    // Double negation is identity.
    assert_eq!(lit(7).negated().negated(), lit(7));
}

/// Algorithm audit: `Literal::from_dimacs` rejects 0 (clause terminator).
/// `i32::MIN` is now a valid literal (variable MAX_VAR, negative polarity)
/// since the `Literal` encoding handles it without overflow.
#[test]
fn test_from_dimacs_valid_values() {
    let l1 = Literal::from_dimacs(1);
    assert!(l1.is_positive());
    assert_eq!(l1.variable().id(), 0);

    let l_neg1 = Literal::from_dimacs(-1);
    assert!(!l_neg1.is_positive());
    assert_eq!(l_neg1.variable().id(), 0);

    let l_max = Literal::from_dimacs(i32::MAX);
    assert!(l_max.is_positive());
    assert_eq!(l_max.variable().id(), (i32::MAX as u32) - 1);

    let l_neg_max = Literal::from_dimacs(-i32::MAX);
    assert!(!l_neg_max.is_positive());
    assert_eq!(l_neg_max.variable().id(), (i32::MAX as u32) - 1);

    let l_min = Literal::from_dimacs(i32::MIN);
    assert!(!l_min.is_positive());
    assert_eq!(l_min.variable().id(), Literal::MAX_VAR);
}

// ─── P1 590: Algorithm audit iteration — additional boundary condition tests ──

/// Algorithm audit: duplicate literals in a derived clause should not cause
/// a panic or incorrect verification. The checker's value() guard in
/// verify_chain() prevents double-assignment on the same variable.
///
/// When clause = [a, a], the first iteration assigns ~a. The second iteration
/// calls value(~a) which returns Some(true) (already assigned), so the
/// duplicate is silently skipped. RUP passes but resolution fails because
/// the resolvent doesn't match the duplicate-containing clause.
#[test]
fn test_duplicate_literal_in_derived_clause_no_panic() {
    let mut checker = LratChecker::new(3);
    // Formula: {a} ∧ {~a}
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    // Derive empty clause: hints [1, 2] produce conflict.
    assert!(checker.add_derived(3, &[], &[1, 2]));
    // Derive a clause with duplicate literals in a fresh checker.
    // RUP passes (no panic from duplicate). Resolution mismatch is tracked
    // (resolvent {a} doesn't match claim {a, a}) but clause is accepted.
    let mut checker2 = LratChecker::new(3);
    checker2.add_original(1, &[lit(1)]);
    checker2.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    let ok = checker2.add_derived(3, &[lit(1), lit(1)], &[1]);
    assert!(ok, "RUP-valid clause accepted despite duplicate literal");
    assert_eq!(checker2.stats.rup_ok, 1);
    assert_eq!(checker2.stats.resolution_mismatch, 1);
    assert_eq!(checker2.stats.failures, 0);
}

/// Algorithm audit: complementary literals in a derived clause cause the
/// clause to be trivially satisfied (tautological). verify_chain() detects
/// this when the second literal's negation is already true and returns true.
#[test]
fn test_complementary_literals_in_derived_clause() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]);
    // Clause [a, ~a] is a tautology — always satisfied.
    // verify_chain: assume ~a → ok. assume a: value(a) is Some(false)
    // → "literal itself is already true" → return true.
    assert!(checker.add_derived(2, &[lit(1), lit(-1)], &[]));
}

/// Algorithm audit: NonUnit hint must cause RUP failure.
///
/// CaDiCaL's LRAT checker rejects hints where more than one literal is
/// non-falsified (NonUnit). This prevents accidentally accepting proofs
/// that rely on non-unit clauses as propagation sources.
///
/// Test: formula {a, b} ∧ {~a}, derive {b}. If we provide hint [1] only
/// (which is {a, b}), after assuming ~b, clause {a, b} has both a (unassigned)
/// and ~b (false), so a is unit → Propagate(a). Then we need another hint.
/// If we provide hint [1] but it had TWO non-falsified literals, it would
/// be NonUnit and fail. This tests that the boundary between unit/non-unit
/// is correct.
#[test]
fn test_nonunit_hint_causes_rup_failure() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2), lit(3)]); // a v b v c
    checker.add_original(2, &[lit(-1)]); // ~a
                                         // Derive {b, c}: assume ~b, ~c. Hint 1 = {a, b, c}: a falsified by
                                         // hint 2? No — we haven't used hint 2 yet. a is unassigned, b is false,
                                         // c is false. Only a is non-falsified → unit. Propagate a. But we want
                                         // NonUnit: provide a hint where 2+ lits are non-falsified.
                                         // Derive {c}: assume ~c. Hint 1 = {a, b, c}: a is unassigned, b is
                                         // unassigned, c is false. non_falsified = 2 → NonUnit → fail.
    assert!(
        !checker.add_derived(3, &[lit(3)], &[1]),
        "NonUnit hint: 2 non-falsified lits in {{a,b,c}} after assuming ~c"
    );
}

/// Algorithm audit: SatisfiedUnit hint should be a no-op (not propagate).
///
/// When a hint clause has exactly 1 non-falsified literal and that literal
/// is already assigned true, the checker treats it as SatisfiedUnit and
/// continues to the next hint. It must NOT try to propagate it (which would
/// be a double-assignment).
#[test]
fn test_satisfied_unit_hint_is_noop() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(3, &[lit(1), lit(-2)]); // a v ~b
    checker.add_original(4, &[lit(-1), lit(-2)]); // ~a v ~b
                                                  // Derive empty clause. After assuming nothing (empty clause):
                                                  // Hint 1 = {a, b}: both unassigned → NonUnit? No, we need a chain.
                                                  // Better test: derive {b} with hints [1, 2].
                                                  // After assuming ~b: hint 1 = {a, b}, b is false, a is unassigned → unit a.
                                                  // Propagate a. Hint 2 = {~a, b}: ~a is false (a=true), b is false → conflict.
    assert!(checker.add_derived(5, &[lit(2)], &[1, 2]));
    // Now derive {~b} with hints [3, 4].
    // After assuming b: hint 3 = {a, ~b}, ~b is false (b=true), a is unassigned → unit a.
    // Propagate a. Hint 4 = {~a, ~b}: ~a is false, ~b is false → conflict.
    assert!(checker.add_derived(6, &[lit(-2)], &[3, 4]));
    // Now derive empty clause with hints [5, 6].
    // Hint 5 = {b}: b is unassigned → unit b. Propagate b.
    // Hint 6 = {~b}: ~b is false (b=true) → conflict!
    assert!(checker.add_derived(7, &[], &[5, 6]));
}

/// Algorithm audit: verify that duplicate hint IDs in RUP chain are rejected.
///
/// CaDiCaL lratchecker.cpp:340-347 rejects duplicate hint IDs. This prevents
/// cyclic proof chains and ensures each hint clause is used at most once.
/// Uses lenient mode so the second derivation exercises the real logic.
#[test]
fn test_duplicate_hint_ids_rejected() {
    let mut checker = LratChecker::new_lenient(3);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    // Derive empty clause with duplicate hint: [1, 1, 2].
    // The second hint ID 1 is a duplicate → fail.
    assert!(
        !checker.add_derived(3, &[], &[1, 1, 2]),
        "duplicate hint ID should be rejected"
    );
    // Normal non-duplicate hints should work.
    assert!(checker.add_derived(4, &[], &[1, 2]));
}

/// Algorithm audit: verify that tautological hint clauses are rejected.
///
/// CaDiCaL lratchecker.cpp:334-339 rejects tautological hint clauses.
/// A tautological clause is always satisfied and should never be used as
/// a unit propagation source. Uses lenient mode so the second derivation
/// exercises the real verification path.
#[test]
fn test_tautological_hint_clause_rejected() {
    let mut checker = LratChecker::new_lenient(3);
    checker.add_original(1, &[lit(1), lit(-1)]); // tautological: {a, ~a}
    checker.add_original(2, &[lit(2)]); // {b}
    checker.add_original(3, &[lit(-2)]); // {~b}
                                         // Try to derive empty clause using tautological hint.
                                         // Hints [1, 2, 3]: hint 1 is tautological → immediate fail.
    assert!(
        !checker.add_derived(4, &[], &[1, 2, 3]),
        "tautological hint clause should be rejected"
    );
    // Without the tautological hint, it works.
    assert!(checker.add_derived(5, &[], &[2, 3]));
}

/// Algorithm audit: verify_proof requires the empty clause to be derived.
///
/// A valid LRAT proof must end with a derivation of the empty clause.
/// If all individual steps verify but no empty clause is derived, the
/// proof is rejected.
#[test]
fn test_verify_proof_requires_empty_clause() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
                                                 // Derive a non-empty clause but never derive the empty clause.
    let steps = vec![LratStep::Add {
        id: 3,
        clause: vec![lit(2)],
        hints: vec![1, 2],
    }];
    assert!(
        !checker.verify_proof(&steps),
        "proof without empty clause should be rejected"
    );
}

/// hint_generation u32 wrap-around: generation 0 is the initial value of
/// ClauseEntry.hint_gen, so wrapping from u32::MAX → 0 would cause every
/// never-used clause to false-positive as "duplicate hint". The fix skips
/// generation 0 on wrap (u32::MAX → 1). This test forces the wrap and
/// verifies that hint processing still works correctly.
#[test]
fn test_hint_generation_wrap_around_skips_zero() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    // Force hint_generation to u32::MAX so the next call wraps.
    checker.hint_generation = u32::MAX;
    // This derivation must succeed: the wrap-around fix skips 0 → 1.
    assert!(
        checker.add_derived(3, &[], &[1, 2]),
        "derivation must succeed after hint_generation wraps past 0"
    );
    assert_eq!(
        checker.hint_generation, 1,
        "hint_generation should be 1 (skipped 0)"
    );
}

// -- Post-conclusion guard (#5321) --

/// add_derived must be rejected after conclude_unsat().
///
/// The `concluded` flag prevents post-conclusion mutation of the clause
/// database, which could corrupt checker state if the caller inspects
/// it after verification.
#[test]
fn test_add_derived_after_conclude_rejected() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    assert!(checker.add_derived(3, &[], &[1, 2]));
    assert_eq!(checker.conclude_unsat(), ConcludeResult::Verified);
    // Post-conclusion add_derived must return false.
    assert!(
        !checker.add_derived(4, &[lit(1)], &[1]),
        "add_derived must be rejected after conclude_unsat"
    );
}

/// add_original must be rejected after conclude_unsat().
#[test]
fn test_add_original_after_conclude_rejected() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    assert!(checker.add_derived(3, &[], &[1, 2]));
    assert_eq!(checker.conclude_unsat(), ConcludeResult::Verified);
    assert!(
        !checker.add_original(4, &[lit(1)]),
        "add_original must be rejected after conclude_unsat"
    );
}

/// delete still works after conclude_unsat (proof cleanup).
#[test]
fn test_delete_after_conclude_still_works() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    assert!(checker.add_derived(3, &[], &[1, 2]));
    assert_eq!(checker.conclude_unsat(), ConcludeResult::Verified);
    // Post-conclusion deletion for cleanup is permitted.
    assert!(
        checker.delete(1),
        "delete should still work after conclusion"
    );
}

// -- num_vars overflow guard (#5321) --

/// 2 * num_vars overflow must panic (not silently produce garbage arrays).
#[test]
#[should_panic(expected = "num_vars too large")]
fn test_num_vars_overflow_panics() {
    let _ = LratChecker::new(usize::MAX);
}

// -- Clause ID boundary tests (#5321) --

/// Clause ID u64::MAX can be added and deleted.
#[test]
fn test_clause_id_u64_max() {
    let mut checker = LratChecker::new(2);
    assert!(checker.add_original(u64::MAX, &[lit(1)]));
    assert!(checker.clause_index.contains_key(&u64::MAX));
    assert!(checker.delete(u64::MAX));
    assert!(!checker.clause_index.contains_key(&u64::MAX));
}

/// Hint ID 0 is the LRAT hint-list terminator and cannot be referenced through
/// the direct checker API.
#[test]
fn test_hint_id_zero_rejected() {
    let mut checker = LratChecker::new_lenient(2);
    assert!(checker.add_original(1, &[lit(1)]));
    assert!(checker.add_original(2, &[lit(-1)]));
    assert!(!checker.add_derived(3, &[], &[0, 1, 2]));
}

// ─── Monotonicity guard ─────────────────────────────────────────────

/// Non-monotonic derived clause IDs must be rejected at runtime.
///
/// CaDiCaL lratchecker.cpp:489 requires strictly monotonic clause IDs.
/// Previously a `debug_assert` (silent in release builds); now a runtime
/// guard that records a failure and returns false.
#[test]
fn test_non_monotonic_derived_clause_id_rejected() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b

    // Derive clause 10 (valid).
    assert!(checker.add_derived(10, &[lit(2)], &[1, 2]));
    assert_eq!(checker.stats.failures, 0);

    // Attempt clause 5 after clause 10 — non-monotonic, must fail.
    assert!(
        !checker.add_derived(5, &[lit(2)], &[1, 2]),
        "non-monotonic clause ID (5 after 10) must be rejected"
    );
    assert_eq!(checker.stats.failures, 1);
}

/// Equal clause ID (not strictly greater) must also be rejected.
#[test]
fn test_equal_derived_clause_id_rejected() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]);
    checker.add_original(2, &[lit(-1), lit(2)]);

    assert!(checker.add_derived(10, &[lit(2)], &[1, 2]));
    // Clause 10 again — duplicate ID is caught by the contains_key check,
    // but even if it weren't, the monotonicity guard rejects id == last_id.
    // The contains_key check fires first in this case, but we test the guard
    // by using a fresh ID that equals last_derived_id.
    //
    // To isolate the monotonicity guard from the duplicate-ID check, we'd
    // need an ID not in clause_index that equals last_derived_id — impossible
    // since add_derived inserts on success. The two checks reinforce each other.
    assert!(
        !checker.add_derived(10, &[lit(2)], &[1, 2]),
        "equal clause ID (10 == 10) must be rejected"
    );
    assert_eq!(checker.stats.failures, 1);
}

// Deletion, resolution, blocked clause, and memory safety tests
// are in tests_algorithm_audit_deletion.rs.
