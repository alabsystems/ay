// Copyright 2026 Andrew Yates
// CaDiCaL lratchecker parity tests (#5234): duplicate hints, tautological hints,
// deletion content verification.

use super::*;

// ─── 1. Duplicate hint rejection (CaDiCaL lratchecker.cpp:341-347) ─────

/// A proof chain that references the same hint clause twice must fail.
#[test]
fn test_duplicate_hint_rejected() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
    checker.add_original(2, &[lit(-1), lit(2)]); // ¬a ∨ b
                                                 // Hint 1 appears twice — must be rejected.
    assert!(
        !checker.add_derived(3, &[lit(2)], &[1, 1, 2]),
        "duplicate hint ID must cause chain failure"
    );
    assert_eq!(checker.stats.failures, 1);
}

/// Non-duplicate hints work normally (sanity check).
#[test]
fn test_unique_hints_accepted() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
    checker.add_original(2, &[lit(-1), lit(2)]); // ¬a ∨ b
                                                 // Both hints are unique — should succeed.
    assert!(checker.add_derived(3, &[lit(2)], &[1, 2]));
    assert_eq!(checker.stats.failures, 0);
}

// ─── 2. Tautological hint rejection (CaDiCaL lratchecker.cpp:334-339) ──

/// A tautological clause (x ∨ ¬x ∨ y) used as a hint must be rejected.
#[test]
fn test_tautological_hint_rejected() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(-1), lit(2)]); // tautological: a ∨ ¬a ∨ b
    checker.add_original(2, &[lit(-2)]); // ¬b
                                         // Hint 1 is tautological — must be rejected even though it exists.
    assert!(
        !checker.add_derived(3, &[], &[1, 2]),
        "tautological hint clause must cause chain failure"
    );
    assert_eq!(checker.stats.failures, 1);
}

/// A non-tautological original clause works as a hint.
#[test]
fn test_non_tautological_hint_accepted() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]); // a (not tautological)
    checker.add_original(2, &[lit(-1)]); // ¬a
    assert!(checker.add_derived(3, &[], &[1, 2]));
    assert_eq!(checker.stats.failures, 0);
}

/// A tautological derived clause is trivially valid and needs no proof chain.
/// CaDiCaL lratchecker.cpp:306-323.
#[test]
fn test_tautological_derived_clause_trivially_valid() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
                                                // Derived clause (a ∨ ¬a) is tautological — trivially valid, empty hints OK.
    assert!(checker.add_derived(2, &[lit(1), lit(-1)], &[]));
    assert_eq!(checker.stats.failures, 0);
}

/// A tautological derived clause gets tracked and is rejected if used as a hint.
#[test]
fn test_tautological_derived_clause_rejected_as_hint() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]); // a
    checker.add_original(2, &[lit(-1)]); // ¬a
                                         // Derive a tautological clause.
    assert!(checker.add_derived(3, &[lit(1), lit(-1)], &[]));
    // Now try to use the tautological derived clause as a hint — must fail.
    assert!(
        !checker.add_derived(4, &[], &[3, 1, 2]),
        "tautological derived clause must be rejected as hint"
    );
}

/// Deletion of a tautological clause removes it from the index.
#[test]
fn test_tautological_clause_cleanup_on_delete() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(-1)]); // tautological
    assert!(
        checker
            .clause_index
            .get(&1)
            .expect("clause 1 must exist")
            .tautological
    );
    checker.delete(1);
    assert!(!checker.clause_index.contains_key(&1));
}

// ─── 3. Deletion content verification (CaDiCaL lratchecker.cpp:634-649) ─

/// Deletion with matching content succeeds.
#[test]
fn test_delete_verified_matching_content() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2), lit(3)]); // a ∨ b ∨ c
    assert!(checker.delete_verified(1, &[lit(1), lit(2), lit(3)]));
    assert!(
        !checker.clause_index.contains_key(&1),
        "clause must be removed"
    );
    assert_eq!(checker.stats.deleted, 1);
}

/// Deletion with extra literals in the command (superset) succeeds.
/// CaDiCaL's check is a superset check: deletion command must contain
/// all stored literals, but may contain extras.
#[test]
fn test_delete_verified_superset_content() {
    let mut checker = LratChecker::new(5);
    checker.add_original(1, &[lit(1), lit(2)]); // stored: a ∨ b
                                                // Deletion command has extra literal 3 — superset is OK.
    assert!(checker.delete_verified(1, &[lit(1), lit(2), lit(3)]));
    assert!(!checker.clause_index.contains_key(&1));
}

/// Deletion with missing content fails.
#[test]
fn test_delete_verified_missing_literal_fails() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2), lit(3)]); // stored: a ∨ b ∨ c
                                                        // Deletion command is missing literal 3.
    assert!(
        !checker.delete_verified(1, &[lit(1), lit(2)]),
        "deletion with missing literal must fail"
    );
    // Clause must NOT be removed on failure.
    assert!(checker.clause_index.contains_key(&1));
    assert_eq!(checker.stats.deleted, 0);
}

/// Deletion with wrong polarity fails.
#[test]
fn test_delete_verified_wrong_polarity_fails() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // stored: a ∨ b
                                                // Deletion command has ¬a instead of a.
    assert!(!checker.delete_verified(1, &[lit(-1), lit(2)]));
    assert!(checker.clause_index.contains_key(&1));
}

/// Deletion of nonexistent clause is rejected (CaDiCaL parity, #5288).
/// CaDiCaL lratchecker.cpp:665-672 treats this as fatal.
#[test]
fn test_delete_verified_nonexistent_clause() {
    let mut checker = LratChecker::new(3);
    assert!(!checker.delete_verified(99, &[lit(1), lit(2)]));
    assert_eq!(checker.stats.deleted, 0);
    assert_eq!(checker.stats.failures, 1);
}

/// Deletion of empty clause with empty deletion literals succeeds.
#[test]
fn test_delete_verified_empty_clause() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]); // a
    checker.add_original(2, &[lit(-1)]); // ¬a
    assert!(checker.add_derived(3, &[], &[1, 2])); // empty clause
    assert!(checker.delete_verified(3, &[]));
    assert!(!checker.clause_index.contains_key(&3));
}

/// delete_verified of a tautological clause succeeds with matching content.
#[test]
fn test_delete_verified_tautological_clause() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(-1), lit(2)]); // tautological: a ∨ ¬a ∨ b
    assert!(
        checker
            .clause_index
            .get(&1)
            .expect("clause 1 exists")
            .tautological,
        "clause must be flagged tautological"
    );
    assert!(checker.delete_verified(1, &[lit(1), lit(-1), lit(2)]));
    assert!(!checker.clause_index.contains_key(&1));
    assert_eq!(checker.stats.deleted, 1);
    assert_eq!(checker.stats.deleted_originals, 1);
}

/// finalize_clause of a tautological original clause succeeds and counts.
#[test]
fn test_finalize_tautological_original_clause() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1), lit(-1)]); // tautological: a ∨ ¬a
    checker.add_original(2, &[lit(2)]);
    checker.add_original(3, &[lit(-2)]);
    assert!(checker.add_derived(4, &[], &[2, 3]));
    // Finalize all three originals including the tautological one.
    assert!(checker.finalize_clause(1, &[lit(1), lit(-1)]));
    assert!(checker.finalize_clause(2, &[lit(2)]));
    assert!(checker.finalize_clause(3, &[lit(-2)]));
    assert_eq!(checker.stats.finalized, 3);
    assert_eq!(checker.conclude_unsat(), ConcludeResult::Verified);
}

/// check_tautological detects multiple complementary pairs.
/// Clause (a, b, ¬a, ¬b) is tautological (first pair: a/¬a).
#[test]
fn test_check_tautological_multiple_pairs() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2), lit(-1), lit(-2)]);
    assert!(
        checker
            .clause_index
            .get(&1)
            .expect("clause 1 exists")
            .tautological,
        "clause with multiple complementary pairs must be tautological"
    );
}

/// check_tautological returns false for complementary across different variables.
/// Clause (a, ¬b) is NOT tautological — a and ¬b are different variables.
#[test]
fn test_check_tautological_different_variables_not_taut() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1), lit(-2)]);
    assert!(
        !checker
            .clause_index
            .get(&1)
            .expect("clause 1 exists")
            .tautological,
        "clause (a, ¬b) must not be tautological"
    );
}

// ─── is_tautological unit tests ─────────────────────────────────────────

#[test]
fn test_is_tautological_true() {
    assert!(is_tautological(&[lit(1), lit(-1)]));
    assert!(is_tautological(&[lit(2), lit(3), lit(-2)]));
    assert!(is_tautological(&[lit(-5), lit(5)]));
}

#[test]
fn test_is_tautological_false() {
    assert!(!is_tautological(&[]));
    assert!(!is_tautological(&[lit(1)]));
    assert!(!is_tautological(&[lit(1), lit(2), lit(3)]));
    assert!(!is_tautological(&[lit(1), lit(1)])); // duplicate, not tautological
}

// ─── 4. SatisfiedUnit hint handling (CaDiCaL lratchecker.cpp:370) ─────
//
// When a hint clause becomes unit under RUP propagation, but the sole
// non-falsified literal is already true (satisfied), it's a no-op.
// CaDiCaL's lratchecker.cpp does `checked_lit(unit) = true` which is a
// no-op when unit is already true. The hint is consumed but no propagation
// occurs, and the chain continues to the next hint.

/// SatisfiedUnit in the middle of a hint chain: the satisfied hint is
/// skipped and the chain continues to find a conflict.
///
/// Formula: C1=(a∨b), C2=(¬a∨b), C3=(a∨¬b), C4=(¬a∨¬b), C5=(c).
///
/// Derive (b) with hints [2, 3, 1]:
///   Assume ¬b.
///   Hint C2=(¬a∨b): b=false → unit(¬a). Assign ¬a.
///   Hint C3=(a∨¬b): a=false (from ¬a), ¬b=true (from assumption).
///     → One non-falsified literal (¬b), already true → SatisfiedUnit (no-op).
///   Hint C1=(a∨b): a=false, b=false → conflict!
#[test]
fn test_satisfied_unit_hint_in_chain() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
    checker.add_original(2, &[lit(-1), lit(2)]); // ¬a ∨ b
    checker.add_original(3, &[lit(1), lit(-2)]); // a ∨ ¬b
    checker.add_original(4, &[lit(-1), lit(-2)]); // ¬a ∨ ¬b
    checker.add_original(5, &[lit(3)]); // c (irrelevant, for sizing)

    // Hint C3 is SatisfiedUnit (¬b already true). Chain must continue.
    assert!(
        checker.add_derived(6, &[lit(2)], &[2, 3, 1]),
        "SatisfiedUnit hint must not block the chain; conflict found at C1"
    );
    assert_eq!(checker.stats.failures, 0);
}

/// SatisfiedUnit as the LAST hint: no conflict is found, RUP fails.
///
/// Derive (b) with hints [2, 3]:
///   Assume ¬b.
///   Hint C2=(¬a∨b): unit(¬a).
///   Hint C3=(a∨¬b): SatisfiedUnit (¬b is true).
///   No more hints, no conflict → RUP fails.
#[test]
fn test_satisfied_unit_as_last_hint_fails() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
    checker.add_original(2, &[lit(-1), lit(2)]); // ¬a ∨ b
    checker.add_original(3, &[lit(1), lit(-2)]); // a ∨ ¬b
    checker.add_original(4, &[lit(-1), lit(-2)]); // ¬a ∨ ¬b

    // Hints [2, 3] end with a SatisfiedUnit (C3), no conflict found.
    assert!(
        !checker.add_derived(5, &[lit(2)], &[2, 3]),
        "SatisfiedUnit as last hint without conflict must fail RUP"
    );
    assert_eq!(checker.stats.failures, 1);
}

/// NonUnit hint: a hint clause with 2+ non-falsified literals is rejected.
///
/// Derive (¬b) with hints [1]:
///   Assume b.
///   Hint C1=(a∨b): a unassigned, b true → 2 non-falsified → NonUnit → reject.
#[test]
fn test_non_unit_hint_rejected() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a ∨ b
    checker.add_original(2, &[lit(-1), lit(-2)]); // ¬a ∨ ¬b

    assert!(
        !checker.add_derived(3, &[lit(-2)], &[1]),
        "hint clause with 2 non-falsified literals must be rejected (NonUnit)"
    );
    assert_eq!(checker.stats.failures, 1);
}

// ─── Literal::index() encoding tests ────────────────────────────────────
// Encoding: positive = 2*var_id, negative = 2*var_id + 1 (var_id is 0-indexed).
// DIMACS 1 → var_id=0, DIMACS 2 → var_id=1, etc.

#[test]
fn test_literal_index_encoding() {
    // Positive literals map to even indices, negative to odd.
    assert_eq!(lit(1).index(), 0); // 2*0 + 0
    assert_eq!(lit(-1).index(), 1); // 2*0 + 1
    assert_eq!(lit(2).index(), 2); // 2*1 + 0
    assert_eq!(lit(-2).index(), 3); // 2*1 + 1
    assert_eq!(lit(100).index(), 198); // 2*99 + 0
    assert_eq!(lit(-100).index(), 199); // 2*99 + 1
}
