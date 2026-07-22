// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::test_util::lit;

#[test]
fn test_lrat_checker_valid_chain_simple() {
    // Formula: (a ∨ b) ∧ (¬a ∨ b) → derive (b)
    // Hint chain: assume ¬b, then clause 1 (a∨b) forces a,
    //             then clause 2 (¬a∨b) has b=false, a=true → ¬a=false → conflict.
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(0, true), lit(1, true)]); // a ∨ b
    checker.add_original(2, &[lit(0, false), lit(1, true)]); // ¬a ∨ b
    checker.add_derived(3, &[lit(1, true)], &[1, 2]); // b
    assert_eq!(checker.failures(), 0);
}

#[test]
fn test_lrat_checker_valid_chain_three_clauses() {
    // (a∨b), (¬a∨c), (¬b∨c) → derive (c)
    // Hints: assume ¬c, clause 2 (¬a∨c) forces ¬a,
    //        clause 3 (¬b∨c) forces ¬b,
    //        clause 1 (a∨b) all false → conflict.
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(0, true), lit(1, true)]); // a ∨ b
    checker.add_original(2, &[lit(0, false), lit(2, true)]); // ¬a ∨ c
    checker.add_original(3, &[lit(1, false), lit(2, true)]); // ¬b ∨ c
    checker.add_derived(4, &[lit(2, true)], &[2, 3, 1]); // c
    assert_eq!(checker.failures(), 0);
}

#[test]
#[should_panic(expected = "LRAT chain verification failed")]
fn test_lrat_checker_invalid_chain_panics() {
    // (a ∨ b) — cannot derive (¬a ∧ ¬b) from this alone.
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(0, true), lit(1, true)]); // a ∨ b
    checker.add_derived(2, &[lit(0, false), lit(1, false)], &[1]); // ¬a ∨ ¬b — invalid
}

#[test]
#[should_panic(expected = "LRAT chain verification failed")]
fn test_lrat_checker_wrong_hint_order_fails() {
    // Same clauses as valid test but wrong hint order.
    // (a∨b), (¬a∨c), (¬b∨c) → derive (c) with hints [1, 2, 3]
    // With hints [1, 2, 3]:
    //   assume ¬c, clause 1 (a∨b) has 2 unassigned → no propagation,
    //   clause 2 (¬a∨c) forces ¬a, clause 3 (¬b∨c) forces ¬b.
    //   But clause 1 was already processed. No conflict.
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(0, true), lit(1, true)]);
    checker.add_original(2, &[lit(0, false), lit(2, true)]);
    checker.add_original(3, &[lit(1, false), lit(2, true)]);
    checker.add_derived(4, &[lit(2, true)], &[1, 2, 3]); // wrong order!
}

#[test]
fn test_lrat_checker_empty_clause_derivation() {
    // (a) ∧ (¬a) → derive empty clause
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(0, true)]); // a
    checker.add_original(2, &[lit(0, false)]); // ¬a
    checker.add_derived(3, &[], &[1, 2]); // empty clause
    assert_eq!(checker.failures(), 0);
}

#[test]
fn test_lrat_checker_deletion_removes_clause() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(0, true), lit(1, true)]);
    checker.add_original(2, &[lit(0, false), lit(1, true)]);
    assert!(checker.clauses.contains_key(&1));
    checker.delete(1);
    assert!(!checker.clauses.contains_key(&1));
}

#[test]
#[should_panic(expected = "LRAT chain verification failed")]
fn test_lrat_checker_empty_clause_no_hints_rejects() {
    // The in-tree LRAT checker rejects empty clause + empty hints,
    // matching the standalone ay-lrat-check and CaDiCaL lratchecker
    // behavior. Callers without a resolution chain must use
    // add_original() instead of try_add_derived() (#5236 Gap 1).
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(0, true)]);
    checker.add_original(2, &[lit(0, false)]);
    // Empty clause with no hints — must fail (strict mode).
    checker.add_derived(3, &[], &[]);
}

#[test]
fn test_lrat_checker_derived_then_used_as_hint() {
    // (a∨b), (¬a∨b) → (b) → (¬b∨c), use (b) as hint for (c)
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(0, true), lit(1, true)]);
    checker.add_original(2, &[lit(0, false), lit(1, true)]);
    checker.add_derived(3, &[lit(1, true)], &[1, 2]); // b

    checker.add_original(4, &[lit(1, false), lit(2, true)]); // ¬b ∨ c
                                                             // Derive (c) using hint chain: (b) forces b, (¬b∨c) forces c.
                                                             // Actually: assume ¬c, hint 3=(b) is unit b → assign b=true,
                                                             // hint 4=(¬b∨c) has b=true → ¬b=false, c=false → conflict!
    checker.add_derived(5, &[lit(2, true)], &[3, 4]); // c
    assert_eq!(checker.failures(), 0);
}

#[test]
#[should_panic(expected = "LRAT chain verification failed")]
fn test_lrat_checker_unknown_hint_id_rejects() {
    // Gap 2 of #5236: unknown hint IDs must cause chain failure.
    // Previously the in-tree checker silently skipped unknown hints.
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(0, true), lit(1, true)]); // a ∨ b
    checker.add_original(2, &[lit(0, false), lit(1, true)]); // ¬a ∨ b
                                                             // Hint 99 does not exist — must fail, not silently skip.
    checker.add_derived(3, &[lit(1, true)], &[99, 1, 2]);
}

#[test]
#[should_panic(expected = "LRAT chain verification failed")]
fn test_lrat_checker_deleted_hint_id_rejects() {
    // A hint referencing a deleted clause must fail (#5236).
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(0, true), lit(1, true)]); // a ∨ b
    checker.add_original(2, &[lit(0, false), lit(1, true)]); // ¬a ∨ b
    checker.delete(1); // Delete clause 1
                       // Hint 1 was deleted — chain must fail.
    checker.add_derived(3, &[lit(1, true)], &[1, 2]);
}

#[test]
#[should_panic(expected = "LRAT chain verification failed")]
fn test_lrat_checker_non_unit_hint_rejects() {
    // Gap 3 of #5236: a hint clause with 2+ non-falsified literals
    // must be rejected (CaDiCaL parity, #5233).
    // Previously the in-tree checker silently skipped such hints.
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(0, true), lit(1, true)]); // a ∨ b
    checker.add_original(2, &[lit(0, false), lit(1, true)]); // ¬a ∨ b
    checker.add_original(3, &[lit(0, true), lit(2, true)]); // a ∨ c

    // Derive (b) with hints [3, 1, 2]:
    //   Assume ¬b.
    //   Hint 3 = (a ∨ c): a=unassigned, c=unassigned → 2 non-falsified → NonUnit.
    //   Must reject here instead of skipping to hints 1 and 2.
    checker.add_derived(4, &[lit(1, true)], &[3, 1, 2]);
}

#[test]
fn test_lrat_checker_satisfied_unit_hint_is_noop() {
    // A hint clause with exactly 1 non-falsified literal that is already
    // satisfied should be a no-op (SatisfiedUnit), not a failure.
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(0, true)]); // (a) — unit
    checker.add_original(2, &[lit(0, true)]); // (a) — same literal, different ID
    checker.add_original(3, &[lit(0, false), lit(1, true)]); // ¬a ∨ b

    // Derive (b) with hints [1, 2, 3]:
    //   Assume ¬b. (variable 1 = false)
    //   Hint 1 = (a): a=unassigned → unit → assign a=true.
    //   Hint 2 = (a): a=true → 1 non-falsified, satisfied → SatisfiedUnit (no-op).
    //   Hint 3 = (¬a ∨ b): a=true → ¬a=false, b=false → conflict!
    checker.add_derived(4, &[lit(1, true)], &[1, 2, 3]);
    assert_eq!(checker.failures(), 0);
}

// ── Cross-validation: online (ay-sat) vs standalone (ay-lrat-check) ──────

/// Helper: convert DIMACS integer to ay-sat Literal.
fn sat_lit(dimacs: i32) -> Literal {
    crate::test_util::lit_signed(dimacs)
}

/// Helper: convert DIMACS integer to ay-proof-common (standalone checker) Literal.
fn proof_lit(dimacs: i32) -> ay_proof_common::literal::Literal {
    ay_proof_common::literal::Literal::from_dimacs(dimacs)
}

/// Cross-validate: both checkers accept a simple RUP derivation.
///
/// Feeds the same formula and proof to both the online (ay-sat) and
/// standalone (ay-lrat-check) checkers and verifies both accept.
/// This catches divergences between the two RUP implementations (#5273).
#[test]
fn test_cross_validate_simple_derivation() {
    // Formula: (a ∨ b) ∧ (¬a ∨ b) → derive (b), then empty clause from (b) ∧ (¬b).
    let dimacs_clauses: &[(u64, &[i32])] = &[
        (1, &[1, 2]),  // a ∨ b
        (2, &[-1, 2]), // ¬a ∨ b
        (3, &[-2]),    // ¬b
    ];
    let derivations: &[(u64, &[i32], &[u64])] = &[
        (4, &[2], &[1, 2]), // derive (b) from hints [1, 2]
        (5, &[], &[4, 3]),  // derive empty clause from (b) and (¬b)
    ];

    // Online checker (ay-sat).
    let mut online = LratChecker::new(3);
    for &(id, lits) in dimacs_clauses {
        let clause: Vec<Literal> = lits.iter().map(|&d| sat_lit(d)).collect();
        online.add_original(id, &clause);
    }
    for &(id, lits, hints) in derivations {
        let clause: Vec<Literal> = lits.iter().map(|&d| sat_lit(d)).collect();
        online.add_derived(id, &clause, hints);
    }
    assert_eq!(online.failures(), 0, "online checker rejected valid proof");

    // Standalone checker (ay-lrat-check).
    let mut standalone = ay_lrat_check::checker::LratChecker::new(3);
    for &(id, lits) in dimacs_clauses {
        let clause: Vec<_> = lits.iter().map(|&d| proof_lit(d)).collect();
        assert!(
            standalone.add_original(id, &clause),
            "standalone: add_original({id}) failed"
        );
    }
    for &(id, lits, hints) in derivations {
        let clause: Vec<_> = lits.iter().map(|&d| proof_lit(d)).collect();
        // Standalone uses i64 hints (signed, for RAT). Convert u64 → i64.
        let hints_i64: Vec<i64> = hints.iter().map(|&h| h as i64).collect();
        assert!(
            standalone.add_derived(id, &clause, &hints_i64),
            "standalone: add_derived({id}) failed"
        );
    }
}

/// Cross-validate: both checkers accept a multi-step proof with deletion.
///
/// Tests the full lifecycle: add originals, derive clauses, delete, derive
/// more, reach empty clause. Both checkers must accept all steps.
#[test]
fn test_cross_validate_derivation_with_deletion() {
    // Formula: (a∨b) ∧ (¬a∨b) ∧ (a∨¬b) ∧ (¬a∨¬b) → UNSAT
    // Proof:
    //   5: (b) from [1, 2]         (assume ¬b, clause 1 forces a, clause 2 conflict)
    //   6: (¬b) from [3, 4]        (assume b, clause 3 forces a, clause 4 conflict)
    //   d 1                        (delete clause 1)
    //   d 2                        (delete clause 2)
    //   7: () from [5, 6]          (empty clause from (b) and (¬b))
    let dimacs_clauses: &[(u64, &[i32])] = &[
        (1, &[1, 2]),   // a ∨ b
        (2, &[-1, 2]),  // ¬a ∨ b
        (3, &[1, -2]),  // a ∨ ¬b
        (4, &[-1, -2]), // ¬a ∨ ¬b
    ];

    // Online checker.
    let mut online = LratChecker::new(3);
    for &(id, lits) in dimacs_clauses {
        let clause: Vec<Literal> = lits.iter().map(|&d| sat_lit(d)).collect();
        online.add_original(id, &clause);
    }
    online.add_derived(5, &[sat_lit(2)], &[1, 2]);
    online.add_derived(6, &[sat_lit(-2)], &[3, 4]);
    online.delete(1);
    online.delete(2);
    online.add_derived(7, &[], &[5, 6]);
    assert_eq!(online.failures(), 0, "online checker rejected valid proof");

    // Standalone checker.
    let mut standalone = ay_lrat_check::checker::LratChecker::new(3);
    for &(id, lits) in dimacs_clauses {
        let clause: Vec<_> = lits.iter().map(|&d| proof_lit(d)).collect();
        assert!(standalone.add_original(id, &clause));
    }
    assert!(standalone.add_derived(5, &[proof_lit(2)], &[1, 2]));
    assert!(standalone.add_derived(6, &[proof_lit(-2)], &[3, 4]));
    assert!(standalone.delete(1));
    assert!(standalone.delete(2));
    assert!(standalone.add_derived(7, &[], &[5, 6]));
}

/// Cross-validate: both checkers accept a proof with derived-as-hint chains.
///
/// Earlier derived clauses are used as hints for later derivations.
/// Tests that both checkers properly track derived clause insertion.
#[test]
fn test_cross_validate_derived_used_as_hints() {
    // Formula: (a∨b) ∧ (¬a∨c) ∧ (¬b∨c) ∧ (¬c) → UNSAT
    // Proof:
    //   5: (c)  from [2, 3, 1]    (assume ¬c, clause 2 forces ¬a, clause 3 forces ¬b,
    //                               clause 1 conflict)
    //   6: ()   from [5, 4]        (empty clause from (c) and (¬c))
    let dimacs_clauses: &[(u64, &[i32])] = &[
        (1, &[1, 2]),  // a ∨ b
        (2, &[-1, 3]), // ¬a ∨ c
        (3, &[-2, 3]), // ¬b ∨ c
        (4, &[-3]),    // ¬c
    ];

    // Online checker.
    let mut online = LratChecker::new(4);
    for &(id, lits) in dimacs_clauses {
        let clause: Vec<Literal> = lits.iter().map(|&d| sat_lit(d)).collect();
        online.add_original(id, &clause);
    }
    online.add_derived(5, &[sat_lit(3)], &[2, 3, 1]);
    online.add_derived(6, &[], &[5, 4]);
    assert_eq!(online.failures(), 0, "online checker rejected valid proof");

    // Standalone checker.
    let mut standalone = ay_lrat_check::checker::LratChecker::new(4);
    for &(id, lits) in dimacs_clauses {
        let clause: Vec<_> = lits.iter().map(|&d| proof_lit(d)).collect();
        assert!(standalone.add_original(id, &clause));
    }
    assert!(standalone.add_derived(5, &[proof_lit(3)], &[2, 3, 1]));
    assert!(standalone.add_derived(6, &[], &[5, 4]));
}

// ── Rejection cross-validation: both checkers must reject invalid proofs (#5334) ──

/// Cross-validate rejection: unknown hint ID.
///
/// Both checkers must reject a derivation referencing a non-existent hint.
/// This catches divergences where one checker silently skips unknown hints
/// while the other correctly rejects (#5236 Gap 2).
#[test]
fn test_cross_validate_reject_unknown_hint() {
    let dimacs_clauses: &[(u64, &[i32])] = &[
        (1, &[1, 2]),  // a ∨ b
        (2, &[-1, 2]), // ¬a ∨ b
    ];

    // Online checker: must panic on unknown hint.
    let mut online = LratChecker::new(3);
    for &(id, lits) in dimacs_clauses {
        let clause: Vec<Literal> = lits.iter().map(|&d| sat_lit(d)).collect();
        online.add_original(id, &clause);
    }
    let online_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut c = LratChecker::new(3);
        for &(id, lits) in dimacs_clauses {
            let clause: Vec<Literal> = lits.iter().map(|&d| sat_lit(d)).collect();
            c.add_original(id, &clause);
        }
        c.add_derived(3, &[sat_lit(2)], &[99, 1, 2]); // hint 99 does not exist
    }));
    assert!(
        online_result.is_err(),
        "online checker must reject unknown hint ID"
    );

    // Standalone checker: must return false.
    let mut standalone = ay_lrat_check::checker::LratChecker::new(3);
    for &(id, lits) in dimacs_clauses {
        let clause: Vec<_> = lits.iter().map(|&d| proof_lit(d)).collect();
        assert!(standalone.add_original(id, &clause));
    }
    let standalone_ok = standalone.add_derived(3, &[proof_lit(2)], &[99, 1, 2]);
    assert!(
        !standalone_ok,
        "standalone checker must reject unknown hint ID"
    );
}

/// Cross-validate rejection: deleted hint clause.
///
/// Both checkers must reject a derivation that references a deleted clause.
#[test]
fn test_cross_validate_reject_deleted_hint() {
    let dimacs_clauses: &[(u64, &[i32])] = &[
        (1, &[1, 2]),  // a ∨ b
        (2, &[-1, 2]), // ¬a ∨ b
    ];

    // Online checker: must panic when hint clause was deleted.
    let online_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut c = LratChecker::new(3);
        for &(id, lits) in dimacs_clauses {
            let clause: Vec<Literal> = lits.iter().map(|&d| sat_lit(d)).collect();
            c.add_original(id, &clause);
        }
        c.delete(1);
        c.add_derived(3, &[sat_lit(2)], &[1, 2]); // hint 1 was deleted
    }));
    assert!(
        online_result.is_err(),
        "online checker must reject deleted hint"
    );

    // Standalone checker: must return false.
    let mut standalone = ay_lrat_check::checker::LratChecker::new(3);
    for &(id, lits) in dimacs_clauses {
        let clause: Vec<_> = lits.iter().map(|&d| proof_lit(d)).collect();
        assert!(standalone.add_original(id, &clause));
    }
    assert!(standalone.delete(1));
    let standalone_ok = standalone.add_derived(3, &[proof_lit(2)], &[1, 2]);
    assert!(
        !standalone_ok,
        "standalone checker must reject deleted hint"
    );
}

/// Cross-validate rejection: non-unit hint (2+ non-falsified literals).
///
/// Both checkers must reject a hint that is not unit after assuming the
/// negation of the target clause. This is the CaDiCaL parity behavior
/// (#5233, #5236 Gap 3).
#[test]
fn test_cross_validate_reject_non_unit_hint() {
    let dimacs_clauses: &[(u64, &[i32])] = &[
        (1, &[1, 2]),  // a ∨ b
        (2, &[-1, 2]), // ¬a ∨ b
        (3, &[1, 3]),  // a ∨ c
    ];

    // Online checker: must panic on non-unit hint.
    let online_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut c = LratChecker::new(4);
        for &(id, lits) in dimacs_clauses {
            let clause: Vec<Literal> = lits.iter().map(|&d| sat_lit(d)).collect();
            c.add_original(id, &clause);
        }
        // Derive (b) with hints [3, 1, 2]:
        // Assume ¬b. Hint 3 = (a ∨ c): a=unassigned, c=unassigned → NonUnit.
        c.add_derived(4, &[sat_lit(2)], &[3, 1, 2]);
    }));
    assert!(
        online_result.is_err(),
        "online checker must reject non-unit hint"
    );

    // Standalone checker: must return false.
    let mut standalone = ay_lrat_check::checker::LratChecker::new(4);
    for &(id, lits) in dimacs_clauses {
        let clause: Vec<_> = lits.iter().map(|&d| proof_lit(d)).collect();
        assert!(standalone.add_original(id, &clause));
    }
    let standalone_ok = standalone.add_derived(4, &[proof_lit(2)], &[3, 1, 2]);
    assert!(
        !standalone_ok,
        "standalone checker must reject non-unit hint"
    );
}

/// Cross-validate rejection: empty clause with empty hints.
///
/// Both checkers must reject deriving the empty clause with no hint chain.
/// The empty clause assertion requires at least one conflict-producing hint.
#[test]
fn test_cross_validate_reject_empty_clause_no_hints() {
    let dimacs_clauses: &[(u64, &[i32])] = &[
        (1, &[1]),  // a
        (2, &[-1]), // ¬a
    ];

    // Online checker: must panic.
    let online_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut c = LratChecker::new(2);
        for &(id, lits) in dimacs_clauses {
            let clause: Vec<Literal> = lits.iter().map(|&d| sat_lit(d)).collect();
            c.add_original(id, &clause);
        }
        c.add_derived(3, &[], &[]); // empty clause, no hints
    }));
    assert!(
        online_result.is_err(),
        "online checker must reject empty clause + empty hints"
    );

    // Standalone checker: must return false.
    let mut standalone = ay_lrat_check::checker::LratChecker::new(2);
    for &(id, lits) in dimacs_clauses {
        let clause: Vec<_> = lits.iter().map(|&d| proof_lit(d)).collect();
        assert!(standalone.add_original(id, &clause));
    }
    let standalone_ok = standalone.add_derived(3, &[], &[]);
    assert!(
        !standalone_ok,
        "standalone checker must reject empty clause + empty hints"
    );
}
