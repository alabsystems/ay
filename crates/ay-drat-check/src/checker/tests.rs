// Copyright 2026 Andrew Yates
// Tests for the DRAT proof checker.

use super::*;
use crate::checker::test_helpers::lit;

#[test]
fn test_rup_unit_resolution() {
    let mut checker = DratChecker::new(3, false);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    checker.add_original(&[lit(0, false), lit(1, true)]);
    assert!(checker.add_derived(&[lit(1, true)]).is_ok());
}

#[test]
fn test_rup_fails_for_non_implied() {
    let mut checker = DratChecker::new(3, false);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    let result = checker.add_derived(&[lit(0, false), lit(1, false)]);
    assert!(result.is_err());
}

#[test]
fn test_resolution_chain() {
    let mut checker = DratChecker::new(4, false);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    checker.add_original(&[lit(0, false), lit(2, true)]);
    checker.add_original(&[lit(1, false), lit(2, true)]);
    assert!(checker.add_derived(&[lit(2, true)]).is_ok());
}

#[test]
fn test_empty_clause() {
    let mut checker = DratChecker::new(2, false);
    checker.add_original(&[lit(0, true)]);
    checker.add_original(&[lit(0, false)]);
    assert!(checker.inconsistent);
}

#[test]
fn test_delete_clause() {
    let mut checker = DratChecker::new(3, false);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    checker.add_original(&[lit(0, false), lit(1, true)]);
    checker.add_original(&[lit(0, true), lit(1, false)]);
    assert!(checker.add_derived(&[lit(0, true)]).is_ok());
    checker.delete_clause(&[lit(0, true), lit(1, true)]);
    assert_eq!(checker.stats.deletions, 1);
}

#[test]
fn deleting_assigned_unit_cannot_create_stale_assignment_proof() {
    // Each added unit is vacuous RAT against the empty formula. Deleting the
    // first unit must be ignored while its top-level assignment is live;
    // otherwise the opposite unit is accepted against a database that no
    // longer contains its complement and the stale assignment fabricates
    // UNSAT for a satisfiable formula.
    let steps = vec![
        ProofStep::Add(vec![lit(0, true)]),
        ProofStep::Delete(vec![lit(0, true)]),
        ProofStep::Add(vec![lit(0, false)]),
        ProofStep::Add(vec![]),
    ];
    let mut checker = DratChecker::new(1, true);
    assert!(checker.verify(&[], &steps).is_err());
    assert_eq!(checker.stats.pseudo_unit_skips, 1);
}

#[test]
fn test_verify_simple_proof() {
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(0, false), lit(1, true)],
        vec![lit(0, true), lit(1, false)],
        vec![lit(0, false), lit(1, false)],
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(0, true)]),
        ProofStep::Add(vec![lit(1, true)]),
        ProofStep::Delete(vec![lit(0, true), lit(1, true)]),
        ProofStep::Add(vec![]),
    ];
    let mut checker = DratChecker::new(2, false);
    assert!(checker.verify(&clauses, &steps).is_ok());
}

#[test]
fn test_verify_rejects_invalid_proof() {
    let clauses = vec![vec![lit(0, true), lit(1, true)]];
    let steps = vec![ProofStep::Add(vec![lit(0, false)])];
    let mut checker = DratChecker::new(2, false);
    assert!(checker.verify(&clauses, &steps).is_err());
}

#[test]
fn test_rat_clause_accepted_when_rat_enabled() {
    // RAT example: introduce a fresh extension variable.
    // Formula: (a v b), (~a v b) — implies b.
    // DRAT add: (c v ~b) where c is fresh (var 2).
    // This is RAT with pivot c: there are no clauses containing ~c,
    // so the RAT condition is vacuously true (no resolvents to check).
    let mut checker = DratChecker::new(3, true); // enable RAT
    checker.add_original(&[lit(0, true), lit(1, true)]); // a v b
    checker.add_original(&[lit(0, false), lit(1, true)]); // ~a v b

    // (c v ~b) is not RUP (c is fresh, ~b is not implied),
    // but IS RAT with pivot c (no clauses contain ~c).
    let result = checker.add_derived(&[lit(2, true), lit(1, false)]);
    assert!(result.is_ok(), "RAT clause should be accepted: {result:?}");
}

#[test]
fn test_rat_clause_rejected_when_rat_disabled() {
    // (c v ~b) is RAT with pivot c (vacuously, no ~c in db), but DRUP mode rejects it.
    let mut checker = DratChecker::new(3, false); // RUP-only
    checker.add_original(&[lit(0, true), lit(1, true)]); // a v b
    checker.add_original(&[lit(0, false), lit(1, true)]); // ~a v b

    let result = checker.add_derived(&[lit(2, true), lit(1, false)]); // c v ~b
    assert!(
        result.is_err(),
        "Non-RUP clause should be rejected in DRUP mode"
    );
}

#[test]
fn test_rat_non_vacuous_resolvent_check() {
    // Non-vacuous RAT: the pivot literal appears negated in the database,
    // so actual resolvents must be checked.
    //
    // Formula: (a v b v c), (~a v b v c), (a v ~b v c), (~a v ~b v c)
    // These 4 clauses imply c.
    //
    // Add (a v b): NOT RUP (c could satisfy everything), but IS RAT with pivot a:
    //   Clauses containing ~a: (~a v b v c), (~a v ~b v c)
    //   Resolvent with (~a v b v c): (b v c) — RUP? assume ~b,~c: (a v b v c) forces a,
    //     (~a v b v c) with a=true,b=false,c=false → conflict. YES RUP.
    //   Resolvent with (~a v ~b v c): (b v ~b v c) — tautology, skip.
    let mut checker = DratChecker::new(4, true); // RAT enabled
    checker.add_original(&[lit(0, true), lit(1, true), lit(2, true)]); // a v b v c
    checker.add_original(&[lit(0, false), lit(1, true), lit(2, true)]); // ~a v b v c
    checker.add_original(&[lit(0, true), lit(1, false), lit(2, true)]); // a v ~b v c
    checker.add_original(&[lit(0, false), lit(1, false), lit(2, true)]); // ~a v ~b v c

    // (a v b) is RAT with pivot a (non-vacuous: ~a appears in clauses 2,4)
    let result = checker.add_derived(&[lit(0, true), lit(1, true)]);
    assert!(
        result.is_ok(),
        "Non-vacuous RAT should be accepted: {result:?}"
    );
    assert!(
        checker.stats.rat_checks > 0,
        "RAT check should have been triggered"
    );
}

#[test]
fn test_tautological_clause_accepted() {
    // Tautological clauses (a v ~a v b) are trivially valid.
    let mut checker = DratChecker::new(3, false);
    checker.add_original(&[lit(0, true)]);
    let result = checker.add_derived(&[lit(0, true), lit(0, false), lit(1, true)]);
    assert!(result.is_ok());
}

#[test]
fn test_large_variable_numbers() {
    // Ensure the checker handles variables beyond initial capacity.
    let mut checker = DratChecker::new(2, false);
    // Add clause with variable 999 (way beyond initial num_vars=2).
    checker.add_original(&[lit(999, true), lit(998, true)]);
    checker.add_original(&[lit(999, false), lit(998, true)]);
    let result = checker.add_derived(&[lit(998, true)]);
    assert!(result.is_ok());
}

#[test]
fn test_already_inconsistent_accepts_any_addition() {
    // Once the formula is inconsistent, all non-empty additions are valid.
    let mut checker = DratChecker::new(3, false);
    checker.add_original(&[lit(0, true)]);
    checker.add_original(&[lit(0, false)]);
    assert!(checker.inconsistent);

    // Any clause should be accepted now.
    assert!(checker.add_derived(&[lit(1, true), lit(2, false)]).is_ok());
}

#[test]
fn test_missed_delete_counted() {
    // Deleting a clause that doesn't exist should not crash, just count.
    let mut checker = DratChecker::new(3, false);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    checker.delete_clause(&[lit(0, false), lit(1, false)]); // not in db
    assert_eq!(checker.stats.missed_deletes, 1);
}

#[test]
fn test_verify_rejects_proof_without_empty_clause() {
    // A proof that adds valid intermediate clauses but never derives the
    // empty clause (contradiction) must be rejected. This was a soundness
    // gap: verify() previously returned Ok(()) for such proofs.
    //
    // Formula: (a v b v c), (~a v b v c) — satisfiable (e.g., b=true).
    // Derive (b v c) which is valid RUP (resolving on a) but does NOT
    // make the formula inconsistent, so the proof should be rejected for
    // not deriving the empty clause.
    let clauses = vec![
        vec![lit(0, true), lit(1, true), lit(2, true)], // a v b v c
        vec![lit(0, false), lit(1, true), lit(2, true)], // ~a v b v c
    ];
    // Derive (b v c) which is valid RUP but doesn't reach contradiction.
    let steps = vec![ProofStep::Add(vec![lit(1, true), lit(2, true)])];
    let mut checker = DratChecker::new(3, false);
    let result = checker.verify(&clauses, &steps);
    assert!(
        result.is_err(),
        "Proof without empty clause should be rejected"
    );
    assert!(
        result.unwrap_err().to_string().contains("empty clause"),
        "Error message should mention empty clause"
    );
}

#[test]
fn test_verify_already_inconsistent_formula_accepts_empty_proof() {
    // If the original formula is already inconsistent (e.g., contains
    // contradictory unit clauses), even an empty proof is valid.
    let clauses = vec![vec![lit(0, true)], vec![lit(0, false)]];
    let steps = vec![];
    let mut checker = DratChecker::new(2, false);
    assert!(checker.verify(&clauses, &steps).is_ok());
}

#[test]
fn test_empty_clause_not_accepted_without_rup() {
    // Soundness test: adding the empty clause should only succeed when BCP
    // derives a conflict (RUP check). A proof consisting of just "0\n"
    // (add empty clause) against a satisfiable formula must be rejected.
    //
    // This was a soundness bug: the checker unconditionally accepted the
    // empty clause addition, bypassing the RUP check.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],  // a v b
        vec![lit(0, false), lit(1, true)], // ~a v b  (together imply b, but not UNSAT)
    ];
    // Proof: just add the empty clause. Since the formula is SAT (b=true),
    // this must be rejected — the empty clause is not RUP-derivable.
    let steps = vec![ProofStep::Add(vec![])];
    let mut checker = DratChecker::new(2, false);
    let result = checker.verify(&clauses, &steps);
    assert!(
        result.is_err(),
        "Empty clause without RUP derivation should be rejected"
    );
}

#[test]
fn test_empty_clause_accepted_when_rup_derivable() {
    // The empty clause should be accepted when the formula IS inconsistent
    // and BCP on the current trail derives a conflict (RUP succeeds).
    // Formula: (a), (~a) — contradictory unit clauses. BCP after adding
    // both original clauses makes the formula inconsistent. Then the empty
    // clause add step should succeed.
    let clauses = vec![
        vec![lit(0, true)],  // a
        vec![lit(0, false)], // ~a
    ];
    let steps = vec![ProofStep::Add(vec![])];
    let mut checker = DratChecker::new(2, false);
    assert!(checker.verify(&clauses, &steps).is_ok());
}

// -- Malformed proof robustness tests (#5314) --

#[test]
fn test_duplicate_literal_in_proof_step_no_crash() {
    // Regression test for #5314: a proof step with duplicate literals should
    // not crash the checker. The old `assert!` in `assign()` would panic on
    // double-assignment; now it silently skips.
    //
    // Formula: (a v b), (~a v b), (a v ~b), (~a v ~b) — UNSAT (XOR).
    // Proof adds a clause with duplicate literal (a, a), then empty clause.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(0, false), lit(1, true)],
        vec![lit(0, true), lit(1, false)],
        vec![lit(0, false), lit(1, false)],
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(0, true), lit(0, true)]), // (a, a) — duplicate
        ProofStep::Add(vec![lit(0, true)]),               // (a) — RUP
        ProofStep::Add(vec![]),                           // empty clause
    ];
    // Must not crash (panicking assert was the old behavior).
    let mut checker = DratChecker::new(2, false);
    let _result = checker.verify(&clauses, &steps);
    // We don't care if it accepts or rejects — just that it doesn't crash.
}

#[test]
fn test_empty_formula_empty_proof_no_crash() {
    // Edge case: empty formula with empty proof. Must not crash.
    let clauses: Vec<Vec<Literal>> = vec![];
    let steps: Vec<ProofStep> = vec![];
    let mut checker = DratChecker::new(0, false);
    let result = checker.verify(&clauses, &steps);
    // Empty proof on empty formula has no empty clause — rejected.
    assert!(result.is_err());
}

#[test]
fn test_proof_references_nonexistent_variables_no_crash() {
    // Proof step references variables beyond num_vars. The checker must
    // handle this via ensure_capacity(), not crash.
    let clauses = vec![vec![lit(0, true)]]; // 1 variable
    let steps = vec![
        ProofStep::Add(vec![lit(5, true)]), // variable 5 not in formula
        ProofStep::Add(vec![]),
    ];
    let mut checker = DratChecker::new(1, false);
    let _result = checker.verify(&clauses, &steps);
    // Must not crash.
}

// -- #5323: Tests that actually exercise the changed code paths in e38b503d8 --

/// Exercise the `assign()` double-assignment guard (mod.rs:165-167).
///
/// The public API's `check_rup()` checks `value()` before calling `assign()`,
/// so duplicate literals in proof steps never reach the guard. This test calls
/// `assign()` directly to confirm the guard prevents panic on double-assignment.
#[test]
fn test_assign_double_assignment_no_panic() {
    let mut checker = DratChecker::new(3, false);
    let a = lit(0, true);
    checker.assign(a);
    assert_eq!(checker.trail.len(), 1);
    // Double-assign same literal — should silently skip, not panic.
    checker.assign(a);
    assert_eq!(
        checker.trail.len(),
        1,
        "double-assign must not extend trail"
    );
    // Double-assign opposite polarity — should also skip (variable already set).
    checker.assign(lit(0, false));
    assert_eq!(checker.trail.len(), 1, "opposite-polarity assign must skip");
}

/// Exercise the `assign_with_reason()` double-assignment guard (mod.rs:180-182).
///
/// During BCP, `assign_with_reason()` is called when unit propagation finds a
/// new implication. If the variable is already assigned (e.g., in a redundant
/// implication graph), the guard prevents panic.
#[test]
fn test_assign_with_reason_double_assignment_no_panic() {
    let mut checker = DratChecker::new(3, false);
    // Add a clause to use as reason.
    let cidx = checker.insert_clause(vec![lit(0, true), lit(1, true)]);
    // First assignment with reason.
    checker.assign_with_reason(lit(0, true), cidx);
    assert_eq!(checker.trail.len(), 1);
    // Double-assign same variable — should skip, not panic.
    checker.assign_with_reason(lit(0, false), cidx);
    assert_eq!(
        checker.trail.len(),
        1,
        "double-assign must not extend trail"
    );
}

/// Exercise the deleted-clause Skip path in BCP (propagation.rs:155-157).
///
/// When a clause is deleted (tombstoned), its watch entries remain in the watch
/// lists (lazy cleanup). BCP must handle stale watches pointing to deleted
/// clauses by returning `Visit::Skip` instead of panicking.
///
/// Note: `visit_clause` catches the `None` case first (line 155); the redundant
/// guard in `visit_long` (line 186) is defense-in-depth, structurally unreachable
/// through `visit_clause`. This test exercises the `visit_clause` guard.
#[test]
fn test_deleted_clause_watch_skip() {
    let mut checker = DratChecker::new(4, false);
    // Add a long clause (3+ literals) so it gets 2WL watches on a and b.
    let c = vec![lit(0, true), lit(1, true), lit(2, true)]; // (a v b v c)
    checker.add_original(&c);
    // Add a unit clause to ensure propagation succeeds later.
    checker.add_original(&[lit(3, true)]); // (d) — unit
                                           // Delete the long clause. Watch entries for lit(0,true) and lit(1,true) remain.
    checker.delete_clause(&c);
    // Now force BCP through the stale watch list by assigning ~a.
    // propagate_watches(~a) takes watches[a.index()], which still contains
    // the deleted clause's stale entry. visit_clause must return Skip.
    let saved = checker.trail.len();
    checker.assign(lit(0, false)); // assign ~a
    let ok = checker.propagate(); // BCP traverses watches for ~a → stale entry → Skip
    assert!(ok, "propagation should not conflict on stale watches");
    checker.backtrack(saved);
}
