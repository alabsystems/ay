// Copyright 2026 Andrew Yates
// Property-based tests for the LRAT proof checker using proptest.
//
// Strategy: Generate random CNF formulas, solve them with a trivial solver
// or known-UNSAT patterns, construct LRAT proofs, and verify that the
// checker accepts valid proofs and rejects invalid ones.

use proptest::prelude::*;

use super::*;
use crate::lrat_parser::LratStep;

// ─── Strategies for generating random proof checker inputs ───────────

/// Generate a random literal in the range [1, max_var] with random polarity.
fn arb_literal(max_var: i32) -> impl Strategy<Value = Literal> {
    (1..=max_var).prop_flat_map(|var| {
        prop::bool::ANY.prop_map(move |positive| {
            if positive {
                Literal::from_dimacs(var)
            } else {
                Literal::from_dimacs(-var)
            }
        })
    })
}

/// Generate a random clause of length 1..=max_len with literals from [1, max_var].
fn arb_clause(max_var: i32, max_len: usize) -> impl Strategy<Value = Vec<Literal>> {
    prop::collection::vec(arb_literal(max_var), 1..=max_len)
}

// ─── Property tests ─────────────────────────────────────────────────

proptest! {
    /// Property: contradictory unit clauses always produce a valid proof.
    ///
    /// For any variable v in [1, max_var], the formula {v} ∧ {~v} is UNSAT,
    /// and the LRAT proof [1, 2] (empty clause from hints to both units)
    /// should always verify.
    #[test]
    fn prop_contradictory_units_always_verify(var in 1..100i32) {
        let mut checker = LratChecker::new((var + 1) as usize);
        let pos = Literal::from_dimacs(var);
        let neg = Literal::from_dimacs(-var);
        checker.add_original(1, &[pos]);
        checker.add_original(2, &[neg]);
        prop_assert!(
            checker.add_derived(3, &[], &[1, 2]),
            "empty clause from contradictory units on var {var}"
        );
        prop_assert!(checker.derived_empty_clause());
    }

    /// Property: tautological clauses are always accepted (trivially satisfied).
    ///
    /// A clause containing both l and ~l is a tautology and should always
    /// be derivable with empty hints (verify_chain detects it during
    /// clause negation when the complementary literal is already assigned).
    #[test]
    fn prop_tautological_clause_always_accepted(var in 1..100i32) {
        let mut checker = LratChecker::new((var + 1) as usize);
        checker.add_original(1, &[Literal::from_dimacs(1)]); // need at least one original
        let pos = Literal::from_dimacs(var);
        let neg = Literal::from_dimacs(-var);
        prop_assert!(
            checker.add_derived(2, &[pos, neg], &[]),
            "tautological clause {{var, ~var}} should be accepted"
        );
    }

    /// Property: duplicate clause IDs are always rejected.
    ///
    /// Adding a derived clause with an ID that already exists in the
    /// database should fail, regardless of the clause content or hints.
    #[test]
    fn prop_duplicate_clause_id_rejected(var in 1..50i32) {
        let mut checker = LratChecker::new((var + 1) as usize);
        let lit = Literal::from_dimacs(var);
        checker.add_original(1, &[lit]);
        // Try to add a derived clause with the same ID as the original.
        prop_assert!(
            !checker.add_derived(1, &[lit], &[]),
            "duplicate clause ID should be rejected"
        );
    }

    /// Property: a valid RUP chain always succeeds.
    ///
    /// For a formula {a, b} ∧ {~a, b}, deriving {b} with hints [1, 2]
    /// should always succeed regardless of variable numbering.
    #[test]
    fn prop_valid_rup_chain_succeeds(
        a in 1..50i32,
        b in 1..50i32,
    ) {
        // Ensure distinct variables.
        prop_assume!(a != b);
        let max_var = a.max(b);
        let mut checker = LratChecker::new((max_var + 1) as usize);
        let la = Literal::from_dimacs(a);
        let lb = Literal::from_dimacs(b);
        let neg_a = Literal::from_dimacs(-a);
        checker.add_original(1, &[la, lb]);      // a v b
        checker.add_original(2, &[neg_a, lb]);    // ~a v b
        // Derive {b}: assume ~b. Hint 1={a,b}: a unassigned, b false → unit a.
        // Propagate a. Hint 2={~a,b}: ~a false, b false → conflict.
        prop_assert!(
            checker.add_derived(3, &[lb], &[1, 2]),
            "valid RUP derivation of b from (a∨b)∧(~a∨b)"
        );
    }

    /// Property: deriving a non-implied clause with no hints fails when the
    /// variable is non-fresh (its negation appears in some clause).
    ///
    /// For a formula with {a} and {~b}, attempting to derive {b} with no hints
    /// should fail: RUP has no hints, RAT has no negative hints, and
    /// check_blocked eliminates b's candidate because ~b exists in the DB.
    #[test]
    fn prop_non_implied_clause_fails(
        a in 1..50i32,
        b in 1..50i32,
    ) {
        prop_assume!(a != b && a != -b);
        let max_var = a.abs().max(b.abs());
        let mut checker = LratChecker::new((max_var + 1) as usize);
        checker.add_original(1, &[Literal::from_dimacs(a)]);
        // Add ~b so that b is non-fresh → check_blocked won't accept it.
        checker.add_original(2, &[Literal::from_dimacs(-b)]);
        prop_assert!(
            !checker.add_derived(3, &[Literal::from_dimacs(b)], &[]),
            "non-implied clause should fail with no hints when ~b is in DB"
        );
    }

    /// Property: deletion followed by re-derivation works correctly.
    ///
    /// After deriving and then deleting a clause, re-deriving it with
    /// a new ID should work (the deletion removes it from the database
    /// but doesn't affect the formula's satisfiability).
    #[test]
    fn prop_delete_and_rederive(var in 1..50i32) {
        let mut checker = LratChecker::new((var + 1) as usize);
        let pos = Literal::from_dimacs(var);
        let neg = Literal::from_dimacs(-var);
        checker.add_original(1, &[pos]);
        checker.add_original(2, &[neg]);
        // Derive empty clause.
        prop_assert!(checker.add_derived(3, &[], &[1, 2]));
        // Delete it.
        checker.delete(3);
        // Re-derive with new ID.
        prop_assert!(checker.add_derived(4, &[], &[1, 2]));
    }

    /// Property: verify_proof rejects any sequence of steps that doesn't
    /// derive the empty clause.
    ///
    /// For a satisfiable formula, no sequence of valid derivations (that
    /// don't derive the empty clause) should cause verify_proof to return true.
    #[test]
    fn prop_verify_proof_rejects_without_empty_clause(
        a in 1..30i32,
        b in 1..30i32,
    ) {
        prop_assume!(a != b);
        let max_var = a.max(b);
        let mut checker = LratChecker::new((max_var + 1) as usize);
        let la = Literal::from_dimacs(a);
        let lb = Literal::from_dimacs(b);
        let neg_a = Literal::from_dimacs(-a);
        checker.add_original(1, &[la, lb]);
        checker.add_original(2, &[neg_a, lb]);
        // Derive {b} but not the empty clause.
        let steps = vec![LratStep::Add {
            id: 3,
            clause: vec![lb],
            hints: vec![1, 2],
        }];
        prop_assert!(
            !checker.verify_proof(&steps),
            "verify_proof should reject without empty clause derivation"
        );
    }

    /// Property: deleting all clauses doesn't affect prior derivation success.
    ///
    /// Once a clause is verified and inserted, deleting other clauses
    /// should not retroactively invalidate it (the checker records
    /// derivation success at insertion time, not re-checks later).
    #[test]
    fn prop_deletion_doesnt_invalidate_prior_success(var in 1..50i32) {
        let mut checker = LratChecker::new((var + 1) as usize);
        let pos = Literal::from_dimacs(var);
        let neg = Literal::from_dimacs(-var);
        checker.add_original(1, &[pos]);
        checker.add_original(2, &[neg]);
        // Derive empty clause.
        prop_assert!(checker.add_derived(3, &[], &[1, 2]));
        // Delete the original clauses.
        checker.delete(1);
        checker.delete(2);
        // The empty clause derivation was already recorded.
        prop_assert!(checker.derived_empty_clause());
    }

    /// Property: the checker handles random clause sizes without panic.
    ///
    /// For any clause size from 0 to 20, the checker should either accept
    /// or reject the derivation without panicking.
    #[test]
    fn prop_random_clause_size_no_panic(
        clause in arb_clause(10, 20),
    ) {
        let mut checker = LratChecker::new(11);
        checker.add_original(1, &[Literal::from_dimacs(1)]);
        checker.add_original(2, &[Literal::from_dimacs(-1)]);
        // Try to derive the random clause — it may or may not succeed,
        // but it must not panic.
        let _ = checker.add_derived(3, &clause, &[1, 2]);
    }

    /// Property: original clause literals must be within declared num_vars.
    ///
    /// Adding an original clause with a variable exceeding num_vars should
    /// always fail.
    #[test]
    fn prop_original_exceeds_num_vars_rejected(
        num_vars in 1..20usize,
        excess in 1..10i32,
    ) {
        let mut checker = LratChecker::new(num_vars);
        let var = (num_vars as i32) + excess;
        prop_assert!(
            !checker.add_original(1, &[Literal::from_dimacs(var)]),
            "variable {var} exceeds num_vars={num_vars}"
        );
    }
}
