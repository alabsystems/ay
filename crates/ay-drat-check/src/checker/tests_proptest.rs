// Copyright 2026 Andrew Yates
// Property-based tests for the DRAT proof checker using proptest.
//
// Strategy: Generate random CNF formulas, construct DRAT proofs from
// known-UNSAT patterns, and verify that the forward (and where applicable
// backward) checker accepts valid proofs and rejects invalid ones.

use proptest::prelude::*;

use super::test_helpers::lit;
use super::DratChecker;
use crate::checker::backward::BackwardChecker;
use crate::drat_parser::ProofStep;

// ─── Strategies for generating random proof checker inputs ───────────

/// Generate a random Literal with variable index in [0, max_var) and random polarity.
fn arb_literal(max_var: u32) -> impl Strategy<Value = crate::literal::Literal> {
    (0..max_var).prop_flat_map(|var| prop::bool::ANY.prop_map(move |positive| lit(var, positive)))
}

/// Generate a random clause of length 1..=max_len with variables in [0, max_var).
fn arb_clause(max_var: u32, max_len: usize) -> impl Strategy<Value = Vec<crate::literal::Literal>> {
    prop::collection::vec(arb_literal(max_var), 1..=max_len)
}

// ─── Property tests ─────────────────────────────────────────────────

proptest! {
    /// Property: contradictory unit clauses always make the formula inconsistent.
    ///
    /// For any variable v in [0, max_var), adding {v} and {~v} as original
    /// clauses should set the checker to inconsistent.
    #[test]
    fn prop_contradictory_units_make_inconsistent(var in 0..100u32) {
        let mut checker = DratChecker::new((var + 2) as usize, false);
        checker.add_original(&[lit(var, true)]);
        checker.add_original(&[lit(var, false)]);
        prop_assert!(checker.inconsistent, "formula with {{v, ~v}} should be inconsistent");
    }

    /// Property: tautological derived clauses are always accepted.
    ///
    /// A clause containing both a and ~a is a tautology. The checker's
    /// is_tautology() check should short-circuit and return Ok.
    #[test]
    fn prop_tautological_derived_always_accepted(var in 0..100u32) {
        let mut checker = DratChecker::new((var + 2) as usize, false);
        checker.add_original(&[lit(0, true)]);  // need at least one original
        let result = checker.add_derived(&[lit(var, true), lit(var, false)]);
        prop_assert!(result.is_ok(), "tautological clause should be accepted: {result:?}");
    }

    /// Property: a valid RUP chain always succeeds.
    ///
    /// For a formula {a, b} ∧ {~a, b}, deriving {b} should always succeed
    /// regardless of variable numbering, because b is RUP-implied:
    /// assume ~b; clause 1={a,b}: b false → a unit; clause 2={~a,b}: both false → conflict.
    #[test]
    fn prop_valid_rup_chain_succeeds(
        a in 0..50u32,
        b in 0..50u32,
    ) {
        prop_assume!(a != b);
        let max_var = a.max(b);
        let mut checker = DratChecker::new((max_var + 2) as usize, false);
        checker.add_original(&[lit(a, true), lit(b, true)]);     // a v b
        checker.add_original(&[lit(a, false), lit(b, true)]);    // ~a v b
        // Derive {b}: assume ~b. Clause 1: a unit. Clause 2: ~a false, b false → conflict.
        let result = checker.add_derived(&[lit(b, true)]);
        prop_assert!(result.is_ok(), "valid RUP derivation of b: {result:?}");
    }

    /// Property: deriving a non-implied clause always fails.
    ///
    /// For a satisfiable formula with a single clause {a}, attempting to
    /// derive {b} (where b ≠ a and b ≠ ~a) should fail because b is
    /// independent of a.
    #[test]
    fn prop_non_implied_clause_fails(
        a in 0..50u32,
        b in 0..50u32,
    ) {
        prop_assume!(a != b);
        let max_var = a.max(b);
        let mut checker = DratChecker::new((max_var + 2) as usize, false);
        checker.add_original(&[lit(a, true)]);
        let result = checker.add_derived(&[lit(b, true)]);
        prop_assert!(result.is_err(), "non-implied clause should fail");
    }

    /// Property: once inconsistent, all non-empty derived clauses are accepted.
    ///
    /// After the checker becomes inconsistent (from contradictory units),
    /// any non-empty derived clause should be trivially accepted because
    /// add_derived short-circuits when inconsistent && !clause.is_empty().
    #[test]
    fn prop_inconsistent_accepts_any_nonempty(
        var in 0..50u32,
        clause in arb_clause(50, 10),
    ) {
        prop_assume!(!clause.is_empty());
        let mut checker = DratChecker::new(52, false);
        checker.add_original(&[lit(var, true)]);
        checker.add_original(&[lit(var, false)]);
        prop_assert!(checker.inconsistent);
        let result = checker.add_derived(&clause);
        prop_assert!(result.is_ok(), "inconsistent checker should accept non-empty: {result:?}");
    }

    /// Property: delete_clause of a non-existent clause increments missed_deletes.
    ///
    /// Deleting a clause that was never added should be a silent no-op
    /// that increments the missed_deletes counter without panic.
    #[test]
    fn prop_delete_nonexistent_increments_counter(
        var in 0..50u32,
    ) {
        let mut checker = DratChecker::new((var + 2) as usize, false);
        checker.add_original(&[lit(var, true)]);
        // Delete a clause we never added.
        checker.delete_clause(&[lit(var, false)]);
        prop_assert_eq!(checker.stats.missed_deletes, 1);
    }

    /// Property: verify() rejects proofs without empty clause derivation.
    ///
    /// For a satisfiable formula (at least 2 variables, no contradiction),
    /// a proof that only adds non-empty clauses (even valid ones) should
    /// be rejected because no empty clause was derived.
    #[test]
    fn prop_verify_rejects_without_empty_clause(
        a in 0..30u32,
        b in 0..30u32,
    ) {
        prop_assume!(a != b);
        let max_var = a.max(b);
        let mut checker = DratChecker::new((max_var + 2) as usize, false);
        let clauses = vec![
            vec![lit(a, true), lit(b, true)],    // a v b
            vec![lit(a, false), lit(b, true)],   // ~a v b
        ];
        let steps = vec![
            ProofStep::Add(vec![lit(b, true)]),  // derive {b} — valid but not empty
        ];
        let result = checker.verify(&clauses, &steps);
        prop_assert!(result.is_err(), "proof without empty clause should fail");
    }

    /// Property: verify() succeeds for simple contradictions.
    ///
    /// For any variable v, the formula {v} ∧ {~v} is UNSAT. The checker
    /// should detect this during add_original without any proof steps.
    #[test]
    fn prop_verify_contradictory_formula_no_steps(var in 0..100u32) {
        let mut checker = DratChecker::new((var + 2) as usize, false);
        let clauses = vec![
            vec![lit(var, true)],
            vec![lit(var, false)],
        ];
        let result = checker.verify(&clauses, &[]);
        prop_assert!(result.is_ok(), "contradictory formula should verify with no steps");
    }

    /// Property: the checker handles random clause sizes without panic.
    ///
    /// For any clause from arb_clause, the checker should either accept
    /// or reject the derivation without panicking.
    #[test]
    fn prop_random_clause_no_panic(
        clause in arb_clause(10, 20),
    ) {
        let mut checker = DratChecker::new(12, false);
        checker.add_original(&[lit(0, true)]);
        checker.add_original(&[lit(0, false)]);
        // Checker is inconsistent. Try to derive the random clause.
        let _ = checker.add_derived(&clause);
    }

    /// Property: forward and backward checkers agree on contradictory formulas.
    ///
    /// For any variable v, the formula {v} ∧ {~v} with proof [empty clause]
    /// should be accepted by both the forward and backward checkers.
    #[test]
    fn prop_forward_backward_agree_on_simple_unsat(var in 0..50u32) {
        let clauses = vec![
            vec![lit(var, true)],
            vec![lit(var, false)],
        ];
        let steps = vec![
            ProofStep::Add(vec![]),  // empty clause
        ];

        let mut forward = DratChecker::new((var + 2) as usize, false);
        let fwd_result = forward.verify(&clauses, &steps);

        let mut backward = BackwardChecker::new((var + 2) as usize, false);
        let bwd_result = backward.verify(&clauses, &steps);

        prop_assert!(fwd_result.is_ok(), "forward should accept: {fwd_result:?}");
        prop_assert!(bwd_result.is_ok(), "backward should accept: {bwd_result:?}");
    }

    /// Property: adding original clauses always succeeds (no return value).
    ///
    /// add_original() doesn't do a RUP check, so it should never fail
    /// regardless of clause content. The function has no error return —
    /// it should simply not panic.
    #[test]
    fn prop_add_original_never_panics(
        clause in arb_clause(20, 15),
    ) {
        let mut checker = DratChecker::new(22, false);
        checker.add_original(&clause);
        // No assertion needed — the property is "doesn't panic."
    }

    /// Property: deletion reduces live_clauses count.
    ///
    /// Adding an original clause and then deleting it should reduce
    /// live_clauses by 1, unless the clause was simplified away
    /// (tautology or satisfied by prior assignments).
    #[test]
    fn prop_add_delete_roundtrip(var in 0..50u32) {
        let mut checker = DratChecker::new((var + 2) as usize, false);
        // Use a non-unit clause. Assigned units are deliberately retained as
        // pseudo-units so deleting them cannot leave a stale top-level value.
        let clause = vec![lit(var, true), lit(var + 1, true)];
        checker.add_original(&clause);
        let live_before = checker.live_clauses;
        prop_assert!(live_before >= 1, "should have at least 1 live clause");
        checker.delete_clause(&clause);
        prop_assert_eq!(
            checker.live_clauses,
            live_before - 1,
            "deleting the clause should reduce live_clauses"
        );
    }

    /// Property: verify() with proof steps that produce conflict via BCP
    /// succeeds for the resolution pattern.
    ///
    /// Formula: {a,b} ∧ {~a,b} ∧ {a,~b} ∧ {~a,~b} is UNSAT.
    /// Proof: derive {b}, derive {~b}, derive empty.
    #[test]
    fn prop_full_resolution_proof(
        a in 0..30u32,
        b in 0..30u32,
    ) {
        prop_assume!(a != b);
        let max_var = a.max(b);
        let clauses = vec![
            vec![lit(a, true), lit(b, true)],     // a v b
            vec![lit(a, false), lit(b, true)],    // ~a v b
            vec![lit(a, true), lit(b, false)],    // a v ~b
            vec![lit(a, false), lit(b, false)],   // ~a v ~b
        ];
        let steps = vec![
            ProofStep::Add(vec![lit(b, true)]),   // derive {b}
            ProofStep::Add(vec![lit(b, false)]),  // derive {~b}
            ProofStep::Add(vec![]),               // derive empty
        ];

        let mut checker = DratChecker::new((max_var + 2) as usize, false);
        let result = checker.verify(&clauses, &steps);
        prop_assert!(result.is_ok(), "full resolution proof should verify: {result:?}");
    }
}
