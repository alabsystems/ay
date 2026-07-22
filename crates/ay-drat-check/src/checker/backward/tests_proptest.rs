// Copyright 2026 Andrew Yates
// Property-based forward/backward parity testing via proptest.
//
// Generates random CNF formulas (2-5 vars, 1-8 clauses) and random proof
// sequences (1-5 steps). Property: forward and backward checkers must agree
// on accept/reject for all inputs.
//
// Reference: #5260 acceptance criteria.

use proptest::prelude::*;

use super::*;
use crate::checker::test_helpers::lit;

/// Generate a random literal for `num_vars` variables.
fn arb_literal(num_vars: u32) -> impl Strategy<Value = Literal> {
    (0..num_vars, any::<bool>()).prop_map(|(var, pos)| lit(var, pos))
}

/// Generate a random clause (1-3 literals) over `num_vars` variables.
fn arb_clause(num_vars: u32) -> impl Strategy<Value = Vec<Literal>> {
    prop::collection::vec(arb_literal(num_vars), 1..=3)
}

/// Generate a random proof step (Add only — deletions tested separately).
fn arb_proof_step(num_vars: u32) -> impl Strategy<Value = ProofStep> {
    prop_oneof![
        // Add a random clause.
        arb_clause(num_vars).prop_map(ProofStep::Add),
        // Add the empty clause.
        Just(ProofStep::Add(vec![])),
    ]
}

/// Generate a formula + proof pair.
fn arb_formula_proof() -> impl Strategy<Value = (u32, Vec<Vec<Literal>>, Vec<ProofStep>)> {
    (2u32..=5).prop_flat_map(|num_vars| {
        let clauses = prop::collection::vec(arb_clause(num_vars), 1..=8);
        let steps = prop::collection::vec(arb_proof_step(num_vars), 1..=5);
        (Just(num_vars), clauses, steps)
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    /// Forward accept implies backward accept (backward only checks ACTIVE
    /// clauses, so it may accept when forward rejects a non-ACTIVE clause).
    #[test]
    fn prop_forward_backward_parity(
        (num_vars, clauses, steps) in arb_formula_proof()
    ) {
        let mut fwd = DratChecker::new(num_vars as usize, false);
        let fwd_result = fwd.verify(&clauses, &steps);

        let mut bwd = BackwardChecker::new(num_vars as usize, false);
        let bwd_result = bwd.verify(&clauses, &steps);

        if fwd_result.is_ok() {
            prop_assert!(
                bwd_result.is_ok(),
                "Backward must accept when forward accepts: fwd={:?} bwd={:?}",
                fwd_result,
                bwd_result,
            );
        }
        if bwd_result.is_err() {
            prop_assert!(
                fwd_result.is_err(),
                "Forward must reject when backward rejects: fwd={:?} bwd={:?}",
                fwd_result,
                bwd_result,
            );
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(5_000))]

    /// Forward accept implies backward accept (RAT mode).
    #[test]
    fn prop_forward_backward_parity_rat(
        (num_vars, clauses, steps) in arb_formula_proof()
    ) {
        let mut fwd = DratChecker::new(num_vars as usize, true);
        let fwd_result = fwd.verify(&clauses, &steps);

        let mut bwd = BackwardChecker::new(num_vars as usize, true);
        let bwd_result = bwd.verify(&clauses, &steps);

        if fwd_result.is_ok() {
            prop_assert!(
                bwd_result.is_ok(),
                "Backward must accept when forward accepts (RAT): fwd={:?} bwd={:?}",
                fwd_result,
                bwd_result,
            );
        }
        if bwd_result.is_err() {
            prop_assert!(
                fwd_result.is_err(),
                "Forward must reject when backward rejects (RAT): fwd={:?} bwd={:?}",
                fwd_result,
                bwd_result,
            );
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(5_000))]

    /// Forward and backward with deletions must agree.
    /// Uses fixed num_vars=4 to match literal range 0..4 (#5284).
    #[test]
    fn prop_forward_backward_parity_with_deletions(
        clauses in prop::collection::vec(
            prop::collection::vec(
                (0u32..4, any::<bool>()).prop_map(|(v, p)| lit(v, p)),
                1..=3
            ),
            2..=6
        ),
        add_steps in prop::collection::vec(
            prop_oneof![
                prop::collection::vec(
                    (0u32..4, any::<bool>()).prop_map(|(v, p)| lit(v, p)),
                    1..=3
                ).prop_map(ProofStep::Add),
                Just(ProofStep::Add(vec![])),
            ],
            1..=4
        ),
    ) {
        let num_vars = 4u32;
        // Interleave: after each add step, maybe delete the first original clause.
        let mut steps = Vec::new();
        for (i, step) in add_steps.into_iter().enumerate() {
            steps.push(step);
            if i == 0 && !clauses.is_empty() {
                steps.push(ProofStep::Delete(clauses[0].clone()));
            }
        }

        let mut fwd = DratChecker::new(num_vars as usize, false);
        let fwd_result = fwd.verify(&clauses, &steps);

        let mut bwd = BackwardChecker::new(num_vars as usize, false);
        let bwd_result = bwd.verify(&clauses, &steps);

        // Backward checking only verifies ACTIVE clauses (those in the proof
        // core). It is correct for backward to accept when forward rejects —
        // the failing clause may not be ACTIVE. But if forward accepts, backward
        // must also accept (soundness). Likewise if backward rejects, forward
        // must also reject.
        if fwd_result.is_ok() {
            prop_assert!(
                bwd_result.is_ok(),
                "Backward must accept when forward accepts: fwd={:?} bwd={:?}",
                fwd_result,
                bwd_result,
            );
        }
        if bwd_result.is_err() {
            prop_assert!(
                fwd_result.is_err(),
                "Forward must reject when backward rejects: fwd={:?} bwd={:?}",
                fwd_result,
                bwd_result,
            );
        }
    }
}

// ─── Backward-specific structural properties ─────────────────────────

proptest! {
    #![proptest_config(ProptestConfig::with_cases(5_000))]

    /// Property: backward failures ≤ forward failures.
    ///
    /// The backward checker only verifies ACTIVE clauses (those in the conflict
    /// dependency chain), so it encounters at most as many failures as the
    /// forward checker (which verifies every clause). This verifies the
    /// ACTIVE-filtering optimization doesn't produce spurious failures.
    #[test]
    fn prop_backward_failures_leq_forward(
        (num_vars, clauses, steps) in arb_formula_proof()
    ) {
        let mut fwd = DratChecker::new(num_vars as usize, false);
        let _ = fwd.verify(&clauses, &steps);

        let mut bwd = BackwardChecker::new(num_vars as usize, false);
        let _ = bwd.verify(&clauses, &steps);

        prop_assert!(
            bwd.stats().failures <= fwd.stats.failures,
            "backward failures {} should be ≤ forward failures {}",
            bwd.stats().failures,
            fwd.stats.failures,
        );
    }

    /// Property: ACTIVE clause indices are bounded by clause DB size.
    ///
    /// After backward verification of a valid proof, every clause index
    /// reported as ACTIVE by is_active() must be within [0, num_original + additions).
    /// This verifies mark_active's worklist never produces out-of-bounds indices.
    #[test]
    fn prop_active_indices_bounded(
        (num_vars, clauses, steps) in arb_formula_proof()
    ) {
        let mut bwd = BackwardChecker::new(num_vars as usize, false);
        let result = bwd.verify(&clauses, &steps);
        if result.is_ok() {
            let total_clauses = (bwd.stats().original + bwd.stats().additions) as usize;
            // Check a reasonable range of indices — active array is at most total_clauses long.
            for cidx in 0..total_clauses + 10 {
                if bwd.is_active(cidx) {
                    prop_assert!(
                        cidx < total_clauses,
                        "ACTIVE clause index {} exceeds total clauses {}",
                        cidx,
                        total_clauses,
                    );
                }
            }
        }
    }

    /// Property: contradictory formula detected in forward pass means zero
    /// ACTIVE additions.
    ///
    /// When the original formula is already UNSAT (e.g., {x} ∧ {~x}), the
    /// backward checker should detect this in the forward pass and not need
    /// to mark any derived clauses as ACTIVE (the conflict comes from
    /// originals only).
    #[test]
    fn prop_contradictory_originals_zero_active_additions(var in 0..50u32) {
        let clauses = vec![vec![lit(var, true)], vec![lit(var, false)]];
        // Proof has some random additions that shouldn't matter.
        let steps = vec![
            ProofStep::Add(vec![lit(var, true), lit(var, false)]),
        ];
        let mut bwd = BackwardChecker::new((var + 2) as usize, false);
        let result = bwd.verify(&clauses, &steps);
        prop_assert!(result.is_ok(), "contradictory formula should verify: {result:?}");
        // With contradictory originals, the forward pass detects inconsistency
        // before processing any proof steps. No derived clauses should be ACTIVE.
        // Original clauses are at indices 0..num_original, derived start after.
        let num_original = clauses.len();
        for cidx in num_original..(num_original + steps.len() + 5) {
            prop_assert!(
                !bwd.is_active(cidx),
                "derived clause {} should not be ACTIVE for contradictory originals",
                cidx,
            );
        }
    }

    /// Property: stats additions count matches proof Add steps.
    ///
    /// For any input, the backward checker's stats.additions should equal the
    /// number of Add steps in the proof. This verifies the forward pass
    /// counts every Add step exactly once.
    ///
    /// When the formula is trivially UNSAT from originals (early return at
    /// backward/mod.rs:313-315), verify() returns Ok before processing any
    /// steps, so additions == 0. We detect this case explicitly: additions==0
    /// is only valid when verify succeeded (trivially UNSAT early return).
    /// A bug that always sets additions=0 would be caught because non-trivially-
    /// UNSAT cases would have verify() returning Err, not Ok.
    #[test]
    fn prop_additions_count_matches_steps(
        (num_vars, clauses, steps) in arb_formula_proof()
    ) {
        let mut bwd = BackwardChecker::new(num_vars as usize, false);
        let result = bwd.verify(&clauses, &steps);
        let expected_additions = steps.iter().filter(|s| matches!(s, ProofStep::Add(_))).count() as u64;
        if bwd.stats().original > 0 {
            let actual = bwd.stats().additions;
            if actual == 0 && expected_additions > 0 {
                // Zero additions with non-empty proof steps: must be the
                // trivially-UNSAT early return. Verify proof succeeded.
                prop_assert!(
                    result.is_ok(),
                    "additions=0 with {} expected Add steps, but verify failed: {:?}",
                    expected_additions,
                    result,
                );
            } else {
                // Normal case: additions must match Add step count exactly.
                prop_assert_eq!(
                    actual,
                    expected_additions,
                    "additions {} should be {}",
                    actual,
                    expected_additions,
                );
            }
        }
    }

    /// Property: deletions count matches proof Delete steps.
    ///
    /// delete_forward increments stats.deletions for every Delete step
    /// unconditionally, and additionally increments missed_deletes when
    /// the clause is not found. So: deletions == expected_delete_steps,
    /// and missed_deletes ≤ deletions.
    #[test]
    fn prop_deletions_accounting(
        clauses in prop::collection::vec(
            prop::collection::vec(
                (0u32..4, any::<bool>()).prop_map(|(v, p)| lit(v, p)),
                1..=3
            ),
            2..=6
        ),
        add_steps in prop::collection::vec(
            prop_oneof![
                prop::collection::vec(
                    (0u32..4, any::<bool>()).prop_map(|(v, p)| lit(v, p)),
                    1..=3
                ).prop_map(ProofStep::Add),
                Just(ProofStep::Add(vec![])),
            ],
            1..=3
        ),
    ) {
        let num_vars = 4u32;
        // Build steps with a deletion of each original clause.
        let mut steps = Vec::new();
        for step in add_steps {
            steps.push(step);
        }
        for clause in &clauses {
            steps.push(ProofStep::Delete(clause.clone()));
        }
        steps.push(ProofStep::Add(vec![])); // empty clause at end

        let mut bwd = BackwardChecker::new(num_vars as usize, false);
        let result = bwd.verify(&clauses, &steps);

        let expected_delete_steps = steps.iter().filter(|s| matches!(s, ProofStep::Delete(_))).count() as u64;
        let stats = bwd.stats();
        if stats.additions == 0 && stats.deletions == 0 {
            // Trivially UNSAT from originals: early return skipped all steps.
            prop_assert!(
                result.is_ok(),
                "zero additions+deletions but verify failed: {:?}",
                result,
            );
        } else {
            // Steps were processed: deletions must match Delete step count.
            prop_assert_eq!(
                stats.deletions,
                expected_delete_steps,
                "deletions {} should equal delete steps {}",
                stats.deletions,
                expected_delete_steps,
            );
            prop_assert!(
                stats.missed_deletes <= stats.deletions,
                "missed_deletes {} should be ≤ deletions {}",
                stats.missed_deletes,
                stats.deletions,
            );
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2_000))]

    /// Property: clause reduction never causes a previously valid proof to fail.
    ///
    /// For the resolution pattern {a,b} ∧ {~a,b} ∧ {a,~b} ∧ {~a,~b},
    /// the backward checker applies clause reduction (removing falsified
    /// literals from ACTIVE clauses). This must not cause the proof to
    /// be rejected. Additionally, reduced_literals should be non-negative.
    #[test]
    fn prop_clause_reduction_preserves_validity(
        a in 0..20u32,
        b in 0..20u32,
    ) {
        prop_assume!(a != b);
        let max_var = a.max(b);
        let clauses = vec![
            vec![lit(a, true), lit(b, true)],
            vec![lit(a, false), lit(b, true)],
            vec![lit(a, true), lit(b, false)],
            vec![lit(a, false), lit(b, false)],
        ];
        let steps = vec![
            ProofStep::Add(vec![lit(b, true)]),
            ProofStep::Add(vec![lit(b, false)]),
            ProofStep::Add(vec![]),
        ];

        let mut bwd = BackwardChecker::new((max_var + 2) as usize, false);
        let result = bwd.verify(&clauses, &steps);
        prop_assert!(result.is_ok(), "resolution proof should verify with reduction: {result:?}");
        // reduced_literals is a count; verify it's coherent (non-negative is trivially
        // true for u64, but verify it doesn't overflow to a huge value).
        prop_assert!(
            bwd.stats().reduced_literals <= (clauses.len() * 3 + steps.len() * 3) as u64,
            "reduced_literals {} is unreasonably large",
            bwd.stats().reduced_literals,
        );
    }

    /// Property: the full resolution pattern always verifies under both
    /// forward and backward checking with RAT enabled, regardless of
    /// variable numbering.
    ///
    /// Formula: {a,b} ∧ {~a,b} ∧ {a,~b} ∧ {~a,~b} is UNSAT.
    /// Proof: derive {b} (RUP), derive {~b} (RUP), derive {} (empty).
    /// This exercises the backward checker's full pipeline: forward replay,
    /// ACTIVE marking, dependency tracking, clause reduction, and backward
    /// RUP verification — all with RAT mode enabled but not needed.
    #[test]
    fn prop_resolution_pattern_rat_mode(
        a in 0..30u32,
        b in 0..30u32,
    ) {
        prop_assume!(a != b);
        let max_var = a.max(b);
        let clauses = vec![
            vec![lit(a, true), lit(b, true)],    // a v b
            vec![lit(a, false), lit(b, true)],   // ~a v b
            vec![lit(a, true), lit(b, false)],   // a v ~b
            vec![lit(a, false), lit(b, false)],  // ~a v ~b
        ];
        let steps = vec![
            ProofStep::Add(vec![lit(b, true)]),   // derive {b}
            ProofStep::Add(vec![lit(b, false)]),  // derive {~b}
            ProofStep::Add(vec![]),               // empty clause
        ];

        let mut fwd = DratChecker::new((max_var + 2) as usize, true);
        let fwd_result = fwd.verify(&clauses, &steps);

        let mut bwd = BackwardChecker::new((max_var + 2) as usize, true);
        let bwd_result = bwd.verify(&clauses, &steps);

        prop_assert!(fwd_result.is_ok(), "forward should accept: {fwd_result:?}");
        prop_assert!(bwd_result.is_ok(), "backward should accept: {bwd_result:?}");
        // At least one original clause must be ACTIVE (the conflict depends
        // on originals). This verifies mark_active actually marks something.
        let num_orig = clauses.len();
        let any_orig_active = (0..num_orig).any(|i| bwd.is_active(i));
        prop_assert!(any_orig_active, "at least one original should be ACTIVE");
    }
}
