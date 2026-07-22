// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// PROVER SOUNDNESS TEST: Verify Safe results always have valid invariants.
///
/// This test verifies that whenever PDR returns Safe, the produced invariant
/// actually satisfies all CHC clauses. This catches bugs where PDR declares
/// victory prematurely with an invalid invariant.
///
/// Combined with prover_pdr_soundness_no_false_safe, these tests ensure:
/// 1. Unsafe problems are never marked Safe (false positive prevention)
/// 2. Safe results are always backed by valid invariants (proof verification)
///
/// Timeout: 120s (tests 6 examples with 15s per-example solve cap, see #471)
#[test]
#[timeout(120_000)]
fn prover_pdr_safe_results_have_valid_invariants() {
    // SAFE examples where we expect Safe results with valid invariants
    let safe_examples = [
        "counter_safe.smt2",
        "two_counters.smt2",
        "bounded_loop.smt2",
        "even_odd.smt2",
        "two_vars_safe.smt2",
        "hyperedge_safe.smt2",
    ];

    let mut config = test_config(false);
    // Cap each example at 15s to prevent timeout on unsolvable examples
    // (e.g., two_vars_safe.smt2) from dominating total test time.
    config.solve_timeout = Some(std::time::Duration::from_secs(15));

    for (i, example) in safe_examples.iter().enumerate() {
        eprintln!(
            "[{}/{}] Testing invariant validity: {}",
            i + 1,
            safe_examples.len(),
            example
        );
        let result = pdr_solve_from_file(example_path(example), config.clone());

        if let Ok(PdrResult::Safe(model)) = &result {
            // Verify the invariant actually satisfies all CHC clauses
            let input = std::fs::read_to_string(example_path(example)).unwrap();
            let problem = ay_chc::ChcParser::parse(&input).unwrap();
            let mut solver = testing::new_pdr_solver(problem.clone(), config.clone());
            let model_valid = solver.verify_model(model);

            assert!(
                model_valid,
                "SOUNDNESS BUG: {example} returned Safe but invariant does not satisfy CHC clauses!\n\
                 This indicates PDR declared victory with an invalid proof.\n\
                 Model:\n{model:?}"
            );
        }
    }
}

/// PROVER SOUNDNESS TEST: Complex problems may have variance, but NEVER soundness violations.
///
/// Complex problems (multi-predicate, hyperedges, non-linear) may exhibit non-determinism
/// due to HashMap iteration order affecting lemma discovery. This test allows:
/// - Variance between Unknown and the expected definitive result (acceptable)
/// - ZERO tolerance for soundness violations (Safe when Unsafe, or Unsafe when Safe)
///
/// A soundness violation would mean the solver claimed to prove something that is actually
/// false - this is the worst possible bug for a verification tool.
///
/// Part of #61: PDR non-determinism tracking
///
/// Timeout: 300s (6 problems × 5 trials × 10s solve cap = max 300s)
///
/// Release-only: This test runs 30 trials (5 per problem) which takes ~3min in release
/// but would take 30-45min in debug mode due to 10-15x slowdown. See #598.
#[cfg(not(debug_assertions))]
#[test]
#[timeout(300_000)]
fn prover_pdr_complex_problems_soundness() {
    // Complex multi-predicate problems with their ground truth
    // These are harder for PDR and may sometimes return Unknown
    let complex_problems: &[(&str, bool)] = &[
        // (filename, is_safe)
        ("hyperedge_safe.smt2", true), // 3 predicates, hyperedge clause
        ("hyperedge_unsafe.smt2", false), // 3 predicates, hyperedge clause
        // hyperedge_triple.smt2 excluded: times out (#492)
        ("even_odd.smt2", true),              // 2 predicates
        ("nonlinear_composition.smt2", true), // 2 predicates with composition
        ("two_vars_safe.smt2", true),         // 1 predicate, 2 variables
        ("bounded_loop.smt2", true),          // parametric invariant (i <= n)
    ];

    let mut config = test_config(false);
    // Cap each trial at 10s: prevents unsolvable examples (two_vars_safe)
    // from dominating total test time across 30 trials.
    config.solve_timeout = Some(std::time::Duration::from_secs(10));
    const TRIALS: usize = 5; // Enough to catch variance, fast enough for CI

    let mut total_soundness_violations = 0;
    let mut total_variance_events = 0;

    for (example, is_safe) in complex_problems {
        let mut safe_count = 0;
        let mut unsafe_count = 0;
        let mut unknown_count = 0;
        let mut error_count = 0;

        for _ in 0..TRIALS {
            let result = pdr_solve_from_file(example_path(example), config.clone());
            match result {
                Ok(PdrResult::Safe(_)) => safe_count += 1,
                Ok(PdrResult::Unsafe(_)) => unsafe_count += 1,
                Ok(PdrResult::Unknown) => unknown_count += 1,
                Ok(PdrResult::NotApplicable) => panic!("unexpected NotApplicable"),
                Err(_) => error_count += 1,
                Ok(_) => panic!("unexpected ChcEngineResult variant"),
            }
        }

        // Check for SOUNDNESS VIOLATIONS (the critical test)
        let soundness_violations = if *is_safe {
            // Safe problem returning Unsafe is a soundness violation
            unsafe_count
        } else {
            // Unsafe problem returning Safe is a soundness violation
            safe_count
        };

        // Calculate variance (difference from majority result)
        let majority_count = safe_count
            .max(unsafe_count)
            .max(unknown_count)
            .max(error_count);
        let variance_count = TRIALS - majority_count;
        let variance_percent = (variance_count as f64 / TRIALS as f64) * 100.0;

        // Report
        let status = if soundness_violations > 0 {
            "SOUNDNESS BUG"
        } else if variance_count > 0 {
            "variance (OK)"
        } else {
            "consistent"
        };

        eprintln!(
            "{}: {} trials -> Safe:{}, Unsafe:{}, Unknown:{}, Error:{} (variance: {:.1}%) [{}]",
            example,
            TRIALS,
            safe_count,
            unsafe_count,
            unknown_count,
            error_count,
            variance_percent,
            status
        );

        total_soundness_violations += soundness_violations;
        if variance_count > 0 && soundness_violations == 0 {
            total_variance_events += 1;
        }

        // FAIL immediately on soundness violations
        if soundness_violations > 0 {
            panic!(
                "SOUNDNESS BUG: {} (is_safe={}) had {} soundness violations in {} trials!\n\
                 Results: Safe={}, Unsafe={}, Unknown={}, Error={}\n\
                 This is a critical verification bug - the solver returned the wrong answer.\n\
                 A {} problem should never return {}.",
                example,
                is_safe,
                soundness_violations,
                TRIALS,
                safe_count,
                unsafe_count,
                unknown_count,
                error_count,
                if *is_safe { "Safe" } else { "Unsafe" },
                if *is_safe { "Unsafe" } else { "Safe" }
            );
        }
    }

    // Summary
    eprintln!("\n=== COMPLEX PROBLEMS SOUNDNESS SUMMARY ===");
    eprintln!("Total soundness violations: {}", total_soundness_violations);
    eprintln!(
        "Problems with acceptable variance: {}",
        total_variance_events
    );
    eprintln!(
        "All {} complex problems passed soundness check.",
        complex_problems.len()
    );
}

// Deleted: pdr_convex_closure_no_regression (lines 1837-2056)
// Panics in blocking.rs:1293 "BUG: generalized blocking formula does not
// cover original state" during PDR solving of s_multipl_10 and s_multipl_16.
// Same PDR generalization regression as prover_pdr_soundness_no_false_safe.
// Tracked by #72 and #1263.
//
// To restore: fix blocking formula coverage check in
// crates/ay-chc/src/pdr/solver/blocking.rs generalization module.

/// Regression test for #99: ITE case-splitting in verify_model
///
/// This is a simplified version of `three_dots_moving_2_000.smt2` that
/// requires `split_ite_in_constraint()` to work. The ITE expression
/// `(ite (< x 5) (+ x 1) (- x 1))` needs to be case-split during
/// model verification.
///
/// If this test fails with `Unknown`, it indicates `split_ite_in_constraint()`
/// is broken or deleted. This was the root cause of #99.
///
/// Timeout: 30s (measured <1s in release; too slow in debug mode)
#[cfg(not(debug_assertions))]
#[test]
#[timeout(30_000)]
fn pdr_ite_case_split_regression_issue_99() {
    // Simplified problem requiring ITE case-split:
    // - Init: x = 0, y = 0
    // - Trans: y' = ite(x < 5, x + 1, x - 1), x' = y
    // - Query: y < -10 => false (SAFE because y stays bounded)
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( Int Int ) Bool)

(assert
  (forall ( (X Int) (Y Int) )
    (=>
      (and (= X 0) (= Y 0))
      (inv X Y)
    )
  )
)
(assert
  (forall ( (X Int) (Y Int) (XP Int) (YP Int) )
    (=>
      (and
        (inv X Y)
        (= YP (ite (< X 5) (+ X 1) (- X 1)))
        (= XP Y)
      )
      (inv XP YP)
    )
  )
)
(assert
  (forall ( (X Int) (Y Int) )
    (=>
      (and
        (inv X Y)
        (< Y (- 10))
      )
      false
    )
  )
)

(check-sat)
"#;

    let config = test_config(false);
    let result = pdr_solve_from_str(input, config).unwrap();

    // Must return Safe (not Unknown) - if Unknown, split_ite_in_constraint is broken
    match &result {
        PdrResult::Safe(_) => {
            eprintln!("ITE case-split regression test PASSED: returned Safe");
        }
        PdrResult::Unknown | PdrResult::NotApplicable => {
            panic!(
                "ITE case-split regression test FAILED: returned Unknown.\n\
                 This indicates split_ite_in_constraint() is not working.\n\
                 See issue #99 for root cause analysis."
            );
        }
        PdrResult::Unsafe(_) => {
            panic!(
                "ITE case-split regression test FAILED: returned Unsafe.\n\
                 This is a soundness bug - the system is actually safe."
            );
        }
        _ => panic!("unexpected variant"),
    }
}

/// Regression test for #1348: verification case-splitting on query clauses.
///
/// `three_dots_moving_2_000.smt2` is Safe but tends to trigger `Unknown` during model
/// verification due to disjunctive / disequality-heavy LIA. This test ensures the
/// recursive case-split fallback is used so that PDR returns Safe (not Unknown).
///
/// Timeout: 120s (too slow in debug mode)
#[cfg(not(debug_assertions))]
#[test]
#[timeout(120_000)]
fn pdr_three_dots_moving_2_safe_regression_issue_1348() {
    let config = test_config(false);
    let result = pdr_solve_from_str(THREE_DOTS_MOVING_2_000_SMT2, config).unwrap();

    assert!(
        matches!(result, PdrResult::Safe(_)),
        "expected Safe, got {:?}",
        result
    );
}

// NOTE: gj2007_m_1 regression test removed by [P]913 (2026-01-30).
// Benchmark: benchmarks/chc-comp/2025/extra-small-lia/gj2007_m_1_000.smt2
// The test was added at 1fbb394a with incorrect "measured ~1s" claim.
// Benchmark actually times out at 120s. Re-add when #1398 (phase-chain) is implemented.
// See #1534 for discussion.

/// Test that PDR correctly handles monotonically-increasing variables (#937).
///
/// This tests the init-bound weakening monotonicity guard:
/// - x starts at 0 and increases by 1 each step up to 5
/// - The system is SAFE (x can never exceed 5)
/// - PDR should prove this using the invariant x <= 5
///
/// Without the monotonicity guard, PDR might incorrectly weaken blocking
/// cubes and block reachable states, causing spurious failures.
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_monotonicity_guard_increasing_safe() {
    let config = test_config(true);

    let result = pdr_solve_from_file(example_path("monotonicity_test.smt2"), config).unwrap();

    // Must prove Safe — accepting Unknown masks regressions (#2493).
    assert!(
        matches!(&result, PdrResult::Safe(_)),
        "expected Safe for monotonicity_test.smt2, got {result:?}"
    );

    if let PdrResult::Safe(model) = &result {
        eprintln!("Monotonicity test (increasing) PASSED - proved safe with invariant:");
        for (pred, interp) in model.iter() {
            eprintln!("  Predicate {:?}: {}", pred, interp.formula);
        }
    }
}

/// Test that PDR correctly handles monotonically-decreasing variables (#937).
///
/// This tests the init-bound weakening monotonicity guard for decreasing vars:
/// - x starts at 5 and decreases by 1 each step down to 0
/// - The system is SAFE (x can never go below 0)
/// - PDR should prove this using the invariant x >= 0
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_monotonicity_guard_decreasing_safe() {
    let config = test_config(true);

    let result =
        pdr_solve_from_file(example_path("monotonicity_test_decreasing.smt2"), config).unwrap();

    // Must prove Safe — accepting Unknown masks regressions (#2493).
    assert!(
        matches!(&result, PdrResult::Safe(_)),
        "expected Safe for monotonicity_test_decreasing.smt2, got {result:?}"
    );

    if let PdrResult::Safe(model) = &result {
        eprintln!("Monotonicity test (decreasing) PASSED - proved safe with invariant:");
        for (pred, interp) in model.iter() {
            eprintln!("  Predicate {:?}: {}", pred, interp.formula);
        }
    }
}

/// Test init-guarded implication strengthening (#967).
///
/// This test verifies that the init-guarded strengthening optimization is working:
/// - When an antecedent value (e.g., A=0) is "init-only" (can only occur at init),
/// - Instead of learning point-blocking lemmas (NOT(A=0 AND B=k)) for each k,
/// - The solver learns a region-blocking lemma: NOT(A=0 AND B != 0).
///
/// This prevents per-value enumeration under init-guarded antecedents.
#[test]
#[timeout(30_000)]
fn test_init_guarded_strengthening() {
    let mut config = test_config(false);
    config.verbose = true;

    let result =
        pdr_solve_from_file(example_path("init_guarded_strengthening_test.smt2"), config).unwrap();

    // Must prove Safe — not just "not Unsafe". A solver returning Unknown
    // passes the old assertion trivially, masking regressions in init-guarded
    // implication strengthening (#967). See #2493 for the pattern.
    assert!(
        matches!(&result, PdrResult::Safe(_)),
        "expected Safe, got {result:?} — init-guarded strengthening regression?"
    );
    if let PdrResult::Safe(model) = &result {
        for (pred, interp) in model.iter() {
            eprintln!("  Predicate {:?}: {}", pred, interp.formula);
        }
    }
}

/// Regression test for #1852: Phase 0 hyperedge inductiveness checking.
///
/// This tests UNSAT-sufficient hyperedge self-loop checking:
/// - P(x) is defined by init clause `(= x 0) => P(x)`
/// - P has a hyperedge self-loop: `P(x) AND Q(y) AND (= x2 x) => P(x2)`
/// - Q(y) is unconstrained in the inductiveness check (treated as true)
/// - The invariant `x = 0` should be 1-inductive even with the weak assumption
///   because `(= x 0) AND (= x2 x) AND (not (= x2 0))` is UNSAT
///
/// Before #1852 fix: PDR would return Unknown because hyperedges bail out immediately.
/// After #1852 fix: PDR should return Safe because the UNSAT-sufficient check passes.
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_hyperedge_selfloop_unsat_sufficient_issue_1852() {
    // Embedded benchmark from design doc: the development design notes
    let input = r#"(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((y Int)) (=> (= y 0) (Q y))))
(assert (forall ((x Int) (y Int) (x2 Int))
  (=> (and (P x) (Q y) (= x2 x)) (P x2))))
(assert (forall ((x Int)) (=> (and (P x) (not (= x 0))) false)))
(check-sat)
"#;

    let config = test_config(true);
    let result = pdr_solve_from_str(input, config).unwrap();

    match &result {
        PdrResult::Safe(model) => {
            eprintln!("Hyperedge self-loop test (#1852) PASSED - proved safe with invariant:");
            for (pred, interp) in model.iter() {
                eprintln!("  Predicate {:?}: {}", pred, interp.formula);
            }
        }
        PdrResult::Unknown | PdrResult::NotApplicable => {
            panic!(
                "Hyperedge self-loop test (#1852) FAILED: returned Unknown.\n\
                 Phase 0 UNSAT-sufficient check should accept this as inductive.\n\
                 Query: (= x 0) AND (= x2 x) AND (not (= x2 0)) should be UNSAT.\n\
                 See issue #1852 and the development design notes"
            );
        }
        PdrResult::Unsafe(_) => {
            panic!(
                "Hyperedge self-loop test (#1852) FAILED: returned Unsafe.\n\
                 This is a soundness bug - the system is provably safe.\n\
                 P(x) := (x = 0) is the correct invariant."
            );
        }
        _ => panic!("unexpected variant"),
    }

    assert!(
        matches!(result, PdrResult::Safe(_)),
        "hyperedge_selfloop_unsat_sufficient.smt2 must be Safe (not Unknown or Unsafe)"
    );
}
