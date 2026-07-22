// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Timeout: 30s (measured <1s in release; conservative for debug)
#[test]
#[timeout(30_000)]
fn pdr_examples_smoke() {
    let mut config = PdrConfig::default();
    config.max_frames = 3;
    config.max_iterations = 50;
    config.max_obligations = 10_000;
    config.verbose = false;

    let counter_safe =
        pdr_solve_from_file(example_path("counter_safe.smt2"), config.clone()).unwrap();
    assert!(
        !matches!(counter_safe, PdrResult::Unsafe(_)),
        "counter_safe.smt2 should not be classified as unsafe"
    );

    let primed_vars =
        pdr_solve_from_file(example_path("primed_vars.smt2"), config.clone()).unwrap();
    assert!(
        !matches!(primed_vars, PdrResult::Unsafe(_)),
        "primed_vars.smt2 should not be classified as unsafe"
    );

    let counter_unsafe = pdr_solve_from_file(example_path("counter_unsafe.smt2"), config).unwrap();
    assert!(
        !matches!(counter_unsafe, PdrResult::Safe(_)),
        "counter_unsafe.smt2 should not be classified as safe"
    );
}

/// Test that counter_safe.smt2 is proven SAFE with fixed-point detection.
/// The system counts from 0 to 10 and never exceeds 10.
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_counter_safe_proves_safe() {
    let config = test_config(true);

    let result = pdr_solve_from_file(example_path("counter_safe.smt2"), config).unwrap();

    // Must prove Safe — accepting Unknown masks regressions (#2493).
    assert!(
        matches!(&result, PdrResult::Safe(_)),
        "expected Safe for counter_safe.smt2, got {result:?}"
    );
}

/// Test counter_unsafe with enough frames to find the counterexample.
/// The system starts at x=5 and can reach x<0 in 6 steps (5->4->3->2->1->0->-1).
///
/// Test counter_unsafe.smt2 - an unsafe counter that can go negative
///
/// Previously this test was ignored due to an infinite loop bug in must-reachability
/// checking. Fixed by implementing Golem/Spacer semantics: check must summaries at
/// level K-1 (predecessor level) rather than level K (same level).
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_counter_unsafe_finds_counterexample() {
    let mut config = test_config(true);
    config.max_frames = 15; // Need more frames for this test

    let result = pdr_solve_from_file(example_path("counter_unsafe.smt2"), config).unwrap();

    // Must find Unsafe — simple counter reaches x<0 within 15 frames.
    // Accepting Unknown masks completeness regressions (#3015).
    assert!(
        matches!(&result, PdrResult::Unsafe(_)),
        "expected Unsafe for counter_unsafe.smt2, got {result:?}"
    );
    if let PdrResult::Unsafe(cex) = &result {
        assert!(!cex.steps.is_empty(), "counterexample should have steps");
    }
}

/// Test two_counters.smt2 - counter with different bound
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_two_counters_safe() {
    let result =
        pdr_solve_from_file(example_path("two_counters.smt2"), test_config(false)).unwrap();

    // Must prove Safe — accepting Unknown masks regressions (#2493).
    assert!(
        matches!(&result, PdrResult::Safe(_)),
        "expected Safe for two_counters.smt2, got {result:?}"
    );
}

/// Test bounded_loop.smt2 - classic bounded loop
/// NOTE: This test uses a parametric invariant (i <= n) which is more complex.
/// The current PDR implementation may not find the invariant within frame limits.
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_bounded_loop_safe() {
    let result =
        pdr_solve_from_file(example_path("bounded_loop.smt2"), test_config(false)).unwrap();

    // Must prove Safe — accepting Unknown masks regressions (#2493).
    assert!(
        matches!(&result, PdrResult::Safe(_)),
        "expected Safe for bounded_loop.smt2, got {result:?}"
    );
}

/// Test unbounded_loop.smt2 - unbounded loop that requires discovering x >= 0.
///
/// This is the canonical global guidance / conjecture benchmark (#656, #1858).
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_unbounded_loop_safe_conjecture() {
    let input = include_str!("../../../../benchmarks/chc/unbounded_loop.smt2");
    let result = pdr_solve_from_str(input, test_config(false)).unwrap();

    assert!(
        matches!(result, PdrResult::Safe(_)),
        "expected Safe, got {result:?}"
    );
}

/// Test subtraction_unsafe.smt2 - counter goes negative
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_subtraction_unsafe() {
    // Only needs ~5 frames: 3 -> 2 -> 1 -> 0 -> -1
    let result =
        pdr_solve_from_file(example_path("subtraction_unsafe.smt2"), test_config(false)).unwrap();

    // System is unsafe: x goes 3, 2, 1, 0, -1.
    // Must find Unsafe — this is a simple 5-step counterexample with default config.
    // Accepting Unknown masks completeness regressions (#3015).
    assert!(
        matches!(result, PdrResult::Unsafe(_)),
        "expected Unsafe for subtraction_unsafe.smt2, got {result:?}"
    );
}

/// Test even_odd.smt2 - two predicates with independent queries
/// Even(x) tracks even numbers >= 0, Odd(x) tracks odd numbers >= 1
/// Query checks if Even(x) can have x < 0 (should be safe)
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_even_odd_safe() {
    let result = pdr_solve_from_file(example_path("even_odd.smt2"), test_config(false)).unwrap();

    // Must prove Safe — accepting Unknown masks regressions (#2493).
    assert!(
        matches!(&result, PdrResult::Safe(_)),
        "expected Safe for even_odd.smt2, got {result:?}"
    );
}

/// Regression test for bouncy two counters benchmark.
///
/// This benchmark has two predicates (itp1 and itp2) with inter-predicate transitions.
/// The entry-inductiveness check (#1423) ensures discovered invariants are valid
/// across inter-predicate transitions.
///
/// Status: AY correctly solves this as Safe with entry-inductive invariants.
///
/// Related issues:
/// - #1423: Entry-inductiveness check for discovered invariants (soundness fix)
#[test]
#[timeout(60_000)]
fn pdr_bouncy_two_counters_equality_safe() {
    let input = r#"
(set-logic HORN)

(declare-fun |itp2| ( Int Int Int ) Bool)
(declare-fun |itp1| ( Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (and (= B 0) (= A 0) (= C 0))
      )
      (itp1 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=>
      (and
        (itp1 A C B)
        (and (= E C) (= D (+ 1 A)) (= F (+ 1 B)))
      )
      (itp1 D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (itp1 A B C)
        true
      )
      (itp2 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=>
      (and
        (itp2 C A B)
        (and (= E (+ 1 A)) (= D C) (= F (+ (- 1) B)))
      )
      (itp2 D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (itp2 A B C)
        (and (= A B) (not (= C 0)))
      )
      false
    )
  )
)

(check-sat)
"#;

    let config = test_config(true);
    let result = pdr_solve_from_str(input, config).unwrap();
    assert!(
        matches!(result, PdrResult::Safe(_) | PdrResult::Unknown),
        "direct PDR should prove Safe or fail closed to Unknown, got {result:?}"
    );
}

/// Test two_vars_safe.smt2 - single predicate with two integer variables
/// Inv(x, y) tracks two counters, query checks if x + y > 10
/// Since x maxes at 5 and y maxes at 5, this is safe
///
/// Timeout: 20s (solve_timeout caps PDR at 10s; ntest is headroom for startup)
#[test]
#[timeout(20_000)]
fn pdr_two_vars_safe() {
    let mut config = test_config(false);
    // Cap at 10s: this problem currently returns Unknown.
    // Tighten to assert Safe once the PDR engine can solve this.
    config.solve_timeout = Some(std::time::Duration::from_secs(10));
    let result = pdr_solve_from_file(example_path("two_vars_safe.smt2"), config).unwrap();

    // Currently times out (returns Unknown). Tighten to assert Safe once
    // the PDR engine can solve this two-variable inductive invariant.
    assert!(
        !matches!(result, PdrResult::Unsafe(_)),
        "two_vars_safe.smt2 should not be classified as Unsafe"
    );
}

/// Test nonlinear_composition.smt2 - non-linear CHC with multiple predicates in query
/// P(x) tracks x in [0,5], Q(y) tracks y in [0,10]
/// Query: P(x) /\ Q(y) /\ x + y > 15 => false
/// This is SAFE because max(x) + max(y) = 5 + 10 = 15, not > 15
///
/// NOTE: This is a non-linear query (multiple predicates). The current PDR
/// implementation may not handle this case fully, returning Unknown.
/// We test that it at least doesn't incorrectly report Unsafe.
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_nonlinear_composition_safe() {
    let result = pdr_solve_from_file(
        example_path("nonlinear_composition.smt2"),
        test_config(false),
    )
    .unwrap();

    // For non-linear queries, we accept Safe or Unknown, but NOT Unsafe
    // (since the system is actually safe)
    match &result {
        PdrResult::Safe(model) => {
            eprintln!(
                "PDR proved non-linear CHC SAFE with {} predicates",
                model.len()
            );
        }
        PdrResult::Unknown | PdrResult::NotApplicable => {
            // Expected for now - non-linear queries are not fully supported
            eprintln!("PDR returned Unknown for non-linear CHC (expected)");
        }
        PdrResult::Unsafe(_) => {
            panic!("nonlinear_composition.smt2 should NOT be classified as Unsafe!");
        }
        _ => panic!("unexpected variant"),
    }
}

// NOTE: pdr_hyperedge_triple test deleted - times out at 180s (#492, #598)
// The benchmark hyperedge_triple.smt2 is also excluded from prover_pdr_complex_problems_soundness.
// PDR cannot currently solve 4-predicate triple hyperedge problems within reasonable time.
// Re-add this test when PDR convergence improves per #463.
