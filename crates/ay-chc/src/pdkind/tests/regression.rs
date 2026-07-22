// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PDKIND regression tests.
//!
//! Extracted from pdkind/tests.rs for file size management.

use super::*;

/// Trivial unsafe: init intersects query → Unsafe(steps=0).
#[test]
fn test_pdkind_trivial_unsafe_init_intersects_query() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));
    let solver = PdkindSolver::new(problem, PdkindConfig::default());
    match solver.solve() {
        ChcEngineResult::Unsafe(cex) => {
            assert_eq!(cex.steps.len(), 1, "Expected 0-step counterexample")
        }
        other => panic!("Expected Unsafe(steps=0), got {other:?}"),
    }
}

/// Regression test #6787: PDKIND must NOT return Safe on two_phase_unsafe_000.
///
/// This problem has init x=0, pc=0. Phase 0 increments x until x>=10, then
/// transitions to phase 1 (pc=1) which decrements x. The query x<0 is
/// reachable after 22 steps (10 increments + 1 transition + 11 decrements).
///
/// The soundness requirement here is negative: PDKIND may return `Unsafe` or
/// `Unknown`, but it must reject vacuous stable frames instead of reporting a
/// bogus `Safe` invariant.
#[test]
fn test_pdkind_rejects_two_phase_unsafe_000_regression_6787() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let pc = ChcVar::new("pc", ChcSort::Int);
    let x1 = ChcVar::new("x1", ChcSort::Int);
    let pc1 = ChcVar::new("pc1", ChcSort::Int);

    // Init: x=0, pc=0 => Inv(x, pc)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())]),
    ));

    // Trans 1: Inv(x, pc) /\ pc=0 /\ x<10 => Inv(x+1, 0)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())])],
            Some(ChcExpr::and(
                ChcExpr::and(
                    ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(0)),
                    ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10)),
                ),
                ChcExpr::and(
                    ChcExpr::eq(
                        ChcExpr::var(x1.clone()),
                        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    ),
                    ChcExpr::eq(ChcExpr::var(pc1.clone()), ChcExpr::int(0)),
                ),
            )),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(x1.clone()), ChcExpr::var(pc1.clone())],
        ),
    ));

    // Trans 2: Inv(x, pc) /\ pc=0 /\ x>=10 => Inv(x, 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())])],
            Some(ChcExpr::and(
                ChcExpr::and(
                    ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(0)),
                    ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10)),
                ),
                ChcExpr::and(
                    ChcExpr::eq(ChcExpr::var(x1.clone()), ChcExpr::var(x.clone())),
                    ChcExpr::eq(ChcExpr::var(pc1.clone()), ChcExpr::int(1)),
                ),
            )),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(x1.clone()), ChcExpr::var(pc1.clone())],
        ),
    ));

    // Trans 3: Inv(x, pc) /\ pc=1 => Inv(x-1, 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())])],
            Some(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(1)),
                ChcExpr::and(
                    ChcExpr::eq(
                        ChcExpr::var(x1.clone()),
                        ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    ),
                    ChcExpr::eq(ChcExpr::var(pc1.clone()), ChcExpr::int(1)),
                ),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x1), ChcExpr::var(pc1)]),
    ));

    // Query: Inv(x, pc) /\ x < 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc)])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let config = PdkindConfig {
        max_iterations: 2,
        max_n: 2,
        max_reachability_depth: 5,
        max_reachability_iterations: 20,
        per_obligation_timeout_secs: 2,
        ..PdkindConfig::default()
    };
    let solver = PdkindSolver::new(problem, config);
    let result = solver.solve_raw();
    assert!(
        !matches!(result, RawPdkindResult::Safe(_)),
        "#6787 regression: expected non-Safe result on two_phase_unsafe_000, got {result}"
    );
}

/// Regression test #6787: the real accumulator_unsafe benchmark must never
/// return a direct PDKIND Safe result.
#[test]
fn test_pdkind_rejects_accumulator_unsafe_000_regression_6787() {
    let problem = crate::ChcParser::parse(accumulator_unsafe_000_input())
        .expect("parse accumulator_unsafe_000");
    let config = PdkindConfig {
        max_iterations: 2,
        max_n: 2,
        max_reachability_depth: 5,
        max_reachability_iterations: 20,
        per_obligation_timeout_secs: 2,
        ..PdkindConfig::default()
    };
    let solver = PdkindSolver::new(problem, config);
    let result = solver.solve_raw();
    assert!(
        !matches!(result, RawPdkindResult::Safe(_)),
        "#6787 regression: PDKIND returned false Safe on accumulator_unsafe_000. Got: {result}"
    );
}

/// max_iterations=1 forces an early bounded result without reporting Unsafe on
/// a safe system.
#[test]
fn test_pdkind_max_iterations_exceeded_returns_unknown() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(100))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(200))),
        ),
        ClauseHead::False,
    ));
    let config = PdkindConfig {
        max_iterations: 1,
        max_n: 2,
        max_reachability_depth: 1,
        max_reachability_iterations: 1,
        per_obligation_timeout_secs: 0,
        ..PdkindConfig::default()
    };
    let solver = PdkindSolver::new(problem, config);
    assert!(matches!(
        solver.solve(),
        ChcEngineResult::Safe(_) | ChcEngineResult::Unknown
    ));
}

/// Verify that FreshOnly incremental mode does not report `Unsafe` on an
/// immediately inductive safe problem. Exercises the non-incremental code path
/// in push() without letting publication test runs spend unbounded time in the
/// general-purpose default search.
#[test]
fn test_pdkind_fresh_only_bounded_no_spurious_unsafe_on_simple_safe() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ne(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));
    let bounded_config = PdkindConfig {
        max_iterations: 3,
        max_n: 3,
        max_reachability_depth: 1,
        max_reachability_iterations: 1,
        per_obligation_timeout_secs: 0,
        ..PdkindConfig::default()
    };
    let default_result = PdkindSolver::new(problem.clone(), bounded_config.clone()).solve();
    let fresh_result = PdkindSolver::new(
        problem,
        PdkindConfig {
            incremental_mode: IncrementalMode::FreshOnly("test: force non-incremental".to_string()),
            ..bounded_config
        },
    )
    .solve();
    assert!(
        !matches!(default_result, ChcEngineResult::Unsafe(_)),
        "bounded default mode must not report Unsafe on a safe system"
    );
    assert!(
        !matches!(fresh_result, ChcEngineResult::Unsafe(_)),
        "bounded FreshOnly mode must not report Unsafe on a safe system"
    );
}

fn dillig02_m_input() -> &'static str {
    r#"
(set-logic HORN)
(declare-fun |inv| ( Int Int Int Int Int Int ) Bool)
(declare-fun |inv1| ( Int Int Int Int Int Int ) Bool)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=>
      (and (and (= E 0) (= D 0) (= C (+ A (* (- 1) B))) (= B 0) (= A 1) (= F 0)))
      (inv A B C D E F))))
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=>
      (and (inv A B C D E F) true)
      (inv1 A B C D E F))))
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) )
    (=>
      (and
        (inv1 E F A C B D)
        (let ((a!1 (= H (ite (= (mod G 2) 1) (+ 1 C) C))))
          (and (= I (+ 1 B)) a!1 (= G (+ A C B D)) (= J (+ 2 D)))))
      (inv1 E F G H I J))))
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=>
      (and (inv1 A B C D E F) true)
      (inv A B C D E F))))
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=>
      (and (inv A B C E F D) (not (= E F)))
      false)))
(check-sat)
"#
}

/// Regression guard for #8161/#2925: SingleLoop LIA problems now use
/// incremental mode (no longer unconditionally forced to FreshOnly).
/// The timeout still auto-bumps to SINGLE_LOOP value when at default.
/// FreshOnly config is preserved when explicitly set (e.g., BV problems).
#[test]
fn test_pdkind_singleloop_incremental_mode_issue_8161() {
    let problem = crate::ChcParser::parse(dillig02_m_input()).expect("parse dillig02_m");

    // Default config: SingleLoop LIA now uses Incremental (#8161)
    let solver_default = PdkindSolver::new(problem.clone(), PdkindConfig::default());
    let (_, default_mode, default_timeout_secs, _) = solver_default
        .extract_transition_system_with_singleloop_fallback()
        .expect("dillig02_m should transform via SingleLoop");
    assert_eq!(
        default_mode,
        IncrementalMode::Incremental,
        "SingleLoop LIA must use Incremental mode (#8161)"
    );
    assert_eq!(
        default_timeout_secs,
        PdkindConfig::SINGLE_LOOP_PER_OBLIGATION_TIMEOUT_SECS,
        "SingleLoop fallback should auto-bump per-obligation timeout"
    );

    // Explicit FreshOnly config: must be preserved through SingleLoop path
    let solver_explicit_fresh = PdkindSolver::new(
        problem,
        PdkindConfig {
            incremental_mode: IncrementalMode::FreshOnly("BitVector state unsupported".to_string()),
            ..PdkindConfig::default()
        },
    );
    let (_, explicit_mode, explicit_timeout_secs, _) = solver_explicit_fresh
        .extract_transition_system_with_singleloop_fallback()
        .expect("dillig02_m should transform via SingleLoop");
    assert!(
        matches!(explicit_mode, IncrementalMode::FreshOnly(_)),
        "explicit FreshOnly config must be preserved through SingleLoop"
    );
    assert_eq!(
        explicit_timeout_secs,
        PdkindConfig::SINGLE_LOOP_PER_OBLIGATION_TIMEOUT_SECS,
        "SingleLoop fallback should still apply the timeout bump"
    );
}

/// Regression guard for #2925/#2765: explicit low timeout values must be
/// preserved. Only the default timeout gets auto-bumped on SingleLoop.
/// SingleLoop LIA uses Incremental mode (#8161).
#[test]
fn test_pdkind_singleloop_preserves_explicit_low_timeout_issue_2925() {
    let problem = crate::ChcParser::parse(dillig02_m_input()).expect("parse dillig02_m");
    let solver_custom_timeout = PdkindSolver::new(
        problem,
        PdkindConfig {
            per_obligation_timeout_secs: 1,
            ..PdkindConfig::default()
        },
    );
    let (_, incremental_mode, timeout_secs, _) = solver_custom_timeout
        .extract_transition_system_with_singleloop_fallback()
        .expect("dillig02_m should transform via SingleLoop");
    assert_eq!(
        incremental_mode,
        IncrementalMode::Incremental,
        "SingleLoop LIA uses Incremental mode (#8161)"
    );
    assert_eq!(
        timeout_secs, 1,
        "explicit per_obligation_timeout_secs must not be overridden"
    );
}

/// Regression test for #2761: PDKind must NOT return spurious Unsafe on dillig02_m.
/// Golem PDKind returns sat (safe) on this benchmark. AY PDKind was returning Unsafe
/// with a spurious counterexample that portfolio validation correctly rejected.
#[test]
fn test_pdkind_dillig02_m_not_spurious_unsafe_issue_2761() {
    let problem = crate::ChcParser::parse(dillig02_m_input()).expect("parse dillig02_m");
    // Test with incremental (default mode, max_iterations=3) to check for
    // quick spurious Unsafe. The issue reports ~180ms spurious Unsafe, so
    // it must happen within the first few iterations. Keep this publication
    // regression bounded; Unknown is acceptable, Unsafe is not.
    let solver_inc = PdkindSolver::new(
        problem,
        PdkindConfig {
            max_iterations: 3,
            max_n: 3,
            max_reachability_depth: 1,
            max_reachability_iterations: 1,
            per_obligation_timeout_secs: 0,
            ..PdkindConfig::default()
        },
    );
    let result = solver_inc.solve();
    // PDKind must NOT return spurious Unsafe on dillig02_m. Previous bug
    // (#2761): the incremental SAT solver produced false UNSAT, causing a
    // spurious stable frame -> Unsafe. The adaptive fallback (degrading
    // incremental_mode after validate_inductive_invariant failure) now
    // correctly retries non-incrementally.
    //
    // We assert !Unsafe rather than Safe because the zero-step
    // reachability double-check (#2750) adds per-call overhead that can
    // push the solver past the 3-iteration budget, yielding Unknown
    // instead of Safe. Unknown is acceptable; Unsafe is not (#2925).
    assert!(
        !matches!(result, ChcEngineResult::Unsafe(_)),
        "PDKind returned spurious Unsafe on dillig02_m (got {result:?}). \
             The #2761 fix (incremental false-UNSAT detection) may have regressed."
    );
}

/// PdkindResult Display formatting.
#[test]
fn test_pdkind_result_display() {
    let safe = RawPdkindResult::Safe(PdkindInvariant {
        formula: ChcExpr::Bool(true),
        induction_depth: 3,
    });
    assert_eq!(format!("{safe}"), "safe (3-inductive invariant)");
    let unsafe_r = RawPdkindResult::Unsafe(PdkindCounterexample { steps: 5 });
    assert_eq!(format!("{unsafe_r}"), "unsafe (counterexample at depth 5)");
    assert_eq!(
        format!("{}", RawPdkindResult::Unknown),
        "unknown (could not determine)"
    );
}

/// validate_counterexample returns true for a genuinely unsafe system.
/// The simple unsafe problem (x=0, x→x+1, x>=1 → false) has a 1-step
/// counterexample: init(0) ∧ Trans(0→1) ∧ query(1). BMC validation
/// must confirm this as SAT.
#[test]
fn test_validate_counterexample_genuine_unsafe_issue_4729() {
    let problem = create_simple_unsafe_problem();
    let ts = TransitionSystem::from_chc_problem(&problem)
        .expect("single-predicate problem must yield a TransitionSystem");

    // 1-step counterexample: 0 → 1, and x>=1 is the query. This is genuine.
    assert!(
        PdkindSolver::validate_counterexample(&ts, 1),
        "1-step counterexample on simple unsafe problem should be genuine (SAT)"
    );
}

/// validate_counterexample returns false for a safe system where no
/// counterexample path exists. The simple safe problem (x=0, x<5→x+1,
/// x>=10 → false) has no reachable path to x>=10.
#[test]
fn test_validate_counterexample_spurious_on_safe_system_issue_4729() {
    let problem = create_simple_safe_problem();
    let ts = TransitionSystem::from_chc_problem(&problem)
        .expect("single-predicate problem must yield a TransitionSystem");

    // Any claimed counterexample is spurious since x can never reach 10.
    // Check depths 0..5. All should return false.
    for steps in 0..6 {
        assert!(
            !PdkindSolver::validate_counterexample(&ts, steps),
            "validate_counterexample(steps={steps}) should be false on safe system"
        );
    }
}

/// validate_counterexample caps unrolling at 50 steps to bound cost.
/// Deep counterexamples return false (treated as spurious/unknown).
#[test]
fn test_validate_counterexample_deep_steps_capped_issue_4729() {
    let problem = create_simple_unsafe_problem();
    let ts = TransitionSystem::from_chc_problem(&problem)
        .expect("single-predicate problem must yield a TransitionSystem");

    // Steps > 50 should always return false regardless of system.
    assert!(
        !PdkindSolver::validate_counterexample(&ts, 51),
        "steps=51 should be capped and return false"
    );
    assert!(
        !PdkindSolver::validate_counterexample(&ts, 100),
        "steps=100 should be capped and return false"
    );

    // Steps at the boundary (50) should still be checked.
    // The unsafe problem has a counterexample at any step ≥1.
    assert!(
        PdkindSolver::validate_counterexample(&ts, 50),
        "steps=50 (at boundary) should still validate on unsafe system"
    );
}

/// PDKIND must not return spurious Unsafe on s_mutants_02 (#4729).
/// This is the benchmark that triggered the MBP overgeneralization bug
/// where Bool(true) generalization caused false Unsafe results.
/// Uses limited iterations to keep test runtime bounded in debug mode.
#[test]
fn test_pdkind_s_mutants_02_not_spurious_unsafe_issue_4729() {
    let input = r#"
(set-logic HORN)
(declare-fun |INV| ( Int Int ) Bool)
(assert
  (forall ( (A Int) (B Int) )
    (=> (and (= A 0) (= B 0)) (INV A B))
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and (INV A B) (= C (+ A 1)) (= D (+ B (+ A 1))))
      (INV C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=> (and (INV A B) (>= A 1) (not (>= B 1))) false)
  )
)
(check-sat)
"#;
    let problem = crate::ChcParser::parse(input).expect("valid SMT-LIB input");
    // Use limited config: the Bool(true) guard bug manifests on the very
    // first push() call (MBP overgeneralization happens at low k).
    // 2 iterations suffices to trigger the bug path. Obligation timeout
    // kept low (1s) since the bug is logic-level, not timeout-dependent.
    let config = PdkindConfig {
        max_iterations: 2,
        max_n: 2,
        max_reachability_depth: 3,
        max_reachability_iterations: 5,
        per_obligation_timeout_secs: 1,
        ..PdkindConfig::default()
    };
    let solver = PdkindSolver::new(problem, config);
    let result = solver.solve_raw();
    assert!(
        !matches!(result, RawPdkindResult::Unsafe(_)),
        "s_mutants_02 is SAT (safe) but PDKIND returned Unsafe — \
             Bool(true) overgeneralization guard may have regressed (#4729)"
    );
}

/// dillig05_m: 2-predicate LIA problem (expected: sat). PDKIND must NOT return
/// Unsafe. Before #6500, the relaxed Bool sort guard let SingleLoop location
/// variables through, causing a false-unsat at step 0.
#[test]
fn test_pdkind_dillig05_m_not_false_unsat_issue_6500() {
    let input = r#"
(set-logic HORN)
(declare-fun |inv| ( Int Int Int Int ) Bool)
(declare-fun |itp| ( Int Int Int Int ) Bool)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=> (and (= C 0) (= B 0) (= A 0) (= D 0)) (inv A B C D))
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=> (and (inv A B C D) true) (itp A B C D))
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) )
    (=>
      (and
        (itp A B C D)
        (and (= H (+ C F)) (= G (+ 1 B)) (= F (+ 1 A))
             (or (= I E) (= I (+ 1 E))) (= E (+ D G))))
      (itp F G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=> (and (itp A B C D) true) (inv A B C D))
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=> (and (inv A B D C) (<= C (+ (- 1) D))) false)
  )
)
(check-sat)
"#;
    let problem = crate::ChcParser::parse(input).expect("valid SMT-LIB input");
    // Default config: bv_to_bool_applied=false. PDKIND should reject the Bool
    // location variables from SingleLoop and return Unknown, not Unsafe.
    let config = PdkindConfig {
        max_iterations: 3,
        max_n: 3,
        max_reachability_depth: 1,
        max_reachability_iterations: 1,
        per_obligation_timeout_secs: 0,
        ..PdkindConfig::default()
    };
    let solver = PdkindSolver::new(problem, config);
    let result = solver.solve_raw();
    assert!(
        !matches!(result, RawPdkindResult::Unsafe(_)),
        "dillig05_m is SAT (safe) but PDKIND returned Unsafe — \
         Bool sort-guard relaxation may have regressed (#6500). \
         Got: {result}"
    );
}
