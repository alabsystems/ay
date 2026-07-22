// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]

use super::*;
use crate::pdr::config::PdrConfig;
use crate::pdr::frame::Frame;
use crate::{ChcExpr, ChcOp, ChcParser};

fn expr_contains(formula: &ChcExpr, needle: &ChcExpr) -> bool {
    if formula == needle {
        return true;
    }
    match formula {
        ChcExpr::Op(_, args) => args.iter().any(|arg| expr_contains(arg, needle)),
        ChcExpr::PredicateApp(_, _, args) => args.iter().any(|arg| expr_contains(arg, needle)),
        _ => false,
    }
}

#[test]
fn main_loop_direct_safety_proof_requires_deeper_frames() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (inv x) (= x2 (+ x 1))) (inv x2))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;

    let mut solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let x = solver.canonical_vars(inv).unwrap()[0].clone();
    let x_ge_0 = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));
    solver.frames[1].add_lemma(Lemma::new(inv, x_ge_0, 1));

    // Default solver has only two frames; the main-loop fallback should be gated off.
    assert!(
        solver.try_main_loop_direct_safety_proof().is_none(),
        "main-loop direct safety proof must be gated while frames.len() <= 3"
    );
}

#[test]
fn main_loop_direct_safety_proof_uses_entry_inductive_fallback_model() {
    // p(1) -> q(1), q self-loop identity.
    // q <= 0 is self-inductive but NOT entry-inductive.
    // q <= 1 is both self-inductive and entry-inductive.
    // The fallback should return a model that keeps q <= 1 and filters q <= 0.
    let smt2 = r#"
(set-logic HORN)
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 1) (p x))))
(assert (forall ((x Int)) (=> (p x) (q x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (q x) (= x2 x)) (q x2))))
(assert (forall ((x Int)) (=> (and (q x) (> x 1)) false)))
(check-sat)
"#;

    let mut solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    let p = solver.problem.lookup_predicate("p").unwrap();
    let p_var = solver.canonical_vars(p).unwrap()[0].clone();
    let p_eq_1 = ChcExpr::eq(ChcExpr::var(p_var), ChcExpr::int(1));
    let q = solver.problem.lookup_predicate("q").unwrap();
    let q_var = solver.canonical_vars(q).unwrap()[0].clone();
    let q_le_1 = ChcExpr::le(ChcExpr::var(q_var.clone()), ChcExpr::int(1));
    let q_le_0 = ChcExpr::le(ChcExpr::var(q_var), ChcExpr::int(0));

    solver.frames[1].add_lemma(Lemma::new(p, p_eq_1, 1));
    solver.frames[1].add_lemma(Lemma::new(q, q_le_1.clone(), 1));
    solver.frames[1].add_lemma(Lemma::new(q, q_le_0.clone(), 1));

    // Trigger main-loop fallback guard.
    while solver.frames.len() <= 3 {
        solver.frames.push(Frame::new());
    }

    // Sanity: strict-inductive-only model keeps both q<=1 and q<=0, and is invalid.
    let strict_only = solver.build_model_from_inductive_lemmas(1);
    assert!(
        !solver.verify_model(&strict_only),
        "strict-inductive-only model should fail entry transition validation"
    );

    let model = solver
        .try_main_loop_direct_safety_proof()
        .expect("main-loop fallback should produce a verified model");
    let q_formula = &model.get(&q).expect("q interpretation missing").formula;

    assert!(
        expr_contains(q_formula, &q_le_1),
        "fallback model should retain entry-inductive lemma q <= 1, got {q_formula}"
    );
    assert!(
        !expr_contains(q_formula, &q_le_0),
        "fallback model should filter non-entry-inductive lemma q <= 0, got {q_formula}"
    );

    // Ensure no accidental disjunction was introduced.
    fn has_or(expr: &ChcExpr) -> bool {
        match expr {
            ChcExpr::Op(ChcOp::Or, _) => true,
            ChcExpr::Op(_, args) => args.iter().any(|arg| has_or(arg)),
            ChcExpr::PredicateApp(_, _, args) => args.iter().any(|arg| has_or(arg)),
            _ => false,
        }
    }
    assert!(
        !has_or(q_formula),
        "expected conjunctive fallback model for q, got {q_formula}"
    );
}

/// Regression test for #2983: strengthen returns Unknown (not Safe) when
/// the obligation queue overflows during processing.
#[test]
fn strengthen_returns_unknown_on_obligation_queue_overflow_issue_2983() {
    use super::StrengthenResult;

    // Safe problem with 3 separate query clauses. Each query creates one
    // POB during strengthen. With max_obligations=1 (cap=2), the 3rd query
    // POB push overflows the queue, triggering the #2983 degradation guard.
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (inv x) (= x2 (+ x 1))) (inv x2))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(assert (forall ((x Int)) (=> (and (inv x) (< x (- 10))) false)))
(assert (forall ((x Int)) (=> (and (inv x) (< x (- 20))) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    // max_obligations=1 → cap=2. Three queries will push 3 POBs, overflowing the cap.
    let config = PdrConfig {
        max_obligations: 1,
        max_iterations: 5,
        max_frames: 5,
        ..PdrConfig::default()
    };

    let mut solver = PdrSolver::new(problem, config);
    let result = solver.strengthen();

    // With 3 query POBs and cap=2, at least one POB is dropped.
    // Strengthen must return Unknown (not Safe) because the exploration
    // is incomplete.
    assert!(
        matches!(result, StrengthenResult::Unknown),
        "strengthen must return Unknown when obligation queue overflows, got {:?}",
        match &result {
            StrengthenResult::Safe => "Safe",
            StrengthenResult::Unsafe(_) => "Unsafe",
            StrengthenResult::Unknown => "Unknown",
            StrengthenResult::Continue => "Continue",
        }
    );
    assert!(
        solver.obligations.overflowed,
        "obligations.overflowed flag must be set after overflow"
    );
}

/// Regression test for #2806: build_trivial_cex() produces a valid
/// counterexample with no steps and no witness, and the solver returns
/// Unsafe with it when init violates safety.
#[test]
fn build_trivial_cex_produces_valid_empty_counterexample() {
    // System where init immediately violates safety:
    //   x = 5 => inv(x)
    //   inv(x) /\ x > 0 => false
    // Init state x=5 directly violates x > 0 => false.
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 5) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (> x 0)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let result = solver.solve();

    match result {
        PdrResult::Unsafe(cex) => {
            assert!(
                cex.steps.is_empty(),
                "trivial counterexample should have empty steps, got {} steps",
                cex.steps.len()
            );
            assert!(
                cex.witness.is_none(),
                "trivial counterexample should not include a witness"
            );
        }
        other => {
            panic!("expected Unsafe for init-violates-safety system, got {other:?}");
        }
    }
}

#[test]
fn note_model_verification_failure_resets_counter_after_learning_progress() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (inv x) (= x2 (+ x 1))) (inv x2))))
(assert (forall ((x Int)) (=> (and (inv x) (> x 10)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    solver.verification.consecutive_unlearnable = 4;
    solver.verification.last_unlearnable_progress = solver.verification_progress_signature();
    let pred = solver.problem.predicates()[0].id;
    solver
        .reachability
        .must_summaries
        .add_filter_only(0, pred, ChcExpr::Bool(true));

    solver.note_model_verification_failure("unit test");

    assert_eq!(
        solver.verification.consecutive_unlearnable, 1,
        "learning progress should reset the counter before recording the new failure"
    );
    assert_eq!(solver.verification.total_model_failures, 1);
}

#[test]
fn note_model_verification_failure_keeps_counter_without_learning_progress() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (inv x) (= x2 (+ x 1))) (inv x2))))
(assert (forall ((x Int)) (=> (and (inv x) (> x 10)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    solver.verification.consecutive_unlearnable = 4;
    solver.verification.last_unlearnable_progress = solver.verification_progress_signature();

    solver.note_model_verification_failure("unit test");

    assert_eq!(
        solver.verification.consecutive_unlearnable, 5,
        "without learning progress the consecutive counter should keep growing"
    );
    assert_eq!(solver.verification.total_model_failures, 1);
}

/// Regression test for #3247 / #3121:
/// Startup runs equality discovery before parity, then retries equality after parity.
/// This verifies the retry is necessary and effective for parity-gated equalities.
///
/// Single-predicate system: inv(a, d, e) where a starts odd, d=e=0.
/// Transition: a' = a+2 (preserves parity), d' = ite(a mod 2 = 1, d+1, d), e' = e+1.
/// Without the parity invariant (a mod 2 = 1), the ITE branch is unconstrained
/// so d may lag behind e, making d=e non-inductive.
/// After parity discovery, the ITE always takes the true branch, so d=e is inductive.
#[test]
fn solve_startup_rediscovers_equalities_after_parity_discovery() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int Int Int) Bool)

; Init: a is odd (a = 1), d = e = 0.
(assert
  (forall ((a Int) (d Int) (e Int))
(=>
  (and (= a 1) (= d 0) (= e 0))
  (inv a d e)
)
  )
)

; Parity-guarded update with oddness-preserving a' = a + 2.
; If a is odd, both d and e increment together.
; If parity is unknown, d may stay while e increments, so d=e is not provable.
(assert
  (forall ((a Int) (d Int) (e Int) (a2 Int) (d2 Int) (e2 Int))
(=>
  (and
    (inv a d e)
    (= a2 (+ a 2))
    (= d2 (ite (= (mod a 2) 1) (+ d 1) d))
    (= e2 (+ e 1))
  )
  (inv a2 d2 e2)
)
  )
)

; Safety: d = e.
(assert
  (forall ((a Int) (d Int) (e Int))
(=>
  (and (inv a d e) (not (= d e)))
  false
)
  )
)

(check-sat)
"#;

    let config = PdrConfig {
        use_entry_cegar_discharge: false,
        ..PdrConfig::default()
    };

    // Simulate the pre-fix startup order: equality discovery, parity discovery,
    // and no post-parity equality retry.
    let mut solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), config);
    let inv = solver.problem.lookup_predicate("inv").unwrap();
    let vars = solver.canonical_vars(inv).unwrap().to_vec();
    assert_eq!(vars.len(), 3);
    let d_eq_e = ChcExpr::eq(ChcExpr::var(vars[1].clone()), ChcExpr::var(vars[2].clone()));
    let a_mod_2_eq_1 = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(vars[0].clone()), ChcExpr::int(2)),
        ChcExpr::int(1),
    );

    // Phase 1: Equality discovery before parity — d=e should NOT be learned.
    solver.discover_equality_invariants();
    assert!(
        !solver.frames[1].contains_lemma(inv, &d_eq_e),
        "without parity prerequisites, startup equality pass must not learn d=e"
    );

    // Phase 2: Parity discovery — a mod 2 = 1 should be learned.
    solver.discover_parity_invariants(None);
    assert!(
        solver.frames[1].contains_lemma(inv, &a_mod_2_eq_1),
        "startup parity discovery should add prerequisite a mod 2 = 1"
    );
    assert!(
        !solver.frames[1].contains_lemma(inv, &d_eq_e),
        "parity alone should not add d=e without equality retry"
    );

    // Phase 3: Equality re-discovery after parity (commit 841012204 behavior).
    solver.discover_equality_invariants();
    assert!(
        solver.frames[1].contains_lemma(inv, &d_eq_e),
        "post-parity equality retry should learn d=e"
    );
}

/// FIX 1 (deadline threading): when the embedding lane installs a TIGHT absolute
/// per-obligation deadline once (via `ScopedSolveDeadline`), `solve_init` must
/// clamp the PDR `solve_deadline` to it — NOT fall back to the 300s
/// `DEFAULT_SAFETY_DEADLINE` just because `config.solve_timeout` is `None`, and
/// NOT re-grant a fresh full budget on each (re-)entry. Sound: the clamp only
/// ever SHORTENS the deadline, so `is_cancelled` (which polls `solve_deadline`)
/// fires at the embedder's budget instead of grinding to the watchdog SIGKILL.
#[test]
fn solve_init_clamps_to_ambient_solve_deadline() {
    use crate::smt::ScopedSolveDeadline;
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (inv x) (= x2 (+ x 1))) (inv x2))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;
    let mut solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    assert!(
        solver.config.solve_timeout.is_none(),
        "default config carries NO solve_timeout, so without the clamp solve_init would \
         install the 300s DEFAULT_SAFETY_DEADLINE"
    );

    // Embedder installs a tight ABSOLUTE per-obligation deadline (100ms) once.
    let tight = ay_core::time::Instant::now() + std::time::Duration::from_millis(100);
    let _guard = ScopedSolveDeadline::new(Some(tight));

    let _ = solver.solve_init();

    let installed = solver
        .solve_deadline
        .expect("solve_init installs a deadline");
    assert!(
        installed <= tight,
        "solve_init must clamp solve_deadline to the tighter ambient deadline"
    );
    assert!(
        installed <= ay_core::time::Instant::now() + std::time::Duration::from_secs(1),
        "solve_init must not fall back to the 300s DEFAULT_SAFETY_DEADLINE when a tighter \
         ambient deadline is installed"
    );
    // The clamped deadline is pushed down to the SMT context (not clobbered by
    // the looser default), so every inner check_sat honors the SAME ceiling.
    assert_eq!(
        solver.smt.current_global_deadline(),
        Some(installed),
        "the clamped deadline must be the one installed on the SmtContext"
    );
}

/// FIX 1 (no per-round re-grant): a caller that installs NO ambient deadline and
/// NO `solve_timeout` still gets the 300s safety default (proof-seeking
/// obligations must keep running), so the clamp is purely additive.
#[test]
fn solve_init_keeps_default_when_no_ambient_deadline() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (inv x) (= x2 (+ x 1))) (inv x2))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;
    let mut solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    let before = ay_core::time::Instant::now();
    let _ = solver.solve_init();
    let installed = solver
        .solve_deadline
        .expect("solve_init installs a deadline");
    assert!(
        installed >= before + std::time::Duration::from_mins(1),
        "with no ambient deadline and no solve_timeout, the generous safety default must remain"
    );
}

// ---------------------------------------------------------------------------
// give_up_on_stuck (wishlist item 5a)
// ---------------------------------------------------------------------------

/// A diverging counter whose error state is only reachable at depth 10^6:
/// PDR can neither prove Safe (the problem is unsafe) nor find the deep
/// counterexample quickly, so the main loop keeps iterating — a
/// deterministic stand-in for the model-checker-consumer guard-timeout class.
fn diverging_counter_problem() -> crate::ChcProblem {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (inv x) (= x2 (+ x 1))) (inv x2))))
(assert (forall ((x Int)) (=> (and (inv x) (= x 1000000)) false)))
(check-sat)
"#;
    ChcParser::parse(smt2).unwrap()
}

#[test]
fn give_up_on_stuck_returns_unknown_early_at_stuck() {
    // Force ConvergenceHealth::Stuck from iteration 0, BEFORE any frame
    // growth — the give-up additionally requires zero frame growth
    // (frames.len() <= 2), because lemma-count windows legitimately stall
    // mid-flight on hard-but-solvable problems (genuine stagnation needs
    // many wall-clock windows — too slow/load-sensitive for a test).
    super::main_loop::FORCE_CONVERGENCE_STUCK_AFTER_ITERATION.with(|c| c.set(Some(0)));
    let config = PdrConfig {
        max_frames: 10_000,
        max_iterations: 60,
        give_up_on_stuck: true,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(diverging_counter_problem(), config);
    let result = solver.solve();
    super::main_loop::FORCE_CONVERGENCE_STUCK_AFTER_ITERATION.with(|c| c.set(None));

    assert!(
        matches!(result, PdrResult::Unknown),
        "give_up_on_stuck must degrade to Unknown, never flip a verdict: {result:?}"
    );
    assert!(
        solver.terminated_by_stagnation,
        "the early give-up must record stagnation evidence"
    );
    assert!(
        solver.iterations <= 2,
        "give_up_on_stuck must return at the first zero-frame-growth Stuck \
         signal, got {} iterations",
        solver.iterations
    );
}

#[test]
fn give_up_on_stuck_continues_when_frames_grew() {
    // A Stuck signal AFTER frame growth must NOT give up: lemma windows
    // stall legitimately during heavy generalization on solvable problems
    // (pdr_s_multipl_12_safe regressed pass->timeout when a mid-flight
    // give-up abandoned the solving stage). Force Stuck from iteration 8 —
    // by then the diverging counter has advanced past the initial frame —
    // and require the loop to keep running to its configured budget.
    super::main_loop::FORCE_CONVERGENCE_STUCK_AFTER_ITERATION.with(|c| c.set(Some(8)));
    let config = PdrConfig {
        max_frames: 10_000,
        max_iterations: 25,
        give_up_on_stuck: true,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(diverging_counter_problem(), config);
    let result = solver.solve();
    super::main_loop::FORCE_CONVERGENCE_STUCK_AFTER_ITERATION.with(|c| c.set(None));

    assert!(
        matches!(result, PdrResult::Unknown),
        "unexpected: {result:?}"
    );
    assert!(
        solver.frames.len() > 2,
        "test premise: frames must have grown past the initial frame by \
         iteration 8, got {}",
        solver.frames.len()
    );
    assert!(
        solver.iterations >= 24,
        "a Stuck signal after frame growth must log-and-continue to the \
         configured budget, got {} iterations",
        solver.iterations
    );
}

#[test]
fn default_config_logs_and_continues_past_stuck() {
    // DEFAULT BEHAVIOR MUST NOT CHANGE: without give_up_on_stuck the Stuck
    // arm records evidence but keeps running to its configured budget
    // (max_iterations here), per the documented load-sensitivity regression.
    super::main_loop::FORCE_CONVERGENCE_STUCK_AFTER_ITERATION.with(|c| c.set(Some(5)));
    let config = PdrConfig {
        max_frames: 10_000,
        max_iterations: 25,
        ..PdrConfig::default()
    };
    assert!(
        !config.give_up_on_stuck,
        "give_up_on_stuck must default OFF"
    );
    let mut solver = PdrSolver::new(diverging_counter_problem(), config);
    let result = solver.solve();
    super::main_loop::FORCE_CONVERGENCE_STUCK_AFTER_ITERATION.with(|c| c.set(None));

    assert!(
        matches!(result, PdrResult::Unknown),
        "unexpected: {result:?}"
    );
    assert!(
        solver.terminated_by_stagnation,
        "the default path still records the stagnation evidence"
    );
    assert!(
        solver.iterations > 6,
        "default config must log-and-continue past the Stuck signal at \
         iteration 5, but stopped at {}",
        solver.iterations
    );
}
