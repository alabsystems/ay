// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{PdrSolver, StartupTimeoutCap};
use crate::{CancellationToken, ChcExpr, ChcParser, PdrConfig};

use crate::transform::ClauseInliner;

#[allow(dead_code)]
fn expected_non_lia_fact_bundle(must_summary: &ChcExpr) -> ChcExpr {
    let mut conjuncts = Vec::new();
    for conjunct in must_summary.collect_conjuncts() {
        if matches!(conjunct, ChcExpr::Bool(true)) {
            continue;
        }
        if conjunct.contains_array_ops() && !conjunct.is_bool_sorted_top_level() {
            continue;
        }
        if !conjuncts.contains(&conjunct) {
            conjuncts.push(conjunct);
        }
    }
    ChcExpr::not(ChcExpr::or_all(conjuncts.into_iter().map(ChcExpr::not)))
}

fn timeout_cap_test_solver(config: PdrConfig) -> PdrSolver {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (inv x) (= x2 x)) (inv x2))))
(assert (forall ((x Int)) (=> (and (inv x) (= x 1)) false)))
(check-sat)
"#;

    PdrSolver::new(ChcParser::parse(smt2).unwrap(), config)
}

#[cfg(feature = "optional-chc25-repo-corpus-tests")]
fn optional_chc25_repo_fixture(relative: &str) -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/chc-comp/chc-comp25-repo")
        .join(relative);
    std::fs::read_to_string(&path).unwrap_or_else(|error| {
        panic!(
            "optional CHC-COMP 2025 repository fixture {} must be provisioned: {error}",
            path.display()
        )
    })
}

#[test]
fn startup_smt_timeout_cap_uses_direct_solve_timeout_before_solve_init() {
    let config = PdrConfig {
        solve_timeout: Some(std::time::Duration::from_millis(500)),
        ..Default::default()
    };
    let solver = timeout_cap_test_solver(config);

    assert_eq!(
        solver.startup_smt_timeout_cap(std::time::Duration::from_secs(10)),
        StartupTimeoutCap::Active(std::time::Duration::from_millis(500)),
        "startup should not install a fixed 10s SMT cap for a 500ms PDR probe"
    );
}

#[test]
fn startup_smt_timeout_cap_uses_remaining_solve_deadline() {
    let config = PdrConfig {
        solve_timeout: Some(std::time::Duration::from_secs(10)),
        ..Default::default()
    };
    let mut solver = timeout_cap_test_solver(config);
    solver.solve_deadline =
        Some(ay_core::time::Instant::now() + std::time::Duration::from_millis(50));

    let StartupTimeoutCap::Active(timeout) =
        solver.startup_smt_timeout_cap(std::time::Duration::from_secs(10))
    else {
        panic!("startup timeout cap should be active while deadline has remaining budget");
    };
    assert!(
        timeout <= std::time::Duration::from_millis(50)
            && timeout < std::time::Duration::from_secs(10),
        "startup SMT timeout should be clipped to remaining solve deadline, got {timeout:?}"
    );
}

#[test]
fn startup_smt_timeout_cap_fails_closed_when_deadline_exhausted() {
    let config = PdrConfig {
        solve_timeout: Some(std::time::Duration::from_millis(500)),
        ..Default::default()
    };
    let mut solver = timeout_cap_test_solver(config);
    solver.solve_deadline = Some(
        ay_core::time::Instant::now()
            .checked_sub(std::time::Duration::from_millis(1))
            .unwrap(),
    );

    assert_eq!(
        solver.startup_smt_timeout_cap(std::time::Duration::from_secs(10)),
        StartupTimeoutCap::Exhausted,
        "startup should fail closed instead of starting an SMT query after deadline expiry"
    );
}

#[test]
fn post_cancel_startup_salvage_stays_disabled_for_short_probes() {
    let config = PdrConfig {
        solve_timeout: Some(std::time::Duration::from_millis(500)),
        ..Default::default()
    };
    let solver = timeout_cap_test_solver(config);

    assert_eq!(
        solver.post_cancel_startup_salvage_budget(),
        None,
        "500ms PDR probes must not receive a fresh post-cancel startup extension"
    );
}

#[test]
fn post_cancel_startup_salvage_remains_available_for_full_pdr_lanes() {
    let config = PdrConfig {
        solve_timeout: Some(std::time::Duration::from_secs(8)),
        ..Default::default()
    };
    let solver = timeout_cap_test_solver(config);

    assert_eq!(
        solver.post_cancel_startup_salvage_budget(),
        Some(std::time::Duration::from_secs(8)),
        "full PDR lanes should keep the bounded startup salvage used by solved Safe cases"
    );
}

#[test]
fn post_cancel_startup_salvage_clips_to_remaining_solve_deadline() {
    let config = PdrConfig {
        solve_timeout: Some(std::time::Duration::from_secs(8)),
        ..Default::default()
    };
    let mut solver = timeout_cap_test_solver(config);
    solver.solve_deadline = Some(ay_core::time::Instant::now() + std::time::Duration::from_secs(1));

    let budget = solver
        .post_cancel_startup_salvage_budget()
        .expect("remaining solve deadline should allow bounded salvage");
    assert!(
        budget <= std::time::Duration::from_secs(1) && budget < std::time::Duration::from_secs(8),
        "post-cancel salvage should be clipped to remaining solve_deadline, got {budget:?}"
    );
}

#[test]
fn post_cancel_startup_salvage_fails_closed_when_inner_deadline_expired() {
    let config = PdrConfig {
        solve_timeout: Some(std::time::Duration::from_secs(8)),
        ..Default::default()
    };
    let mut solver = timeout_cap_test_solver(config);
    solver.solve_deadline = Some(
        ay_core::time::Instant::now()
            .checked_sub(std::time::Duration::from_millis(1))
            .unwrap(),
    );

    assert_eq!(
        solver.post_cancel_startup_salvage_budget(),
        None,
        "post-cancel salvage must not reopen budget after solve_deadline expiry"
    );
}

#[test]
fn post_cancel_startup_salvage_denies_cancelled_parent_token() {
    let token = CancellationToken::new();
    token.cancel();

    let config = PdrConfig {
        solve_timeout: Some(std::time::Duration::from_secs(8)),
        cancellation_token: Some(token),
        ..Default::default()
    };
    let solver = timeout_cap_test_solver(config);

    assert_eq!(
        solver.post_cancel_startup_salvage_budget(),
        None,
        "cancelled caller token must deny post-cancel startup salvage"
    );
}

#[test]
fn startup_direct_safety_is_skipped_for_single_predicate_bv() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x #x00) (inv x))))
(assert (forall ((x (_ BitVec 8)) (x2 (_ BitVec 8)))
  (=> (and (inv x) (= x2 x)) (inv x2))))
(assert (forall ((x (_ BitVec 8))) (=> (and (inv x) (= x #x01)) false)))
(check-sat)
"#;

    let solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    assert!(
        solver.skip_startup_direct_safety_proof(),
        "single-predicate native-BV problems should bypass startup direct safety"
    );
    assert!(
        !solver.use_bv_native_fast_startup_path(),
        "small native-BV simple loops should still run the full startup discovery pipeline"
    );
}

#[test]
fn startup_direct_safety_still_runs_for_non_bv_problem() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (inv x) (= x2 x)) (inv x2))))
(assert (forall ((x Int)) (=> (and (inv x) (= x 1)) false)))
(check-sat)
"#;

    let solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    assert!(
        !solver.skip_startup_direct_safety_proof(),
        "non-BV problems should keep the startup direct safety shortcut"
    );
}

#[test]
fn startup_direct_safety_still_runs_for_multi_transition_bv_problem() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x #x00) (inv x))))
(assert (forall ((x (_ BitVec 8)) (x2 (_ BitVec 8)))
  (=> (and (inv x) (= x2 (bvadd x #x01))) (inv x2))))
(assert (forall ((x (_ BitVec 8)) (x2 (_ BitVec 8)))
  (=> (and (inv x) (= x2 (bvsub x #x01))) (inv x2))))
(assert (forall ((x (_ BitVec 8))) (=> (and (inv x) (= x #x01)) false)))
(check-sat)
"#;

    let solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    assert!(
        !solver.skip_startup_direct_safety_proof(),
        "multi-transition BV problems should keep the startup direct safety shortcut"
    );
}

#[test]
fn startup_fast_path_is_used_for_large_single_predicate_bv_problem() {
    const TEMP_COUNT: usize = 192;

    let binder_vars = (1..=TEMP_COUNT)
        .map(|i| format!("(t{i} (_ BitVec 8))"))
        .collect::<Vec<_>>()
        .join(" ");

    let mut transition = String::from("(and (inv x)");
    for i in 0..TEMP_COUNT {
        let src = if i == 0 {
            "x".to_string()
        } else {
            format!("t{i}")
        };
        let dst = format!("t{}", i + 1);
        transition.push_str(&format!(" (= {dst} (bvadd {src} #x01))"));
    }
    transition.push_str(&format!(" (= x2 t{TEMP_COUNT}))"));

    let smt2 = format!(
        r#"
(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x #x00) (inv x))))
(assert (forall ((x (_ BitVec 8))
                 (x2 (_ BitVec 8))
                 {binder_vars})
          (=> {transition} (inv x2))))
(assert (forall ((x (_ BitVec 8))) (=> (and (inv x) (= x #x01)) false)))
(check-sat)
"#
    );

    let solver = PdrSolver::new(ChcParser::parse(&smt2).unwrap(), PdrConfig::default());
    assert!(
        solver.skip_startup_direct_safety_proof(),
        "large native-BV simple loops should still bypass startup direct safety"
    );
    assert!(
        solver.use_bv_native_fast_startup_path(),
        "large native-BV simple loops should keep the lightweight startup path"
    );
}

#[test]
fn startup_nonfixpoint_applies_transition_affine_hints() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun P (Int Int) Bool)
(declare-fun Q (Int Int) Bool)

(assert (forall ((a Int) (b Int))
  (=> (and (= a 0) (= b 0)) (P a b))))

(assert (forall ((a Int) (b Int) (a2 Int) (b2 Int))
  (=> (and (P a b) (= a2 (+ a 1)) (= b2 (+ b 2))) (P a2 b2))))

(assert (forall ((a Int) (b Int) (u Int) (v Int))
  (=> (and (P a b) (= u (+ a 1)) (= v (+ b 2))) (Q u v))))

(assert (forall ((u Int) (v Int) (u2 Int) (v2 Int))
  (=> (and (Q u v) (= u2 (+ u 1)) (= v2 (+ v 2))) (Q u2 v2))))

(assert (forall ((u Int) (v Int)) (=> (and (Q u v) (< v 0)) false)))

(check-sat)
"#;

    let mut solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    let q = solver.problem.lookup_predicate("Q").unwrap();

    let result = solver.run_nonfixpoint_discovery();
    assert!(
        result.is_none(),
        "nonfixpoint discovery should not terminate solve early in this fixture"
    );

    let q_vars = solver.canonical_vars(q).unwrap().to_vec();
    let expected = solver
        .normalize_affine_equality_for_target(
            q,
            &ChcExpr::eq(
                ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(q_vars[0].clone())),
                ChcExpr::var(q_vars[1].clone()),
            ),
        )
        .expect("normalize propagated affine equality");

    assert!(
        solver.frames[1].contains_lemma(q, &expected),
        "startup should inject propagated affine hint for Q"
    );
}

#[test]
fn startup_parity_retry_recovers_count_by_2_m_nest_after_inlining() {
    let input = include_str!(
        "../../../../../../benchmarks/chc-comp/2025/extra-small-lia/count_by_2_m_nest_000.smt2"
    );

    let problem = ChcParser::parse(input).unwrap();
    let inlined = ClauseInliner::new().inline(&problem);
    assert_eq!(
        inlined.predicates().len(),
        1,
        "multi-def inlining should collapse count_by_2_m_nest to one predicate"
    );

    let mut solver = PdrSolver::new(inlined, PdrConfig::default());
    assert!(
        solver.run_fixpoint_discovery().is_none(),
        "startup fixpoint should not terminate early for this benchmark"
    );
    assert!(
        solver.run_nonfixpoint_discovery().is_none(),
        "nonfixpoint startup should not terminate early for this benchmark"
    );

    let pred = solver.problem.predicates()[0].id;
    let vars = solver.canonical_vars(pred).unwrap().to_vec();

    let outer_mod_16 = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(vars[0].clone()), ChcExpr::Int(16)),
        ChcExpr::Int(0),
    );
    let inner_exit_bound = ChcExpr::le(ChcExpr::var(vars[1].clone()), ChcExpr::Int(16));

    assert!(
        solver.frames[1].contains_lemma(pred, &inner_exit_bound),
        "parity retry should recover the deferred inner-loop exit bound"
    );
    assert!(
        solver.frames[1].contains_lemma(pred, &outer_mod_16),
        "inner-loop parity + exit bound should strengthen the outer counter to mod 16"
    );
}

#[cfg(feature = "optional-chc25-repo-corpus-tests")]
#[test]
fn startup_nonfixpoint_builds_splitter_resistant_simple_bv_fact_bundle() {
    let input = optional_chc25_repo_fixture("vmt-chc-benchmarks/bv/simple.c_000.smt2");

    let solver = PdrSolver::new(ChcParser::parse(&input).unwrap(), PdrConfig::default());
    let pred = solver.problem.predicates()[0].id;
    let vars = solver.canonical_vars(pred).unwrap().to_vec();
    let must_summary = ChcExpr::and_all([
        ChcExpr::not(ChcExpr::var(vars[0].clone())),
        ChcExpr::not(ChcExpr::var(vars[1].clone())),
        ChcExpr::not(ChcExpr::var(vars[2].clone())),
    ]);
    let expected = expected_non_lia_fact_bundle(&must_summary);

    assert_eq!(
        solver.build_conjunctive_fact_clause_lemma(must_summary.collect_conjuncts()),
        expected,
        "simple.c_000 should encode the startup fact bundle in a splitter-resistant BV form"
    );
    assert_ne!(
        expected,
        ChcExpr::and_all(must_summary.collect_conjuncts()),
        "non-LIA startup fact bundles must avoid a plain top-level And that generic frame insertion can split"
    );
}

// ---------------------------------------------------------------------------
// Wide-var startup cap on Real-sorted transition systems (CHC-COMP LRA-Lin).
//
// `wide_var_startup_budget` excluded `has_real_sorts()` problems from the
// inc-12 total-startup cap even though its own rationale ("wide-var linear
// problems (max arity >= 12, scalar, linear, no mod/div)") never named Real,
// and Reals have no alternative startup route. On the sally / vmt LRA
// transition systems the uncapped discovery passes consumed the whole engine
// window and the IC3 loop never ran (frames=2, obligations=0). These tests pin
// the cap for Real state and check that PDR actually gets past startup.
// ---------------------------------------------------------------------------

/// `om1_with_relays_agreement_000` (sally oral_messages, CHC-COMP 2026
/// LRA-Lin): one predicate over 40 Real + 8 Bool, 3 clauses, expected `sat`.
fn om1_with_relays_agreement_fixture() -> crate::ChcProblem {
    let input = include_str!(
        "../../../../../../benchmarks/chc-comp/2026/lra-lin/om1_with_relays_agreement_000.smt2"
    );
    ChcParser::parse(input).expect("om1_with_relays_agreement_000 must parse")
}

#[test]
fn wide_var_startup_cap_applies_to_real_transition_systems() {
    let config = PdrConfig {
        solve_timeout: Some(std::time::Duration::from_secs(8)),
        ..Default::default()
    };
    let solver = PdrSolver::new(om1_with_relays_agreement_fixture(), config);
    assert!(
        solver.problem.has_real_sorts(),
        "fixture must carry Real state"
    );
    assert!(
        solver.problem.predicates()[0].arg_sorts.len() >= super::WIDE_VAR_STARTUP_ARITY,
        "fixture must be wide-var"
    );

    let budget = solver
        .wide_var_startup_budget()
        .expect("Real-sorted wide-var transition systems must receive the startup cap");
    // 25 % of the remaining window (8 s -> 2 s), never below the 250 ms floor.
    assert!(
        budget >= std::time::Duration::from_millis(250)
            && budget <= std::time::Duration::from_millis(2_050),
        "unexpected startup budget {budget:?}"
    );
}

#[test]
fn wide_var_startup_cap_treats_real_and_int_state_alike() {
    let real = r#"
(set-logic HORN)
(declare-fun inv (Real Real Real Real Real Real Real Real Real Real Real Real Bool) Bool)
(assert (forall ((a Real) (b Real) (c Real) (d Real) (e Real) (f Real) (g Real) (h Real) (i Real) (j Real) (k Real) (l Real) (p Bool))
  (=> (and (= a 0.0) (= b 0.0) (= c 0.0) (= d 0.0) (= e 0.0) (= f 0.0) (= g 0.0) (= h 0.0) (= i 0.0) (= j 0.0) (= k 0.0) (= l 0.0) p)
      (inv a b c d e f g h i j k l p))))
(assert (forall ((a Real) (b Real) (c Real) (d Real) (e Real) (f Real) (g Real) (h Real) (i Real) (j Real) (k Real) (l Real) (p Bool) (a2 Real))
  (=> (and (inv a b c d e f g h i j k l p) (= a2 (+ a 1.0)))
      (inv a2 b c d e f g h i j k l p))))
(assert (forall ((a Real) (b Real) (c Real) (d Real) (e Real) (f Real) (g Real) (h Real) (i Real) (j Real) (k Real) (l Real) (p Bool))
  (=> (and (inv a b c d e f g h i j k l p) (< a 0.0)) false)))
(check-sat)
"#;
    let int = real
        .replace("Real", "Int")
        .replace("0.0", "0")
        .replace("1.0", "1");
    let config = PdrConfig {
        solve_timeout: Some(std::time::Duration::from_secs(4)),
        ..Default::default()
    };
    let real_solver = PdrSolver::new(ChcParser::parse(real).unwrap(), config.clone());
    let int_solver = PdrSolver::new(ChcParser::parse(&int).unwrap(), config);
    let real_budget = real_solver
        .wide_var_startup_budget()
        .expect("13-arity Real transition system must be capped");
    let int_budget = int_solver
        .wide_var_startup_budget()
        .expect("13-arity Int transition system must be capped");
    let delta = real_budget.abs_diff(int_budget);
    assert!(
        delta <= std::time::Duration::from_millis(50),
        "Real and Int state must receive the same startup budget: {real_budget:?} vs {int_budget:?}"
    );
}

#[test]
fn narrow_real_problem_keeps_full_startup_discovery() {
    // Arity below WIDE_VAR_STARTUP_ARITY: the accumulator classes where
    // discovery wins keep the uncapped pipeline, Real or not.
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Real Real) Bool)
(assert (forall ((x Real) (y Real)) (=> (and (= x 0.0) (= y 0.0)) (inv x y))))
(assert (forall ((x Real) (y Real) (x2 Real)) (=> (and (inv x y) (= x2 (+ x 1.0))) (inv x2 y))))
(assert (forall ((x Real) (y Real)) (=> (and (inv x y) (< x 0.0)) false)))
(check-sat)
"#;
    let config = PdrConfig {
        solve_timeout: Some(std::time::Duration::from_secs(4)),
        ..Default::default()
    };
    let solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), config);
    assert!(solver.wide_var_startup_budget().is_none());
}

#[test]
fn real_transition_system_reaches_the_ic3_loop_under_the_startup_cap() {
    // Before the fix this solve spent its whole window in startup discovery:
    // `frames` stayed at 2 (the initial frame pair) and no proof obligation
    // was ever created. With the cap, startup yields after 25 % of the window
    // and the main loop expands frames.
    let config = PdrConfig {
        solve_timeout: Some(std::time::Duration::from_secs(8)),
        ..Default::default()
    };
    let mut solver = PdrSolver::new(om1_with_relays_agreement_fixture(), config);
    let result = solver.solve();
    assert!(
        solver.startup_deadline.is_some(),
        "the wide-var startup cap must be installed for Real state"
    );
    let definitive = matches!(
        result,
        crate::pdr::PdrResult::Safe(_) | crate::pdr::PdrResult::Unsafe(_)
    );
    assert!(
        definitive || solver.frames.len() > 2,
        "PDR must leave startup discovery and expand frames within the window \
         (frames={}, result definitive={definitive})",
        solver.frames.len()
    );
    // The fixture is `sat`. Leaving startup changes which level-0 predecessor
    // queries run on it, so pin that the IC3 loop never claims a counterexample.
    assert!(
        !matches!(result, crate::pdr::PdrResult::Unsafe(_)),
        "om1_with_relays_agreement_000 is sat: PDR must not return Unsafe"
    );
}

#[test]
fn spent_wide_var_startup_cap_ends_discovery_not_the_solve() {
    // Rung 0 made `is_cancelled` poll the thread SMT deadline, and the inc-12
    // wide-var startup cap is installed as one: while its expired scope is
    // live the solve reads as cancelled, which turned "startup budget spent"
    // into a terminal `Unknown` at 25 % of the window (frames=2). Leaving the
    // scope must restore the enclosing deadline; a cancellation that is still
    // there after leaving it stays terminal.
    let config = PdrConfig {
        solve_timeout: Some(std::time::Duration::from_secs(10)),
        ..Default::default()
    };
    let spent = ay_core::time::Instant::now()
        .checked_sub(std::time::Duration::from_millis(1))
        .unwrap();
    {
        let mut solver = timeout_cap_test_solver(config.clone());
        let _solve_scope =
            crate::smt::ScopedSmtDeadline::install(std::time::Duration::from_secs(10));
        solver.startup_deadline = Some(spent);
        let mut startup_scope = Some(crate::smt::ScopedSmtDeadline::install_until(spent));
        assert!(
            solver.is_cancelled(),
            "an expired startup scope reads as a cancellation while it is installed"
        );
        assert!(
            solver.leave_spent_startup_scope(&mut startup_scope),
            "a spent startup cap under a live solve window must not end the solve"
        );
        assert!(startup_scope.is_none(), "the startup scope must be left");
        assert!(
            !solver.is_cancelled(),
            "leaving the startup scope restores the enclosing solve deadline"
        );
    }
    {
        let mut solver = timeout_cap_test_solver(config.clone());
        let _expired_enclosing = crate::smt::ScopedSmtDeadline::install_until(spent);
        solver.startup_deadline = Some(spent);
        let mut startup_scope = Some(crate::smt::ScopedSmtDeadline::install_until(spent));
        assert!(
            !solver.leave_spent_startup_scope(&mut startup_scope),
            "an expired enclosing deadline must still cancel once the startup scope is left"
        );
    }
    {
        let mut solver = timeout_cap_test_solver(config);
        solver.startup_deadline =
            Some(ay_core::time::Instant::now() + std::time::Duration::from_secs(10));
        let mut startup_scope = Some(crate::smt::ScopedSmtDeadline::install(
            std::time::Duration::from_secs(10),
        ));
        assert!(
            !solver.leave_spent_startup_scope(&mut startup_scope),
            "before the cap runs out an `Unknown` is a real cancellation"
        );
        assert!(
            startup_scope.is_some(),
            "a live startup scope must not be left early"
        );
    }
}
