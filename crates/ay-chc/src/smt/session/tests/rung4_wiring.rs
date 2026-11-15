// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rung-4 wiring locks (#horn-smt-session §8 Rung 4, Bool+LRA).
//!
//! * The bypass entry points (`IncrementalQueryContext::check_sat_incremental`,
//!   `PersistentExecutorSmtContext::check_query`,
//!   `engine_utils::search_check_sat_with_timeout`) reach the session exactly
//!   under the router gate: a `Search`-lane holder, no live
//!   `ScopedVerificationMode`, mode ≥ 1 — and answer what the legacy path
//!   answers.
//! * L1 for the newly wired engines: with every routed answer stubbed to
//!   `Unsat`, IMC, DAR and PDKind on an UNSAFE problem never end in `Safe` (their
//!   Craig / inductive validations stay pinned).

use std::time::Duration;

use ay_core::kani_compat::DetHashMap as FxHashMap;

use crate::engine_result::ChcEngineResult;
use crate::smt::incremental::{IncrementalCheckResult, IncrementalQueryContext};
use crate::smt::lane::{self, stub::ScopedWrongUnsat, ScopedSessionMode, ScopedVerificationMode};
use crate::smt::{PersistentExecutorSmtContext, SmtContext, SmtResult};
use crate::{ChcExpr, ChcParser, ChcProblem, ChcSort, ChcVar};

fn x() -> ChcExpr {
    ChcExpr::var(ChcVar::new("x", ChcSort::Real))
}

fn real(n: i64) -> ChcExpr {
    ChcExpr::Real(n, 1)
}

/// `0 <= x <= 10`.
fn background() -> ChcExpr {
    ChcExpr::and(ChcExpr::ge(x(), real(0)), ChcExpr::le(x(), real(10)))
}

fn inc_verdict(r: &IncrementalCheckResult) -> &'static str {
    match r {
        IncrementalCheckResult::Sat(_) => "sat",
        IncrementalCheckResult::Unsat => "unsat",
        IncrementalCheckResult::Unknown => "unknown",
    }
}

fn smt_verdict(r: &SmtResult) -> &'static str {
    match r {
        SmtResult::Sat(_) => "sat",
        SmtResult::Unknown => "unknown",
        _ => "unsat",
    }
}

fn run_incremental(smt: &mut SmtContext, assumption: &ChcExpr) -> &'static str {
    let mut ctx = IncrementalQueryContext::new();
    ctx.assert_background(&background(), smt);
    inc_verdict(&ctx.check_sat_incremental(
        std::slice::from_ref(assumption),
        smt,
        Some(Duration::from_secs(5)),
    ))
}

#[test]
fn incremental_query_routes_on_a_search_context_only() {
    let _mode = ScopedSessionMode::set(1);
    let sat_q = ChcExpr::ge(x(), real(5));
    let unsat_q = ChcExpr::gt(x(), real(20));

    let mut search = SmtContext::new_search();
    assert_eq!(run_incremental(&mut search, &sat_q), "sat");
    assert!(
        search.has_session(),
        "a Search-lane caller reaches the session"
    );
    assert_eq!(run_incremental(&mut search, &unsat_q), "unsat");
    assert_eq!(search.session_stats().map(|s| s.queries), Some(2));

    let mut verification = SmtContext::new();
    assert_eq!(run_incremental(&mut verification, &sat_q), "sat");
    assert!(
        !verification.has_session(),
        "the Verification lane never routes"
    );

    let mut pinned = SmtContext::new_search();
    {
        let _pin = ScopedVerificationMode::install();
        assert_eq!(run_incremental(&mut pinned, &unsat_q), "unsat");
    }
    assert!(
        !pinned.has_session(),
        "a live verification pin closes the gate"
    );
}

#[test]
fn incremental_query_answers_match_with_the_session_off() {
    for q in [
        ChcExpr::ge(x(), real(5)),
        ChcExpr::gt(x(), real(20)),
        ChcExpr::and(ChcExpr::gt(x(), real(3)), ChcExpr::lt(x(), real(4))),
    ] {
        let off = {
            let _mode = ScopedSessionMode::set(0);
            run_incremental(&mut SmtContext::new_search(), &q)
        };
        let on = {
            let _mode = ScopedSessionMode::set(1);
            run_incremental(&mut SmtContext::new_search(), &q)
        };
        assert_eq!(off, on, "session on/off disagree on {q:?}");
    }
}

fn run_persistent(ctx: &mut PersistentExecutorSmtContext, delta: &ChcExpr) -> &'static str {
    assert!(ctx.ensure_background(&background(), Duration::from_secs(5)));
    smt_verdict(&ctx.check_query(delta, &FxHashMap::default(), Duration::from_secs(5)))
}

#[test]
fn persistent_executor_routes_only_when_built_for_search() {
    let _mode = ScopedSessionMode::set(1);
    let sat_q = ChcExpr::le(x(), real(1));
    let unsat_q = ChcExpr::lt(x(), real(-1));

    let mut search = PersistentExecutorSmtContext::new_search();
    assert_eq!(run_persistent(&mut search, &sat_q), "sat");
    assert!(search.has_session(), "new_search() opts into the session");
    assert_eq!(run_persistent(&mut search, &unsat_q), "unsat");

    let mut plain = PersistentExecutorSmtContext::new();
    assert_eq!(run_persistent(&mut plain, &sat_q), "sat");
    assert_eq!(run_persistent(&mut plain, &unsat_q), "unsat");
    assert!(
        !plain.has_session(),
        "the default context stays on the executor"
    );

    let mut pinned = PersistentExecutorSmtContext::new_search();
    {
        let _pin = ScopedVerificationMode::install();
        assert_eq!(run_persistent(&mut pinned, &unsat_q), "unsat");
    }
    assert!(
        !pinned.has_session(),
        "a live verification pin closes the gate"
    );
}

#[test]
fn persistent_executor_int_background_never_reaches_the_session() {
    let _mode = ScopedSessionMode::set(1);
    let i = ChcExpr::var(ChcVar::new("i", ChcSort::Int));
    let mut ctx = PersistentExecutorSmtContext::new_search();
    assert!(ctx.ensure_background(
        &ChcExpr::ge(i.clone(), ChcExpr::int(0)),
        Duration::from_secs(5)
    ));
    let r = ctx.check_query(
        &ChcExpr::lt(i, ChcExpr::int(0)),
        &FxHashMap::default(),
        Duration::from_secs(5),
    );
    assert_eq!(smt_verdict(&r), "unsat");
    assert!(
        !ctx.has_session(),
        "an ineligible (Int) background is filtered before the session"
    );
}

#[test]
fn search_helper_uses_a_persistent_session_only_with_the_session_on() {
    let q = ChcExpr::and(background(), ChcExpr::ge(x(), real(5)));
    let off = std::thread::spawn({
        let q = q.clone();
        move || {
            let _mode = ScopedSessionMode::set(0);
            let r = crate::engine_utils::search_check_sat_with_timeout(&q, Duration::from_secs(5));
            (
                smt_verdict(&r),
                crate::engine_utils::thread_search_smt_has_session(),
            )
        }
    })
    .join()
    .expect("thread");
    assert_eq!(
        off,
        ("sat", false),
        "mode 0: a fresh context per call, no session"
    );

    let on = std::thread::spawn({
        let q = q.clone();
        move || {
            let _mode = ScopedSessionMode::set(1);
            let first =
                crate::engine_utils::search_check_sat_with_timeout(&q, Duration::from_secs(5));
            let second = crate::engine_utils::search_check_sat_with_timeout(
                &ChcExpr::and(background(), ChcExpr::gt(x(), real(10))),
                Duration::from_secs(5),
            );
            (
                smt_verdict(&first),
                smt_verdict(&second),
                crate::engine_utils::thread_search_smt_has_session(),
            )
        }
    })
    .join()
    .expect("thread");
    assert_eq!(
        on,
        ("sat", "unsat", true),
        "mode 1: one warm session per thread"
    );

    let pinned = std::thread::spawn(move || {
        let _mode = ScopedSessionMode::set(1);
        let _pin = ScopedVerificationMode::install();
        let r = crate::engine_utils::search_check_sat_with_timeout(&q, Duration::from_secs(5));
        (
            smt_verdict(&r),
            crate::engine_utils::thread_search_smt_has_session(),
        )
    })
    .join()
    .expect("thread");
    assert_eq!(
        pinned,
        ("sat", false),
        "a live verification pin closes the gate"
    );
}

// ---------------------------------------------------------------------------
// L1 for the Rung-4 engines
// ---------------------------------------------------------------------------

/// x from 0, +1 per step; the error `x >= 3` is reachable in three steps.
/// Int, so every engine applies (the stub answers every routed query,
/// whatever its theory).
const UNSAFE_LIA: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (= y (+ x 1))) (P y))))
(assert (forall ((x Int)) (=> (and (P x) (>= x 3)) false)))
";

fn problem() -> ChcProblem {
    ChcParser::parse(UNSAFE_LIA).expect("parse")
}

fn under_stub(name: &str, run: impl FnOnce() -> ChcEngineResult) {
    let _mode = ScopedSessionMode::set(1);
    let before = lane::stub::hits();
    let result = {
        let _stub = ScopedWrongUnsat::install();
        run()
    };
    let hits = lane::stub::hits() - before;
    let verdict = match &result {
        ChcEngineResult::Safe(_) => "safe",
        ChcEngineResult::Unsafe(_) => "unsafe",
        _ => "unknown",
    };
    eprintln!("[L1 {name}] verdict={verdict} stubbed_answers={hits}");
    assert!(
        hits > 0,
        "{name}: the stub must have answered search queries"
    );
    assert_ne!(
        verdict, "safe",
        "{name}: a stub UNSAT on the search lane produced a wrong Safe"
    );
}

#[test]
fn l1_imc_with_stub_wrong_unsat_never_ends_in_safe() {
    under_stub("imc", || {
        let config = crate::imc::ImcConfig {
            max_k: 6,
            query_timeout: Duration::from_secs(2),
            total_timeout: Duration::from_secs(20),
            ..crate::imc::ImcConfig::default()
        };
        crate::imc::ImcSolver::new(problem(), config).solve()
    });
}

#[test]
fn l1_dar_with_stub_wrong_unsat_never_ends_in_safe() {
    under_stub("dar", || {
        let config = crate::dar::DarConfig {
            max_n: 6,
            query_timeout: Duration::from_secs(2),
            total_timeout: Duration::from_secs(20),
            ..crate::dar::DarConfig::default()
        };
        crate::dar::DarSolver::new(problem(), config).solve()
    });
}

#[test]
fn l1_pdkind_with_stub_wrong_unsat_never_ends_in_safe() {
    under_stub("pdkind", || {
        let config = crate::PdkindConfig {
            max_iterations: 20,
            max_n: 6,
            max_reachability_depth: 6,
            max_reachability_iterations: 50,
            per_obligation_timeout_secs: 2,
            ..crate::PdkindConfig::default()
        };
        crate::PdkindSolver::new(problem(), config).solve()
    });
}

/// CEGAR's abstract-post context is a session opt-in (Verification lane,
/// `with_session_opt_in`): with every routed answer stubbed to `Unsat`, the
/// engine may claim `Safe` (no abstract edge is feasible), but the portfolio's
/// per-rule validation on a Verification-lane validator must reject it.
#[test]
fn l1_cegar_with_stub_wrong_unsat_never_ends_in_safe_after_validation() {
    let _mode = ScopedSessionMode::set(1);
    let prob = problem();
    let before = lane::stub::hits();
    let result = {
        let _stub = ScopedWrongUnsat::install();
        crate::cegar::CegarEngine::new(prob.clone(), crate::cegar::CegarConfig::default()).solve()
    };
    let hits = lane::stub::hits() - before;
    let final_verdict = match &result {
        crate::cegar::CegarResult::Safe(model) => {
            let mut verifier = crate::PdrSolver::new(
                prob,
                crate::PdrConfig {
                    strict_proofs: true,
                    solve_timeout: Some(Duration::from_secs(20)),
                    ..crate::PdrConfig::default()
                },
            );
            if verifier.verify_model_per_rule(model, Duration::from_secs(5)) {
                "safe"
            } else {
                "unknown"
            }
        }
        crate::cegar::CegarResult::Unsafe(_) => "unsafe",
        _ => "unknown",
    };
    eprintln!("[L1 cegar] final={final_verdict} stubbed_answers={hits}");
    assert!(
        hits > 0,
        "cegar: the stub must have answered abstract-post queries"
    );
    assert_ne!(
        final_verdict, "safe",
        "cegar: a wrong Safe survived validation"
    );
}

#[test]
fn session_opt_in_routes_on_the_verification_lane_and_keeps_the_lane() {
    let _mode = ScopedSessionMode::set(1);
    let q = ChcExpr::and(background(), ChcExpr::ge(x(), real(5)));
    let mut opted = SmtContext::new().with_session_opt_in();
    assert_eq!(
        opted.lane(),
        crate::smt::SmtLane::Verification,
        "the legacy schedule is kept"
    );
    assert_eq!(
        smt_verdict(&opted.check_sat_with_timeout(&q, Duration::from_secs(5))),
        "sat"
    );
    assert!(opted.has_session(), "an opt-in context reaches the session");
    let mut plain = SmtContext::new();
    assert_eq!(
        smt_verdict(&plain.check_sat_with_timeout(&q, Duration::from_secs(5))),
        "sat"
    );
    assert!(!plain.has_session());
    let mut pinned = SmtContext::new().with_session_opt_in();
    {
        let _pin = ScopedVerificationMode::install();
        let _ = pinned.check_sat_with_timeout(&q, Duration::from_secs(5));
    }
    assert!(
        !pinned.has_session(),
        "a live verification pin closes the gate"
    );
}

/// PDR's IUC / PDKind's explanation arm: the reported core is over the
/// ASSUMPTIONS, whole, and covers every assumption the refutation needs.
#[test]
fn assumption_conjunct_search_arm_reports_a_sufficient_assumption_core() {
    let _mode = ScopedSessionMode::set(1);
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Real));
    let bg = vec![ChcExpr::le(x(), real(10))];
    let a_needed = ChcExpr::ge(x(), real(12));
    let a_extra = ChcExpr::ge(y.clone(), real(0));
    let a_pair = ChcExpr::and(ChcExpr::le(y.clone(), real(4)), ChcExpr::ge(x(), real(0)));
    let assumptions = vec![a_extra.clone(), a_needed.clone(), a_pair.clone()];
    let mut smt = SmtContext::new_search();
    let r = smt.check_sat_with_assumption_conjuncts_search(&bg, &assumptions);
    assert!(smt.has_session(), "the search arm reached the session");
    let SmtResult::UnsatWithCore(core) = r else {
        panic!("expected UnsatWithCore, got {r:?}");
    };
    assert!(
        core.conjuncts.contains(&a_needed),
        "the needed assumption is in the core: {core:?}"
    );
    for c in &core.conjuncts {
        assert!(
            assumptions.contains(c),
            "core names only (whole) assumptions: {c:?}"
        );
    }
    // The reported core is sufficient: background ∧ core is UNSAT for legacy.
    let mut legacy = SmtContext::new();
    let check = ChcExpr::and_all(bg.iter().cloned().chain(core.conjuncts.iter().cloned()));
    assert_eq!(
        smt_verdict(&legacy.check_sat_with_timeout(&check, Duration::from_secs(5))),
        "unsat"
    );

    // Sat stays Sat with a model; the gate closed runs the legacy method.
    let sat =
        smt.check_sat_with_assumption_conjuncts_search(&bg, &[a_extra.clone(), a_pair.clone()]);
    assert!(matches!(sat, SmtResult::Sat(_)), "{sat:?}");
    let mut verification = SmtContext::new();
    let _ = verification.check_sat_with_assumption_conjuncts_search(&bg, &assumptions);
    assert!(!verification.has_session());
}
