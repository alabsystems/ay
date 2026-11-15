// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Design §7.1 regression locks L1–L3 and the INV-S1/INV-S2 gate locks
//! (#horn-smt-session Rung 1; owner WP-4 / D).
//!
//! * L1 (audit pin #4): a `Search`-lane context whose every session answer is
//!   stubbed to `Unsat` (`lane::stub::ScopedWrongUnsat`) must not change the
//!   FINAL verdict of a small safe and a small unsafe problem through the
//!   proof-grade entry (`engines::solve_pdr_proof` = PDR search +
//!   `validate_pdr_proof_result`, the CLI's path): `unknown` or the right
//!   answer, never the wrong one. The unsafe loop is decided before the
//!   search by the original-clause reachability prepass, so its lock also
//!   runs with that prepass closed (`disable_cex_replay`) to keep the stub
//!   on the deciding path.
//! * L2: `constructions_in_verification == 0` after a real session-backed
//!   solve (the process-wide tripwire; checked directly against the counter
//!   below — a CLI run of the `ay` binary re-checks it live under
//!   `--chc-session 2 --chc-session-strict full`), and the gate semantics
//!   that make it unreachable: no session on the `Verification` lane, none
//!   under `ScopedVerificationMode`, one on a plain `Search` context.
//! * L3 (k-induction): with the stub answering every Search-lane `check_sat`
//!   `Unsat`, a `KindSolver` run on an UNSAFE transition system must not end
//!   in `Safe` once its result passes the portfolio's validation
//!   (`verify_model_per_rule` on a `Verification`-lane `PdrSolver`);
//!   documents that `kind/solve.rs`'s fresh base-case retry is an Unknown
//!   retry, not a false-UNSAT check (critique B-lifetime M9).

use std::time::Duration;

use crate::smt::lane::{self, stub::ScopedWrongUnsat, ScopedSessionMode, ScopedVerificationMode};
use crate::smt::session::harness::{gen_conjunct, Rng, Vocab};
use crate::smt::{SmtContext, SmtLane};
use crate::{
    engines, ChcParser, ChcProblem, KindConfig, KindResult, KindSolver, PdrConfig, PdrSolver,
    VerifiedChcResult,
};

/// x starts at 0, increments by 1; the error `x < 0` is unreachable.
const SAFE_LRA: &str = "(set-logic HORN)
(declare-fun P (Real) Bool)
(assert (forall ((x Real)) (=> (= x 0.0) (P x))))
(assert (forall ((x Real) (y Real)) (=> (and (P x) (= y (+ x 1.0))) (P y))))
(assert (forall ((x Real)) (=> (and (P x) (< x 0.0)) false)))
";

/// Same loop; the error `x >= 3` is reachable in three steps.
const UNSAFE_LRA: &str = "(set-logic HORN)
(declare-fun P (Real) Bool)
(assert (forall ((x Real)) (=> (= x 0.0) (P x))))
(assert (forall ((x Real) (y Real)) (=> (and (P x) (= y (+ x 1.0))) (P y))))
(assert (forall ((x Real)) (=> (and (P x) (>= x 3.0)) false)))
";

/// Int twin of `UNSAFE_LRA` (k-induction skips Real problems outright,
/// `kind/solve.rs`): x from 0, +1 per step, error at `x >= 3`.
const UNSAFE_LIA: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (= y (+ x 1))) (P y))))
(assert (forall ((x Int)) (=> (and (P x) (>= x 3)) false)))
";

fn problem(text: &str) -> ChcProblem {
    ChcParser::parse(text).expect("parse")
}

fn pdr_config() -> PdrConfig {
    PdrConfig {
        solve_timeout: Some(Duration::from_secs(20)),
        ..PdrConfig::default()
    }
}

fn verdict_name(r: &VerifiedChcResult) -> &'static str {
    match r {
        VerifiedChcResult::Safe(_) => "safe",
        VerifiedChcResult::Unsafe(_) => "unsafe",
        _ => "unknown",
    }
}

// ---------------------------------------------------------------------------
// Gate semantics (INV-S1 / INV-S2)
// ---------------------------------------------------------------------------

fn small_query() -> crate::ChcExpr {
    let mut rng = Rng::new(3);
    let v = Vocab::new(3, 1);
    crate::ChcExpr::and_all((0..4).map(|_| gen_conjunct(&mut rng, &v)))
}

#[test]
fn search_lane_context_creates_a_session_and_the_verification_lane_never_does() {
    let _mode = ScopedSessionMode::set(2);
    let q = small_query();
    let mut search = SmtContext::new_search();
    let _ = search.check_sat_with_timeout(&q, Duration::from_secs(2));
    assert!(
        search.has_session(),
        "Search lane + mode 2 routes to the session"
    );
    assert_eq!(search.session_stats().map(|s| s.queries), Some(1));

    let mut verification = SmtContext::new();
    let _ = verification.check_sat_with_timeout(&q, Duration::from_secs(2));
    assert!(
        !verification.has_session(),
        "INV-S1: no session on the Verification lane"
    );

    // Moving a context off the Search lane drops its session.
    search.set_lane(SmtLane::Verification);
    assert!(
        !search.has_session(),
        "set_lane(Verification) drops the session"
    );
}

#[test]
fn verification_mode_pins_a_search_context_off_the_session() {
    let _mode = ScopedSessionMode::set(2);
    let q = small_query();
    let mut search = SmtContext::new_search();
    {
        let _pin = ScopedVerificationMode::install();
        let r = search.check_sat_with_timeout(&q, Duration::from_secs(2));
        assert!(
            !search.has_session(),
            "INV-S2: no session while a verifier pin is alive"
        );
        assert!(!r.is_unknown(), "the legacy path still decides the query");
    }
    let _ = search.check_sat_with_timeout(&q, Duration::from_secs(2));
    assert!(
        search.has_session(),
        "the same context routes again once the pin is gone"
    );
}

#[test]
fn mode_zero_never_creates_a_session() {
    let _mode = ScopedSessionMode::set(0);
    let mut search = SmtContext::new_search();
    let _ = search.check_sat_with_timeout(&small_query(), Duration::from_secs(2));
    assert!(!search.has_session());
}

#[test]
fn reset_preserves_the_session() {
    let _mode = ScopedSessionMode::set(2);
    let q = small_query();
    let mut search = SmtContext::new_search();
    let _ = search.check_sat_with_timeout(&q, Duration::from_secs(2));
    search.reset();
    assert!(
        search.has_session(),
        "reset() keeps the warm session (design §2.11)"
    );
    let _ = search.check_sat_with_timeout(&q, Duration::from_secs(2));
    assert_eq!(search.session_stats().map(|s| s.queries), Some(2));
}

// ---------------------------------------------------------------------------
// L1 — stub wrong-UNSAT backend never reaches a verdict
// ---------------------------------------------------------------------------

#[test]
fn l1_stub_wrong_unsat_never_changes_the_final_verdict_of_an_unsafe_problem() {
    let _mode = ScopedSessionMode::set(1);
    // Default entry: the bounded original-clause reachability prepass
    // (`engines::original_unsafe`) decides this shallow loop from a concrete
    // ground derivation before any Search-lane query, so the stub cannot
    // reach the verdict at all here.
    let prepass = {
        let _stub = ScopedWrongUnsat::install();
        engines::solve_pdr_proof(problem(UNSAFE_LRA), pdr_config()).expect("solve")
    };
    assert_ne!(
        verdict_name(prepass.result()),
        "safe",
        "the default CLI entry under the stub produced a wrong Safe"
    );
    // The lock proper needs the PDR search to run on the stubbed lane:
    // `disable_cex_replay` is that prepass's eligibility gate, leaving the
    // ordinary PDR search plus `validate_pdr_proof_result`. Unstubbed, that
    // same entry decides Unsafe, so a stubbed Unknown is the stub's doing.
    let search_config = || PdrConfig {
        disable_cex_replay: true,
        ..pdr_config()
    };
    let honest = engines::solve_pdr_proof(problem(UNSAFE_LRA), search_config()).expect("solve");
    assert_eq!(verdict_name(honest.result()), "unsafe");
    let hits_before = lane::stub::hits();
    let result = {
        let _stub = ScopedWrongUnsat::install();
        engines::solve_pdr_proof(problem(UNSAFE_LRA), search_config()).expect("solve")
    };
    let hits = lane::stub::hits() - hits_before;
    let verdict = verdict_name(result.result());
    eprintln!("[L1 unsafe] verdict={verdict} stubbed_answers={hits}");
    assert!(hits > 0, "the stub must have answered search queries");
    assert_ne!(
        verdict, "safe",
        "a stub UNSAT on the search lane produced a wrong Safe"
    );
}

#[test]
fn l1_stub_wrong_unsat_never_changes_the_final_verdict_of_a_safe_problem() {
    let _mode = ScopedSessionMode::set(1);
    let hits_before = lane::stub::hits();
    let result = {
        let _stub = ScopedWrongUnsat::install();
        engines::solve_pdr_proof(problem(SAFE_LRA), pdr_config()).expect("solve")
    };
    let hits = lane::stub::hits() - hits_before;
    let verdict = verdict_name(result.result());
    eprintln!("[L1 safe] verdict={verdict} stubbed_answers={hits}");
    assert!(hits > 0, "the stub must have answered search queries");
    assert_ne!(
        verdict, "unsafe",
        "a stub UNSAT on the search lane produced a wrong Unsafe"
    );
}

// ---------------------------------------------------------------------------
// L2 — constructions_in_verification stays 0 on a real session-backed solve
// ---------------------------------------------------------------------------

#[test]
fn l2_real_session_solve_keeps_constructions_in_verification_at_zero() {
    let _mode = ScopedSessionMode::set(1);
    let before = lane::constructions_in_verification();
    let routed_before = lane::totals()
        .routed
        .load(std::sync::atomic::Ordering::Relaxed);
    let unsafe_run = engines::solve_pdr_proof(problem(UNSAFE_LRA), pdr_config()).expect("solve");
    let safe_run = engines::solve_pdr_proof(problem(SAFE_LRA), pdr_config()).expect("solve");
    let routed = lane::totals()
        .routed
        .load(std::sync::atomic::Ordering::Relaxed)
        - routed_before;
    eprintln!(
        "[L2] unsafe={} safe={} routed={routed}",
        verdict_name(unsafe_run.result()),
        verdict_name(safe_run.result())
    );
    assert_eq!(
        lane::constructions_in_verification(),
        before,
        "a session was created or queried under verification mode"
    );
    assert!(routed > 0, "the session must have served search queries");
    assert_ne!(verdict_name(unsafe_run.result()), "safe");
    assert_ne!(verdict_name(safe_run.result()), "unsafe");
}

/// Session on (mode 1) vs off must agree on the two small problems — the
/// session is search guidance, so a lost verdict here is a regression, not a
/// soundness issue, but it is exactly what the board must not hide.
#[test]
fn l2_session_on_and_off_agree_on_the_small_problems() {
    let off = {
        let _mode = ScopedSessionMode::set(0);
        (
            verdict_name(
                engines::solve_pdr_proof(problem(UNSAFE_LRA), pdr_config())
                    .expect("solve")
                    .result(),
            ),
            verdict_name(
                engines::solve_pdr_proof(problem(SAFE_LRA), pdr_config())
                    .expect("solve")
                    .result(),
            ),
        )
    };
    let on = {
        let _mode = ScopedSessionMode::set(1);
        (
            verdict_name(
                engines::solve_pdr_proof(problem(UNSAFE_LRA), pdr_config())
                    .expect("solve")
                    .result(),
            ),
            verdict_name(
                engines::solve_pdr_proof(problem(SAFE_LRA), pdr_config())
                    .expect("solve")
                    .result(),
            ),
        )
    };
    eprintln!(
        "[L2 on/off] off=(unsafe:{}, safe:{}) on=(unsafe:{}, safe:{})",
        off.0, off.1, on.0, on.1
    );
    assert_eq!(off, on, "session on/off verdicts differ (off, on)");
}

// ---------------------------------------------------------------------------
// L3 — k-induction with a forced wrong-UNSAT on the search lane
// ---------------------------------------------------------------------------

#[test]
fn l3_kind_with_stub_wrong_unsat_never_ends_in_safe_after_validation() {
    let _mode = ScopedSessionMode::set(1);
    let prob = problem(UNSAFE_LIA);
    let hits_before = lane::stub::hits();
    let kind_result = {
        let _stub = ScopedWrongUnsat::install();
        let config = KindConfig::with_engine_config(
            6,
            Duration::from_secs(5),
            Duration::from_secs(20),
            false,
            None,
        );
        KindSolver::new(prob.clone(), config).solve()
    };
    let hits = lane::stub::hits() - hits_before;
    let final_verdict = match &kind_result {
        KindResult::Safe(model) => {
            // Portfolio Step 5 on a Verification-lane validator.
            let mut verifier = PdrSolver::new(
                prob.clone(),
                PdrConfig {
                    strict_proofs: true,
                    solve_timeout: Some(Duration::from_secs(20)),
                    ..PdrConfig::default()
                },
            );
            if verifier.verify_model_per_rule(model, Duration::from_secs(5)) {
                "safe"
            } else {
                "unknown"
            }
        }
        KindResult::Unsafe(_) => "unsafe",
        _ => "unknown",
    };
    eprintln!("[L3] kind={kind_result:?} final={final_verdict} stubbed_answers={hits}");
    assert!(
        !matches!(kind_result, KindResult::NotApplicable),
        "Kind must run on the Int TS"
    );
    assert_ne!(final_verdict, "safe", "a wrong Safe survived validation");
}

/// The deferred `¬query` Safe of an UNSAFE problem is rejected by the
/// portfolio's Verification-lane validator even with the session on in
/// session-only mode: the validator is pinned (INV-S1 + INV-S2), so the
/// session can neither answer nor weaken its checks.
#[test]
fn l3_deferred_not_query_safe_is_rejected_by_the_pinned_validator() {
    let _mode = ScopedSessionMode::set(2);
    let prob = problem(UNSAFE_LIA);
    let pred = prob.predicates()[0].id;
    let x = crate::ChcVar::new("x", crate::ChcSort::Int);
    let not_query = crate::ChcExpr::not(crate::ChcExpr::ge(
        crate::ChcExpr::var(x.clone()),
        crate::ChcExpr::Int(3),
    ));
    let mut model = crate::InvariantModel::default();
    model.set(
        pred,
        crate::PredicateInterpretation::new(vec![x], not_query),
    );
    let mut verifier = PdrSolver::new(
        prob,
        PdrConfig {
            strict_proofs: true,
            solve_timeout: Some(Duration::from_secs(20)),
            ..PdrConfig::default()
        },
    );
    assert!(
        !verifier.verify_model_per_rule(&model, Duration::from_secs(5)),
        "the deferred ¬query invariant of an unsafe problem must fail per-rule validation"
    );
    assert!(
        verifier.verify_model_query_only(&model),
        "query-only alone accepts ¬query (why per-rule is the gate)"
    );
}
