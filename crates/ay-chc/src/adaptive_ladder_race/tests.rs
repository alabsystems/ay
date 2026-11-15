// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Mutex;
use std::time::Duration;

use ay_core::time::Instant;

use super::*;
use crate::adaptive::AdaptiveConfig;
use crate::pdr::InvariantModel;
use crate::ChcParser;

const COUNTER: &str = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (y Int)) (=> (and (inv x) (= y (+ x 1))) (inv y))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;

/// Upper bound on any waiting loop below, so a broken cancellation fails the
/// test instead of hanging it.
const SAFETY: Duration = Duration::from_secs(30);

fn portfolio(config: AdaptiveConfig) -> AdaptivePortfolio {
    AdaptivePortfolio::new(ChcParser::parse(COUNTER).expect("fixture parses"), config)
}

fn safe() -> LadderOutcome {
    (
        PortfolioResult::Safe(InvariantModel::new()),
        ValidationEvidence::FullVerification,
    )
}

fn unknown() -> LadderOutcome {
    (
        PortfolioResult::Unknown,
        ValidationEvidence::FullVerification,
    )
}

/// Spin until this thread's lane is cancelled (or the safety bound).
fn wait_for_lane_cancellation() -> bool {
    let started = Instant::now();
    while started.elapsed() < SAFETY {
        if crate::smt::deadline::lane_cancelled() {
            return true;
        }
        std::thread::sleep(Duration::from_millis(2));
    }
    false
}

#[test]
fn member_verdict_decides_and_cancels_the_foreground() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let foreground_started = AtomicBool::new(false);
    let foreground_cancelled = AtomicBool::new(false);
    let started = Instant::now();
    let members = vec![LadderMember::new("member", || {
        let waiting = Instant::now();
        while !foreground_started.load(Ordering::Acquire) && waiting.elapsed() < SAFETY {
            std::thread::yield_now();
        }
        assert!(foreground_started.load(Ordering::Acquire));
        Some(safe())
    })];
    let (result, _) = portfolio.race_ladder("test", members, || {
        foreground_started.store(true, Ordering::Release);
        foreground_cancelled.store(wait_for_lane_cancellation(), Ordering::Relaxed);
        unknown()
    });
    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert!(
        foreground_cancelled.load(Ordering::Relaxed),
        "the member's verdict must cancel the foreground's lane"
    );
    assert!(started.elapsed() < SAFETY, "the race must return promptly");
}

#[test]
fn foreground_verdict_cancels_members_and_their_route_tokens() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let member_started = AtomicBool::new(false);
    let lane_cancelled = AtomicBool::new(false);
    let token_cancelled = AtomicBool::new(false);
    let settled = AtomicBool::new(false);
    let members = vec![LadderMember::new("member", || {
        // A route token built on the member's thread observes its lane.
        let token = portfolio.lane_token();
        assert!(!race_settled(), "an open race is not settled");
        member_started.store(true, Ordering::Release);
        lane_cancelled.store(wait_for_lane_cancellation(), Ordering::Relaxed);
        token_cancelled.store(token.is_cancelled(), Ordering::Relaxed);
        settled.store(race_settled(), Ordering::Relaxed);
        None
    })];
    // The foreground decides only once the member runs (a member whose race
    // is decided before it starts is skipped, never run).
    let (result, _) = portfolio.race_ladder("test", members, || {
        let started = Instant::now();
        while !member_started.load(Ordering::Acquire) && started.elapsed() < SAFETY {
            std::thread::sleep(Duration::from_millis(1));
        }
        safe()
    });
    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert!(lane_cancelled.load(Ordering::Relaxed));
    assert!(
        token_cancelled.load(Ordering::Relaxed),
        "lane_token() on a member thread must link the member's lane"
    );
    assert!(
        settled.load(Ordering::Relaxed),
        "a member cancelled by the race's verdict must see the race settled"
    );
    assert!(
        !race_settled(),
        "the caller's thread leaves the race unsettled"
    );
    assert!(
        !portfolio.cancellation_token.is_cancelled(),
        "deciding a race must never cancel the solve's own handle"
    );
    assert!(
        !crate::smt::deadline::lane_cancelled(),
        "the caller's thread must leave the race without a lane binding"
    );
}

#[test]
fn non_definitive_member_outcome_does_not_decide() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let members = vec![LadderMember::new("gives_up", || Some(unknown()))];
    let (result, _) = portfolio.race_ladder("test", members, || {
        std::thread::sleep(Duration::from_millis(50));
        assert!(
            !crate::smt::deadline::lane_cancelled(),
            "a member giving up must not stop the foreground"
        );
        safe()
    });
    assert!(matches!(result, PortfolioResult::Safe(_)));
}

#[test]
fn undecided_race_returns_the_foreground_outcome_after_members_finish() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let member_finished = AtomicBool::new(false);
    let members = vec![LadderMember::new("slow", || {
        std::thread::sleep(Duration::from_millis(50));
        member_finished.store(true, Ordering::Relaxed);
        None
    })];
    let (result, _) = portfolio.race_ladder("test", members, unknown);
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(
        member_finished.load(Ordering::Relaxed),
        "an undecided race joins every member before returning"
    );
}

#[test]
fn members_inherit_the_callers_thread_boundaries() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let solve_deadline = Instant::now() + Duration::from_secs(40);
    let smt_deadline = Instant::now() + Duration::from_secs(30);
    let _solve = crate::smt::ScopedSolveDeadline::new(Some(solve_deadline));
    let _smt = crate::smt::ScopedSmtDeadline::install_until(smt_deadline);
    let _term = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(123_456));
    let seen = Mutex::new(None);
    let members = vec![LadderMember::new("member", || {
        *seen.lock().expect("lock") = Some((
            crate::smt::current_thread_solve_deadline(),
            crate::smt::deadline::current_smt_deadline(),
            crate::smt::SmtContext::current_thread_term_memory_budget(),
        ));
        None
    })];
    let _ = portfolio.race_ladder("test", members, unknown);
    let seen = seen.lock().expect("lock").take().expect("member ran");
    assert_eq!(seen.0, Some(solve_deadline));
    assert_eq!(seen.1, Some(smt_deadline));
    assert_eq!(seen.2, Some(123_456));
}

#[test]
fn deterministic_mode_runs_members_then_foreground_on_the_caller_thread() {
    let portfolio = portfolio(
        AdaptiveConfig::test_default()
            .with_execution_mode(AdaptiveExecutionMode::DeterministicSequential),
    );
    let caller = std::thread::current().id();
    let order = Mutex::new(Vec::new());
    let record = |name: &'static str| {
        assert_eq!(std::thread::current().id(), caller);
        order.lock().expect("lock").push(name);
    };
    let members = vec![
        LadderMember::new("first", || {
            record("first");
            Some(unknown())
        }),
        LadderMember::new("second", || {
            record("second");
            None
        }),
    ];
    let (result, _) = portfolio.race_ladder("test", members, || {
        record("foreground");
        safe()
    });
    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert_eq!(
        *order.lock().expect("lock"),
        vec!["first", "second", "foreground"]
    );
}

#[test]
fn panicking_member_is_no_verdict() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let members = vec![LadderMember::new("panics", || -> Option<LadderOutcome> {
        panic!("member failure")
    })];
    let (result, _) = portfolio.race_ladder("test", members, safe);
    assert!(matches!(result, PortfolioResult::Safe(_)));
}

#[test]
fn nested_race_participant_sees_the_outer_verdict() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let inner_member_started = AtomicBool::new(false);
    let inner_settled = AtomicBool::new(false);
    let outer_members = vec![LadderMember::new("outer_member", || {
        std::thread::sleep(Duration::from_millis(20));
        let started = Instant::now();
        while !inner_member_started.load(Ordering::Acquire) && started.elapsed() < SAFETY {
            std::thread::sleep(Duration::from_millis(1));
        }
        Some(safe())
    })];
    let (result, _) = portfolio.race_ladder("outer", outer_members, || {
        // A race nested in the outer foreground: its member observes the
        // OUTER verdict through the settlement chain.
        let inner_members = vec![LadderMember::new("inner_member", || {
            inner_member_started.store(true, Ordering::Release);
            let started = Instant::now();
            while !race_settled() && started.elapsed() < SAFETY {
                std::thread::sleep(Duration::from_millis(1));
            }
            inner_settled.store(race_settled(), Ordering::Relaxed);
            None
        })];
        portfolio.race_ladder("inner", inner_members, || {
            wait_for_lane_cancellation();
            unknown()
        })
    });
    assert!(matches!(result, PortfolioResult::Safe(_)));
    assert!(inner_settled.load(Ordering::Relaxed));
}

/// An unbounded solve (no deadline, no time budget: the CLI without a
/// timeout) has no budget share to give the front BMC member, so the
/// SimpleLoop ladder does not race it, and the foreground (which drops the
/// portfolio's BMC exactly when a `FRONT_BMC_MEMBER` races) keeps its own BMC
/// engine. At e2e3bd3a8 the member returned at once while the portfolio had
/// dropped its BMC, so such a solve ran no BMC at all.
#[test]
fn an_unbounded_solve_keeps_the_portfolio_bmc_engine() {
    let problem = ChcParser::parse(COUNTER).expect("fixture parses");
    let features = crate::classifier::ProblemClassifier::classify(&problem);
    let races_front_bmc = |portfolio: &AdaptivePortfolio, deadline: Option<Instant>| {
        portfolio
            .simple_loop_ladder_members(&features, deadline, false)
            .iter()
            .any(|member| member.name == FRONT_BMC_MEMBER)
    };

    let unbounded = portfolio(AdaptiveConfig::test_default().with_time_budget(Duration::ZERO));
    assert!(
        unbounded.front_bmc_probe_applies(&features),
        "setup: the front BMC probe applies to this simple loop"
    );
    assert!(!races_front_bmc(&unbounded, None));

    let bounded = portfolio(AdaptiveConfig::test_default());
    assert!(
        races_front_bmc(&bounded, None),
        "a time budget alone gives it a share"
    );
    let deadline = Some(Instant::now() + Duration::from_secs(10));
    assert!(races_front_bmc(&bounded, deadline));
}

#[test]
fn cancelled_member_candidate_cannot_decide_or_cancel_other_participants() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let state = RaceState::new(&portfolio.cancellation_token, 2, None);
    let refused = Mutex::new(Some(LadderMember::new("cancelled", || {
        crate::smt::deadline::current_lane_token()
            .expect("member lane")
            .cancel();
        Some(safe())
    })));
    portfolio.run_ladder_member(&state, &refused, &state.tokens[0]);
    assert!(!state.decided(), "a cancelled candidate is not a winner");
    assert!(state.tokens[0].is_cancelled());
    assert!(!state.tokens[1].is_cancelled(), "another member stays open");
    assert!(!state.foreground_token().is_cancelled());
    assert!(!portfolio.cancellation_token.is_cancelled());

    let accepted = Mutex::new(Some(LadderMember::new("healthy", || Some(safe()))));
    portfolio.run_ladder_member(&state, &accepted, &state.tokens[1]);
    assert!(state.decided(), "an ordinary open member still wins");
    assert!(state.foreground_token().is_cancelled());
    assert!(!portfolio.cancellation_token.is_cancelled());
    let (result, _) = portfolio.conclude_ladder_race("test", Instant::now(), &state, None);
    assert!(matches!(result, PortfolioResult::Safe(_)));
}

#[test]
fn cancelled_foreground_candidate_degrades_to_unknown_without_deciding() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let state = RaceState::new(&portfolio.cancellation_token, 1, None);
    let foreground = portfolio.run_ladder_foreground(&state, || {
        crate::smt::deadline::current_lane_token()
            .expect("foreground lane")
            .cancel();
        safe()
    });
    assert!(!state.decided());
    assert!(!state.tokens[0].is_cancelled());
    assert!(!portfolio.cancellation_token.is_cancelled());
    assert!(!crate::smt::deadline::lane_cancelled(), "scope restored");
    let (result, _) = portfolio.conclude_ladder_race("test", Instant::now(), &state, foreground);
    assert!(matches!(result, PortfolioResult::Unknown));
}

#[test]
fn expired_original_solve_deadline_refuses_member_with_live_caller() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let deadline = Instant::now() + Duration::from_secs(1);
    let state = RaceState::new(&portfolio.cancellation_token, 1, Some(deadline));
    let ran = AtomicBool::new(false);
    let member = Mutex::new(Some(LadderMember::new("late", || {
        ran.store(true, Ordering::Relaxed);
        // Enter while the original boundary is live, then exhaust it during
        // real callback work to exercise terminal, not preflight, admission.
        std::thread::sleep(deadline.saturating_duration_since(Instant::now()));
        Some(safe())
    })));
    portfolio.run_ladder_member(&state, &member, &state.tokens[0]);
    assert!(ran.load(Ordering::Relaxed), "exercise terminal admission");
    assert!(!state.decided());
    assert!(!state.foreground_token().is_cancelled());
    assert!(!portfolio.cancellation_token.is_cancelled());
    let foreground_ran = AtomicBool::new(false);
    let foreground = portfolio.run_ladder_foreground(&state, || {
        foreground_ran.store(true, Ordering::Relaxed);
        safe()
    });
    assert!(!foreground_ran.load(Ordering::Relaxed));
    let (result, _) = portfolio.conclude_ladder_race("test", Instant::now(), &state, foreground);
    assert!(matches!(result, PortfolioResult::Unknown));
}

#[test]
fn expired_original_smt_deadline_refuses_foreground_with_live_caller() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let _smt = crate::smt::ScopedSmtDeadline::install_until(Instant::now());
    let state = RaceState::new(&portfolio.cancellation_token, 1, None);
    let ran = AtomicBool::new(false);
    let foreground = portfolio.run_ladder_foreground(&state, || {
        ran.store(true, Ordering::Relaxed);
        safe()
    });
    assert!(
        !ran.load(Ordering::Relaxed),
        "a preclosed callback is skipped"
    );
    assert!(!state.decided());
    assert!(!state.tokens[0].is_cancelled());
    assert!(!portfolio.cancellation_token.is_cancelled());
    let (result, _) = portfolio.conclude_ladder_race("test", Instant::now(), &state, foreground);
    assert!(matches!(result, PortfolioResult::Unknown));
}

#[test]
fn memory_tripped_member_refuses_candidate_even_if_its_flag_is_cleared() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let mut state = RaceState::new(&portfolio.cancellation_token, 1, None);
    state.memory_limits = Some(LaneMemoryLimits {
        soft: 1024 * 1024,
        hard: usize::MAX,
    });
    let ran = AtomicBool::new(false);
    let member = Mutex::new(Some(LadderMember::new("memory", || {
        ran.store(true, Ordering::Relaxed);
        // A thread-local synthetic charge: no allocation, process limit or
        // hard-limit flag is changed by this controlled soft-trip test.
        ay_sys::charge_current_for_testing(2 * 1024 * 1024);
        assert!(ay_sys::current_memory_group_soft_tripped());
        let token = crate::smt::deadline::current_lane_token().expect("member lane");
        assert!(token.is_cancelled());
        token.reset();
        assert!(!token.is_cancelled(), "the sticky observation must suffice");
        Some(safe())
    })));
    portfolio.run_ladder_member(&state, &member, &state.tokens[0]);
    assert!(ran.load(Ordering::Relaxed));
    assert!(!state.decided());
    assert!(!state.foreground_token().is_cancelled());
    assert!(!portfolio.cancellation_token.is_cancelled());
    let finishes = lock(&state.finishes);
    assert!(finishes[0].memory_tripped);
    assert_eq!(finishes[0].result, "unknown");
}

#[test]
fn preclosed_current_memory_refuses_foreground_without_running_callback() {
    let portfolio = portfolio(AdaptiveConfig::test_default());
    let state = RaceState::new(&portfolio.cancellation_token, 1, None);
    let group = ay_sys::MemoryGroup::new(1024 * 1024, usize::MAX, Arc::new(AtomicBool::new(false)));
    let _group = ay_sys::enter_memory_group(group);
    ay_sys::charge_current_for_testing(2 * 1024 * 1024);
    let ran = AtomicBool::new(false);
    let foreground = portfolio.run_ladder_foreground(&state, || {
        ran.store(true, Ordering::Relaxed);
        safe()
    });
    assert!(!ran.load(Ordering::Relaxed));
    assert!(!state.decided());
    let (result, _) = portfolio.conclude_ladder_race("memory", Instant::now(), &state, foreground);
    assert!(matches!(result, PortfolioResult::Unknown));
    assert!(!portfolio.cancellation_token.is_cancelled());
}

#[path = "tests/admission.rs"]
mod admission;
