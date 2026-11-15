// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deterministic control tests. Synthetic queued outcomes test refusal only;
//! the parent's original-clause positive/negative solver tests remain separate.

use super::*;
use crate::adaptive::AdaptiveConfig;
use crate::classifier::ProblemClassifier;
use crate::{ChcParser, SmtContext};

fn portfolio() -> AdaptivePortfolio {
    let source = "(set-logic HORN)
        (declare-fun state (Int Bool) Bool)
        (assert (forall ((x Int) (ok Bool)) (=> (and (= x 0) ok) (state x ok))))
        (assert (forall ((x Int) (ok Bool) (y Int) (next Bool))
          (=> (and (state x ok) (= y (+ x 1)) (= next ok)) (state y next))))
        (assert (forall ((x Int) (ok Bool)) (=> (and (state x ok) (not ok)) false)))";
    AdaptivePortfolio::new(
        ChcParser::parse(source).unwrap(),
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20)),
    )
}

fn control(parent: &CancellationToken) -> RaceControl {
    RaceControl::capture(Instant::now() + Duration::from_secs(30), None, parent)
}

fn queued_race(control: RaceControl) -> QueryFlagRace {
    let (sender, receiver) = mpsc::channel();
    // Not solver evidence: only used to establish that receipt cannot bypass
    // an exhausted or cancelled owner's publication boundary.
    sender
        .send(QueryFlagRaceOutcome::Proven(InvariantModel::new()))
        .unwrap();
    QueryFlagRace {
        started: Instant::now(),
        budget: Duration::from_secs(30),
        signal: CancellationToken::new(),
        control,
        observer: None,
        worker: None,
        receiver,
        resolution: None,
    }
}

#[test]
fn capture_keeps_earliest_deadline_and_memory_after_parent_scopes_drop() {
    let parent = CancellationToken::new();
    let now = Instant::now();
    let early = now + Duration::from_secs(10);
    let late = now + Duration::from_secs(20);
    let captured = {
        let _solve = ScopedSolveDeadline::new(Some(late));
        let _smt = ScopedSmtDeadline::install_until(early);
        let _memory = SmtContext::scoped_thread_term_memory_budget(Some(8192));
        let captured = RaceControl::capture(late, Some(16384), &parent);
        assert_eq!(captured.term_memory_limit, Some(8192));
        assert_eq!(captured.deadline, early);
        assert_eq!(
            RaceControl::capture(late, Some(4096), &parent).term_memory_limit,
            Some(4096)
        );
        captured
    };
    assert_eq!(
        captured.wait_budget_at(Duration::from_secs(30), now),
        Duration::from_secs(10)
    );
    assert_eq!(
        captured.wait_budget_at(Duration::from_secs(1), now),
        Duration::from_secs(1)
    );
    assert_eq!(
        captured.wait_budget_at(Duration::from_secs(1), early),
        Duration::ZERO
    );
    assert!(captured.open_at(now));
    assert!(!captured.open_at(early));
    assert!(!captured.open_at(now), "observed expiry must not reopen");
}

#[test]
fn entry_refuses_zero_memory_and_an_earlier_expired_smt_scope() {
    let portfolio = portfolio();
    let features = ProblemClassifier::classify(&portfolio.problem);
    assert!(portfolio.query_flag_candidate_model(&features).is_some());
    {
        let _memory = SmtContext::scoped_thread_term_memory_budget(Some(0));
        assert!(!portfolio.start_query_flag_candidate_race(&features, None));
        assert!(lock_race(&portfolio.query_flag_race).is_none());
    }
    {
        let _smt = ScopedSmtDeadline::install_until(Instant::now());
        assert!(!portfolio.start_query_flag_candidate_race(&features, None));
        assert!(lock_race(&portfolio.query_flag_race).is_none());
    }
}

#[test]
fn linked_caller_cancellation_is_sticky_and_reaches_the_existing_observer() {
    let upstream = CancellationToken::new();
    let parent = upstream.child();
    let mut captured = control(&parent);
    let mut observer = InterruptObserver::new(&captured.cancellation).unwrap();
    captured.interrupt = observer.interrupt();
    upstream.cancel();
    // finish joins the real observer and samples the complete linked token;
    // no scheduler timing or polling sleep is needed to establish observation.
    assert!(!observer.finish());
    upstream.reset();
    assert!(!parent.is_cancelled());
    assert!(!captured.open());
    assert!(captured.interrupt.load(Ordering::Relaxed));
    assert!(control(&parent).open(), "only a fresh attempt may resume");
}

#[test]
fn queued_candidates_are_revoked_after_cancel_reset_or_deadline() {
    for expired in [false, true] {
        let portfolio = portfolio();
        let parent = CancellationToken::new();
        let captured = control(&parent);
        let observer_copy = captured.clone();
        *lock_race(&portfolio.query_flag_race) = Some(queued_race(captured));
        if expired {
            assert!(!observer_copy.open_at(observer_copy.deadline));
        } else {
            parent.cancel();
            assert!(!observer_copy.open());
            parent.reset();
        }
        assert!(portfolio
            .query_flag_race_poll("cancelled fixture")
            .is_none());
        assert!(portfolio.query_flag_race_poll("later fixture").is_none());
        assert!(matches!(
            lock_race(&portfolio.query_flag_race)
                .as_ref()
                .unwrap()
                .resolution,
            Some(Resolution::Settled)
        ));
    }
}

#[test]
fn worker_refuses_zero_and_small_captured_caps_without_sending_a_candidate() {
    for limit in [0, 1] {
        let parent = CancellationToken::new();
        let captured = RaceControl::capture(
            Instant::now() + Duration::from_secs(30),
            Some(limit),
            &parent,
        );
        let caller = captured.clone();
        let (sender, receiver) = mpsc::channel();
        let signal = CancellationToken::new();
        QueryFlagRaceWorker {
            obligations: Vec::new(),
            model: InvariantModel::new(),
            control: captured,
            signal: signal.clone(),
            sender,
        }
        .run();
        assert!(matches!(
            receiver.try_recv(),
            Err(TryRecvError::Disconnected)
        ));
        assert!(!signal.is_cancelled());
        assert!(!caller.open());
    }
}

#[test]
fn backend_limits_and_refusal_survive_reset_without_touching_default_policy() {
    let future = Instant::now() + Duration::from_secs(30);
    let mut backend = PdrExecutorBackend::new();
    assert!(backend.resources_open());
    assert!(backend.set_resource_limits(future, Some(usize::MAX)));
    backend.reset();
    assert!(backend.resources_open());
    assert!(!backend.set_resource_limits(future, Some(1)));
    backend.reset();
    assert!(!backend.set_resource_limits(future, Some(usize::MAX)));

    let mut backend = PdrExecutorBackend::new();
    assert!(!backend.set_resource_limits(Instant::now(), None));
    backend.reset();
    assert!(!backend.set_resource_limits(future, None));
    assert!(matches!(
        backend.check_sat_with_dv_hint(&ChcExpr::Bool(false), Duration::from_secs(1), false),
        SmtResult::Unknown
    ));

    let flag = Arc::new(AtomicBool::new(false));
    let mut backend = PdrExecutorBackend::new();
    backend.set_interrupt(Arc::clone(&flag));
    assert!(backend.set_resource_limits(future, None));
    flag.store(true, Ordering::Relaxed);
    assert!(!backend.resources_open());
    flag.store(false, Ordering::Relaxed);
    backend.reset();
    assert!(
        !backend.resources_open(),
        "reset must retain observed interruption"
    );
}

#[test]
fn drop_interrupts_but_does_not_join_an_unfinished_opaque_worker() {
    let parent = CancellationToken::new();
    let captured = control(&parent);
    let stopped = Arc::clone(&captured.interrupt);
    let mut race = queued_race(captured);
    let (started_tx, started_rx) = mpsc::channel();
    let (release_tx, release_rx) = mpsc::channel();
    let (done_tx, done_rx) = mpsc::channel();
    race.worker = Some(std::thread::spawn(move || {
        started_tx.send(()).unwrap();
        // Simulate an opaque interval without solver work. A finite safety
        // timeout prevents a broken drop implementation hanging this test.
        let _ = release_rx.recv_timeout(Duration::from_secs(2));
        done_tx.send(()).unwrap();
    }));
    started_rx.recv_timeout(Duration::from_secs(1)).unwrap();
    drop(race);
    assert!(stopped.load(Ordering::Relaxed));
    assert!(matches!(done_rx.try_recv(), Err(TryRecvError::Empty)));
    release_tx.send(()).unwrap();
    done_rx.recv_timeout(Duration::from_secs(1)).unwrap();
}
