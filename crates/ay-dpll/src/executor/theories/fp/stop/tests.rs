// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor_types::SolveResult;
use ay_core::time::Instant;
use std::sync::atomic::{AtomicU64, AtomicUsize};
use std::time::Duration;

fn memory_probe(
    interrupt: Option<Arc<AtomicBool>>,
    deadline: SolveDeadlineCell,
    exceeded: &Arc<AtomicBool>,
    calls: &Arc<AtomicUsize>,
) -> FpStop {
    let (exceeded, calls) = (Arc::clone(exceeded), Arc::clone(calls));
    FpStop::with_sources(
        interrupt,
        deadline,
        Box::new(move || {
            calls.fetch_add(1, Ordering::Relaxed);
            exceeded.load(Ordering::Relaxed)
        }),
    )
}

#[test]
fn actual_executor_interrupt_is_live_and_reset_cannot_revive_the_attempt() {
    let mut executor = Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));
    let stop = FpStop::from_executor(&executor);
    assert_eq!(stop.check(), Ok(()));
    interrupt.store(true, Ordering::Relaxed);
    assert_eq!(stop.check(), Err(UnknownOrigin::InterruptFlag));
    interrupt.store(false, Ordering::Relaxed);
    assert_eq!(stop.check(), Err(UnknownOrigin::InterruptFlag));
    assert!(stop.should_stop());
    assert_eq!(FpStop::from_executor(&executor).check(), Ok(()));

    let detached = FpStop::from_executor(&executor);
    drop(executor);
    interrupt.store(true, Ordering::Relaxed);
    assert_eq!(detached.check(), Err(UnknownOrigin::InterruptFlag));
}

#[test]
fn actual_executor_deadline_remains_live_but_observed_expiry_is_sticky() {
    let mut executor = Executor::new();
    let stop = FpStop::from_executor(&executor);
    assert_eq!(stop.check(), Ok(()));
    executor.set_deadline(Some(Instant::now()));
    assert_eq!(stop.check(), Err(UnknownOrigin::SolveDeadline));
    executor.set_deadline(Some(Instant::now() + Duration::from_secs(60)));
    assert_eq!(stop.check(), Err(UnknownOrigin::SolveDeadline));
    assert_eq!(FpStop::from_executor(&executor).check(), Ok(()));

    executor.set_deadline(Some(Instant::now()));
    let extended_before_poll = FpStop::from_executor(&executor);
    executor.set_deadline(None);
    assert_eq!(extended_before_poll.check(), Ok(()));
}

#[test]
fn disappearing_memory_failure_does_not_repoll_or_revive_an_attempt() {
    let exceeded = Arc::new(AtomicBool::new(false));
    let calls = Arc::new(AtomicUsize::new(0));
    let stop = memory_probe(None, SolveDeadlineCell::new(), &exceeded, &calls);
    assert_eq!(stop.check(), Ok(()));
    assert_eq!(calls.load(Ordering::Relaxed), 1);
    exceeded.store(true, Ordering::Relaxed);
    assert_eq!(stop.check(), Err(UnknownOrigin::MemoryBudget));
    assert_eq!(calls.load(Ordering::Relaxed), 2);
    exceeded.store(false, Ordering::Relaxed);
    assert_eq!(stop.check(), Err(UnknownOrigin::MemoryBudget));
    assert!(stop.should_stop());
    assert_eq!(
        calls.load(Ordering::Relaxed),
        2,
        "a latched refusal never resamples a source"
    );
    let fresh = memory_probe(None, SolveDeadlineCell::new(), &exceeded, &calls);
    assert_eq!(fresh.check(), Ok(()));
    assert_eq!(calls.load(Ordering::Relaxed), 3);
}

#[test]
fn first_poll_uses_existing_executor_source_priority() {
    let interrupt = Arc::new(AtomicBool::new(true));
    let deadline = SolveDeadlineCell::new();
    deadline.set(Some(Instant::now()));
    let exceeded = Arc::new(AtomicBool::new(true));
    let calls = Arc::new(AtomicUsize::new(0));
    let stop = memory_probe(
        Some(Arc::clone(&interrupt)),
        deadline.clone(),
        &exceeded,
        &calls,
    );
    assert_eq!(stop.check(), Err(UnknownOrigin::InterruptFlag));
    assert_eq!(calls.load(Ordering::Relaxed), 0);
    interrupt.store(false, Ordering::Relaxed);
    let deadline_stop = memory_probe(None, deadline.clone(), &exceeded, &calls);
    assert_eq!(deadline_stop.check(), Err(UnknownOrigin::SolveDeadline));
    assert_eq!(calls.load(Ordering::Relaxed), 0);
    deadline.set(None);
    let memory_stop = memory_probe(None, deadline, &exceeded, &calls);
    assert_eq!(memory_stop.check(), Err(UnknownOrigin::MemoryBudget));
    assert_eq!(calls.load(Ordering::Relaxed), 1);
    assert_eq!(stop.check(), Err(UnknownOrigin::InterruptFlag));
    assert_eq!(deadline_stop.check(), Err(UnknownOrigin::SolveDeadline));
}

#[test]
fn builder_refusals_keep_the_first_captured_origin() {
    let exceeded = Arc::new(AtomicBool::new(false));
    let calls = Arc::new(AtomicUsize::new(0));
    let variable_stop = memory_probe(None, SolveDeadlineCell::new(), &exceeded, &calls);
    assert_eq!(
        variable_stop.refuse_build_error(FpBuildError::VariableLimit),
        UnknownOrigin::DeterministicResourceBudget
    );
    exceeded.store(true, Ordering::Relaxed);
    assert_eq!(
        variable_stop.refuse_build_error(FpBuildError::Interrupted),
        UnknownOrigin::DeterministicResourceBudget
    );
    assert_eq!(calls.load(Ordering::Relaxed), 0);

    let memory_stop = memory_probe(None, SolveDeadlineCell::new(), &exceeded, &calls);
    assert_eq!(
        memory_stop.refuse_build_error(FpBuildError::Interrupted),
        UnknownOrigin::MemoryBudget
    );
    exceeded.store(false, Ordering::Relaxed);
    assert_eq!(
        memory_stop.refuse_build_error(FpBuildError::VariableLimit),
        UnknownOrigin::MemoryBudget
    );
    assert_eq!(calls.load(Ordering::Relaxed), 1);

    let fallback = memory_probe(None, SolveDeadlineCell::new(), &exceeded, &calls);
    assert_eq!(
        fallback.refuse_build_error(FpBuildError::Interrupted),
        UnknownOrigin::InterruptFlag
    );
    assert_eq!(fallback.check(), Err(UnknownOrigin::InterruptFlag));
    assert_eq!(calls.load(Ordering::Relaxed), 2);
}

#[test]
fn an_interrupted_builder_uses_the_live_deadline_not_an_interrupt_fallback() {
    let mut executor = Executor::new();
    let stop = FpStop::from_executor(&executor);
    executor.set_deadline(Some(Instant::now()));
    assert_eq!(
        stop.refuse_build_error(FpBuildError::Interrupted),
        UnknownOrigin::SolveDeadline
    );
    executor.set_deadline(None);
    assert_eq!(
        stop.refuse_build_error(FpBuildError::VariableLimit),
        UnknownOrigin::SolveDeadline
    );
}

#[test]
fn recorded_sat_budget_cannot_be_replaced_by_later_external_stops() {
    let mut executor = Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));
    let stop = FpStop::from_executor(&executor);
    assert_eq!(stop.check(), Ok(()));
    assert_eq!(
        stop.refuse(UnknownOrigin::DeterministicResourceBudget),
        UnknownOrigin::DeterministicResourceBudget
    );
    executor.set_deadline(Some(Instant::now()));
    assert_eq!(
        FpStop::from_executor(&executor).check(),
        Err(UnknownOrigin::SolveDeadline)
    );
    assert_eq!(
        stop.check(),
        Err(UnknownOrigin::DeterministicResourceBudget)
    );
    executor.set_deadline(None);
    interrupt.store(true, Ordering::Relaxed);
    assert_eq!(
        FpStop::from_executor(&executor).check(),
        Err(UnknownOrigin::InterruptFlag)
    );
    assert_eq!(
        stop.refuse(UnknownOrigin::InterruptFlag),
        UnknownOrigin::DeterministicResourceBudget
    );
    interrupt.store(false, Ordering::Relaxed);
    assert_eq!(
        stop.refuse_build_error(FpBuildError::Interrupted),
        UnknownOrigin::DeterministicResourceBudget
    );
    assert_eq!(FpStop::from_executor(&executor).check(), Ok(()));
}

#[test]
fn actual_exhausted_term_admission_is_captured_before_borrowed_encoding() {
    let mut executor = Executor::new();
    executor.set_term_memory_limit(Some(0));
    assert!(executor.term_memory_exceeded());
    let stop = FpStop::from_executor(&executor);
    executor.set_term_memory_limit(None);
    assert_eq!(stop.check(), Err(UnknownOrigin::MemoryBudget));
    assert_eq!(FpStop::from_executor(&executor).check(), Ok(()));
}

#[test]
fn memory_poll_gate_observes_first_then_once_per_interval() {
    let gate = MemoryPollGate::new();
    let now = Instant::now();
    assert!(
        gate.due(now),
        "the first check of an attempt always observes"
    );
    for check in 1..MEMORY_POLL_INTERVAL {
        assert!(!gate.due(now), "check {check} is inside the interval");
    }
    assert!(gate.due(now), "the interval's last check observes");
    assert!(!gate.due(now), "an observation restarts the interval");
}

#[test]
fn memory_poll_gate_observes_once_the_period_has_elapsed() {
    let gate = MemoryPollGate::new();
    let start = Instant::now();
    assert!(gate.due(start));
    assert!(!gate.due(start + MEMORY_POLL_PERIOD / 2));
    assert!(gate.due(start + MEMORY_POLL_PERIOD));
    assert!(!gate.due(start + MEMORY_POLL_PERIOD));
    assert!(
        !gate.due(start),
        "a clock reading earlier than the last observation never forces one"
    );
}

/// A per-clause checkpoint loop must not pay one operating-system memory
/// observation per check: that was 25.9M `/proc/self/statm` reads and about
/// 70 of the 85 seconds of a Float64 `fp.rem` CLI solve.
#[test]
fn a_hot_check_loop_takes_one_observation_per_interval_or_period() {
    const CHECKS: u64 = 1 << 18;
    let observations = Arc::new(AtomicU64::new(0));
    let counted = Arc::clone(&observations);
    let stop = FpStop::with_sources(None, SolveDeadlineCell::new(), {
        let gate = MemoryPollGate::new();
        memory_source(
            false,
            move || gate.due_lazily(Instant::now),
            move || {
                counted.fetch_add(1, Ordering::Relaxed);
                false
            },
        )
    });
    let started = Instant::now();
    for _ in 0..CHECKS {
        assert_eq!(stop.check(), Ok(()));
    }
    let periods = started.elapsed().as_nanos() / MEMORY_POLL_PERIOD.as_nanos();
    let bound = 1 + CHECKS / u64::from(MEMORY_POLL_INTERVAL) + periods as u64;
    assert!(
        (1..=bound).contains(&observations.load(Ordering::Relaxed)),
        "{} observations for {CHECKS} checks (bound {bound})",
        observations.load(Ordering::Relaxed)
    );
}

#[test]
fn executor_stop_observes_a_process_memory_breach_within_one_interval() {
    let executor = Executor::new();
    let stop = FpStop::from_executor(&executor);
    // Taken BEFORE the first observation: the gate's period runs from that
    // observation, so a thread descheduled between it and the forced breach
    // must not read as an early (unlimited) observation.
    let forced = Instant::now();
    assert_eq!(stop.check(), Ok(()), "the first check observes memory");
    ay_sys::force_process_memory_exceeded_for_testing(true);
    let mut checks = 0u32;
    let outcome = loop {
        checks += 1;
        match stop.check() {
            Ok(()) if checks < MEMORY_POLL_INTERVAL => {}
            outcome => break outcome,
        }
    };
    let elapsed = forced.elapsed();
    ay_sys::force_process_memory_exceeded_for_testing(false);
    assert_eq!(outcome, Err(UnknownOrigin::MemoryBudget));
    assert!(
        checks == MEMORY_POLL_INTERVAL || elapsed >= MEMORY_POLL_PERIOD,
        "the breach was observed after {checks} checks and {elapsed:?}: the \
         process-memory observation is not rate limited"
    );
    assert_eq!(
        stop.check(),
        Err(UnknownOrigin::MemoryBudget),
        "the observed breach stays sticky"
    );
}

/// The period test must not read the wall clock on every check either: one
/// read per check was a quarter of the fixed Float64 `fp.rem` solve's user
/// time.
#[test]
fn memory_poll_gate_reads_the_clock_once_per_stride() {
    let gate = MemoryPollGate::new();
    let start = Instant::now();
    let reads = Cell::new(0u32);
    let clock = || {
        reads.set(reads.get() + 1);
        start
    };
    assert!(gate.due_lazily(clock), "the first check observes");
    for check in 1..MEMORY_POLL_INTERVAL {
        assert!(
            !gate.due_lazily(clock),
            "check {check} is inside the interval"
        );
    }
    assert!(gate.due_lazily(clock), "the interval's last check observes");
    assert_eq!(
        reads.get(),
        2 + (MEMORY_POLL_INTERVAL - 1) / MEMORY_CLOCK_STRIDE,
        "one clock read per stride, plus the first check and the interval's last"
    );

    let late = Cell::new(start);
    let gate = MemoryPollGate::new();
    assert!(gate.due_lazily(|| late.get()));
    late.set(start + MEMORY_POLL_PERIOD);
    for check in 1..MEMORY_CLOCK_STRIDE {
        assert!(
            !gate.due_lazily(|| late.get()),
            "check {check} reads no clock"
        );
    }
    assert!(
        gate.due_lazily(|| late.get()),
        "an elapsed period is seen at the next stride boundary"
    );
}

/// Every FP lane runs its SAT search under the query's stop, through
/// `solve_sat_under_query_stop`: the interrupt flag, the deadline and the
/// deadline's timer flag, which the passes inside SAT preprocessing poll and a
/// `should_stop` closure cannot reach. `lane` drives one lane on an executor
/// armed with a live interrupt flag and an hour-long deadline; a lane that
/// searched any other way would leave no record.
fn searches_under_the_query_stop(script: &str, lane: impl FnOnce(&mut Executor)) {
    use crate::executor::theories::sat_stop::searches;

    let interrupt = Arc::new(AtomicBool::new(false));
    let deadline = Instant::now() + Duration::from_secs(3600);
    let mut executor = Executor::new();
    executor
        .execute_all(&ay_frontend::parse(script).unwrap())
        .unwrap();
    executor.set_solve_controls(Some(Arc::clone(&interrupt)), Some(deadline));
    searches::take();
    lane(&mut executor);
    let searches = searches::take();
    assert!(!searches.is_empty(), "no search under the query stop");
    for search in searches {
        assert!(
            search
                .interrupt
                .is_some_and(|flag| Arc::ptr_eq(&flag, &interrupt)),
            "searched without the query's interrupt flag"
        );
        assert_eq!(search.deadline, Some(deadline));
    }
}

const PURE_FP: &str = "(set-logic QF_FP)
    (declare-const x (_ FloatingPoint 5 11))
    (assert (fp.isZero x))";

#[test]
fn the_stateless_lane_searches_under_the_query_stop() {
    searches_under_the_query_stop(PURE_FP, |executor| {
        assert!(matches!(
            executor.solve_fp_stateless().unwrap(),
            SolveResult::Sat
        ));
    });
}

#[test]
fn the_incremental_lane_searches_under_the_query_stop() {
    searches_under_the_query_stop(&format!("{PURE_FP} (push 1)"), |executor| {
        assert!(matches!(
            executor.try_solve_fp_incremental().unwrap(),
            Some(SolveResult::Sat)
        ));
    });
}

#[test]
fn the_fp_to_real_lane_searches_under_the_query_stop() {
    let script = "(set-logic QF_FPLRA)
        (declare-const x (_ FloatingPoint 5 11))
        (assert (not (fp.isNaN x)))
        (assert (not (fp.isInfinite x)))
        (assert (= (fp.to_real x) 3.5))";
    searches_under_the_query_stop(script, |executor| {
        assert!(executor.solve_fp_to_real().unwrap().is_sat());
    });
}
