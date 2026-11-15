// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::super::super::cancellation::Cancellation;
use super::*;

fn limits() -> BackwardProofLimits {
    let mut limits = generous_limits();
    limits.deadline = None;
    limits
}

#[test]
fn refusal_is_sticky_even_when_the_callback_would_resume() {
    let calls = Cell::new(0);
    let callback = || {
        calls.set(calls.get() + 1);
        calls.get() != 1
    };
    let control = Cancellation::new(&callback);
    assert_eq!(control.poll(), Err(BackwardProofFailure::Cancelled));
    assert_eq!(control.poll(), Err(BackwardProofFailure::Cancelled));
    assert_eq!(calls.get(), 1);
    assert_eq!(Cancellation::new(&callback).poll(), Ok(()));
}

#[test]
fn reentrant_refusal_cannot_be_cleared_by_an_outer_true() {
    let holder: Cell<Option<&Cancellation<'_>>> = Cell::new(None);
    let calls = Cell::new(0);
    let callback = || {
        calls.set(calls.get() + 1);
        let nested = holder.get().expect("installed borrowed control");
        assert_eq!(nested.poll(), Err(BackwardProofFailure::Cancelled));
        true
    };
    let control = Cancellation::new(&callback);
    holder.set(Some(&control));
    assert_eq!(control.poll(), Err(BackwardProofFailure::Cancelled));
    assert_eq!(control.poll(), Err(BackwardProofFailure::Cancelled));
    assert_eq!(
        control.check_latched(),
        Err(BackwardProofFailure::Cancelled)
    );
    assert_eq!(calls.get(), 1);
}

#[test]
fn a_caught_callback_panic_cannot_revive_the_meter() {
    let calls = Cell::new(0);
    let callback = || {
        calls.set(calls.get() + 1);
        if calls.get() == 2 {
            std::panic::panic_any("backward callback panic");
        }
        true
    };
    let limits = limits();
    let mut meter = BackwardProofMeter::with_cancellation(&limits, &callback).expect("entry");
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| meter.tick()))
        .expect_err("the caller panic is not swallowed here");
    assert_eq!(
        panic.downcast_ref::<&str>(),
        Some(&"backward callback panic")
    );
    assert_eq!(meter.tick(), Err(BackwardProofFailure::Cancelled));
    assert_eq!(meter.check_deadline(), Err(BackwardProofFailure::Cancelled));
    assert_eq!(calls.get(), 2);
}

#[test]
fn already_expired_deadline_keeps_pre_callback_precedence() {
    let mut limits = limits();
    limits.deadline = Some(Instant::now());
    let calls = Cell::new(0);
    let callback = || {
        calls.set(calls.get() + 1);
        false
    };
    assert!(matches!(
        BackwardProofMeter::with_cancellation(&limits, &callback),
        Err(BackwardProofFailure::Deadline)
    ));
    assert_eq!(calls.get(), 0);
}

#[test]
fn clone_and_dense_fill_are_polled_without_inventing_work_charges() {
    let limits = limits();
    let calls = Cell::new(0);
    let callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let mut meter = BackwardProofMeter::with_cancellation(&limits, &callback).expect("entry");
    let values = [7_u64; 96];
    let copy = meter
        .clone_slice(&values, BackwardProofResource::Hints)
        .expect("copy");
    let visited = ClauseIdVisited::new_bounded(1_025, &mut meter).expect("dense words");
    let ClauseIdVisited::Dense { words, .. } = visited else {
        panic!("tiny dense set");
    };
    assert_eq!(copy, values);
    assert_eq!(words, vec![0_u64; 17]);
    assert_eq!(
        meter.bytes,
        (copy.capacity() + words.capacity()) * size_of::<u64>()
    );
    assert_eq!(
        (meter.work, meter.steps, meter.literals, meter.hints),
        (0, 0, 0, 0)
    );
    assert!(calls.get() >= values.len() + words.len());
}

fn inner_storage_work(callback: &dyn Fn() -> bool) -> Result<(), BackwardProofFailure> {
    let limits = limits();
    let mut meter = BackwardProofMeter::with_cancellation(&limits, callback)?;
    let copy = meter.clone_slice(&[4_u64; 32], BackwardProofResource::Hints)?;
    let mut visited = ClauseIdVisited::new_bounded(1_025, &mut meter)?;
    for index in [0, 1, 1_024, 1_024] {
        let _ = visited.mark(index, &mut meter)?;
    }
    let mut seen = HashSet::new();
    for value in 0..12 {
        meter.insert_seen(&mut seen, value)?;
    }
    let mut steps: Vec<_> = [11, 5, 9, 7]
        .into_iter()
        .map(|clause_id| LratStep {
            clause_id,
            literals: Vec::new(),
            hints: Vec::new(),
        })
        .collect();
    meter.sort_steps_by_clause_id(&mut steps)?;
    assert_eq!(meter.work, 11, "frozen heap-sort tick count");
    assert_eq!(
        steps.iter().map(|step| step.clause_id).collect::<Vec<_>>(),
        vec![5, 7, 9, 11]
    );
    drop((copy, visited, seen, steps));
    meter.check_deadline()
}

#[test]
fn every_storage_and_sort_poll_can_refuse_then_fresh_retry_succeeds() {
    let calls = Cell::new(0);
    inner_storage_work(&|| {
        calls.set(calls.get() + 1);
        true
    })
    .expect("baseline");
    let count = calls.get();
    assert!((70..512).contains(&count));
    for stop in 1..=count {
        calls.set(0);
        assert_eq!(
            inner_storage_work(&|| {
                calls.set(calls.get() + 1);
                calls.get() != stop
            }),
            Err(BackwardProofFailure::Cancelled)
        );
        assert_eq!(calls.get(), stop);
    }
    assert_eq!(inner_storage_work(&|| true), Ok(()));
}

#[test]
fn exact_counts_and_retained_byte_failures_are_unchanged() {
    let limits = limits();
    let mut meter = BackwardProofMeter::with_cancellation(&limits, &|| true).expect("meter");
    let mut values = Vec::new();
    for value in 0_u64..22 {
        meter
            .push(&mut values, value, BackwardProofResource::Hints)
            .expect("push");
    }
    meter.add_step().expect("step");
    meter.add_literals(22).expect("literals");
    meter.add_hint().expect("hint");
    assert_eq!(
        (meter.steps, meter.literals, meter.hints, meter.work),
        (1, 22, 1, 0)
    );
    assert_eq!(meter.bytes, values.capacity() * size_of::<u64>());
    let mut denied = limits.clone();
    denied.max_bytes = 31;
    let mut meter = BackwardProofMeter::with_cancellation(&denied, &|| true).expect("meter");
    assert_eq!(
        meter.clone_slice(&[0_u64; 4], BackwardProofResource::Hints),
        Err(BackwardProofFailure::Limit {
            resource: BackwardProofResource::Bytes,
            limit: 31,
            actual: 32
        })
    );
    assert_eq!(meter.bytes, 0);
}
