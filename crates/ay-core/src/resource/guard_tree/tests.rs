// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M1 (the development design notes §8): the tree's semantics, rule by rule.
//! The count (GT2, DR-38's tick shares, DR-39's allotments, saturation and
//! the setters' views) is `tests/count.rs`.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{mpsc, Arc};
use std::time::Duration;

use super::*;
use crate::resource::{Exhausted, WorkSnapshot};
use crate::time::Instant;

mod check;
mod count;

fn check_with(flag: &Arc<AtomicBool>) -> Guard {
    Guard::root_child(ChildSpec::new(NodeLabel::Check).with_external(Arc::clone(flag)))
}

fn budget(rlimit: u64) -> Guard {
    Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(rlimit)))
}

fn worker(index: usize) -> ChildSpec {
    ChildSpec::new(NodeLabel::Worker(WorkerId(index)))
}

fn same(a: &Guard, b: &Guard) -> bool {
    Arc::ptr_eq(&a.node, &b.node)
}

const HOUR: Duration = Duration::from_secs(3600);

#[test]
fn gt1_a_cancel_reaches_through_three_levels_and_never_up() {
    let interrupt = Arc::new(AtomicBool::new(false));
    let check = check_with(&interrupt);
    let search = check.child(ChildSpec::new(NodeLabel::Search));
    let lane = search.child(worker(0));
    let engine = lane.child(worker(0));
    assert_eq!(engine.exhausted(), None);

    lane.cancel();
    assert_eq!(engine.tick(1), Err(Exhausted::Cancelled));
    assert_eq!(lane.exhausted(), Some(Exhausted::Cancelled));
    assert_eq!(
        search.exhausted(),
        None,
        "a parent never reads a child's flag"
    );
    assert_eq!(check.exhausted(), None);

    let sibling = search.child(worker(1)).child(worker(1));
    assert_eq!(sibling.tick(1), Ok(()));
    interrupt.store(true, Ordering::Relaxed);
    assert_eq!(sibling.tick(1), Err(Exhausted::Cancelled));
    assert_eq!(search.exhausted(), Some(Exhausted::Cancelled));
}

#[test]
fn gt1_cancel_only_skips_the_ancestors_deadlines_but_not_their_cancels() {
    let interrupt = Arc::new(AtomicBool::new(false));
    let past = Instant::now();
    let check = Guard::root_child(
        ChildSpec::new(NodeLabel::Check)
            .with_external(Arc::clone(&interrupt))
            .with_deadline(DeadlineSource::Fixed(past)),
    );
    let nested = check.child(ChildSpec::new(NodeLabel::Search));
    let envelope = Instant::now() + HOUR;
    let certify = check.child(
        ChildSpec::new(NodeLabel::Certify)
            .cancel_only()
            .with_deadline(DeadlineSource::Fixed(envelope)),
    );
    let inside = certify.child(ChildSpec::new(NodeLabel::Check));

    assert_eq!(nested.exhausted(), Some(Exhausted::Deadline));
    assert_eq!(
        certify.exhausted(),
        None,
        "the search wall does not reach Certify"
    );
    assert_eq!(inside.exhausted(), None);
    assert_eq!(inside.effective_deadline(), Some(envelope));

    interrupt.store(true, Ordering::Relaxed);
    assert_eq!(certify.exhausted(), Some(Exhausted::Cancelled));
    assert_eq!(inside.tick(1), Err(Exhausted::Cancelled));
}

#[test]
fn gt1_a_nested_check_under_certify_obeys_the_envelope() {
    let certify = Guard::root_child(
        ChildSpec::new(NodeLabel::Certify)
            .cancel_only()
            .with_deadline(DeadlineSource::Fixed(Instant::now())),
    );
    let nested = certify.child(ChildSpec::new(NodeLabel::Check));
    assert_eq!(nested.exhausted(), Some(Exhausted::Deadline));
}

#[test]
fn gt4_a_spawned_worker_sees_its_checks_stop() {
    let interrupt = Arc::new(AtomicBool::new(false));
    let check = check_with(&interrupt);
    let lane = check.child(worker(0));
    let (entered, wait_entered) = mpsc::channel();
    let (raised, wait_raised) = mpsc::channel::<()>();
    let thread = std::thread::spawn(move || {
        let _scope = lane.enter();
        let current = current_guard().expect("the worker entered its node");
        let before = current.should_stop();
        entered.send(()).expect("the test is waiting");
        wait_raised.recv().expect("the test raises the stop");
        (before, current_guard().and_then(|guard| guard.exhausted()))
    });
    wait_entered.recv().expect("the worker entered");
    interrupt.store(true, Ordering::Relaxed);
    raised.send(()).expect("the worker is waiting");
    let (before, after) = thread.join().expect("the worker ran");
    assert!(!before);
    assert_eq!(after, Some(Exhausted::Cancelled));
    assert!(current_guard().is_none(), "this thread entered nothing");
}

#[test]
fn gt4_nested_scopes_restore_and_an_out_of_order_drop_hides_nothing() {
    let outer = Guard::new();
    let inner = outer.child(ChildSpec::new(NodeLabel::Search));
    {
        let _outer = outer.enter();
        {
            let _inner = inner.enter();
            assert!(same(&current_guard().expect("entered"), &inner));
            assert_eq!(with_current_guard(|guard| same(guard, &inner)), Some(true));
        }
        assert!(same(&current_guard().expect("entered"), &outer));
    }
    assert!(current_guard().is_none());

    let first = outer.enter();
    let second = inner.enter();
    drop(first);
    assert!(same(&current_guard().expect("still open"), &inner));
    drop(second);
    assert!(current_guard().is_none());
    assert_eq!(with_current_guard(Guard::should_stop), None);
}

#[test]
fn gt5_a_childs_work_sums_into_its_ancestors_exactly() {
    const TICKS: u64 = 10_000;
    let check = Guard::new();
    let search = check.child(ChildSpec::new(NodeLabel::Search));
    let workers: Vec<_> = (0..4)
        .map(|index| {
            let lane = search.child(worker(index));
            std::thread::spawn(move || {
                let _scope = lane.enter();
                for _ in 0..TICKS {
                    lane.tick(1).expect("no limit is set");
                }
                lane.record_work(&WorkSnapshot {
                    sat_conflicts: 3,
                    split_round_trips: 1,
                    ..WorkSnapshot::default()
                });
                lane.ledger_ticks()
            })
        })
        .collect();
    for lane in workers {
        assert_eq!(lane.join().expect("the worker ran"), TICKS);
    }
    for node in [&search, &check] {
        assert_eq!(node.ledger_ticks(), 4 * TICKS);
        assert_eq!(node.ledger().sat_conflicts, 12);
        assert_eq!(node.ledger().split_round_trips, 4);
    }
}

#[test]
fn gt6_a_share_never_moves_the_parent_deadline() {
    let wall = Instant::now() + HOUR;
    let cell = LiveDeadline::new(Some(wall));
    let check = Guard::root_child(
        ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Live(cell.clone())),
    );
    let share = check.share(Portion::Half).expect("there is time to divide");
    let half = share.deadline().expect("a time share has its own deadline");
    assert!(half < wall && half > Instant::now() + HOUR / 3, "{half:?}");
    assert_eq!((check.deadline(), cell.get()), (Some(wall), Some(wall)));
    assert_eq!(share.effective_deadline(), Some(half));
    assert_eq!(check.ledger().deadline_shares, 1);
    drop(share);
    assert_eq!(check.ledger().deadline_shares_spent, 0);

    let later = wall + HOUR;
    cell.set(Some(later));
    assert_eq!(
        check.deadline(),
        Some(later),
        "a live deadline moves for every reader"
    );

    let spent = Guard::root_child(
        ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Fixed(Instant::now())),
    );
    drop(
        spent
            .share(Portion::Half)
            .expect("a passed deadline still divides"),
    );
    assert_eq!(spent.ledger().deadline_shares_spent, 1);
    assert!(
        Guard::new().share(Portion::Half).is_none(),
        "nothing to divide"
    );
}

#[test]
fn gt7_the_first_stop_reason_is_latched() {
    let interrupt = Arc::new(AtomicBool::new(false));
    let node = Guard::root_child(
        ChildSpec::new(NodeLabel::Check)
            .with_external(Arc::clone(&interrupt))
            .with_deadline(DeadlineSource::Fixed(Instant::now())),
    );
    assert_eq!(node.stopped(), None);
    assert_eq!(node.exhausted(), Some(Exhausted::Deadline));
    interrupt.store(true, Ordering::Relaxed);
    assert_eq!(node.exhausted(), Some(Exhausted::Deadline));
    assert_eq!(node.tick(1), Err(Exhausted::Deadline));
    assert_eq!(node.stopped(), Some(Exhausted::Deadline));
}

#[test]
fn gt7_a_latched_stop_holds_after_a_live_deadline_moves_and_reaches_full_children() {
    let cell = LiveDeadline::new(Some(Instant::now()));
    let check = Guard::root_child(
        ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Live(cell.clone())),
    );
    assert_eq!(check.exhausted(), Some(Exhausted::Deadline));
    cell.set(Some(Instant::now() + HOUR));
    assert_eq!(check.exhausted(), Some(Exhausted::Deadline));
    let late = check.child(ChildSpec::new(NodeLabel::Search));
    assert_eq!(late.exhausted(), Some(Exhausted::Deadline));
    let certify = check.child(ChildSpec::new(NodeLabel::Certify).cancel_only());
    assert_eq!(certify.exhausted(), None);
}

#[test]
fn gt8_a_memory_share_trip_stops_only_its_node_as_memout() {
    const MIB: usize = 1 << 20;
    let check = Guard::new();
    let share = MemoryShare {
        soft_bytes: MIB,
        hard_bytes: 64 * MIB,
    };
    let runaway = check.child(worker(0).with_memory(share));
    let sibling = check.child(worker(1).with_memory(share));
    {
        let _scope = runaway.enter();
        ay_sys::charge_current_for_testing(2 * MIB);
    }
    assert_eq!(runaway.exhausted(), Some(Exhausted::Memory));
    assert_eq!(Exhausted::Memory.reason(), "memout");
    assert_eq!(sibling.exhausted(), None);
    assert_eq!(check.exhausted(), None);
}

#[test]
fn gt8_a_worker_without_a_share_is_charged_to_its_ancestors() {
    const MIB: usize = 1 << 20;
    let check = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_memory(MemoryShare {
        soft_bytes: MIB,
        hard_bytes: 64 * MIB,
    }));
    let lane = check.child(worker(0));
    let seen = std::thread::spawn(move || {
        let _scope = lane.enter();
        ay_sys::charge_current_for_testing(2 * MIB);
        lane.exhausted()
    })
    .join()
    .expect("the worker ran");
    assert_eq!(seen, Some(Exhausted::Memory));
    assert_eq!(check.exhausted(), Some(Exhausted::Memory));
}

#[test]
fn the_process_memory_budget_reaches_full_nodes_only() {
    let check = Guard::new();
    let certify = check.child(ChildSpec::new(NodeLabel::Certify).cancel_only());
    let search = check.child(ChildSpec::new(NodeLabel::Search));
    ay_sys::force_process_memory_exceeded_for_testing(true);
    let seen = (search.exhausted(), certify.exhausted());
    ay_sys::force_process_memory_exceeded_for_testing(false);
    assert_eq!(seen, (Some(Exhausted::Memory), None));
}

#[test]
fn a_spent_cpu_slice_stops_its_node_as_timeout() {
    let spent = Guard::root_child(worker(0).with_cpu(Duration::ZERO));
    assert_eq!(spent.exhausted(), Some(Exhausted::Cpu));
    assert_eq!(Exhausted::Cpu.reason(), "timeout");
    let check = Guard::root_child(worker(1).with_cpu(HOUR));
    let lane = check.child(worker(1));
    let _scope = check.enter();
    assert_eq!(lane.exhausted(), None);
    assert!(check
        .node
        .cpu
        .as_ref()
        .is_some_and(|cpu| cpu.spent() < HOUR));
}

#[test]
fn an_unmeasurable_cpu_clock_reads_as_a_spent_slice() {
    let open = Guard::root_child(worker(0).with_cpu(HOUR));
    let cpu = open.node.cpu.as_ref().expect("a slice");
    assert!(cpu.enter_unmeasurable());
    assert_eq!(open.exhausted(), Some(Exhausted::Cpu));
    cpu.exit();

    let closed = Guard::root_child(worker(1).with_cpu(HOUR));
    let cpu = closed.node.cpu.as_ref().expect("a slice");
    assert!(cpu.enter_unmeasurable());
    cpu.exit();
    assert_eq!(
        closed.exhausted(),
        Some(Exhausted::Cpu),
        "and stays spent once closed"
    );
}

#[test]
fn a_live_deadline_reads_back_what_was_set() {
    let at = Instant::now() + HOUR;
    let cell = LiveDeadline::new(Some(at));
    let handle = cell.clone();
    assert_eq!(handle.get(), Some(at));
    let generation = handle.generation();
    cell.set(None);
    assert_eq!((handle.get(), handle.generation()), (None, generation + 1));
    cell.set(Some(Instant::now()));
    assert!(handle.get().is_some_and(|read| read <= Instant::now()));
}
