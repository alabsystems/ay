// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M1 for the count (`count.rs`): GT2's allotments and closes, DR-38's tick
//! shares, DR-39's `CancelOnly` allotments, saturation, and the views a
//! setter on a shared guard makes.

use std::sync::atomic::AtomicU64;

use super::*;

#[test]
fn gt2_sibling_allotments_are_independent() {
    let check = budget(100);
    let w0 = check.child(worker(0).with_rlimit(Some(40)));
    let w1 = check.child(worker(1).with_rlimit(Some(40)));
    assert_eq!((w0.allotment(), w1.allotment()), (Some(40), Some(40)));
    assert_eq!(check.remaining(), Some(20));

    assert_eq!(w0.tick(39), Ok(()));
    assert_eq!(w0.tick(1), Err(Exhausted::Rlimit));
    assert_eq!(
        w1.tick(39),
        Ok(()),
        "a sibling's spend is not this worker's"
    );
    assert_eq!(w1.exhausted(), None);
    assert_eq!(check.exhausted(), None, "lent ticks are not spent ones");
}

#[test]
fn gt2_unspent_ticks_return_in_close_order() {
    let check = budget(100);
    let w0 = check.child(worker(0).with_rlimit(Some(40)));
    let w1 = check.child(worker(1).with_rlimit(Some(40)));
    w0.tick(10).expect("within its allotment");
    w1.tick(5).expect("within its allotment");

    drop(w0);
    assert_eq!((check.ticks(), check.remaining()), (10, Some(50)));
    drop(w1);
    assert_eq!((check.ticks(), check.remaining()), (15, Some(85)));

    let greedy = check.child(worker(2).with_rlimit(Some(1_000)));
    assert_eq!(
        greedy.allotment(),
        Some(85),
        "a request is capped by the remainder"
    );
    drop(greedy);
    let unasked = check.child(worker(3));
    assert_eq!(
        unasked.allotment(),
        Some(85),
        "no request draws the whole remainder"
    );
    assert_eq!(check.remaining(), Some(0));
    assert_eq!(
        check.tick(1),
        Err(Exhausted::Rlimit),
        "lent ticks cannot be spent"
    );
}

#[test]
fn gt2_an_overdraw_into_lent_ticks_latches_and_new_children_take_them_back() {
    let check = budget(100);
    let lane = check.child(worker(0));
    assert_eq!(
        check.tick(1),
        Err(Exhausted::Rlimit),
        "every tick it has is lent"
    );
    drop(lane);
    assert_eq!(check.remaining(), Some(99));
    assert_eq!(
        check.exhausted(),
        Some(Exhausted::Rlimit),
        "the stop is latched (GT7), though the lent ticks came back"
    );
    let late = check.child(worker(1));
    assert_eq!(late.allotment(), Some(99), "a new child takes them");
    assert_eq!(late.tick(98), Ok(()));
}

#[test]
fn gt2_a_closing_childs_spend_is_never_missing_from_the_remainder() {
    // One thread builds, spends and closes children of R ticks, R - 1 spent
    // each; another reads the remainder. Once the g-th child exists the
    // check has committed at least g (R - 1): a child's grant is held until
    // its close, and its spend after it, never neither.
    const R: u64 = 1_000;
    const CHILDREN: u64 = 200_000;
    const LIMIT: u64 = u64::MAX / 4;
    let check = budget(LIMIT);
    let built = Arc::new(AtomicU64::new(0));
    let done = Arc::new(AtomicBool::new(false));
    let reader = {
        let (check, built, done) = (check.clone(), Arc::clone(&built), Arc::clone(&done));
        std::thread::spawn(move || {
            let mut over = 0_u64;
            while !done.load(Ordering::Relaxed) {
                let g = built.load(Ordering::Acquire);
                let left = check.remaining().expect("a budget");
                over += u64::from(left > LIMIT - g * (R - 1));
            }
            over
        })
    };
    for _ in 0..CHILDREN {
        let child = check.child(worker(0).with_rlimit(Some(R)));
        built.fetch_add(1, Ordering::Release);
        child.tick(R - 1).expect("within its allotment");
    }
    done.store(true, Ordering::Relaxed);
    assert_eq!(reader.join().expect("the reader ran"), 0);
    assert_eq!(check.ticks(), CHILDREN * (R - 1));
}

#[test]
fn a_saturated_count_stays_saturated_up_the_tree() {
    let check = budget(100);
    let child = check.child(worker(0).with_rlimit(Some(50)));
    assert_eq!(child.tick(u64::MAX), Err(Exhausted::Rlimit));
    assert_eq!(child.tick(2), Err(Exhausted::Rlimit));
    assert_eq!(child.ticks(), u64::MAX, "the count does not wrap");
    drop(child);
    assert_eq!(check.ticks(), u64::MAX);
    assert_eq!(check.remaining(), Some(0));
    assert_eq!(check.exhausted(), Some(Exhausted::Rlimit));
    assert_eq!(check.child(worker(1)).allotment(), Some(0));
    assert_eq!(check.ledger_ticks(), u64::MAX);

    // A node with no count saturates as well, and keeps reading its clock.
    let cell = LiveDeadline::new(Some(Instant::now() + HOUR));
    let open = Guard::root_child(worker(2).with_deadline(DeadlineSource::Live(cell.clone())));
    assert_eq!(open.tick(u64::MAX), Ok(()));
    assert_eq!(open.tick(1), Ok(()));
    assert_eq!(open.ticks(), u64::MAX);
    cell.set(Some(Instant::now()));
    assert_eq!(open.tick(1), Err(Exhausted::Deadline));
}

#[test]
fn dr39_an_unasked_cancel_only_child_of_a_counted_node_has_a_count_of_0() {
    let check = budget(100);
    let certify = check.child(ChildSpec::new(NodeLabel::Certify).cancel_only());
    assert_eq!(certify.allotment(), Some(0), "never no count (DR-39)");
    assert_eq!(check.remaining(), Some(100));
    let nested = certify.child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(10)));
    assert_eq!(nested.allotment(), Some(0));
    assert_eq!(certify.tick(1), Err(Exhausted::Rlimit));

    let ground = Guard::new().child(ChildSpec::new(NodeLabel::Certify).cancel_only());
    assert_eq!(
        ground.allotment(),
        None,
        "without a budget, the ground allowance applies (DR-39)"
    );
}

#[test]
fn dr39_a_cancel_only_allotment_does_not_move_with_its_parent_remainder() {
    let check = budget(100);
    let certify = check.child(
        ChildSpec::new(NodeLabel::Certify)
            .cancel_only()
            .with_rlimit(Some(25)),
    );
    assert_eq!(
        check.remaining(),
        Some(100),
        "not deducted from the remainder"
    );

    check.tick(90).expect("within the check's budget");
    assert_eq!(check.remaining(), Some(10));
    assert_eq!(certify.allotment(), Some(25), "fixed at creation");
    assert_eq!(certify.tick(24), Ok(()), "more than the check has left");
    assert_eq!(certify.tick(1), Err(Exhausted::Rlimit));
    assert_eq!(
        check.remaining(),
        Some(10),
        "its ticks do not move the remainder"
    );

    let late = check.child(
        ChildSpec::new(NodeLabel::Certify)
            .cancel_only()
            .with_rlimit(Some(25)),
    );
    assert_eq!(
        late.allotment(),
        Some(25),
        "not capped by the remainder either"
    );
    drop((certify, late));
    assert_eq!((check.ticks(), check.remaining()), (90, Some(10)));
}

#[test]
fn dr39_a_cancel_only_childs_ticks_reach_the_parent_ledger() {
    let check = budget(100);
    let search = check.child(ChildSpec::new(NodeLabel::Search).with_rlimit(Some(50)));
    let certify = search.child(
        ChildSpec::new(NodeLabel::Certify)
            .cancel_only()
            .with_rlimit(Some(25)),
    );
    search.tick(7).expect("within its allotment");
    certify.tick(3).expect("within its allotment");
    let nested = certify.child(ChildSpec::new(NodeLabel::Check));
    assert_eq!(
        nested.allotment(),
        Some(22),
        "a nested check draws on Certify"
    );
    nested.tick(11).expect("within its allotment");
    assert_eq!(
        certify.ledger_ticks(),
        3,
        "an open child's ticks go up per stride"
    );

    drop(nested);
    assert_eq!(certify.ledger_ticks(), 14);
    drop(certify);
    assert_eq!(search.ledger_ticks(), 21);
    assert_eq!(
        search.ticks(),
        7,
        "Certify's ticks are not the search's spend"
    );
    assert_eq!(
        check.ledger_ticks(),
        14,
        "the open search's own ticks trail"
    );
    drop(search);
    assert_eq!(check.ledger_ticks(), 21);

    let open = check.child(
        ChildSpec::new(NodeLabel::Certify)
            .cancel_only()
            .with_rlimit(Some(4 * TICKS_PER_CLOCK_READ)),
    );
    open.tick(TICKS_PER_CLOCK_READ)
        .expect("within its allotment");
    assert_eq!(
        check.ledger_ticks(),
        21 + TICKS_PER_CLOCK_READ,
        "a stride's ticks reach the ledgers above while the child is open"
    );
}

#[test]
fn a_recorded_charge_counts_and_reaches_the_ledgers_but_reads_nothing() {
    let interrupt = Arc::new(AtomicBool::new(true));
    let run = check_with(&interrupt).child(ChildSpec::new(NodeLabel::Check));
    run.record_ticks(5);
    assert_eq!(
        (run.ticks(), run.stopped()),
        (5, None),
        "a raised flag is not read and nothing is latched"
    );
    assert_eq!(
        run.poll(),
        Some(Exhausted::Cancelled),
        "a poll still reads it"
    );
    let above = check_with(&Arc::new(AtomicBool::new(false)));
    let below = above.child(ChildSpec::new(NodeLabel::Check));
    below.record_ticks(TICKS_PER_CLOCK_READ);
    assert_eq!(
        above.ledger_ticks(),
        TICKS_PER_CLOCK_READ,
        "a stride's charge reaches the ledgers above while the node is open"
    );

    let counted = budget(10);
    counted.record_ticks(12);
    assert_eq!(
        counted.stopped(),
        None,
        "an overdraw by a charge latches nothing"
    );
    assert_eq!(
        counted.tick(0),
        Err(Exhausted::Rlimit),
        "the next tick reads the charged spend"
    );
}

#[test]
fn dr38_under_a_tick_budget_a_share_divides_ticks_not_time() {
    let wall = Instant::now() + HOUR;
    let check = Guard::root_child(
        ChildSpec::new(NodeLabel::Check)
            .with_rlimit(Some(100))
            .with_deadline(DeadlineSource::Fixed(wall)),
    );
    check.tick(20).expect("within the budget");
    let share = check
        .share(Portion::Half)
        .expect("there are ticks to divide");
    assert_eq!(share.allotment(), Some(40));
    assert_eq!(share.deadline(), None, "the deadline stays whole");
    assert_eq!(share.effective_deadline(), Some(wall));
    assert_eq!(share.tick(40), Err(Exhausted::Rlimit));
    drop(share);
    assert_eq!((check.ticks(), check.remaining()), (60, Some(40)));
    assert_eq!(check.ledger().deadline_shares_spent, 1);
}

#[test]
fn a_setter_on_a_shared_guard_adds_a_stop_and_lifts_none() {
    let mut guard = Guard::new();
    guard.set_rlimit(Some(100));
    let twin = guard.clone();
    let flag = Arc::new(AtomicBool::new(false));
    guard.set_cancel(Some(Arc::clone(&flag)));
    guard.set_rlimit(None);
    assert_eq!(
        guard.allotment(),
        Some(100),
        "the shared budget still binds"
    );
    assert_eq!(twin.remaining(), Some(100), "a view reserves nothing");
    assert_eq!(twin.tick(1), Ok(()));
    assert_eq!(guard.tick(60), Ok(()));
    assert_eq!(
        (guard.ticks(), twin.ticks()),
        (61, 61),
        "one count, as the old guard's clones shared"
    );
    flag.store(true, Ordering::Relaxed);
    assert_eq!(guard.exhausted(), Some(Exhausted::Cancelled));
    assert_eq!(twin.exhausted(), None, "the other holder keeps its limits");
    assert_eq!(twin.tick(39), Err(Exhausted::Rlimit));

    let mut original = Guard::new();
    original.set_rlimit(Some(1_000));
    let mut clone = original.clone();
    clone.set_deadline(None);
    assert_eq!(original.tick(1), Ok(()));
    clone.set_deadline(Some(Instant::now()));
    assert_eq!(clone.exhausted(), Some(Exhausted::Deadline));
    assert_eq!(original.exhausted(), None);
}

#[test]
fn a_view_caps_the_shared_count_and_a_view_of_it_cannot_lift_the_cap() {
    let shared = Guard::new();
    let mut capped = shared.clone();
    capped.set_rlimit(Some(10));
    assert_eq!(shared.tick(10), Ok(()), "the node itself has no count");
    assert_eq!(capped.ticks(), 10);
    assert_eq!(capped.exhausted(), Some(Exhausted::Rlimit));

    let mut wider = capped.clone();
    wider.set_rlimit(Some(1_000));
    assert_eq!(wider.allotment(), Some(10));
    assert_eq!(wider.exhausted(), Some(Exhausted::Rlimit));
    assert_eq!(shared.exhausted(), None);
}
