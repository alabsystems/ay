// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic, clippy::expect_used)]
use std::cell::Cell;
use std::time::{Duration, Instant};

use super::*;

const GIB: usize = 1 << 30;

fn lane(live_gib: usize) -> MemoryGroupUsage {
    MemoryGroupUsage {
        label: "PDKIND",
        live_bytes: isize::try_from(live_gib * GIB).expect("fits"),
    }
}

#[test]
fn below_the_shed_share_nothing_happens() {
    let mut governor = MemoryGovernor::new(10 * GIB);
    let events = governor.poll_with(
        Instant::now(),
        || 6 * GIB,
        || panic!("no purge below the shed share"),
        || panic!("no shed below the shed share"),
    );
    assert_eq!(events, Vec::<GovernorEvent>::new());
}

#[test]
fn a_purge_that_relieves_the_pressure_sheds_nothing() {
    let mut governor = MemoryGovernor::new(10 * GIB);
    let readings = Cell::new(0);
    let events = governor.poll_with(
        Instant::now(),
        || {
            readings.set(readings.get() + 1);
            if readings.get() == 1 {
                8 * GIB
            } else {
                5 * GIB
            }
        },
        || true,
        || panic!("the purge relieved the pressure"),
    );
    assert_eq!(
        events,
        vec![GovernorEvent::Purged {
            before: 8 * GIB,
            after: 5 * GIB
        }]
    );
}

#[test]
fn pressure_that_survives_the_purge_sheds_the_fattest_lane() {
    let mut governor = MemoryGovernor::new(10 * GIB);
    let events = governor.poll_with(Instant::now(), || 8 * GIB, || true, || Some(lane(3)));
    assert_eq!(
        events,
        vec![
            GovernorEvent::Purged {
                before: 8 * GIB,
                after: 8 * GIB
            },
            GovernorEvent::Shed {
                lane: lane(3),
                pressure: 8 * GIB
            },
        ]
    );
}

#[test]
fn a_second_shed_waits_for_the_first_to_settle_unless_urgent() {
    let mut governor = MemoryGovernor::new(100 * GIB);
    let start = Instant::now();
    let first = governor.poll_with(start, || 75 * GIB, || false, || Some(lane(30)));
    assert_eq!(first.len(), 1, "no purge hook: the shed is the only event");

    let settling = governor.poll_with(
        start + Duration::from_millis(10),
        || 80 * GIB,
        || false,
        || panic!("the first shed is still settling"),
    );
    assert_eq!(settling, Vec::<GovernorEvent>::new());

    let urgent = governor.poll_with(
        start + Duration::from_millis(20),
        || 90 * GIB,
        || false,
        || Some(lane(20)),
    );
    assert!(
        matches!(urgent.as_slice(), [GovernorEvent::Shed { .. }]),
        "above the urgent share the next lane goes at once"
    );

    let settled = governor.poll_with(
        start + Duration::from_millis(20) + SHED_SETTLE,
        || 75 * GIB,
        || false,
        || Some(lane(10)),
    );
    assert!(matches!(settled.as_slice(), [GovernorEvent::Shed { .. }]));
}

#[test]
fn purges_are_spaced() {
    let mut governor = MemoryGovernor::new(10 * GIB);
    let start = Instant::now();
    let purges = Cell::new(0);
    let purge = || {
        purges.set(purges.get() + 1);
        true
    };
    governor.poll_with(start, || 8 * GIB, purge, || None);
    governor.poll_with(
        start + Duration::from_millis(10),
        || 8 * GIB,
        purge,
        || None,
    );
    assert_eq!(purges.get(), 1);
    governor.poll_with(start + PURGE_INTERVAL, || 8 * GIB, purge, || None);
    assert_eq!(purges.get(), 2);
}

#[test]
fn no_budget_never_polls() {
    let mut governor = MemoryGovernor::new(0);
    let events = governor.poll_with(
        Instant::now(),
        || panic!("no budget: no reading"),
        || panic!("no purge"),
        || panic!("no shed"),
    );
    assert_eq!(events, Vec::<GovernorEvent>::new());
}
