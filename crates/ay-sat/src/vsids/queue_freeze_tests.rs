// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-queue-freeze-kissat`: stable bumps leave the focused queue alone.

use super::VSIDS;
use crate::literal::Variable;

fn focused_queue_then_stable_bumps(freeze: bool) -> (VSIDS, Vec<u64>) {
    let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        queue_freeze_kissat: Some(freeze),
        ..Default::default()
    });
    let mut vsids = VSIDS::new(4);
    let vals = vec![0i8; 8];
    for i in 0..4 {
        vsids.bump(Variable(i), &vals, false);
    }
    let focused_order = vsids.bump_order.clone();
    vsids.bump(Variable(0), &vals, true);
    vsids.batch_bump(&[1], &vals, true);
    vsids.bump_vmtf_order_only(Variable(2), &vals);
    (vsids, focused_order)
}

#[test]
fn stable_bumps_leave_the_frozen_queue_alone() {
    let (mut vsids, focused_order) = focused_queue_then_stable_bumps(true);
    assert_eq!(vsids.bump_order, focused_order);
    assert!(!vsids.vmtf_is_deferred());
    vsids.reset_vmtf_search_to_last();
    assert_eq!(
        vsids.vmtf_unassigned, 3,
        "the search resumes at the queue's end"
    );
    assert_eq!(vsids.vmtf_unassigned_bumped, focused_order[3]);
}

#[test]
fn default_stable_bumps_reorder_the_queue() {
    let (vsids, focused_order) = focused_queue_then_stable_bumps(false);
    assert_ne!(vsids.bump_order, focused_order);
    assert!(vsids.vmtf_is_deferred());
}
