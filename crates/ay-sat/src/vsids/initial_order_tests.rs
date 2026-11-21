// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-initial-order-high-first`: the first decision takes the highest
//! variable index (CaDiCaL `init_queue`, Kissat parse-order activation);
//! the default takes the lowest.

use super::VSIDS;
use crate::literal::Variable;

fn with_switch(on: Option<bool>) -> ay_core::sat_ab_test_override::Guard {
    ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        initial_order_high_first: on,
        ..Default::default()
    })
}

#[test]
fn default_order_decides_the_lowest_index_first() {
    let _switches = with_switch(None);
    let mut vsids = VSIDS::new(5);
    let vals = vec![0i8; 10];
    assert_eq!(vsids.pick_branching_variable_vmtf(&vals), Some(Variable(0)));
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(0)));
}

#[test]
fn high_first_order_decides_the_highest_index_first_in_queue_and_heap() {
    let _switches = with_switch(Some(true));
    let mut vsids = VSIDS::new(5);
    let mut vals = vec![0i8; 10];
    assert_eq!(vsids.pick_branching_variable_vmtf(&vals), Some(Variable(4)));
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(4)));
    // Assigned variables are skipped in descending index order.
    vals[4 * 2] = 1;
    vals[4 * 2 + 1] = -1;
    assert_eq!(vsids.pick_branching_variable_vmtf(&vals), Some(Variable(3)));
    assert_eq!(vsids.pick_branching_variable(&vals), Some(Variable(3)));
}

#[test]
fn high_first_order_still_lets_a_bump_win() {
    let _switches = with_switch(Some(true));
    let mut vsids = VSIDS::new(5);
    let vals = vec![0i8; 10];
    vsids.bump(Variable(1), &vals, false);
    assert_eq!(vsids.pick_branching_variable_vmtf(&vals), Some(Variable(1)));
}

#[test]
fn high_first_order_is_the_same_through_the_counted_constructor() {
    let _switches = with_switch(Some(true));
    for size in [0, 1, 7] {
        let owner = crate::counted_storage::test_owner(100_000, 100_000);
        let actual = VSIDS::try_new_counted(size, &owner).unwrap();
        let expected = VSIDS::new(size);
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }
}
