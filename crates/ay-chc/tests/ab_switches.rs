// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Set-once semantics for the CHC A/B switch bridge. An INTEGRATION test on
//! purpose: installs are process-global (see ay-pb-core's B14 lesson — a
//! lib.rs draft flipped the engine under unrelated tests).

use ay_chc::ab_switches::{get, set, ChcAbSwitches};

#[test]
fn set_once_semantics_and_all_on_default() {
    assert_eq!(get(), ChcAbSwitches::default());
    assert!(
        ChcAbSwitches::default().ground_witness,
        "default is the shipped engine"
    );
    let flipped = ChcAbSwitches {
        diseq_swap: false,
        ..ChcAbSwitches::default()
    };
    set(flipped).expect("first install wins");
    assert_eq!(get(), flipped);
    assert_eq!(set(ChcAbSwitches::default()), Err(ChcAbSwitches::default()));
    assert_eq!(get(), flipped, "the rejected install must not apply");
}
