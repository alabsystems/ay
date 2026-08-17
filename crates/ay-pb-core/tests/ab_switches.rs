// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Set-once semantics for the engine A/B switch bridge.
//!
//! Deliberately an INTEGRATION test: `ab_switches::set` mutates a
//! process-global `OnceLock`, so exercising it inside the lib test binary
//! would flip the engine under every other test in that process (it did —
//! five counting-propagation tests failed the first time this lived in
//! `lib.rs`). One test binary, one process, one install.

use ay_pb_core::ab_switches::{get, set, PbAbSwitches};

#[test]
fn set_once_semantics_and_all_on_default() {
    assert_eq!(get(), PbAbSwitches::default());
    assert!(
        PbAbSwitches::default().counting,
        "default is the shipped engine"
    );
    let flipped = PbAbSwitches {
        counting: false,
        ..PbAbSwitches::default()
    };
    set(flipped).expect("first install wins");
    assert_eq!(get(), flipped);
    assert_eq!(set(PbAbSwitches::default()), Err(PbAbSwitches::default()));
    assert_eq!(get(), flipped, "the rejected install must not apply");
}
