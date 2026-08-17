// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{child_order, ChildOrder};
use crate::tune::{activate_caller, Knob, Profile, Setting};

#[test]
fn market_split_defaults_to_dn_and_explicit_override_wins() {
    assert!(
        child_order(false, true) == ChildOrder::Dn,
        "market-split solves must default to the down child"
    );

    // B37: the explicit force rides the caller layer (`--child-order`).
    for (mode, expected) in [
        (3usize, ChildOrder::Lp),
        (0, ChildOrder::Away),
        (1, ChildOrder::Up),
        (2, ChildOrder::Dn),
    ] {
        let _tuned =
            activate_caller(Profile::EMPTY.with(Knob::ChildOrderMode, Setting::Count(mode)));
        assert!(
            child_order(false, true) == expected,
            "explicit mode {mode} child order must override the market-split default"
        );
    }
}
