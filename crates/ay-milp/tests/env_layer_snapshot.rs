// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The SHIPPED environment layer: the arm a unit test structurally cannot see.
//!
//! `tune::env_layer` forks on `cfg(test)`. Under `cfg(test)` it reads the
//! process environment live, which is what lets the crate's own kill-switch
//! tests set `AY_MILP_NO_CUTS` at runtime and mean it. Every RELEASE instead
//! resolves from `EnvSnapshot`, captured once into a `OnceLock` — and that arm
//! was covered by nothing: unit tests compile the other one, and an integration
//! test, which does link the crate without `cfg(test)`, never set a tuned
//! variable. Replacing the snapshot's `var_os` with `var` would have destroyed
//! the presence-vs-UTF-8 distinction `tune::on` rests on — a non-UTF-8
//! `AY_MILP_NO_CUTS` would read as *absent* and silently turn a consumer's kill
//! switch back on — and passed the whole suite.
//!
//! # Two constraints that decide the shape of this file
//!
//! **The capture is lazy and one-shot.** It happens on the first `env_layer`
//! call in the process and never again, so a test binary observes exactly one
//! environment. Everything this file wants in the snapshot has to be exported
//! before the first probe call, and there is no second chance — hence ONE
//! `#[test]` function here, whose first statements are the exports. A second
//! `#[test]` would race it for the capture (cargo runs test functions on
//! parallel threads) and whichever lost would assert about the other's
//! environment. If this file ever needs a second scenario, it needs a second
//! *file*: one binary, one capture.
//!
//! **No solve runs here.** Setting a tuned variable is process-global, and the
//! knobs used below are chosen so that even that would not matter:
//! `AY_MILP_SAT_STOP_SECS` is set to `15`, which is the compiled default it
//! would resolve to anyway (`bab.rs:13030`), and the other two resolve to their
//! compiled defaults because their values do not parse.

use ay_milp::diag_env_layer;
use std::ffi::OsStr;

/// Set to a well-formed value that is also the compiled default, so the export
/// is observable through the layer and inert through the engine.
const WELL_FORMED: &str = "AY_MILP_SAT_STOP_SECS";
/// Set to bytes that are not UTF-8 — the case that separates `var_os` from
/// `var`, and the only input that can tell the two apart. Unix-only: a Windows
/// environment value is UTF-16 and cannot carry it.
#[cfg_attr(not(unix), allow(dead_code))]
const NON_UTF8: &str = "AY_MILP_FLIP_CAP_SECS";
/// Removed before the capture, then set after it: absence in the snapshot has
/// to be absence, and has to stay absence.
const ABSENT: &str = "AY_MILP_SAT_STOP_MULT";

#[test]
fn the_shipped_env_layer_resolves_from_a_frozen_snapshot() {
    // FIRST, before anything can touch an accessor and freeze the capture.
    let _lock = ay_test_support::env::lock_env();
    let _well_formed = ay_test_support::env::ScopedEnvVar::set(WELL_FORMED, "15");
    let _absent = ay_test_support::env::ScopedEnvVar::unset(ABSENT);
    #[cfg(unix)]
    let _non_utf8 = {
        use std::os::unix::ffi::OsStrExt;
        ay_test_support::env::ScopedEnvVar::set(NON_UTF8, OsStr::from_bytes(b"9\xff0"))
    };

    let set = diag_env_layer(WELL_FORMED).expect("a tuned knob reads this variable");
    assert_eq!(
        set.layer.as_deref(),
        Some(OsStr::new("15")),
        "the shipped layer must see a variable exported before the capture"
    );
    assert_eq!(
        set.layer, set.capture,
        "the shipped layer and a fresh EnvSnapshot::capture() must agree"
    );
    assert!(set.on, "an exported variable is present");
    assert_eq!(set.real_opt, Some(15.0), "and parses through `real_opt`");

    let unset = diag_env_layer(ABSENT).expect("a tuned knob reads this variable");
    assert_eq!(unset.layer, None, "an unset variable is absent, not empty");
    assert_eq!(unset.capture, None);
    assert!(!unset.on);
    assert_eq!(unset.real_opt, None);

    // THE `var_os` vs `var` PIN. This is the assertion that fails if the
    // snapshot is ever rewritten to store `String`: `var` reports a non-UTF-8
    // value as absent, so `on` would go false and `AY_MILP_NO_CUTS=<invalid
    // utf-8>` would stop disabling cuts. Unix-only because Windows environment
    // values are UTF-16 and cannot carry this case at all.
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt;
        let raw = diag_env_layer(NON_UTF8).expect("a tuned knob reads this variable");
        assert_eq!(
            raw.layer.as_deref(),
            Some(OsStr::from_bytes(b"9\xff0")),
            "the snapshot keeps the raw bytes; a String snapshot would drop them"
        );
        assert_eq!(raw.layer, raw.capture);
        assert!(
            raw.on,
            "presence is var_os: a non-UTF-8 value is SET, however unreadable"
        );
        assert_eq!(
            raw.real_opt, None,
            "and the parsing accessors are var: unreadable reads as absent"
        );
        assert_eq!(raw.count_opt, None);
    }

    // FROZEN, not live. Mutating the environment now must not move the shipped
    // layer — and the fresh capture beside it proves the `None` above is the
    // snapshot's answer rather than a read that simply missed.
    let _late = ay_test_support::env::ScopedEnvVar::set(ABSENT, "2.5");
    let after = diag_env_layer(ABSENT).expect("a tuned knob reads this variable");
    assert_eq!(
        after.layer, None,
        "the shipped layer is captured once; a mid-process export is not seen"
    );
    assert_eq!(
        after.capture.as_deref(),
        Some(OsStr::new("2.5")),
        "a fresh capture does see it, so the layer's None is the freeze"
    );
    assert!(
        !after.on,
        "and every accessor resolves from the frozen layer"
    );
    assert_eq!(after.real_opt, None);

    assert!(
        diag_env_layer("AY_MILP_NOT_A_TUNED_KNOB").is_none(),
        "the probe is addressed by a knob's own name, not by an arbitrary one"
    );
}
