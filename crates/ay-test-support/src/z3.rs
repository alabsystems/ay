// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The ONE z3 oracle policy for tests: which z3 a test may take a verdict
//! from, and what a test does when there is none.
//!
//! Resolution and identity live in [`ay_sys::z3_oracle`]: `Z3_PATH`, else the
//! first z3 on `PATH` that proves it is z3 (the banner, plus a negative control
//! that refuses an AY drop-in), walking past aterm's reroute stubs the way the
//! stub's own passthrough does. Nothing in a test spawns `z3` by name: a
//! by-name spawn under aterm reaches a stub that refuses, and each suite that
//! did so either failed, or quietly stopped comparing against z3 at all.
//!
//! Policy:
//!
//! * [`require_z3`] is for a MANDATORY oracle: no z3 is a failure.
//! * [`optional_z3`] is for a leg that strengthens a test when z3 is present.
//!   Absence is a visible [`SKIP_MARKER`] line on the raw stderr handle
//!   (libtest captures `eprintln!`), and becomes a failure when
//!   `Z3_DIFFERENTIAL_REQUIRED` is truthy. A set-but-wrong `Z3_PATH` is always a
//!   failure: an explicit oracle choice never degrades into a skip.
//! * Both announce the oracle a suite used once per process with an
//!   [`ORACLE_MARKER`] line naming its path, banner and what was passed over.
//!
//! Callers keep treating a non-answer from the oracle (a crash, a timeout,
//! `unknown`) as absence of evidence, never as disagreement.

use std::collections::BTreeSet;
use std::io::Write as _;
use std::sync::{Mutex, OnceLock};

pub use ay_sys::z3_oracle::{
    parse_banner_version, z3_version_banner, Z3Oracle, Z3Source, Z3Unavailable,
};

/// Prefix of the line announcing a skipped z3 leg.
pub const SKIP_MARKER: &str = "AY-TEST-SKIP";

/// Prefix of the line naming the z3 a suite took verdicts from.
pub const ORACLE_MARKER: &str = "AY-TEST-Z3";

/// The switch that turns every optional z3 leg into a mandatory one.
const REQUIRED_ENV: &str = "Z3_DIFFERENTIAL_REQUIRED";

/// True when `Z3_DIFFERENTIAL_REQUIRED` is truthy (`1`, `true`, `yes`, `on`).
pub fn differential_required() -> bool {
    std::env::var(REQUIRED_ENV).is_ok_and(|value| is_truthy(&value))
}

/// The truthy spellings of a switch, ignoring case and surrounding space.
pub fn is_truthy(value: &str) -> bool {
    matches!(
        value.trim().to_ascii_lowercase().as_str(),
        "1" | "true" | "yes" | "on"
    )
}

/// The z3 for a suite whose oracle is MANDATORY; panics with the reason when
/// none resolves.
pub fn require_z3(suite: &str) -> &'static Z3Oracle {
    match ay_sys::z3_oracle::z3_oracle() {
        Ok(oracle) => {
            announce(
                ORACLE_MARKER,
                suite,
                &format!("oracle={}", oracle.identity()),
            );
            oracle
        }
        Err(reason) => panic!(
            "{suite}: this suite's z3 oracle is mandatory and none is usable: {reason}. \
             Put a real z3 on PATH or set Z3_PATH to its path."
        ),
    }
}

/// The z3 for a leg that runs only when z3 is present, or `None` after a
/// visible skip line. Panics instead when `Z3_DIFFERENTIAL_REQUIRED` is truthy
/// or when `Z3_PATH` is set and wrong.
pub fn optional_z3(suite: &str) -> Option<&'static Z3Oracle> {
    match ay_sys::z3_oracle::z3_oracle() {
        Ok(oracle) => {
            announce(
                ORACLE_MARKER,
                suite,
                &format!("oracle={}", oracle.identity()),
            );
            Some(oracle)
        }
        Err(reason) => {
            assert!(
                !reason.is_misconfigured(),
                "{suite}: {reason}. An explicit z3 choice never degrades into a skip."
            );
            assert!(
                !differential_required(),
                "{suite}: {REQUIRED_ENV} is set but no z3 is usable: {reason}"
            );
            announce(
                SKIP_MARKER,
                suite,
                &format!("reason=z3-unavailable: {reason} (set {REQUIRED_ENV}=1 to fail instead)"),
            );
            None
        }
    }
}

/// Write `MARKER suite=SUITE detail` to the raw stderr handle, once per
/// (marker, suite) per process.
fn announce(marker: &str, suite: &str, detail: &str) {
    static ANNOUNCED: OnceLock<Mutex<BTreeSet<(String, String)>>> = OnceLock::new();
    let first = ANNOUNCED
        .get_or_init(|| Mutex::new(BTreeSet::new()))
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .insert((marker.to_string(), suite.to_string()));
    if first {
        let _ = writeln!(std::io::stderr().lock(), "{marker} suite={suite} {detail}");
    }
}

#[cfg(test)]
mod tests {
    use super::is_truthy;

    #[test]
    fn truthy_values_are_explicit() {
        for value in ["1", "TRUE", " yes ", "On", "true"] {
            assert!(is_truthy(value), "{value:?} should be truthy");
        }
        for value in ["", "0", "false", "required", "2"] {
            assert!(!is_truthy(value), "{value:?} should not be truthy");
        }
    }
}
