// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The scripts this check has itself decided `unsat` in this process.
//!
//! One empty-model SAFE is decided by this check at the adaptive finalize
//! gate and then again by the discharge gate (CLI) or the external
//! validation backstop (MODEL_CHECKER_CONSUMER). Both runs render the same script, so the
//! second is answered from here instead of paying the executor again
//! (count_zero, memchar_naive: 4-9 s per decision on a loaded host, against
//! a 15 s per-harness gate).
//!
//! This is not the engine-result memo the check replaced
//! (`crate::acyclic_cert_cache`): only [`super::check`] writes here, only
//! after a fresh executor answered `unsat` on exactly that script, and a
//! lookup compares the whole script byte for byte, so a hit is the same
//! claim this check already established. Nothing else can make a script
//! "confirmed". A poisoned lock reads as a miss (the caller decides afresh).

use std::collections::VecDeque;
use std::sync::{Mutex, OnceLock};

/// Total bytes of remembered scripts; the oldest are forgotten first.
const MAX_TOTAL_BYTES: usize = 8 << 20;

fn confirmed_scripts() -> &'static Mutex<VecDeque<String>> {
    static CONFIRMED: OnceLock<Mutex<VecDeque<String>>> = OnceLock::new();
    CONFIRMED.get_or_init(|| Mutex::new(VecDeque::new()))
}

/// Whether this check already decided exactly `script` `unsat`.
pub(super) fn confirmed_before(script: &str) -> bool {
    confirmed_scripts()
        .lock()
        .is_ok_and(|confirmed| confirmed.iter().any(|seen| seen == script))
}

/// Remember that a fresh executor decided `script` `unsat`.
pub(super) fn record_confirmed(script: String) {
    if script.len() > MAX_TOTAL_BYTES {
        return;
    }
    let Ok(mut confirmed) = confirmed_scripts().lock() else {
        return;
    };
    if confirmed.iter().any(|seen| *seen == script) {
        return;
    }
    let mut total: usize = confirmed.iter().map(String::len).sum();
    while total + script.len() > MAX_TOTAL_BYTES {
        let Some(oldest) = confirmed.pop_front() else {
            break;
        };
        total -= oldest.len();
    }
    confirmed.push_back(script);
}
