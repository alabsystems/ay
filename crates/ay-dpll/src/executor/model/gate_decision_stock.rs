// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `gate_decision.rs` without its native `ensures` clause, for compilers that
//! cannot parse one.
//!
//! DO NOT EDIT THE DECISION HERE ALONE. This file exists only because a native
//! contract clause is raw grammar that stock rustc rejects at parse time; the
//! CONTRACT-CARRYING definition in `gate_decision.rs` is the authority, and this
//! is that definition with one line removed. `mod.rs` selects between them on
//! `cfg(deductive_verify)`, so the verifier NEVER reads this file and the gate is
//! never verified in a weakened form.
//!
//! `tests/smt_model_gate_conformance.rs` pins both files to the same decision
//! expression and to the proof fixture, so a divergence fails the suite rather
//! than silently shipping an unproven gate.

/// See `gate_decision.rs` for the soundness argument and the postcondition this
/// spelling cannot carry.
pub(super) fn gate_keeps_sat(was_sat: bool, confirmed: bool, enforce: bool) -> bool {
    was_sat && (confirmed || !enforce)
}
