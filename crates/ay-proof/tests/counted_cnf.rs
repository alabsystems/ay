// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

//! Public counted-CNF output replayed by the real strict proof checker.
//!
//! The encoder and immutable source terms are borrowed, never cloned or
//! repaired by this consumer. Proof/Vec allocation and the tiny unit-resolution
//! driver are test scaffolding, not production counted-proof accounting.

use ay_core::original_query::{CountedAdmission, FiniteAdmissionGrant};
use ay_core::term::{CountedBuiltin, CountedTermBuilder};
use ay_core::{
    AletheRule, CountedCnf, CountedCnfJustification as Justification,
    CountedCnfSourceLit as SourceLit, Proof, ProofId, ProofStep, Sort, TermId, TermStore,
};
use std::sync::Arc;

#[path = "counted_cnf/bridge.rs"]
mod bridge;
#[path = "counted_cnf/cases.rs"]
mod cases;
#[path = "counted_cnf/degenerate.rs"]
mod degenerate;
#[path = "counted_cnf/native.rs"]
mod native;

use native::Native;

fn owner() -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(10_000_000, 128 * 1024 * 1024),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}

#[test]
fn every_boolean_gate_replays_all_input_polarities_through_real_strict_checker() {
    for op in [
        CountedBuiltin::Not,
        CountedBuiltin::And,
        CountedBuiltin::Or,
        CountedBuiltin::Implies,
        CountedBuiltin::Xor,
        CountedBuiltin::Eq,
        CountedBuiltin::Iff,
        CountedBuiltin::Distinct,
        CountedBuiltin::Ite,
    ] {
        for assignment in 0..8 {
            cases::with_gate(op, assignment, |mut native| {
                native.close_by_units();
                native.require_valid();
            });
        }
    }
}
