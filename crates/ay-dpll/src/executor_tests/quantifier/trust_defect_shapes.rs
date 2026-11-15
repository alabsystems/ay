// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The six quantified shapes the trust router pinned as undecided
//! (`trust-router::in_process_ay_backend::defect_shapes`, measured 2026-09-19),
//! carried here as ay's own permanent record.
//!
//! All six now have decisive regressions. Every row states the
//! shape's truth and how that truth is established WITHOUT trusting the answer
//! under test, then pins the verdict and its required publication authority.
//!
//! # Why fixing a gap must preserve its publication gate
//!
//! Quantifier instantiation is the classic source of a wrong `unsat`, and a
//! relaxed ground encoding is the classic source of a wrong `sat`. Each of the
//! former withheld shapes reached a fail-closed gate that prevents one of
//! those; NONE is closed by loosening its gate:
//!
//! * `BVFP` — now has a checked authored `forall_inst` derivation and an exact
//!   FP refutation of the raw extract-based instance. Its artifact gate
//!   (`quantified_semantic_unsat_or_unknown`) is unchanged; no empty-clause
//!   `hole` or self-corroborating re-solve may supply publication authority.
//! * `FPLRA` — the relaxed ground FP lane still refuses its model, but an
//!   independently checked zero instance now supplies an authored refutation.
//!   No counterexample-model value or relaxed ground verdict authorizes it.
//! * `AUFBVFP` — all 256 ground Boolean function outputs are clause-forced
//!   equal, so congruence is complete without quadratic pairs. FP arguments
//!   are materialized and exact array-read rewrite provenance restores the
//!   original UF assignments. The unchanged independent model gate confirms
//!   the reconstructed witness; no model of a relaxation supplies authority.

use super::*;

mod closed;
mod left_open;

/// The last output of a whole SMT-LIB script — the `check-sat` answer.
fn solve_one(input: &str) -> String {
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    outputs.last().cloned().unwrap_or_default()
}

/// The bridge lowers `FpFromBits(q)` to the `(fp s e m)` extract form, NOT to
/// `((_ to_fp 11 53) q)` (`trust-types::ay_bridge::fp_from_bv_expr`). The two
/// spellings take DIFFERENT paths through ay: with `to_fp` these shapes answer
/// differently and the pin silently stops measuring what it names. Every
/// `fromBits` below uses the bridge's own spelling.
fn from_bits_f64(bv: &str) -> String {
    format!("(fp ((_ extract 63 63) {bv}) ((_ extract 62 52) {bv}) ((_ extract 51 0) {bv}))",)
}
