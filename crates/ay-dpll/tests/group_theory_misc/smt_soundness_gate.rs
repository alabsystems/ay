// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT Soundness Gate — Packet 1
//!
//! Systematic integration tests for DPLL(T) theory interaction correctness.
//! Each P1 logic (QF_LIA, QF_LRA, QF_UF, QF_BV, QF_AX) is tested for:
//!
//! 1. SAT with explicit model validation (`validate_model()`)
//! 2. UNSAT with proof-envelope validation
//! 3. One logic-specific edge case
//! 4. One push/pop incremental scope regression
//!
//! See the development design notes.

#![allow(clippy::panic)]

#[path = "smt_soundness_gate/abv.rs"]
mod abv;
#[path = "smt_soundness_gate/auflia.rs"]
mod auflia;
#[path = "smt_soundness_gate/auflira.rs"]
mod auflira;
#[path = "smt_soundness_gate/ax.rs"]
mod ax;
#[path = "smt_soundness_gate/bv.rs"]
mod bv;
#[path = "smt_soundness_gate/dt.rs"]
mod dt;
#[path = "smt_soundness_gate/fp.rs"]
mod fp;
#[path = "smt_soundness_gate/helpers.rs"]
mod helpers;
#[path = "smt_soundness_gate/lia.rs"]
mod lia;
#[path = "smt_soundness_gate/lira.rs"]
mod lira;
#[path = "smt_soundness_gate/lra.rs"]
mod lra;
#[path = "smt_soundness_gate/nra.rs"]
mod nra;
#[path = "smt_soundness_gate/seq.rs"]
mod seq;
#[path = "smt_soundness_gate/uf.rs"]
mod uf;
#[path = "smt_soundness_gate/uflia.rs"]
mod uflia;
#[path = "smt_soundness_gate/uflra.rs"]
mod uflra;
