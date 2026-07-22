// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Tests for direct AY Program execution, split by concern (#5033).

mod test_basic;
mod test_bridge_errors;
mod test_bv;
mod test_details;
mod test_fallback;
mod test_incremental;
mod test_nra;
mod test_omt;
mod test_panic_boundary;
mod test_proof_witness;
mod test_real;
mod test_solver_api;
mod test_typed_results;
mod test_validation_boundary;

pub(super) use super::context::catch_execute_stage;
pub(super) use super::translate::translate_sort;
pub(crate) use super::*;
pub(crate) use crate::sort::Sort;
pub(crate) use crate::Expr;
pub(crate) use ay_dpll::api::Sort as ApiSort;
pub(crate) use ay_dpll::SolveResult;
