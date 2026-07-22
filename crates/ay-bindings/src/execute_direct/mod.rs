// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Direct AY Program Execution.
//!
//! This module provides direct execution of `AYProgram` against the
//! `ay_dpll::api::Solver` without SMT-LIB2 serialization and parsing.
//!
//! Decomposed into submodules per #1056.
//!
//! ## Architecture
//!
//! Old path (SMT-LIB text file):
//! ```text
//! AYProgram → Display::fmt → .smt2 file → Parser → Executor
//! ```
//!
//! New path (direct execution):
//! ```text
//! AYProgram → execute_direct → ay_dpll::api::Solver → result
//! ```
//!
//! ## Fallback
//!
//! Some constructs are not yet supported by direct execution (and will trigger fallback):
//! - CHC commands (DeclareRel, Rule, Query)
//! - Soft assertions (MaxSAT)
//!
//! When these are detected, `execute` returns `ExecuteResult::NeedsFallback`
//! and the caller should use the SMT-LIB file-based path.
//!
//! The following are now handled directly (no fallback):
//! - CheckSatAssuming (#5456)
//! - Bv2Int, Int2Bv, IntToReal, RealToInt, IsInt (#5406)
//! - Quantifiers (Forall/Exists) and function application (#5406)
//! - Non-recursive function definitions (`define-fun`) via inline expansion (#8613)
//! - Datatypes (constructors, selectors, testers) (#5406)
//! - Integer/real constants of arbitrary size (via BigInt API)
//! - FP comparisons, classification, constants, unary ops, conversions (#5774)
//! - FP arithmetic (add, sub, mul, div, fma, sqrt, rem, roundToIntegral) (#6128)
//! - Optimization objectives (maximize/minimize/get-objectives) via OMT bridge (#6702)
//!
//! ## GetValue Support (#1977)
//!
//! GetValue commands are now supported via direct execution. Terms are collected
//! during constraint processing and evaluated after check-sat returns SAT.
//! Results are included in `ExecuteResult::Counterexample::values`.
//!
//! ## Panic Handling (#1044, #6329)
//!
//! All phases — constraint translation, check_sat, and model extraction — use
//! `ay_core::catch_ay_panics` to distinguish ay-internal panics from
//! programmer errors. ay-classified panics (sort mismatches, conflict
//! verification failures, etc.) degrade to `ExecuteResult::Unknown`.
//! Non-ay panics (index out of bounds, assertion failures) propagate via
//! `resume_unwind` so programmer errors are not silently swallowed.
//!
//! ## Usage
//!
//! ```rust,no_run
//! use ay_bindings::{AYProgram, execute_direct::{execute, ExecuteResult}};
//!
//! fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     let program = AYProgram::qf_bv();
//!     // ... add constraints ...
//!
//!     match execute(&program)? {
//!         ExecuteResult::Verified => println!("All properties verified"),
//!         ExecuteResult::Counterexample { .. } => println!("Found counterexample"),
//!         ExecuteResult::NeedsFallback(reason) => {
//!             println!("Fallback needed: {}", reason);
//!             // Use SMT-LIB file-based path
//!         }
//!         ExecuteResult::Unknown(reason) => println!("Unknown: {}", reason),
//!         _ => {} // future ExecuteResult variants
//!     }
//!     Ok(())
//! }
//! ```
//!
//! See issue #513 for context.

mod constraints;
mod context;
mod driver;
mod extract;
mod fallback;
mod incremental;
mod logic;
mod omt;
mod translate;
mod translate_bridge;
mod types;

use crate::program::AYProgram;
use driver::{execute_typed_with_details_impl, into_untyped_details, render_execute_result};

pub use ay_dpll::api::ModelValue;
pub use types::{
    CheckSatOutcome, ExecuteCounterexample, ExecuteDegradation, ExecuteDegradationKind,
    ExecuteDetails, ExecuteError, ExecuteFallback, ExecuteFallbackKind, ExecuteResult,
    ExecuteTypedDetails, ExecuteTypedResult, ExecuteValueMap,
};

/// Execute a AYProgram directly using ay_dpll's native API.
///
/// When the program contains multiple `check-sat` commands, returns the
/// result of the **last** check-sat. Use [`execute_all`] to get one result
/// per check-sat command.
///
/// # Returns
///
/// - `Ok(ExecuteResult::Verified)` if all assertions hold (UNSAT)
/// - `Ok(ExecuteResult::Counterexample { .. })` if a counterexample exists (SAT)
/// - `Ok(ExecuteResult::NeedsFallback(reason))` if direct execution not supported
/// - `Ok(ExecuteResult::Unknown(reason))` if solver returns unknown or panics (#1044)
/// - `Err(ExecuteError)` on execution failure
///
/// # Fallback Conditions
///
/// Returns `NeedsFallback` when the program contains unsupported constructs:
/// - CHC commands (DeclareRel, Rule, Query)
/// - Soft assertions (MaxSAT)
/// - Integer/real/bitvector constants that exceed i64
///
/// Unsupported logics (e.g., `HORN`) return
/// `Err(ExecuteError::UnsupportedLogic(..))` and should use the fallback path.
///
/// See module-level documentation for the complete list.
/// Arm a process-wide memory ceiling for in-process solving, exactly once.
///
/// In-process consumers (notably `compiler_consumer`, which links `ay-dpll` directly and
/// never runs ay's `main()`) would otherwise leave `PROCESS_MEMORY_LIMIT` unset
/// (no ceiling), so a runaway solve could grow the host process without bound —
/// the in-process analogue of the standalone-`ay` OOM. We arm the EMBEDDED
/// default ceiling (`default_embedded_memory_limit`, ~phys/8, 2–16 GB — a
/// verification pass shares its host process), but only if an
/// embedder has not already chosen one. The existing `should_abort_theory_loop`
/// checkpoint then trips `Unknown(MemoryLimit)` — soundness-neutral (only ever
/// drives Unknown, never a wrong SAT/UNSAT).
fn arm_process_memory_limit_once() {
    use std::sync::Once;
    static ARM: Once = Once::new();
    ARM.call_once(|| {
        if ay_sys::get_process_memory_limit() == 0 {
            ay_sys::set_process_memory_limit(ay_sys::default_embedded_memory_limit());
        }
    });
}

#[must_use = "execute returns a Result that must be used"]
pub fn execute(program: &AYProgram) -> Result<ExecuteResult, ExecuteError> {
    Ok(execute_with_details(program)?.result)
}

/// Execute a AYProgram directly and return the untyped result plus provenance.
#[must_use = "execute_with_details returns a Result that must be used"]
pub fn execute_with_details(program: &AYProgram) -> Result<ExecuteDetails, ExecuteError> {
    Ok(into_untyped_details(execute_typed_with_details(program)?))
}

/// Execute a AYProgram directly and preserve typed model values.
#[must_use = "execute_typed returns a Result that must be used"]
pub fn execute_typed(program: &AYProgram) -> Result<ExecuteTypedResult, ExecuteError> {
    Ok(execute_typed_with_details(program)?.result)
}

/// Execute a AYProgram directly with typed values and detailed provenance.
#[must_use = "execute_typed_with_details returns a Result that must be used"]
pub fn execute_typed_with_details(
    program: &AYProgram,
) -> Result<ExecuteTypedDetails, ExecuteError> {
    arm_process_memory_limit_once();
    execute_typed_with_details_impl(program)
}

/// Execute a multi-check-sat program incrementally (#8154).
#[must_use = "execute_incremental returns a Result that must be used"]
pub fn execute_incremental(program: &AYProgram) -> Result<Vec<CheckSatOutcome>, ExecuteError> {
    arm_process_memory_limit_once();
    incremental::execute_incremental_impl(program)
}

/// Execute a multi-check-sat program and return one [`ExecuteResult`] per
/// `check-sat` command (#8154).
///
/// Each result carries its own model, proof certificate, and unsat core.
/// For programs with a single `check-sat`, the returned `Vec` has exactly
/// one element, identical to what [`execute`] would return.
///
/// Callers that only need the last result can use [`execute`] instead.
///
/// # Example
///
/// ```rust,no_run
/// use ay_bindings::{AYProgram, Sort, Expr, execute_direct::{execute_all, ExecuteResult}};
///
/// let mut program = AYProgram::new();
/// program.set_logic("QF_LIA");
/// let x = program.declare_const("x", Sort::int());
/// program.assert(x.clone().int_gt(Expr::int(0)));
/// program.check_sat(); // first check-sat
///
/// program.push();
/// program.assert(x.clone().int_lt(Expr::int(0)));
/// program.check_sat(); // second check-sat (contradicts first assert)
/// program.pop(1);
///
/// let results = execute_all(&program).unwrap();
/// assert_eq!(results.len(), 2);
/// ```
#[must_use = "execute_all returns a Result that must be used"]
pub fn execute_all(program: &AYProgram) -> Result<Vec<ExecuteResult>, ExecuteError> {
    let outcomes = incremental::execute_incremental_impl(program)?;
    Ok(outcomes
        .into_iter()
        .map(|outcome| render_execute_result(outcome.result))
        .collect())
}

/// Execute a multi-check-sat program and return one [`CheckSatOutcome`] per
/// `check-sat` command, preserving typed model values and solve metadata (#8154).
///
/// This is the typed, detail-rich counterpart to [`execute_all`].
#[must_use = "execute_all_typed returns a Result that must be used"]
pub fn execute_all_typed(program: &AYProgram) -> Result<Vec<CheckSatOutcome>, ExecuteError> {
    incremental::execute_incremental_impl(program)
}

/// Check if direct execution is available (compile-time feature gate).
#[must_use]
pub fn is_available() -> bool {
    true
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
