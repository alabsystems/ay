// W8 NEGATIVE — identical postcondition to repr_ge_pos.rs, but the body is the
// WRONG comparison (`>` instead of `>=`). MUST be REFUTED non-vacuously.
// Counterexample exists at lhs == rhs (body=false, post wants true). Evidence
// (stage1 compiler_consumer @ gap-1 HEAD): [postcond] FAILED (trust-full-verifier);
// counterexample: verified_counterexample = true; model_checker_consumer PDR refuted obligation.
// NOTE: rely on the VERBOSE verdict line, not the process exit code — under the
// standalone (non-cargo) invocation the refutation is always printed but the
// exit code can be 0 depending on model_checker_consumer/verification_consumer owner-reconciliation order.
#![feature(contracts)]
extern crate core;
use core::contracts::ensures;
#[ensures(result == (lhs >= rhs))]
pub fn ge(lhs: i128, rhs: i128) -> bool { lhs > rhs }
