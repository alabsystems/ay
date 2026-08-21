// W8 BLOCKER reproducer — minimal isolation of the wall that stops the real
// `eval_constraint` postcondition (the verdict-fn discharge target).
//
// The `#[ensures]` references a USER FUNCTION CALL `lhs_of(a)`. `lhs_of` is a
// TOTAL identity (no overflow, no panic), so this is purely about whether a
// call can appear inside a spec predicate — NOT about gap-1 / iterator
// nondeterminism (gap-1 is already committed and makes `eval_terms` itself
// lower: its ArithmeticSafety obligation is PROVED).
//
// OBSERVED (stage1 compiler_consumer @ gap-1 HEAD, `-Z deductive-verify-full`,
// `TRUST_NATIVE_DEBUG=1`):
//   vc:decide:assertion:0 kind=Assertion
//     typed_chc_lowering=UNSUPPORTED: "TrustSpecPredicate lowered to boolean
//     true; no model-checker-consumer CHC error condition was emitted"
//   -> routed to the v1/ay MIR-bridge -> [assert] FAILED (ay-in-process);
//      counterexample:   (EMPTY = fail-closed, NOT a real refutation)
//
// ROOT CAUSE: `trust_verifier_api::TrustSpecExprKind`
// (crates/trust-verifier-api/src/lib.rs:356) has NO `Call` node (and no
// enum-match/discriminant node). The spec builder abstracts the `lhs_of(a)`
// call to boolean `true`, so model-checker-consumer declines and the MIR-bridge cannot
// equate the body's call with the postcondition's call (no congruence).
// This is the precise persistent blocker for `eval_constraint` /
// `verify_all_constraints`, whose contracts are call-compositions.
//
// CONTRAST: `repr_ge_pos.rs` / `repr_ge_neg.rs` are the SAME verdict
// comparison with the sum supplied as a SCALAR (call-free) — those discharge
// non-vacuously (POS proved by model-checker-consumer PdrInvariant, NEG refuted with
// verified_counterexample=true).
#![feature(contracts)]
extern crate core;
use core::contracts::ensures;

fn lhs_of(a: i128) -> i128 {
    a
}

#[ensures(result == (lhs_of(a) >= rhs))]
pub fn decide(a: i128, rhs: i128) -> bool {
    let lhs = lhs_of(a);
    lhs >= rhs
}
