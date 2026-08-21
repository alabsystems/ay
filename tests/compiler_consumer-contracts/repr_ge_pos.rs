// W8 POSITIVE — the eval_constraint Ge-arm verdict comparison, with the term
// sum supplied as the scalar `lhs` (call-free => representable). MUST be PROVED
// non-vacuously. Evidence (stage1 compiler_consumer @ gap-1 HEAD):
//   note: Trust verification: 1 proved, 0 failed ...
//   native model_checker_consumer typed CHC/PDR ... proved obligation ...-proof-2 with PdrInvariant
// Paired with repr_ge_neg.rs (identical postcondition, false body) which MUST
// be refuted — non-vacuity.
#![feature(contracts)]
extern crate core;
use core::contracts::ensures;
#[ensures(result == (lhs >= rhs))]
pub fn ge(lhs: i128, rhs: i128) -> bool { lhs >= rhs }
