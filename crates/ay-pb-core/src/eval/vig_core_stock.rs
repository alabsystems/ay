// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// `vig_core.rs` without its native `ensures` clause, for compilers that cannot
// parse one.
//
// DO NOT EDIT THE BODY HERE ALONE. `vig_core.rs` is the authority; this is that
// fragment with one line removed, because a native contract clause is raw grammar
// that a stock rustc rejects at parse time. `eval.rs` selects between them on
// `cfg(deductive_verify)`, so the verifier NEVER reads this file and the gate is never
// verified in a weakened form. `tests/native_contract_twins.rs` pins the two
// bodies together, so a divergence fails the suite instead of shipping silently.

/// See `vig_core.rs` for the incumbent-gate contract and the postcondition this
/// spelling cannot carry.
pub fn verify_all_constraints(constraints: &[PbConstraint], assignment: &[bool]) -> bool {
    constraints.iter().all(|c| eval_constraint(c, assignment))
}
