// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// `optimum_guard.rs` without its native `ensures` clause, for compilers that cannot
// parse one.
//
// DO NOT EDIT THE BODY HERE ALONE. `optimum_guard.rs` is the authority; this is that
// fragment with one line removed, because a native contract clause is raw grammar
// that a stock rustc rejects at parse time. `portfolio.rs` selects between them on
// `cfg(deductive_verify)`, so the verifier NEVER reads this file and the OPTIMUM upgrade
// gate is never verified in a weakened form. `tests/native_contract_twins.rs` pins
// the two bodies together, so a divergence fails the suite instead of shipping an
// unproven gate.

/// See `optimum_guard.rs` for the OPTIMUM-upgrade contract and the postcondition
/// this spelling cannot carry.
fn optimum_upgrade_guard(
    value: i128,
    floor: i128,
    constraints: &[crate::types::PbConstraint],
    assignment: &[bool],
) -> bool {
    value <= floor && verify_all_constraints(constraints, assignment)
}
