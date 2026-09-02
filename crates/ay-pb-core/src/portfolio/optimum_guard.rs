// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Contract-carrying fragment of `portfolio.rs`, `include!`d into module `portfolio`
// — so `optimum_upgrade_guard` keeps its module, its crate-private visibility and
// its doc links, and only the ONE file a stock compiler cannot read is swapped.
//
// It is a separate file because a native Trust clause is RAW GRAMMAR: cfg-stripping
// runs after parsing, so no `cfg` can hide one and a compiler without the extension
// rejects the WHOLE FILE it appears in — here, 10k lines of portfolio solver.
// `optimum_guard_stock.rs` is this fragment minus the clause; `portfolio.rs` selects
// between them on `cfg(deductive_verify)`, and `tests/native_contract_twins.rs` pins the
// two together.

/// VIG-backed soundness guard for the `OptimumFound` upgrade.
///
/// Returns `true` iff it is sound to upgrade a `Satisfiable` incumbent with
/// objective `value` to `OptimumFound`: the incumbent must (a) meet a SOUND lower
/// bound `floor` on the objective (`value <= floor`, so `value == floor ==`
/// optimum), AND (b) re-pass the Verified Incumbent Gate against the ORIGINAL
/// constraints (defence-in-depth on the bound's soundness). The `&&`
/// short-circuits, so the VIG re-check runs only when the cheap `value <= floor`
/// test already holds — preserving the prior inline behaviour exactly.
///
/// # Embedded deductive contract (`ensures` clause)
///
/// The postcondition pins the gate decision to EXACTLY `value <= floor &&
/// verify_all_constraints(..)`: the upgrade can NEVER fire when `value > floor`
/// (sound bound not met) or when the incumbent fails the VIG. Combined with the
/// sound-LB hypothesis `floor <= obj_x` at every feasible point, this yields
/// global optimality of `value`; the embedded deductive contract below pins the
/// implementation to that exact gate.
///
/// It is written in the native clause grammar, which the default
/// (Trust) toolchain parses unconditionally — no `cfg` gate and no
/// `--extern trust` overlay, so unlike the ``
/// spelling it replaced, this contract is present in every build that can read
/// this file at all.
///
/// NEGATIVE CONTROL (non-vacuity): dropping the lower-bound guard
/// (`result == verify_all_constraints(..)`, i.e. upgrading any feasible incumbent
/// to OPTIMUM regardless of `value` vs `floor`) is UNSOUND and MUST be rejected
/// by this gate's negative-control tests.
///
/// The `deductive_checks_fixture_conformance` pin on this body is RED, and has been since
/// `fe36913a0` — see `eval/vig_core.rs` for the measured cause (rule 6 reaches a
/// clause only WITHIN a signature line, and `trustfmt` reflows that form onto its
/// own line unconditionally). It is a defect in the fixture normalization, not in
/// this body, and it is not repaired here.
fn optimum_upgrade_guard(
    value: i128,
    floor: i128,
    constraints: &[crate::types::PbConstraint],
    assignment: &[bool],
) -> bool
    ensures result == (value <= floor && verify_all_constraints(constraints, assignment))
{
    value <= floor && verify_all_constraints(constraints, assignment)
}
