// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;
use ay_dpll::UnknownReason;

fn incomplete_division() -> AYProgram {
    let mut program = AYProgram::new();
    program.set_logic("QF_NRA");
    let x = program.declare_const("x", Sort::real());
    program.assert(x.clone().real_gt(Expr::real(1)));
    program.assert(Expr::real(1).real_div(x).real_ge(Expr::real(1)));
    program.check_sat();
    program
}

#[test]
fn native_unknown_retains_theory_incompleteness_reason() {
    let details = execute_typed_with_details(&incomplete_division()).unwrap();
    assert_eq!(
        details.result,
        ExecuteTypedResult::Unknown("incomplete".into())
    );
    let solve = details.solve_details.unwrap();
    assert_eq!(solve.unknown_reason, Some(UnknownReason::Incomplete));
    assert_eq!(
        solve.unknown_diagnostic.unwrap().reason,
        UnknownReason::Incomplete
    );
    assert!(details.unsat_proof.is_none());
}

#[test]
fn incremental_unknown_retains_theory_incompleteness_reason() {
    let outcomes = execute_incremental(&incomplete_division()).unwrap();
    assert_eq!(outcomes.len(), 1);
    let outcome = &outcomes[0];
    assert_eq!(
        outcome.result,
        ExecuteTypedResult::Unknown("incomplete".into())
    );
    let solve = outcome.solve_details.as_ref().unwrap();
    assert_eq!(solve.unknown_reason, Some(UnknownReason::Incomplete));
    assert_eq!(
        solve.unknown_diagnostic.as_ref().unwrap().reason,
        UnknownReason::Incomplete
    );
    assert!(outcome.unsat_proof.is_none());
}

/// Trust's bitwise operator bridged into a nonlinear Int product, reduced:
/// the low four bits of the 32-bit `l` (`bvand`), read as an Int (`bv2int`),
/// times the Int `a`, above 10. That one assertion holds the symbols of both
/// theories, so the query is one component, which the partition rescue cannot
/// split, and ay has no combined lane for bitvectors with nonlinear integer
/// arithmetic (the router's `LogicCategory::Other`). Trust's native lane names
/// the mix `QF_AUFBVNIA` and enables proofs, as here.
fn bridged_bv_nia_theory_mix() -> AYProgram {
    let mut program = AYProgram::new();
    program.add_constraint(crate::constraint::Constraint::set_option(
        ":produce-proofs",
        "true",
    ));
    program.set_logic("QF_AUFBVNIA");
    let l = program.declare_const("l", Sort::bv32());
    let a = program.declare_const("a", Sort::int());
    let low = l.bvand(Expr::bitvec_const(15u64, 32)).bv2int();
    program.assert(low.int_mul(a).int_gt(Expr::int(10)));
    program.check_sat();
    program
}

/// AD1 (Trust DECISION_QUEUE AD1-PRODUCER-1, trust-ratio): a theory mix with
/// no combined decision procedure is ay's own deterministic refusal, the one
/// the router already publishes as `incomplete` for a fail-closed combined
/// logic (`FAIL_CLOSED_COMBINED`). It is not an internal error. Published as
/// `internal_error`, it read as a solver FAULT to every embedder — Trust
/// counted it as a non-reproducible `solver-fault` where its multiply-overflow
/// record or a bitwise operator bridged into a nonlinear product met this
/// refusal. The refusal's text is the diagnostic's detail, under phase
/// `theory-combination`.
///
/// The fixture is the bridged shape, one component, so the refusal is the
/// answer. The multiply-overflow record was the fixture before: its two halves
/// share no symbol, so since 550b6b40e (DR-119) the partition rescue splits it
/// into two components and searches them. Each half is unsatisfiable, so
/// `unsat` is that record's answer, and this test on it ended
/// `unknown`/`timeout` after about 300 s instead of with the refusal.
/// f990caf2cd moved ay-dpll's twin,
/// `test_theory_mix_without_a_lane_is_incomplete_not_internal_error`, to the
/// bridged shape for the same reason.
#[test]
fn incremental_theory_mix_without_a_lane_is_incomplete_not_internal_error() {
    let outcomes = execute_incremental(&bridged_bv_nia_theory_mix()).unwrap();
    assert_eq!(outcomes.len(), 1);
    let outcome = &outcomes[0];
    let solve = outcome.solve_details.as_ref().unwrap();
    assert_ne!(
        solve.unknown_reason,
        Some(UnknownReason::InternalError),
        "a theory mix with no combined lane is a refusal, not an executor fault: {outcome:?}"
    );
    assert_eq!(
        outcome.result,
        ExecuteTypedResult::Unknown("incomplete".into()),
        "{outcome:?}"
    );
    assert_eq!(solve.unknown_reason, Some(UnknownReason::Incomplete));
    let diagnostic = solve.unknown_diagnostic.as_ref().unwrap();
    assert_eq!(
        diagnostic.phase.as_deref(),
        Some("theory-combination"),
        "{diagnostic:?}"
    );
    assert!(
        diagnostic
            .detail
            .as_deref()
            .is_some_and(|detail| detail.contains("unsupported logic: QF_AUFBVNIA")),
        "{diagnostic:?}"
    );
    assert!(outcome.unsat_proof.is_none());
}
