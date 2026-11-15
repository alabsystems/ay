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

/// Trust's unsigned var*var multiply-overflow obligation, reduced (Trust
/// `crates/deductive-checksgen/src/generate/overflow_vc.rs`, the UMUL record): the
/// 64-bit bitvector overflow predicate over FRESH operand images `l`/`r`,
/// beside the Int out-of-range reading of the same product over the real
/// operands `a`/`b`. The halves share no symbol, the product makes the Int half
/// nonlinear, and ay has no combined BV + NIA lane (`QfBvLiaIndep if nl_int =>
/// Other`), so the check-sat ends undecided. Trust's native lane names the mix
/// `QF_AUFBVNIA` and enables proofs, as here.
fn bv_nia_theory_mix() -> AYProgram {
    let mut program = AYProgram::new();
    program.add_constraint(crate::constraint::Constraint::set_option(
        ":produce-proofs",
        "true",
    ));
    program.set_logic("QF_AUFBVNIA");
    let l = program.declare_const("l", Sort::bv32()).zero_extend(32);
    let r = program.declare_const("r", Sort::bv32()).zero_extend(32);
    let a = program.declare_const("a", Sort::int());
    let b = program.declare_const("b", Sort::int());
    program.assert(l.clone().eq(Expr::bitvec_const(0u64, 64)).not());
    program.assert(l.clone().bvmul(r.clone()).bvudiv(l).eq(r).not());
    for operand in [&a, &b] {
        program.assert(operand.clone().int_ge(Expr::int(0)));
        program.assert(operand.clone().int_le(Expr::int(u32::MAX)));
    }
    let product = a.int_mul(b);
    program.assert(
        product
            .clone()
            .int_lt(Expr::int(0))
            .or(product.int_gt(Expr::int(u64::MAX))),
    );
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
/// `theory-combination`: the query never searched.
#[test]
fn incremental_theory_mix_without_a_lane_is_incomplete_not_internal_error() {
    let outcomes = execute_incremental(&bv_nia_theory_mix()).unwrap();
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
