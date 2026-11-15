// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The refusal diagnostic of a theory mix with no combined lane (phase
//! `theory-combination`) beside the symbol-disjoint partition rescue, which the
//! router's `unknown` lets run: the diagnostic describes the published
//! `unknown` only when that is the refusal's own.

use std::time::Duration;

use crate::api::*;
use crate::UnknownReason;

fn assert_refusal_diagnostic(details: &SolveDetails) {
    assert_eq!(details.result, SolveResult::Unknown, "{:?}", details.result);
    assert_eq!(details.unknown_reason, Some(UnknownReason::Incomplete));
    let diagnostic = details
        .unknown_diagnostic
        .as_ref()
        .expect("an unknown carries a diagnostic");
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
}

/// `(> (* (bv2nat (bvand l #x0000000f)) a) 10)`: one shared symbol between
/// the bitvector and the nonlinear Int side, so one component and no lane.
fn bridged_mix(solver: &mut Solver) -> Term {
    let l = solver.declare_const("l", Sort::bitvec(32));
    let mask = solver.bv_const(15, 32);
    let low_bits = solver.bvand(l, mask);
    let low = solver.bv2int(low_bits);
    let a = solver.declare_const("a", Sort::Int);
    let product = solver.mul(low, a);
    let ten = solver.int_const(10);
    solver.gt(product, ten)
}

/// `(> (* a b) 10)` over fresh Ints.
fn nonlinear_int_conjunct(solver: &mut Solver) -> Term {
    let a = solver.declare_const("a", Sort::Int);
    let b = solver.declare_const("b", Sort::Int);
    let product = solver.mul(a, b);
    let ten = solver.int_const(10);
    solver.gt(product, ten)
}

/// The `check-sat-assuming` arm refuses the same mix the same way.
#[test]
fn check_sat_assuming_refuses_a_theory_mix_without_a_lane_as_incomplete() {
    let mut solver = Solver::try_new_with_smtlib_logic("QF_AUFBVNIA").unwrap();
    let mix = bridged_mix(&mut solver);

    let details = solver.check_sat_assuming_with_details(&[mix]).solve;
    assert_refusal_diagnostic(&details);
    assert_eq!(solver.executor_error(), None);
}

/// Two components, each SAT in its own lane, whose models the rescue cannot
/// merge (an array symbol is no scalar connector): the rescue fires, searches
/// and restores the refusal's `unknown`, and with it the refusal's diagnostic,
/// not whatever its component solves left behind.
#[test]
fn a_rescue_that_restores_the_refusal_restores_its_diagnostic() {
    let mut solver = Solver::try_new_with_smtlib_logic("QF_AUFBVNIA").unwrap();
    let cells = solver.declare_const("cells", Sort::array(Sort::bitvec(4), Sort::bitvec(8)));
    let i = solver.declare_const("i", Sort::bitvec(4));
    let read = solver.select(cells, i);
    let five = solver.bv_const(5, 8);
    let read_is_five = solver.eq(read, five);
    solver.assert_term(read_is_five);
    let nonlinear = nonlinear_int_conjunct(&mut solver);
    solver.assert_term(nonlinear);

    let details = solver.check_sat_with_details();
    let statistics = solver.statistics();
    assert_eq!(statistics.get_int("solver.partition_rescue.fired"), Some(1));
    assert_eq!(
        statistics.get_string("solver.partition_rescue.outcome"),
        Some("restore-unknown")
    );
    assert_refusal_diagnostic(&details);
}

/// The bitvector half of Trust's unsigned var*var multiply-overflow record as
/// Trust emits it (the 64-bit images of 32-bit operands; ay-bindings
/// `bv_nia_theory_mix`) beside a nonlinear Int conjunct. The rescue fires and
/// its bitvector component runs to the deadline: the published `unknown` is
/// the deadline's, and so is its diagnostic, not the refusal, which would
/// claim no lane searched.
#[test]
fn a_rescue_that_stops_at_the_deadline_reports_the_deadline() {
    let mut solver = Solver::try_new_with_smtlib_logic("QF_AUFBVNIA").unwrap();
    solver.set_timeout(Some(Duration::from_secs(1)));
    let l = solver.declare_const("l", Sort::bitvec(32));
    let r = solver.declare_const("r", Sort::bitvec(32));
    let l = solver.bvzeroext(l, 32);
    let r = solver.bvzeroext(r, 32);
    let zero = solver.bv_const(0, 64);
    let l_is_zero = solver.eq(l, zero);
    let l_nonzero = solver.not(l_is_zero);
    solver.assert_term(l_nonzero);
    let product = solver.bvmul(l, r);
    let recovered = solver.bvudiv(product, l);
    let recovers = solver.eq(recovered, r);
    let overflows = solver.not(recovers);
    solver.assert_term(overflows);
    let nonlinear = nonlinear_int_conjunct(&mut solver);
    solver.assert_term(nonlinear);

    let details = solver.check_sat_with_details();
    assert_eq!(
        solver.statistics().get_int("solver.partition_rescue.fired"),
        Some(1)
    );
    assert_eq!(details.result, SolveResult::Unknown, "{:?}", details.result);
    assert_eq!(details.unknown_reason, Some(UnknownReason::Timeout));
    let diagnostic = details
        .unknown_diagnostic
        .as_ref()
        .expect("an unknown carries a diagnostic");
    assert_ne!(
        diagnostic.phase.as_deref(),
        Some("theory-combination"),
        "{diagnostic:?}"
    );
    assert!(
        diagnostic
            .detail
            .as_deref()
            .is_some_and(|detail| !detail.contains("unsupported logic")),
        "{diagnostic:?}"
    );
}
