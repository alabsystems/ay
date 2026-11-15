// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A BV assumption is a proof premise as well as a SAT activation. These
//! native API queries retain Core's mixed named/unnamed signed-i32 shapes.
//! The separate satisfiable precheck is deliberately a different Solver.

use crate::api::{Logic, SolveDetails, Solver, Sort, Term};
use crate::CounterexampleStyle;

fn solver() -> Solver {
    let mut solver = Solver::try_new(Logic::All).expect("Core-selected logic");
    solver.set_counterexample_style(CounterexampleStyle::Readable);
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);
    solver.set_timeout(Some(std::time::Duration::from_millis(120_000)));
    solver.set_quantifier_deadline_backstop(false);
    solver
        .try_set_option("rlimit", "400000")
        .expect("Core conflict bound");
    // Preserve Core's process-memory formula, including the existing default
    // floor and current RSS, rather than substituting an unrelated fixed cap.
    let requested = 512_usize.saturating_mul(1024 * 1024);
    let memory = requested
        .max(ay_sys::default_memory_limit())
        .max(ay_sys::current_rss_bytes().saturating_add(requested));
    solver.set_memory_limit((memory > 0).then_some(memory));
    assert!(solver.executor.proof_reconstruction_step_budget.is_none());
    solver
}

fn with_named_assumption(boolean: bool) -> (Solver, Term, Term) {
    let mut solver = solver();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let zero = solver.try_bv_const(0, 32).expect("signed zero");
    let assumption = if boolean {
        let ten = solver.try_bv_const(10, 32).expect("signed upper bound");
        let lower = solver.try_bvsle(zero, x).expect("0 <= x");
        let upper = solver.try_bvslt(x, ten).expect("x < 10");
        solver.try_and(lower, upper).expect("bounded interval")
    } else {
        solver.try_bvslt(zero, x).expect("0 < x")
    };
    solver
        .try_assert_named(assumption, "__deductive_checks_assumption_0")
        .expect("Core's native named assumption");
    (solver, x, zero)
}

fn require_strict_unsat(solver: &Solver, details: &SolveDetails) {
    assert!(details.result.is_unsat(), "{details:?}");
    assert!(
        details.result.was_unsat_strictly_verified(),
        "the actual result needs a complete strict proof: {details:?}"
    );
    assert!(details
        .accept_for_consumer()
        .expect("checked UNSAT is consumable")
        .is_unsat());
    assert!(solver.executor.proof_reconstruction_step_budget.is_none());
}

fn check_native_history(boolean: bool) {
    // Core constructs its vacuity precheck separately from its main encoder.
    {
        let (mut precheck, _, _) = with_named_assumption(boolean);
        let details = precheck.check_sat_with_details();
        assert!(details.result.is_sat(), "{details:?}");
        assert!(details
            .accept_for_consumer()
            .expect("satisfiable precheck")
            .is_sat());
    }

    let (mut solver, x, zero) = with_named_assumption(boolean);
    let target = if boolean {
        let ten = solver.try_bv_const(10, 32).expect("signed upper bound");
        let below = solver.try_bvslt(x, zero).expect("x < 0");
        let above = solver.try_bvsle(ten, x).expect("10 <= x");
        solver.try_or(below, above).expect("outside the interval")
    } else {
        solver.try_bvslt(x, zero).expect("x < 0")
    };

    solver.try_push().expect("Core target frame");
    solver
        .try_assert_term(target)
        .expect("Core's unnamed target");
    let primary = solver.check_sat_with_details();
    require_strict_unsat(&solver, &primary);
    solver.try_pop().expect("remove only the target frame");

    // Removing the contradictory target must recover the satisfiable base.
    let restored = solver.check_sat_with_details();
    assert!(restored.result.is_sat(), "{restored:?}");
    assert!(restored
        .accept_for_consumer()
        .expect("restored base")
        .is_sat());

    // Exercise the same target as a genuinely temporary public assumption,
    // with named core tracking still active. Its proof cannot outlive this
    // query as an active premise of the following assumption-free query.
    let assumed = solver
        .try_check_sat_assuming_with_details(&[target])
        .expect("temporary contradictory assumption");
    require_strict_unsat(&solver, &assumed.solve);
    let after_assumption = solver.check_sat_with_details();
    assert!(after_assumption.result.is_sat(), "{after_assumption:?}");
    assert!(after_assumption
        .accept_for_consumer()
        .expect("no stale assumption")
        .is_sat());
    assert!(solver.executor.proof_reconstruction_step_budget.is_none());
}

#[test]
fn core_named_boolean_bounds_keep_bv_assumption_proof_leaves() {
    check_native_history(true);
}

#[test]
fn core_named_positive_bound_keeps_bv_assumption_proof_leaves() {
    check_native_history(false);
}
