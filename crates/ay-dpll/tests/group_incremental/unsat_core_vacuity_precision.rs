// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pinning tests for unsat-core semantics under the cores redirect
//! (#vacuity-core-precision).
//!
//! `get-unsat-core` feeds verifier vacuity detection (verification-consumer
//! `is_vacuous_unsat`: a proof is vacuous iff the negated-goal label is
//! ABSENT from the core). These tests pin the core shapes that detection
//! depends on:
//!
//! (a) named premises contradictory, goal irrelevant -> core EXCLUDES the
//!     goal name (vacuity detectable on the SAT-harvested path);
//! (b) DOCUMENTED LIMITATION: unnamed base assertions contradictory alone
//!     -> the core is PADDED to all named assertions (so it contains the
//!     irrelevant goal name). An honest empty `()` is not currently
//!     possible because theory-level conflicts can prove UNSAT with an
//!     empty SAT-level core even when assumptions ARE load-bearing (EUF
//!     transitivity does), so empty cannot be distinguished from lost
//!     tracking without origin-tagged authority (future work). CONSUMER
//!     CONSEQUENCE: goal-name-in-core is NOT evidence of non-vacuity;
//!     verifiers must base-recheck before accepting a proof as genuine
//!     (verification-consumer's solve paths do);
//! (c) goal genuinely load-bearing -> goal name IS in the core.

#![allow(deprecated)]

use ay_dpll::api::{Logic, Solver, Sort};
use ntest::timeout;

/// (a) Premise-contradiction vacuity: x>0 and x<0 are named and contradict
/// each other; the named "goal" y>5 is irrelevant to the refutation. The
/// harvested core must exclude the goal name so vacuity detection can fire.
#[test]
#[timeout(15_000)]
fn core_excludes_irrelevant_goal_when_named_premises_contradict() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let zero = solver.int_const(0);
    let five = solver.int_const(5);

    let x_pos = solver.gt(x, zero);
    solver
        .try_assert_named(x_pos, "premise_x_positive")
        .unwrap();
    let x_neg = solver.lt(x, zero);
    solver
        .try_assert_named(x_neg, "premise_x_negative")
        .unwrap();
    let goal = solver.gt(y, five);
    solver.try_assert_named(goal, "negated_goal").unwrap();

    assert!(solver.check_sat().is_unsat(), "x>0 AND x<0 must be unsat");

    let core = solver.try_get_unsat_core().expect("core must be available");
    assert!(
        !core.iter().any(|n| n == "negated_goal"),
        "irrelevant goal must NOT be in the core (vacuity must be \
         detectable); got core {core:?}"
    );
    assert!(
        core.iter().any(|n| n.starts_with("premise_x_")),
        "the contradicting premises must be in the core; got {core:?}"
    );
}

/// (b) Padding limitation pin: the UNNAMED base alone is contradictory; the
/// only named assertion is the (irrelevant) goal. The core comes back PADDED
/// to all named assertions — i.e. it CONTAINS the irrelevant goal name.
///
/// This pins a documented LIMITATION, not an ideal: an honest empty `()`
/// cannot currently be distinguished from lost assumption tracking, because
/// theory-level conflicts legitimately produce empty SAT-level cores while
/// every assumption is load-bearing (see the EUF transitivity annotated-core
/// test). The consumer consequence is the important part: a verifier's
/// vacuity check MUST NOT treat goal-name-in-core as proof of non-vacuity —
/// an independent base-recheck (assert base without the negated goal, check
/// SAT) is required before accepting a proof as genuine. If this test ever
/// fails because the core became honestly empty, ay has gained origin-tagged
/// core authority — update verification-consumer's vacuity contract notes accordingly.
#[test]
#[timeout(15_000)]
fn padded_core_contains_irrelevant_goal_when_unnamed_base_alone_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let zero = solver.int_const(0);
    let five = solver.int_const(5);

    // UNNAMED contradictory base.
    let x_pos = solver.gt(x, zero);
    solver.assert_term(x_pos);
    let x_neg = solver.lt(x, zero);
    solver.assert_term(x_neg);
    // Named but irrelevant goal.
    let goal = solver.gt(y, five);
    solver.try_assert_named(goal, "negated_goal").unwrap();

    assert!(
        solver.check_sat().is_unsat(),
        "unnamed x>0 AND x<0 must be unsat"
    );

    let core = solver.try_get_unsat_core().expect("core must be available");
    assert!(
        core.iter().any(|n| n == "negated_goal"),
        "PINNED LIMITATION: base-alone-UNSAT currently pads the core to all \
         named assertions, so the irrelevant goal name appears in it. If \
         this assertion fails with an EMPTY core, ay gained origin-tagged \
         core authority -- great; flip this test to pin `()` and notify \
         verifier consumers; got {core:?}"
    );
}

/// (c) Genuine proof: the goal is load-bearing (x>0 named premise, x<0 as
/// the negated goal). The core must contain the goal name so the proof is
/// classified non-vacuous.
#[test]
#[timeout(15_000)]
fn core_contains_goal_when_goal_is_load_bearing() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);

    let x_pos = solver.gt(x, zero);
    solver
        .try_assert_named(x_pos, "premise_x_positive")
        .unwrap();
    let goal = solver.lt(x, zero);
    solver.try_assert_named(goal, "negated_goal").unwrap();

    assert!(solver.check_sat().is_unsat(), "x>0 AND x<0 must be unsat");

    let core = solver.try_get_unsat_core().expect("core must be available");
    assert!(
        core.iter().any(|n| n == "negated_goal"),
        "load-bearing goal must be in the core (genuine, non-vacuous \
         proof); got {core:?}"
    );
}
