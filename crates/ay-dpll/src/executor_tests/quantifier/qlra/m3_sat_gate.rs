// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M3b: a nested `sat` (nested search on, the default) PUBLISHES through the
//! quantified model gate, whose confirm-only expansion route refutes the
//! Herbrand expansion of each negated authored conjunct built from the
//! search's instance log (untrusted hints). Each publishing test also reads
//! the lane's statistics, so the verdict is the lane's and — where the
//! existing routes cannot decide the conjunct — the expansion route's.
//!
//! The micros are the plan's n11, p10 and m7 (cvc5 1.3.0: sat); the
//! exemplars are verbatim SMT-LIB 2025 LRA files with `:status sat`. Forged
//! and false-model hints are covered against the route itself in
//! `independent_gate/expansion_route_tests.rs`.

use super::{run, run_with, LaneRun};

fn run_nested(smt: &str, z3_mode: bool) -> LaneRun {
    let flags = ay_core::MiscCliFlags {
        no_qlra_nested: false,
        // The QSAT route (587104eaa) runs first and decides these fixtures;
        // these tests pin the nested-CEGQI lane, so take QSAT out of the way.
        no_qsat: true,
        ..ay_core::misc_cli_flags().clone()
    };
    let _guard = ay_core::misc_test_override::set(flags);
    run_with(smt, z3_mode)
}

/// The lane's nested search found `sat`, and the lane's gate arm published
/// it. `through_expansion`: the expansion route confirmed at least one
/// conjunct (the existing routes alone do not decide it).
fn assert_published_sat(name: &str, smt: &str, through_expansion: bool) -> LaneRun {
    let lane = run_nested(smt, false);
    assert_eq!(
        lane.shadow.as_deref(),
        Some("sat"),
        "{name}: shadow verdict"
    );
    assert_eq!(
        lane.verdict, "sat",
        "{name}: public verdict (gate={:?} decline={:?} xp={}/{})",
        lane.gate, lane.decline, lane.xp_confirmed, lane.xp_consulted
    );
    assert_eq!(
        lane.gate.as_deref(),
        Some("confirmed"),
        "{name}: the lane's gate arm must be the publisher"
    );
    if through_expansion {
        assert!(
            lane.xp_confirmed >= 1,
            "{name}: the expansion route must confirm (consulted {})",
            lane.xp_consulted
        );
    }
    lane
}

const N11: &str = "(set-logic LRA)(assert (forall ((x Real)) (exists ((y Real)) \
                   (and (> y x) (< y (+ x 1))))))(check-sat)";
const P10: &str =
    "(set-logic LRA)(assert (forall ((a Real)) (exists ((x Real)) (<= (+ x a) 3))))(check-sat)";
const M7: &str =
    "(set-logic LRA)(assert (forall ((x Real)) (exists ((y Real)) (> y x))))(check-sat)";

#[test]
fn n11_open_interval_publishes_sat() {
    assert_published_sat("n11", N11, true);
}

#[test]
fn p10_upper_bound_publishes_sat() {
    assert_published_sat("p10", P10, true);
}

#[test]
fn m7_unbounded_publishes_sat() {
    assert_published_sat("m7", M7, true);
}

/// The CLI's `--z3-mode` posture (no parsed-assertion retention, proof-cycle
/// shedding) publishes the same way.
#[test]
fn n11_publishes_sat_under_z3_mode() {
    let lane = run_nested(N11, true);
    assert_eq!(lane.verdict, "sat", "gate={:?}", lane.gate);
    assert!(lane.xp_confirmed >= 1, "consulted {}", lane.xp_consulted);
}

macro_rules! exemplar {
    ($test:ident, $file:literal, $through_expansion:literal) => {
        #[test]
        fn $test() {
            assert_published_sat(
                $file,
                include_str!(concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/tests/fixtures/quantifier/qlra/",
                    $file
                )),
                $through_expansion,
            );
        }
    };
}

exemplar!(rndpre_3_3_publishes_sat, "RNDPRE_3_3.smt2", true);
exemplar!(rnd_4_3_publishes_sat, "RND_4_3.smt2", true);
exemplar!(
    mjollnir3_202_publishes_sat,
    "mjollnir3_formula_202.smt2",
    true
);

/// Under the kill switch (`--no-qlra-nested`) no hint is ever installed, so
/// the route is never consulted and the answer path is the depth-1 one.
#[test]
fn the_route_is_inert_under_the_kill_switch() {
    let flags = ay_core::MiscCliFlags {
        no_qlra_nested: true,
        ..ay_core::misc_cli_flags().clone()
    };
    let _guard = ay_core::misc_test_override::set(flags);
    let lane = run(N11);
    assert_eq!(lane.shadow, None);
    assert_eq!(lane.xp_consulted, 0);
    assert_ne!(lane.verdict, "unsat", "n11 is sat");
}
