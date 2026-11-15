// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M2: the nested search (Fig. 8 recursion) end to end (default ON;
//! `--no-qlra-nested` turns it off). Its verdicts are SHADOW ONLY: every test here asserts the
//! recorded `qlra.shadow_verdict` against the known status, and that the
//! PUBLIC answer is never the opposite one (a nested `unsat` never publishes;
//! a nested `sat` publishes only if the quantified model gate confirms it).
//!
//! The micros are the plan's p2, n11, p10 and m7 (cvc5 1.3.0: unsat, sat, sat,
//! sat); the exemplars are verbatim SMT-LIB 2025 LRA files with `:status`.

use super::{run, LaneRun};

/// Run `smt` with the nested search switched on.
fn run_nested(smt: &str, legacy_ce_free_resolve: bool) -> LaneRun {
    let flags = ay_core::MiscCliFlags {
        no_qlra_nested: false,
        // The QSAT route (587104eaa) runs first and decides these fixtures;
        // these tests pin the nested-CEGQI lane, so take QSAT out of the way.
        no_qsat: true,
        no_quantifier_ce_free_resolve: !legacy_ce_free_resolve,
        ..ay_core::misc_cli_flags().clone()
    };
    let _guard = ay_core::misc_test_override::set(flags);
    run(smt)
}

fn assert_shadow(name: &str, smt: &str, expected: &str) {
    assert_shadow_with(name, smt, expected, true);
}

fn assert_shadow_with(name: &str, smt: &str, expected: &str, legacy_ce_free_resolve: bool) {
    let lane = run_nested(smt, legacy_ce_free_resolve);
    assert!(
        lane.recognized,
        "{name}: the lane must recognize the problem"
    );
    assert_eq!(
        lane.shadow.as_deref(),
        Some(expected),
        "{name}: shadow verdict (decline={:?})",
        lane.decline
    );
    let opposite = if expected == "sat" { "unsat" } else { "sat" };
    assert_ne!(lane.verdict, opposite, "{name}: WRONG public verdict");
    if expected == "unsat" {
        assert_ne!(
            lane.cert.as_deref(),
            Some("installed"),
            "{name}: a nested unsat must never publish through the M1 replay"
        );
    }
}

#[test]
fn p2_exists_forall_is_refuted_in_shadow() {
    assert_shadow(
        "p2",
        "(set-logic LRA)(assert (exists ((y Real)) (forall ((x Real)) (> y x))))(check-sat)",
        "unsat",
    );
}

#[test]
fn n11_forall_exists_open_interval_is_sat_in_shadow() {
    assert_shadow(
        "n11",
        "(set-logic LRA)(assert (forall ((x Real)) (exists ((y Real)) \
         (and (> y x) (< y (+ x 1))))))(check-sat)",
        "sat",
    );
}

#[test]
fn p10_forall_exists_upper_bound_is_sat_in_shadow() {
    assert_shadow(
        "p10",
        "(set-logic LRA)(assert (forall ((a Real)) (exists ((x Real)) (<= (+ x a) 3))))(check-sat)",
        "sat",
    );
}

#[test]
fn m7_forall_exists_unbounded_is_sat_in_shadow() {
    assert_shadow(
        "m7",
        "(set-logic LRA)(assert (forall ((x Real)) (exists ((y Real)) (> y x))))(check-sat)",
        "sat",
    );
}

macro_rules! exemplar {
    ($test:ident, $file:literal, $status:literal) => {
        #[test]
        fn $test() {
            assert_shadow(
                $file,
                include_str!(concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/tests/fixtures/quantifier/qlra/",
                    $file
                )),
                $status,
            );
        }
    };
}

exemplar!(
    mjollnir3_155_shadow_unsat,
    "mjollnir3_formula_155.smt2",
    "unsat"
);
exemplar!(
    mjollnir3_202_shadow_sat,
    "mjollnir3_formula_202.smt2",
    "sat"
);
/// The legacy path's `ce_free_vector_invariant_holds` debug assertion fires
/// on this file after the lane declines, with or without the nested search
/// (pre-existing on main @ 4c7343ad8; release builds decline instead), so
/// the legacy re-solve is switched off here: this test is about the shadow.
#[test]
fn mjollnir2_219_shadow_unsat() {
    assert_shadow_with(
        "mjollnir2_formula_219.smt2",
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/quantifier/qlra/mjollnir2_formula_219.smt2"
        )),
        "unsat",
        false,
    );
}
exemplar!(
    mjollnir4_252_shadow_unsat,
    "mjollnir4_formula_252.smt2",
    "unsat"
);
exemplar!(rndpre_3_3_shadow_sat, "RNDPRE_3_3.smt2", "sat");
exemplar!(rndpre_4_18_shadow_unsat, "RNDPRE_4_18.smt2", "unsat");
exemplar!(rnd_3_5_shadow_unsat, "RND_3_5.smt2", "unsat");
exemplar!(rnd_4_3_shadow_sat, "RND_4_3.smt2", "sat");

const FORALL_EXISTS: &str =
    "(set-logic LRA)(assert (forall ((x Real)) (exists ((y Real)) (> y x))))(check-sat)";

/// ON by default: a shape the depth-1 builder declines runs the nested
/// search without any flag.
#[test]
fn nested_search_is_on_by_default() {
    assert!(
        !ay_core::MiscCliFlags::default().no_qlra_nested,
        "the nested search is the default"
    );
    let flags = ay_core::MiscCliFlags {
        no_qlra_nested: false,
        ..ay_core::misc_cli_flags().clone()
    };
    let _guard = ay_core::misc_test_override::set(flags);
    let lane = run(FORALL_EXISTS);
    assert!(lane.recognized);
    assert_eq!(lane.shadow.as_deref(), Some("sat"), "the nested search ran");
}

/// The kill switch: with `--no-qlra-nested` the nested search never runs and
/// the lane is the depth-1-only lane.
#[test]
fn nested_search_is_off_under_the_kill_switch() {
    let flags = ay_core::MiscCliFlags {
        no_qlra_nested: true,
        ..ay_core::misc_cli_flags().clone()
    };
    let _guard = ay_core::misc_test_override::set(flags);
    let lane = run(FORALL_EXISTS);
    assert!(
        lane.recognized,
        "the depth-1 lane still recognizes the shape"
    );
    assert_eq!(lane.shadow, None, "no nested search under --no-qlra-nested");
    assert!(
        lane.decline
            .as_deref()
            .is_some_and(|d| d.starts_with("shape-")),
        "the depth-1 builder declines: {:?}",
        lane.decline
    );
}
