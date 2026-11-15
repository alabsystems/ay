// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Wrong `unsat` on satisfiable UF + NIA inputs, every lane, found by the
//! row-D soundness review (fuzz family `nia3`, seed 4413) and reduced.
//!
//! The LRA's fixed-term export turned two same-valued fixings into the
//! equality `lhs = rhs` and cited the union of the two sides' reasons. A side
//! pinned by an NIA model guess (a patch pin on the monomial `x*e`) has no
//! reasons, so the union was the other side's alone: `d <= 0, d >= 0` was
//! exported as the reason for `x*d = x*e`. EUF merged it against the asserted
//! disequality and conflict analysis learned `d = 0 -> x*d = x*e`, which the
//! input does not imply. The divisor being a UF application is what made the
//! NIA pin the monomial; the exact-quotient division lemmas force `d = 0`
//! quickly, which is how the quantified EucDiv/Mul shapes reached it.
//!
//! Each `f*` fixture is a quantifier-free repro (z3 4.12.5 `sat`) with two
//! twins: `_model` pins z3's model and must answer `sat`, and `_unsat_twin`
//! changes one product so the forced `d = 0` refutes it, and must answer
//! `unsat`. Each `q*` fixture states the same kind of query Verus-style, with
//! the operators behind triggered universals; its `_ground` twin inlines the
//! definitions and is `sat` for z3. Neither may answer `unsat`. Every pin runs
//! in the default posture and in the proof-free competition posture.
//!
//! The review answered `unsat` on one reduction under every logic line it
//! tried, so the `logic_*` tests run a fixture again with each of those lines
//! in front: the logic picks the preprocessing route, and no route may refute.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn solve(src: &str, competition: bool) -> String {
    let commands = parse(src).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.set_competition_mode(competition);
    exec.set_timeout(Some(Duration::from_secs(10)));
    exec.set_memory_limit(Some(8 << 30));
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    outputs.last().cloned().unwrap_or_default()
}

fn assert_never_unsat(name: &str, src: &str) {
    for competition in [false, true] {
        let verdict = solve(src, competition);
        assert_ne!(
            verdict, "unsat",
            "{name} (competition={competition}) is satisfiable; AY must never answer unsat"
        );
    }
}

fn assert_verdict(name: &str, src: &str, expected: &str) {
    for competition in [false, true] {
        let verdict = solve(src, competition);
        assert_eq!(
            verdict, expected,
            "{name} (competition={competition}) must answer {expected}"
        );
    }
}

macro_rules! fixture {
    ($file:literal, $suffix:literal) => {
        include_str!(concat!(
            "ufnia_fixed_pair_fixtures/",
            $file,
            $suffix,
            ".smt2"
        ))
    };
}

/// A quantifier-free repro, its sat model twin and its unsat twin.
macro_rules! qf_repro {
    ($test:ident, $file:literal) => {
        #[test]
        #[timeout(240_000)]
        fn $test() {
            assert_never_unsat($file, fixture!($file, ""));
            assert_verdict(concat!($file, "_model"), fixture!($file, "_model"), "sat");
            assert_verdict(
                concat!($file, "_unsat_twin"),
                fixture!($file, "_unsat_twin"),
                "unsat",
            );
        }
    };
}

/// A Verus-style quantified repro and its ground sat twin.
macro_rules! quantified_repro {
    ($test:ident, $file:literal) => {
        #[test]
        #[timeout(240_000)]
        fn $test() {
            assert_never_unsat($file, fixture!($file, ""));
            assert_never_unsat(concat!($file, "_ground"), fixture!($file, "_ground"));
        }
    };
}

/// A quantifier-free repro and its twins with a logic line in front.
macro_rules! qf_repro_under_logic {
    ($test:ident, $file:literal, $logic:literal) => {
        #[test]
        #[timeout(240_000)]
        fn $test() {
            let with_logic = |src: &str| format!("(set-logic {})\n{src}", $logic);
            assert_never_unsat(
                concat!($file, " under ", $logic),
                &with_logic(fixture!($file, "")),
            );
            assert_verdict(
                concat!($file, "_model under ", $logic),
                &with_logic(fixture!($file, "_model")),
                "sat",
            );
            assert_verdict(
                concat!($file, "_unsat_twin under ", $logic),
                &with_logic(fixture!($file, "_unsat_twin")),
                "unsat",
            );
        }
    };
}

/// A Verus-style quantified repro with a logic line in front.
macro_rules! quantified_repro_under_logic {
    ($test:ident, $file:literal, $logic:literal) => {
        #[test]
        #[timeout(240_000)]
        fn $test() {
            let src = format!("(set-logic {})\n{}", $logic, fixture!($file, ""));
            assert_never_unsat(concat!($file, " under ", $logic), &src);
        }
    };
}

qf_repro!(bounds_pinned_divisor_is_not_unsat, "f01_min3_bounds");
qf_repro!(div_self_pinned_divisor_is_not_unsat, "f02_div_self");
qf_repro!(mod_mul_self_0204_is_not_unsat, "f03_mod_mul_self_0204");
qf_repro!(mod_mul_self_0000_is_not_unsat, "f04_mod_mul_self_0000");
qf_repro!(mod_mul_self_0006_is_not_unsat, "f05_mod_mul_self_0006");
qf_repro!(mod_mul_self_0043_is_not_unsat, "f06_mod_mul_self_0043");
qf_repro!(div_three_d_0002_is_not_unsat, "f07_div_three_d_0002");
qf_repro!(clip_divisor_is_not_unsat, "f08_nclip_div_self");
qf_repro!(array_read_divisor_is_not_unsat, "f09_array_divisor");
qf_repro!(
    div_self_free_dividend_is_not_unsat,
    "f10_div_self_free_dividend"
);

quantified_repro!(eucdiv_div_self_is_not_unsat, "q01_min2_eucdiv");
quantified_repro!(eucdiv_0016_is_not_unsat, "q02_eucdiv_0016");
quantified_repro!(eucdiv_0052_is_not_unsat, "q03_eucdiv_0052");
quantified_repro!(eucdiv_0055_is_not_unsat, "q04_eucdiv_0055");
quantified_repro!(eucdiv_0110_is_not_unsat, "q05_eucdiv_0110");
quantified_repro!(eucdiv_0193_is_not_unsat, "q06_eucdiv_0193");

qf_repro_under_logic!(logic_all_is_not_unsat, "f10_div_self_free_dividend", "ALL");
qf_repro_under_logic!(
    logic_qf_auflia_is_not_unsat,
    "f10_div_self_free_dividend",
    "QF_AUFLIA"
);
qf_repro_under_logic!(
    logic_qf_uflia_is_not_unsat,
    "f10_div_self_free_dividend",
    "QF_UFLIA"
);
qf_repro_under_logic!(
    logic_qf_ufnia_is_not_unsat,
    "f10_div_self_free_dividend",
    "QF_UFNIA"
);

quantified_repro_under_logic!(logic_all_eucdiv_is_not_unsat, "q01_min2_eucdiv", "ALL");
quantified_repro_under_logic!(
    logic_auflia_eucdiv_is_not_unsat,
    "q01_min2_eucdiv",
    "AUFLIA"
);
quantified_repro_under_logic!(logic_uflia_eucdiv_is_not_unsat, "q01_min2_eucdiv", "UFLIA");
quantified_repro_under_logic!(logic_ufnia_eucdiv_is_not_unsat, "q01_min2_eucdiv", "UFNIA");
