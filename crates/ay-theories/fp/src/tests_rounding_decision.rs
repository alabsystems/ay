// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests_support::{extract_lit, solve_fp_clauses};
use super::*;

fn test_rounding_decision(
    rm: RoundingMode,
    sign_val: bool,
    last_val: bool,
    round_val: bool,
    sticky_val: bool,
) -> bool {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);

    let sgn = solver.fresh_var();
    solver.add_clause(CnfClause::unit(if sign_val { sgn } else { -sgn }));

    let last = solver.fresh_var();
    solver.add_clause(CnfClause::unit(if last_val { last } else { -last }));

    let round = solver.fresh_var();
    solver.add_clause(CnfClause::unit(if round_val { round } else { -round }));

    let sticky = solver.fresh_var();
    solver.add_clause(CnfClause::unit(if sticky_val { sticky } else { -sticky }));

    let inc = solver.make_rounding_decision(rm, sgn, last, round, sticky);
    let model = solve_fp_clauses(&solver);
    extract_lit(&model, inc)
}

#[test]
fn test_rounding_decision_rne() {
    for sign in [false, true] {
        assert!(!test_rounding_decision(
            RoundingMode::RNE,
            sign,
            false,
            false,
            false
        ));
        assert!(!test_rounding_decision(
            RoundingMode::RNE,
            sign,
            false,
            false,
            true
        ));
        assert!(!test_rounding_decision(
            RoundingMode::RNE,
            sign,
            false,
            true,
            false
        ));
        assert!(
            !test_rounding_decision(RoundingMode::RNE, sign, false, true, false),
            "RNE: tie with even last should NOT increment"
        );
        assert!(
            test_rounding_decision(RoundingMode::RNE, sign, false, true, true),
            "RNE: round=1, sticky=1 (above halfway) should increment"
        );
        assert!(!test_rounding_decision(
            RoundingMode::RNE,
            sign,
            true,
            false,
            false
        ));
        assert!(!test_rounding_decision(
            RoundingMode::RNE,
            sign,
            true,
            false,
            true
        ));
        assert!(
            test_rounding_decision(RoundingMode::RNE, sign, true, true, false),
            "RNE: tie with odd last should increment (round to even)"
        );
        assert!(
            test_rounding_decision(RoundingMode::RNE, sign, true, true, true),
            "RNE: round=1, last=1, sticky=1 should increment"
        );
    }
}

#[test]
fn test_rounding_decision_rna() {
    for sign in [false, true] {
        assert!(!test_rounding_decision(
            RoundingMode::RNA,
            sign,
            false,
            false,
            false
        ));
        assert!(!test_rounding_decision(
            RoundingMode::RNA,
            sign,
            false,
            false,
            true
        ));
        assert!(
            test_rounding_decision(RoundingMode::RNA, sign, false, true, false),
            "RNA: round=1 should always increment"
        );
        assert!(test_rounding_decision(
            RoundingMode::RNA,
            sign,
            false,
            true,
            true
        ));
        assert!(!test_rounding_decision(
            RoundingMode::RNA,
            sign,
            true,
            false,
            false
        ));
        assert!(!test_rounding_decision(
            RoundingMode::RNA,
            sign,
            true,
            false,
            true
        ));
        assert!(
            test_rounding_decision(RoundingMode::RNA, sign, true, true, false),
            "RNA: round=1 should always increment"
        );
        assert!(test_rounding_decision(
            RoundingMode::RNA,
            sign,
            true,
            true,
            true
        ));
    }
}

#[test]
fn test_rounding_decision_rtp() {
    for (last_val, round_val, sticky_val) in [
        (false, false, false),
        (false, false, true),
        (false, true, false),
        (false, true, true),
        (true, false, false),
        (true, false, true),
        (true, true, false),
        (true, true, true),
    ] {
        let has_remainder = round_val || sticky_val;
        assert_eq!(
            test_rounding_decision(RoundingMode::RTP, false, last_val, round_val, sticky_val),
            has_remainder
        );
        assert!(!test_rounding_decision(
            RoundingMode::RTP,
            true,
            last_val,
            round_val,
            sticky_val
        ));
    }
}

#[test]
fn test_rounding_decision_rtn() {
    for (last_val, round_val, sticky_val) in [
        (false, false, false),
        (false, false, true),
        (false, true, false),
        (false, true, true),
        (true, false, false),
        (true, false, true),
        (true, true, false),
        (true, true, true),
    ] {
        let has_remainder = round_val || sticky_val;
        assert!(!test_rounding_decision(
            RoundingMode::RTN,
            false,
            last_val,
            round_val,
            sticky_val
        ));
        assert_eq!(
            test_rounding_decision(RoundingMode::RTN, true, last_val, round_val, sticky_val),
            has_remainder
        );
    }
}

#[test]
fn test_rounding_decision_rtz() {
    for sign in [false, true] {
        for (last_val, round_val, sticky_val) in [
            (false, false, false),
            (false, false, true),
            (false, true, false),
            (false, true, true),
            (true, false, false),
            (true, false, true),
            (true, true, false),
            (true, true, true),
        ] {
            assert!(!test_rounding_decision(
                RoundingMode::RTZ,
                sign,
                last_val,
                round_val,
                sticky_val
            ));
        }
    }
}
