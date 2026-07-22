// Copyright 2026 Andrew Yates
// Fmla guarded-equivalence LRAT certificate boundary tests.

use super::*;
use crate::lrat_parser::LratStep;

const FMLA_PATH_NUM_VARS: usize = 28_141;

fn add_fmla_path_clauses(checker: &mut LratChecker, include_guard_units: bool) {
    // Original endpoint units from the Fmla chain.
    assert!(checker.add_original(1, &[lit(1)]));
    assert!(checker.add_original(37, &[lit(-7)]));

    // Guarded ternaries along the exact 4-edge path.
    assert!(checker.add_original(126_913, &[lit(-28_120), lit(-1), lit(1_297)]));
    assert!(checker.add_original(142_465, &[lit(-27_364), lit(-1_297), lit(2_593)]));
    assert!(checker.add_original(142_538, &[lit(-27_365), lit(-2_593), lit(1_303)]));
    assert!(checker.add_original(126_986, &[lit(-28_141), lit(-1_303), lit(7)]));

    if include_guard_units {
        assert!(checker.add_original(437_953, &[lit(28_120)]));
        assert!(checker.add_original(437_954, &[lit(27_364)]));
        assert!(checker.add_original(437_955, &[lit(27_365)]));
        assert!(checker.add_original(437_956, &[lit(28_141)]));
    }
}

fn fmla_guarded_path_proof() -> Vec<LratStep> {
    crate::lrat_parser::parse_text_lrat(
        "\
437957 -1 1297 0 126913 437953 0
437958 -1297 2593 0 142465 437954 0
437959 -2593 1303 0 142538 437955 0
437960 -1303 7 0 126986 437956 0
437961 0 1 437957 437958 437959 437960 37 0
",
    )
    .expect("embedded Fmla LRAT proof parses")
}

#[test]
fn fmla_guarded_path_augmented_units_verify_empty_clause() {
    let mut checker = LratChecker::new(FMLA_PATH_NUM_VARS);
    add_fmla_path_clauses(&mut checker, true);

    let steps = fmla_guarded_path_proof();
    assert!(checker.verify_proof(&steps));
    assert!(checker.derived_empty_clause());
    assert_eq!(checker.stats.failures, 0);
}

#[test]
fn fmla_guarded_path_without_augmented_units_rejects_missing_hints() {
    let mut checker = LratChecker::new(FMLA_PATH_NUM_VARS);
    add_fmla_path_clauses(&mut checker, false);

    let steps = fmla_guarded_path_proof();
    assert!(!checker.verify_proof(&steps));
    assert!(!checker.derived_empty_clause());
    assert_eq!(checker.stats.failures, 1);
}
