// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! These are REAL fresh frontend declaration-route controls, not a source
//! credential passed into the word checker. Bare TermStore membership and
//! Uninterpreted("RoundingMode") spelling cannot authenticate an original
//! script. The enclosing original reader must retain this reserved signature.

use ay_frontend::{parse, Context, ElaborateError};

fn rejects(input: &str) -> ElaborateError {
    let commands = parse(input).expect("hostile declaration syntax");
    let mut context = Context::new();
    commands
        .iter()
        .find_map(|command| context.process_command(command).err())
        .expect("actual fresh original declaration route refuses")
}

#[test]
fn original_frontend_rejects_counterfeit_rounding_sort_and_datatype_signatures() {
    for input in [
        "(declare-sort RoundingMode 0)",
        "(define-sort RoundingMode () Bool)",
        "(declare-datatype RoundingMode ((sixthMode)))",
        "(declare-datatypes ((Other 0) (RoundingMode 0)) (((other)) ((sixthMode))))",
    ] {
        assert!(
            matches!(rejects(input), ElaborateError::ReservedSymbol(name) if name == "RoundingMode")
        );
    }
}

#[test]
fn original_frontend_rejects_counterfeit_operator_and_rounding_literal_bindings() {
    for name in [
        "fp",
        "fp.add",
        "fp.sub",
        "fp.mul",
        "RNE",
        "RNA",
        "RTP",
        "RTN",
        "RTZ",
        "roundNearestTiesToEven",
        "roundNearestTiesToAway",
        "roundTowardPositive",
        "roundTowardNegative",
        "roundTowardZero",
    ] {
        for input in [
            format!("(declare-fun {name} () Bool)"),
            format!("(define-fun {name} () Bool true)"),
        ] {
            assert!(
                matches!(rejects(&input), ElaborateError::ReservedSymbol(actual) if actual == name)
            );
        }
    }
}

#[test]
fn ordinary_nominal_mode_and_wrong_sort_never_gain_five_value_theory_authority() {
    for mode in ["FakeMode", "Bool"] {
        let declarations = if mode == "FakeMode" {
            "(declare-sort FakeMode 0)"
        } else {
            ""
        };
        let input = format!(
            "{declarations} (declare-const rm {mode}) \
            (declare-const x (_ FloatingPoint 3 4)) (assert (= (fp.add rm x x) x))"
        );
        assert!(matches!(
            rejects(&input),
            ElaborateError::SortMismatch { .. }
        ));
    }
    // Context-free checker syntax recognition is intentionally NOT asserted
    // to reject fabricated nominal-declaration history it cannot observe.
}
