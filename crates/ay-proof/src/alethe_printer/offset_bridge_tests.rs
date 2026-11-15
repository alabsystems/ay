// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn the_printed_factor_is_read_off_the_printed_atoms() {
    let w = 64;
    // frame + 31 = vbase + 1  as  (vbase - frame) = 30, with lhs - rhs = -(d - k).
    let lhs = "(bvadd (bvadd (_ bv24 64) (_ bv7 64)) frame)";
    let rhs = "(bvadd (_ bv1 64) vbase)";
    let ones = format!("(_ bv{} 64)", u64::MAX);
    assert_eq!(
        printed_factor(lhs, rhs, "(bvsub vbase frame)", "(_ bv30 64)", w),
        Some(ones)
    );
    assert_eq!(
        printed_factor(rhs, lhs, "(bvsub vbase frame)", "(_ bv30 64)", w),
        Some("(_ bv1 64)".to_string())
    );
    // A wrong constant, a wrong word, or a wrong width is no bridge.
    assert_eq!(
        printed_factor(lhs, rhs, "(bvsub vbase frame)", "(_ bv31 64)", w),
        None
    );
    assert_eq!(
        printed_factor(lhs, rhs, "(bvsub vbase frame2)", "(_ bv30 64)", w),
        None
    );
    assert_eq!(
        printed_factor(lhs, rhs, "(bvsub vbase frame)", "(_ bv30 32)", w),
        None
    );
    // The literal spellings the printer emits all read as their values.
    assert_eq!(
        printed_factor(
            "(bvadd #x0001 x)",
            "y",
            "(bvsub y x)",
            "#b0000000000000001",
            16
        ),
        Some(format!("(_ bv{} 16)", u16::MAX))
    );
}

#[test]
fn integer_cancellation_does_not_drop_modular_zero_monomials() {
    assert_eq!(
        printed_factor("(bvadd b b)", "(_ bv0 1)", "a", "a", 1),
        None
    );
    for width in [1, 8, 64, 128] {
        let lhs = "(bvsub (bvadd a c) b)";
        let rhs = "(bvadd (bvsub c b) a)";
        assert_eq!(
            printed_factor(lhs, rhs, "a", "a", width),
            Some(format!("(_ bv1 {width})"))
        );
    }
    // Negation must retain a modular-zero monomial's support as well.
    assert!(printed_factor(
        "(bvadd b b)",
        "(_ bv0 1)",
        "(bvneg (bvadd b b))",
        "(_ bv0 1)",
        1
    )
    .is_some());
}
