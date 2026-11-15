// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the T5 design's P0.2 quarantine, implementer X
//! (`~/ay-bench/campaign/2026-10-02-T5-DESIGN.md` §4 P0.2), item Q4 for the
//! Boolean connectives: a non-Bool operand is a sort error, never a panic,
//! and `Z3_mk_iff` is z3's `=`, with `to_real` on an Int beside a Real.
//!
//! The pins are `q4_bool_pins.py` (`~/ay-bench/campaign/t5design-probes/t5x/`,
//! with its `*.real.out` from z3-solver 5.1.0.0 via that directory's
//! `run.py`): z3 answers "Sort mismatch at argument #1 for function
//! (declare-fun not (Bool) Bool)" (and likewise for and, or, =>, xor),
//! "invalid non-Boolean sort applied to Pseudo-Boolean relation", `(= bx by)`
//! for `Z3_mk_iff(bx:Int, by:Int)` and `(= (to_real bx) br)` for an Int
//! beside a Real. AY panicked in its builders for each refused operand and
//! for the Int/Real `iff` ("panic in FFI: sort mismatch in ..."). The last
//! test pins the zero-argument `Z3_mk_add` / `Z3_mk_mul` error.

use super::t5x_quarantine_support::*;

/// Each Boolean connective refuses an Int operand with `Z3_SORT_ERROR` and no
/// panic, and the context keeps working afterwards (z3: sat).
#[test]
fn q4_bool_connectives_refuse_non_bool_operands() {
    // SAFETY: every handle lives in `c`; arrays outlive each call.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let (x, y) = (konst(c, c"bx", int_sort), konst(c, c"by", int_sort));
        let p = konst(c, c"bp", Z3_mk_bool_sort(c));
        let pair = [x, y];
        let mixed = [x, p];
        for (label, built) in [
            ("not", Z3_mk_not(c, x)),
            ("and", Z3_mk_and(c, 2, pair.as_ptr())),
            ("or", Z3_mk_or(c, 2, mixed.as_ptr())),
            ("implies", Z3_mk_implies(c, x, y)),
            ("xor", Z3_mk_xor(c, x, y)),
            ("atmost", Z3_mk_atmost(c, 2, pair.as_ptr(), 1)),
            ("pble", Z3_mk_pble(c, 2, pair.as_ptr(), [1, 1].as_ptr(), 1)),
        ] {
            assert_eq!(built, 0, "{label}");
            assert_eq!(Z3_get_error_code(c), Z3_SORT_ERROR, "{label}");
            assert!(
                !error_text(c).contains("panic"),
                "{label}: {}",
                error_text(c)
            );
        }
        assert_eq!(check(c, &[Z3_mk_gt(c, x, int(c, 1))]), Z3_L_TRUE, "z3: sat");
        Z3_del_context(c);
    }
}

/// `Z3_mk_iff` is `=` over any one sort (z3: `(= bx by)` for Int operands),
/// and coerces an Int beside a Real (`(= (to_real bx) br)`), so `bx = 1, by =
/// 2` refutes `iff(bx, by)` and `br = 1/2` refutes `iff(bx, br)` (z3: unsat
/// both). AY panicked on the Int/Real pair. A Bool beside an Int, which z3
/// coerces to `(ite b 1 0)`, AY refuses.
#[test]
fn q4_iff_is_equality_with_to_real() {
    // SAFETY: every handle lives in `c`.
    unsafe {
        let c = ctx();
        let int_sort = Z3_mk_int_sort(c);
        let (x, y) = (konst(c, c"bx", int_sort), konst(c, c"by", int_sort));
        let r = konst(c, c"br", Z3_mk_real_sort(c));
        let same = Z3_mk_iff(c, x, y);
        assert_ne!(same, 0, "{}", error_text(c));
        let facts = [same, Z3_mk_eq(c, x, int(c, 1)), Z3_mk_eq(c, y, int(c, 2))];
        assert_eq!(check(c, &facts), Z3_L_FALSE, "z3: unsat");
        let mixed = Z3_mk_iff(c, x, r);
        assert_ne!(mixed, 0, "{}", error_text(c));
        assert!(
            text(c, mixed).contains("(to_real bx)"),
            "{}",
            text(c, mixed)
        );
        assert_eq!(
            check(c, &[mixed, Z3_mk_eq(c, r, real(c, 1, 2))]),
            Z3_L_FALSE,
            "z3: unsat"
        );
        assert_eq!(
            check(c, &[mixed, Z3_mk_eq(c, r, int_real(c, 3))]),
            Z3_L_TRUE,
            "z3: sat"
        );
        let p = konst(c, c"bp", Z3_mk_bool_sort(c));
        assert_eq!(Z3_mk_iff(c, p, x), 0);
        assert_eq!(Z3_get_error_code(c), Z3_SORT_ERROR);
        Z3_del_context(c);
    }
}

/// `Z3_mk_add` / `Z3_mk_mul` with no argument is an error (z3: "no arguments
/// supplied to arithmetical operator", `q4_app_pins.py`). AY returned null
/// with the error code of an earlier call still set.
#[test]
fn q4_nary_arithmetic_without_arguments_is_an_error() {
    // SAFETY: `c` is live; a null argument array with a zero count is legal.
    unsafe {
        let c = ctx();
        for (label, built) in [
            ("add", Z3_mk_add(c, 0, std::ptr::null())),
            ("mul", Z3_mk_mul(c, 0, std::ptr::null())),
        ] {
            assert_eq!(built, 0, "{label}");
            assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG, "{label}");
            assert!(error_text(c).contains("no arguments"), "{}", error_text(c));
        }
        Z3_del_context(c);
    }
}
