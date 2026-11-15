// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the T1 verification findings on text: numeral text,
//! string accessors and the identity of parsed declarations (see
//! `t1_repair_tests.rs` for the structural and declaration findings).

use std::ffi::{c_char, CStr};
use std::ptr;

use crate::z3_compat::*;

/// Fresh context; caller frees via `Z3_del_context`.
unsafe fn ctx() -> Z3_context {
    // SAFETY: standard config/context construction; config freed immediately.
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        c
    }
}

unsafe fn konst(c: Z3_context, name: &CStr, sort: Z3_sort) -> Z3_ast {
    // SAFETY: `c` is live and `name` NUL-terminated.
    unsafe { Z3_mk_const(c, Z3_mk_string_symbol(c, name.as_ptr()), sort) }
}

unsafe fn text(p: *const c_char) -> String {
    // SAFETY: `p` is a context-owned NUL-terminated string.
    unsafe { CStr::from_ptr(p).to_string_lossy().into_owned() }
}

/// `decl_probe2.py`: z3 parses decimal, scientific and blank-padded numeral
/// text; AY returned a NULL AST with no error.
#[test]
fn mk_numeral_reads_z3_numeral_text() {
    // SAFETY: every handle lives in one context.
    unsafe {
        let c = ctx();
        let (int, real) = (Z3_mk_int_sort(c), Z3_mk_real_sort(c));
        let cases: [(&CStr, i64, i64); 9] = [
            (c"0.5", 1, 2),
            (c"-0.5", -1, 2),
            (c"0.1", 1, 10),
            (c"1e2", 100, 1),
            (c"-1.25e1", -25, 2),
            (c".5", 1, 2),
            (c"2.", 2, 1),
            (c" 2", 2, 1),
            (c"3/6", 1, 2),
        ];
        for (literal, n, d) in cases {
            let got = Z3_mk_numeral(c, literal.as_ptr(), real);
            assert_eq!(Z3_get_error_code(c), Z3_OK, "{literal:?}");
            assert_eq!(got, Z3_mk_real(c, n as i32, d as i32), "{literal:?}");
        }
        assert_eq!(Z3_mk_numeral(c, c" 5".as_ptr(), int), Z3_mk_int(c, 5, int));
        assert_eq!(
            Z3_mk_numeral(c, c"1e2".as_ptr(), int),
            Z3_mk_int(c, 100, int)
        );
        for bad in [c"abc", c"", c"1/0", c"1e", c"--1"] {
            assert_eq!(Z3_mk_numeral(c, bad.as_ptr(), real), 0, "{bad:?}");
            assert_ne!(Z3_get_error_code(c), Z3_OK, "{bad:?}");
        }
        assert_eq!(Z3_mk_numeral(c, c"0.5".as_ptr(), int), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        Z3_del_context(c);
    }
}

/// `str_edge.py`: string accessors on a non-literal raise z3's
/// `Z3_INVALID_ARG` instead of reading as the empty literal; the unit of a
/// Char is a String.
#[test]
fn string_accessors_and_char_unit() {
    // SAFETY: every handle lives in one context; buffers outlive the calls.
    unsafe {
        let c = ctx();
        let zz = konst(c, c"zz", Z3_mk_string_sort(c));
        assert_eq!(text(Z3_get_string(c, zz)), "");
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        assert_eq!(Z3_get_string_length(c, zz), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        let mut buf = [0_u32; 2];
        Z3_get_string_contents(c, zz, 2, buf.as_mut_ptr());
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);

        let unit = Z3_mk_seq_unit(c, Z3_mk_char(c, 0x41));
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, unit)), Z3_SEQ_SORT);
        assert!(Z3_is_string_sort(c, Z3_get_sort(c, unit)));
        let lit = Z3_mk_string(c, c"A".as_ptr());
        let eq = Z3_mk_eq(c, unit, lit);
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        let simplified = Z3_simplify(c, unit);
        assert_eq!(Z3_get_string_length(c, simplified), 1);
        Z3_get_string_contents(c, simplified, 1, buf.as_mut_ptr());
        assert_eq!(buf[0], 0x41);
        let s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        Z3_solver_assert(c, s, Z3_mk_not(c, eq));
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE);
        Z3_solver_dec_ref(c, s);
        Z3_del_context(c);
    }
}

/// `shared_sym.py`, `sexpr_rt.py`: z3 identifies a declaration by its name
/// and signature. A parse redeclaring an earlier parse's constant reuses it
/// (it no longer fails and disables the context); `Z3_mk_const` of a parsed
/// constant is that constant; a parse declaring a name the API declared binds
/// to the API's constant instead of making a second, unrelated one.
#[test]
fn parsed_declarations_share_z3_identity() {
    // SAFETY: every handle lives in one context.
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let parse = |src: &CStr| {
            Z3_parse_smtlib2_string(
                c,
                src.as_ptr(),
                0,
                ptr::null(),
                ptr::null(),
                0,
                ptr::null(),
                ptr::null(),
            )
        };
        let v1 = parse(c"(declare-fun y () Int)(assert (> y 5))");
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        let v2 = parse(c"(declare-fun y () Int)(assert (< y 3))");
        assert_eq!(Z3_get_error_code(c), Z3_OK, "redeclaration across parses");
        let y = konst(c, c"y", int);
        let s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        assert_eq!(Z3_get_error_code(c), Z3_OK, "context still usable");
        Z3_solver_assert(c, s, Z3_ast_vector_get(c, v1, 0));
        Z3_solver_assert(c, s, Z3_mk_lt(c, y, Z3_mk_int(c, 3, int)));
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE, "API y is the parsed y");
        Z3_solver_reset(c, s);
        Z3_solver_assert(c, s, Z3_ast_vector_get(c, v1, 0));
        Z3_solver_assert(c, s, Z3_ast_vector_get(c, v2, 0));
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE, "both parses share y");

        // libz3 5.1.0 (measured with z3py's parse_smt2_string after
        // Int('x')): Z3_OK, one assertion, its `x` is the API's `x` (decl and
        // AST eq), and with `x < 3` the solver answers unsat.
        let x = konst(c, c"x", int);
        let v3 = parse(c"(declare-fun x () Int)(assert (> x 5))");
        assert_eq!(Z3_get_error_code(c), Z3_OK, "the parse binds the API's x");
        assert_eq!(Z3_ast_vector_size(c, v3), 1);
        Z3_solver_reset(c, s);
        Z3_solver_assert(c, s, Z3_ast_vector_get(c, v3, 0));
        Z3_solver_assert(c, s, Z3_mk_lt(c, x, Z3_mk_int(c, 3, int)));
        assert_eq!(Z3_solver_check(c, s), Z3_L_FALSE, "API x is the parsed x");
        Z3_solver_dec_ref(c, s);
        Z3_del_context(c);
    }
}

/// `is_expr(FPVal(1.0))`: z3py sends FloatingPoint numerals to
/// `Z3_mk_numeral` as `<rational>p<exponent>` (`1/1p0`). Rational inputs round
/// once to the target format; malformed text remains an error. The maintained
/// C consumer also checks the exact binary32 encoding against pinned Z3.
#[test]
fn mk_numeral_reads_floating_point_text() {
    // SAFETY: every handle lives in one context.
    unsafe {
        let c = ctx();
        let f32_sort = Z3_mk_fpa_sort_32(c);
        for (literal, value) in [
            (c"1/1p0", 1.0),
            (c"3/2p1", 3.0),
            (c"-1/4p0", -0.25),
            (c"5p-3", 0.625),
            (c"0p0", 0.0),
            (c"1/3p0", 1.0 / 3.0),
        ] {
            let got = Z3_mk_numeral(c, literal.as_ptr(), f32_sort);
            assert_eq!(Z3_get_error_code(c), Z3_OK, "{literal:?}");
            assert_eq!(
                got,
                Z3_mk_fpa_numeral_double(c, value, f32_sort),
                "{literal:?}"
            );
        }
        for bad in [c"1p", c"xp0"] {
            assert_eq!(Z3_mk_numeral(c, bad.as_ptr(), f32_sort), 0, "{bad:?}");
            assert_ne!(Z3_get_error_code(c), Z3_OK, "{bad:?}");
        }
        Z3_del_context(c);
    }
}
