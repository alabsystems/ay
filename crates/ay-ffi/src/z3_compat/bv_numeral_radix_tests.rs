// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Radix parity for bit-vector numerals on the Z3-compatible C API.
//!
//! SMT-LIB 2.6 gives `#x` exactly 4 bits per digit and `#b` exactly 1 bit per
//! digit, so a BV numeral's *printed form encodes its sort*. Printing a
//! `(_ BitVec 5)` value 17 as `#x11` is not a cosmetic difference: that text
//! reparses as `(_ BitVec 8)`, and genuine z3 5.0.0 rejects it against a
//! width-5 declaration with
//! `Sorts (_ BitVec 5) and (_ BitVec 8) are incompatible`.
//!
//! Measured against genuine z3 5.0.0 (`Z3_ast_to_string`, byte-for-byte, over
//! every width 1..=64 plus 65/100/128 at values 0, 1, 2^(w-1) and 2^w-1):
//! z3 prints `#x` iff the width is a multiple of 4 and `#b` otherwise, at every
//! width — it never falls back to the indexed `(_ bvN w)` form.
//!
//! These tests exercise the real C entry points, not the internal formatter, so
//! they pin the path that regressed (the executor's term printer, which backs
//! `Z3_ast_to_string` and every sibling printer that can carry a numeral).

use std::{
    ffi::{CStr, CString},
    ptr,
};

use super::*;

/// The widths under test: every width 1..=64, plus representative widths above
/// the 64-bit boundary in both radix classes.
fn audit_widths() -> Vec<u32> {
    (1..=64).chain([65, 100, 128]).collect()
}

/// Decimal text for the values probed at `width`: 0, 1, 2^(width-1), 2^width-1.
fn audit_values(width: u32) -> Vec<num_bigint::BigUint> {
    use num_bigint::BigUint;
    let one = BigUint::from(1u8);
    let max = (&one << width) - &one;
    let mid = &one << (width - 1);
    let mut vals = vec![BigUint::from(0u8), one];
    if width > 1 {
        vals.push(mid);
        vals.push(max);
    }
    vals
}

/// Render an AST through the C API, requiring a non-null result.
///
/// # Safety
/// `c` must be a live context and `a` an AST it owns.
unsafe fn ast_text(c: Z3_context, a: Z3_ast) -> String {
    // SAFETY: caller guarantees `c`/`a` are live; `Z3_ast_to_string` returns a
    // NUL-terminated string owned by the context.
    unsafe {
        let p = Z3_ast_to_string(c, a);
        assert!(!p.is_null(), "Z3_ast_to_string returned null");
        CStr::from_ptr(p)
            .to_str()
            .expect("Z3_ast_to_string must return UTF-8")
            .to_string()
    }
}

/// The SMT-LIB 2.6 well-formed rendering of `value` at `width`, derived here
/// independently of the production formatter so the test is a real oracle.
fn expected_numeral(value: &num_bigint::BigUint, width: u32) -> String {
    if width.is_multiple_of(4) {
        let digits = (width / 4) as usize;
        format!("#x{:0>digits$}", value.to_str_radix(16))
    } else {
        let digits = width as usize;
        format!("#b{:0>digits$}", value.to_str_radix(2))
    }
}

#[test]
fn ast_to_string_prints_bv_numerals_in_the_sort_preserving_radix() {
    for width in audit_widths() {
        for value in audit_values(width) {
            // SAFETY: a fresh config/context per case; every handle below is
            // created by and owned by that context and used before it is
            // dropped.
            unsafe {
                let cfg = Z3_mk_config();
                let ctx = Z3_mk_context(cfg);
                Z3_del_config(cfg);

                let sort = Z3_mk_bv_sort(ctx, width);
                let dec =
                    CString::new(value.to_str_radix(10)).expect("decimal text has no interior NUL");
                let num = Z3_mk_numeral(ctx, dec.as_ptr(), sort);
                assert_ne!(num, 0, "Z3_mk_numeral failed at width {width}");

                let got = ast_text(ctx, num);
                let want = expected_numeral(&value, width);
                assert_eq!(
                    got, want,
                    "Z3_ast_to_string radix/width mismatch at (_ BitVec {width}) value {value}"
                );

                // The printed digit count must equal the declared width exactly:
                // one hex digit = 4 bits, one binary digit = 1 bit. A shorter or
                // longer literal denotes a different sort.
                let (prefix, digits) = got.split_at(2);
                let printed_bits = match prefix {
                    "#x" => digits.len() as u32 * 4,
                    "#b" => digits.len() as u32,
                    other => panic!("unexpected numeral prefix {other:?} in {got}"),
                };
                assert_eq!(
                    printed_bits, width,
                    "printed literal {got} denotes {printed_bits} bits, declared width is {width}"
                );

                Z3_del_context(ctx);
            }
        }
    }
}

#[test]
fn hex_is_used_exactly_when_the_width_is_a_multiple_of_four() {
    // The defect printed hex at every width. Pin both directions so a future
    // change cannot silently swap the radix rule back.
    for width in audit_widths() {
        // SAFETY: fresh context per width; all handles are owned by it.
        unsafe {
            let cfg = Z3_mk_config();
            let ctx = Z3_mk_context(cfg);
            Z3_del_config(cfg);
            let sort = Z3_mk_bv_sort(ctx, width);
            let one = CString::new("1").expect("literal has no interior NUL");
            let num = Z3_mk_numeral(ctx, one.as_ptr(), sort);
            let got = ast_text(ctx, num);
            if width.is_multiple_of(4) {
                assert!(
                    got.starts_with("#x"),
                    "width {width} is a multiple of 4 but printed {got}"
                );
            } else {
                assert!(
                    got.starts_with("#b"),
                    "width {width} is not a multiple of 4 but printed {got}; \
                     `#x` would reparse at a different width"
                );
            }
            Z3_del_context(ctx);
        }
    }
}

#[test]
fn sibling_printers_agree_with_ast_to_string_on_bv_numerals() {
    // Every printer that a BV numeral can reach must use the same rendering:
    // a solver dump, a model, a benchmark and a pattern all carry numerals into
    // text that consumers reparse.
    for width in [1u32, 3, 5, 7, 8, 13, 16, 31, 32, 65, 100] {
        // SAFETY: fresh context per width; all handles below are owned by it and
        // used before it is dropped.
        unsafe {
            let cfg = Z3_mk_config();
            let ctx = Z3_mk_context(cfg);
            Z3_del_config(cfg);

            let sort = Z3_mk_bv_sort(ctx, width);
            let dec = CString::new("1").expect("literal has no interior NUL");
            let num = Z3_mk_numeral(ctx, dec.as_ptr(), sort);
            let canonical = ast_text(ctx, num);

            let yname = CString::new("y").expect("name has no interior NUL");
            let y = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, yname.as_ptr()), sort);
            let eq = Z3_mk_eq(ctx, y, num);

            let solver = Z3_mk_solver(ctx);
            Z3_solver_inc_ref(ctx, solver);
            Z3_solver_assert(ctx, solver, eq);

            let mut surfaces: Vec<(&str, String)> = Vec::new();
            surfaces.push(("Z3_ast_to_string", ast_text(ctx, eq)));

            let dump = Z3_solver_to_string(ctx, solver);
            assert!(!dump.is_null(), "Z3_solver_to_string returned null");
            surfaces.push((
                "Z3_solver_to_string",
                CStr::from_ptr(dump)
                    .to_str()
                    .expect("solver dump must be UTF-8")
                    .to_string(),
            ));

            let bname = CString::new("b").expect("name has no interior NUL");
            let logic = CString::new("QF_BV").expect("logic has no interior NUL");
            let status = CString::new("unknown").expect("status has no interior NUL");
            let attrs = CString::new("").expect("attrs have no interior NUL");
            let bench = Z3_benchmark_to_smtlib_string(
                ctx,
                bname.as_ptr(),
                logic.as_ptr(),
                status.as_ptr(),
                attrs.as_ptr(),
                0,
                ptr::null(),
                eq,
            );
            assert!(
                !bench.is_null(),
                "Z3_benchmark_to_smtlib_string returned null"
            );
            surfaces.push((
                "Z3_benchmark_to_smtlib_string",
                CStr::from_ptr(bench)
                    .to_str()
                    .expect("benchmark text must be UTF-8")
                    .to_string(),
            ));

            let fname = CString::new("f").expect("name has no interior NUL");
            let domain = [sort];
            let f = Z3_mk_func_decl(
                ctx,
                Z3_mk_string_symbol(ctx, fname.as_ptr()),
                1,
                domain.as_ptr(),
                sort,
            );
            let args = [num];
            let app = Z3_mk_app(ctx, f, 1, args.as_ptr());
            let terms = [app];
            let pat = Z3_mk_pattern(ctx, 1, terms.as_ptr());
            let pat_text = Z3_pattern_to_string(ctx, pat);
            assert!(!pat_text.is_null(), "Z3_pattern_to_string returned null");
            surfaces.push((
                "Z3_pattern_to_string",
                CStr::from_ptr(pat_text)
                    .to_str()
                    .expect("pattern text must be UTF-8")
                    .to_string(),
            ));

            if Z3_solver_check(ctx, solver) == Z3_L_TRUE {
                let model = Z3_solver_get_model(ctx, solver);
                if !model.is_null() {
                    Z3_model_inc_ref(ctx, model);
                    let m = Z3_model_to_string(ctx, model);
                    assert!(!m.is_null(), "Z3_model_to_string returned null");
                    surfaces.push((
                        "Z3_model_to_string",
                        CStr::from_ptr(m)
                            .to_str()
                            .expect("model text must be UTF-8")
                            .to_string(),
                    ));
                }
            }

            for (name, text) in &surfaces {
                // Some surfaces legitimately render the value in the indexed
                // `(_ bvN w)` form; what must never happen is a `#`-literal
                // whose digit count contradicts the declared width.
                for tok in text
                    .split(|ch: char| ch.is_whitespace() || ch == '(' || ch == ')')
                    .filter(|t| t.starts_with("#x") || t.starts_with("#b"))
                {
                    let bits = if let Some(d) = tok.strip_prefix("#x") {
                        d.len() as u32 * 4
                    } else {
                        tok.len() as u32 - 2
                    };
                    assert_eq!(
                        bits, width,
                        "{name} emitted {tok} ({bits} bits) for a (_ BitVec {width}) value; \
                         canonical rendering is {canonical}"
                    );
                }
            }

            Z3_del_context(ctx);
        }
    }
}
