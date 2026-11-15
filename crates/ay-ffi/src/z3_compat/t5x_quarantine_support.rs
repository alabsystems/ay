// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared helpers of the T5 P0.2 quarantine regression tests
//! (`t5x_quarantine_q1_tests.rs`, `t5x_quarantine_q34_tests.rs`).

use std::ffi::{c_int, c_uint, CStr};
use std::ptr;

pub(super) use crate::z3_compat::*;

/// Fresh context; caller frees via `Z3_del_context`.
pub(super) unsafe fn ctx() -> Z3_context {
    // SAFETY: standard config/context construction; config freed immediately.
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        c
    }
}

pub(super) unsafe fn sym(c: Z3_context, name: &CStr) -> Z3_symbol {
    // SAFETY: `c` is live and `name` NUL-terminated.
    unsafe { Z3_mk_string_symbol(c, name.as_ptr()) }
}

pub(super) unsafe fn konst(c: Z3_context, name: &CStr, sort: Z3_sort) -> Z3_ast {
    // SAFETY: `c` is live and `name` NUL-terminated.
    unsafe { Z3_mk_const(c, sym(c, name), sort) }
}

pub(super) unsafe fn text(c: Z3_context, a: Z3_ast) -> String {
    // SAFETY: `a` is a live AST of `c`; the string is context-owned.
    unsafe {
        CStr::from_ptr(Z3_ast_to_string(c, a))
            .to_string_lossy()
            .into_owned()
    }
}

pub(super) unsafe fn error_text(c: Z3_context) -> String {
    // SAFETY: `c` is live; the message is context-owned.
    unsafe {
        CStr::from_ptr(Z3_get_error_msg(c, Z3_get_error_code(c)))
            .to_string_lossy()
            .into_owned()
    }
}

/// The verdict of a fresh solver over `assertions`.
pub(super) unsafe fn check(c: Z3_context, assertions: &[Z3_ast]) -> c_int {
    // SAFETY: every assertion is a live Bool AST of `c`.
    unsafe {
        let s = Z3_mk_solver(c);
        Z3_solver_inc_ref(c, s);
        for &a in assertions {
            Z3_solver_assert(c, s, a);
        }
        let r = Z3_solver_check(c, s);
        Z3_solver_dec_ref(c, s);
        r
    }
}

pub(super) unsafe fn not(c: Z3_context, a: Z3_ast) -> Z3_ast {
    // SAFETY: `a` is a live Bool AST of `c`.
    unsafe { Z3_mk_not(c, a) }
}

/// `Z3_mk_quantifier` over de Bruijn declarations (names innermost last).
pub(super) unsafe fn db_quantifier(
    c: Z3_context,
    is_forall: bool,
    sorts: &[Z3_sort],
    names: &[&CStr],
    patterns: &[Z3_pattern],
    body: Z3_ast,
) -> Z3_ast {
    // SAFETY: the arrays outlive the call and hold live handles of `c`.
    unsafe {
        let symbols: Vec<Z3_symbol> = names.iter().map(|name| sym(c, name)).collect();
        Z3_mk_quantifier(
            c,
            is_forall,
            0,
            patterns.len() as c_uint,
            if patterns.is_empty() {
                ptr::null()
            } else {
                patterns.as_ptr()
            },
            sorts.len() as c_uint,
            sorts.as_ptr(),
            symbols.as_ptr(),
            body,
        )
    }
}

/// `Z3_mk_lambda` over one de Bruijn declaration.
pub(super) unsafe fn db_lambda(c: Z3_context, sort: Z3_sort, name: &CStr, body: Z3_ast) -> Z3_ast {
    // SAFETY: the one-element arrays outlive the call.
    unsafe {
        let symbol = sym(c, name);
        Z3_mk_lambda(c, 1, &raw const sort, &raw const symbol, body)
    }
}

pub(super) unsafe fn add(c: Z3_context, args: &[Z3_ast]) -> Z3_ast {
    // SAFETY: `args` holds live ASTs of `c`.
    unsafe { Z3_mk_add(c, args.len() as c_uint, args.as_ptr()) }
}

pub(super) unsafe fn int(c: Z3_context, v: i32) -> Z3_ast {
    // SAFETY: `c` is live.
    unsafe { Z3_mk_int(c, v, Z3_mk_int_sort(c)) }
}

/// The Real numeral `v`.
pub(super) unsafe fn int_real(c: Z3_context, v: i32) -> Z3_ast {
    // SAFETY: `c` is live.
    unsafe { Z3_mk_real(c, v, 1) }
}

pub(super) unsafe fn real(c: Z3_context, num: i32, den: i32) -> Z3_ast {
    // SAFETY: `c` is live.
    unsafe { Z3_mk_real(c, num, den) }
}

pub(super) unsafe fn subst(
    c: Z3_context,
    t: Z3_ast,
    from: &[Z3_ast],
    to: &[Z3_ast],
) -> (Z3_ast, c_uint) {
    // SAFETY: `from`/`to` hold `from.len()` live ASTs of `c`.
    unsafe {
        let r = Z3_substitute(c, t, from.len() as c_uint, from.as_ptr(), to.as_ptr());
        (r, Z3_get_error_code(c))
    }
}

pub(super) unsafe fn update(c: Z3_context, t: Z3_ast, args: &[Z3_ast]) -> (Z3_ast, c_uint) {
    // SAFETY: `args` holds live ASTs of `c`.
    unsafe {
        let r = Z3_update_term(c, t, args.len() as c_uint, args.as_ptr());
        (r, Z3_get_error_code(c))
    }
}
