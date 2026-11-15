// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible BV overflow/underflow check and reduction operations.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use ay_dpll::api::Sort;

use super::{ffi_guard_mk, mk_ast, require_ast_or_return, stated_sort, Z3_ast, Z3_context};

// ---- BV overflow/underflow check operations ----
// These return Bool-sorted AST nodes that are true iff the operation
// does NOT overflow/underflow.

/// Check that bvadd does not overflow.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvadd_no_overflow(
    c: Z3_context,
    t1: Z3_ast,
    t2: Z3_ast,
    is_signed: bool,
) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_bvadd_no_overflow", |ctx| {
            let t1 =
                require_ast_or_return!(ctx, t1, "Z3_mk_bvadd_no_overflow", "left operand", 0).term;
            let t2 =
                require_ast_or_return!(ctx, t2, "Z3_mk_bvadd_no_overflow", "right operand", 0).term;
            let t = ctx.solver.bvadd_no_overflow(t1, t2, is_signed);
            mk_ast(ctx, t, Sort::Bool)
        })
    }
}

/// Check that signed bvadd does not underflow.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvadd_no_underflow(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_bvadd_no_underflow", |ctx| {
            let t1 =
                require_ast_or_return!(ctx, t1, "Z3_mk_bvadd_no_underflow", "left operand", 0).term;
            let t2 =
                require_ast_or_return!(ctx, t2, "Z3_mk_bvadd_no_underflow", "right operand", 0)
                    .term;
            let t = ctx.solver.bvadd_no_underflow(t1, t2);
            mk_ast(ctx, t, Sort::Bool)
        })
    }
}

/// Check that signed bvsub does not overflow.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvsub_no_overflow(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_bvsub_no_overflow", |ctx| {
            let t1 =
                require_ast_or_return!(ctx, t1, "Z3_mk_bvsub_no_overflow", "left operand", 0).term;
            let t2 =
                require_ast_or_return!(ctx, t2, "Z3_mk_bvsub_no_overflow", "right operand", 0).term;
            let t = ctx.solver.bvsub_no_overflow(t1, t2);
            mk_ast(ctx, t, Sort::Bool)
        })
    }
}

/// Check that bvsub does not underflow.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvsub_no_underflow(
    c: Z3_context,
    t1: Z3_ast,
    t2: Z3_ast,
    is_signed: bool,
) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_bvsub_no_underflow", |ctx| {
            let t1 =
                require_ast_or_return!(ctx, t1, "Z3_mk_bvsub_no_underflow", "left operand", 0).term;
            let t2 =
                require_ast_or_return!(ctx, t2, "Z3_mk_bvsub_no_underflow", "right operand", 0)
                    .term;
            let t = ctx.solver.bvsub_no_underflow(t1, t2, is_signed);
            mk_ast(ctx, t, Sort::Bool)
        })
    }
}

/// Check that signed bvsdiv does not overflow (INT_MIN / -1).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvsdiv_no_overflow(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_bvsdiv_no_overflow", |ctx| {
            let t1 =
                require_ast_or_return!(ctx, t1, "Z3_mk_bvsdiv_no_overflow", "left operand", 0).term;
            let t2 =
                require_ast_or_return!(ctx, t2, "Z3_mk_bvsdiv_no_overflow", "right operand", 0)
                    .term;
            let t = ctx.solver.bvsdiv_no_overflow(t1, t2);
            mk_ast(ctx, t, Sort::Bool)
        })
    }
}

/// Check that signed bvneg does not overflow (negating INT_MIN).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvneg_no_overflow(c: Z3_context, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_bvneg_no_overflow", |ctx| {
            let t1 = require_ast_or_return!(ctx, t1, "Z3_mk_bvneg_no_overflow", "operand", 0).term;
            let t = ctx.solver.bvneg_no_overflow(t1);
            mk_ast(ctx, t, Sort::Bool)
        })
    }
}

/// Check that bvmul does not overflow.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvmul_no_overflow(
    c: Z3_context,
    t1: Z3_ast,
    t2: Z3_ast,
    is_signed: bool,
) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_bvmul_no_overflow", |ctx| {
            let t1 =
                require_ast_or_return!(ctx, t1, "Z3_mk_bvmul_no_overflow", "left operand", 0).term;
            let t2 =
                require_ast_or_return!(ctx, t2, "Z3_mk_bvmul_no_overflow", "right operand", 0).term;
            let t = ctx.solver.bvmul_no_overflow(t1, t2, is_signed);
            mk_ast(ctx, t, Sort::Bool)
        })
    }
}

/// Check that signed bvmul does not underflow.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvmul_no_underflow(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_bvmul_no_underflow", |ctx| {
            let t1 =
                require_ast_or_return!(ctx, t1, "Z3_mk_bvmul_no_underflow", "left operand", 0).term;
            let t2 =
                require_ast_or_return!(ctx, t2, "Z3_mk_bvmul_no_underflow", "right operand", 0)
                    .term;
            let t = ctx.solver.bvmul_no_underflow(t1, t2);
            mk_ast(ctx, t, Sort::Bool)
        })
    }
}

// ---- BV reduction operations ----

/// Take the AND of all bits, returning a 1-bit bitvector.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvredand(c: Z3_context, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_bvredand", |ctx| {
            let operand = require_ast_or_return!(ctx, t1, "Z3_mk_bvredand", "operand", 0);
            let term = operand.term;
            let width = match stated_sort(ctx, operand) {
                Some(Sort::BitVec(bv)) => bv.width,
                _ => return 0,
            };
            // redand(x) = (x == ~0) where ~0 is all-ones of the same width
            let zero_w = ctx.solver.bv_const(0, width);
            let all_ones = ctx.solver.bvnot(zero_w);
            let eq = ctx.solver.eq(term, all_ones);
            // Convert Bool to BV1: ite(eq, 1bv1, 0bv1)
            let one = ctx.solver.bv_const(1, 1);
            let zero = ctx.solver.bv_const(0, 1);
            let t = ctx.solver.ite(eq, one, zero);
            mk_ast(ctx, t, Sort::bitvec(1))
        })
    }
}

/// Take the OR of all bits, returning a 1-bit bitvector.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvredor(c: Z3_context, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_bvredor", |ctx| {
            let operand = require_ast_or_return!(ctx, t1, "Z3_mk_bvredor", "operand", 0);
            let term = operand.term;
            let width = match stated_sort(ctx, operand) {
                Some(Sort::BitVec(bv)) => bv.width,
                _ => return 0,
            };
            // redor(x) = (x != 0)
            let zero_bv = ctx.solver.bv_const(0, width);
            let eq_zero = ctx.solver.eq(term, zero_bv);
            let neq = ctx.solver.not(eq_zero);
            // Convert Bool to BV1: ite(neq, 1bv1, 0bv1)
            let one = ctx.solver.bv_const(1, 1);
            let zero = ctx.solver.bv_const(0, 1);
            let t = ctx.solver.ite(neq, one, zero);
            mk_ast(ctx, t, Sort::bitvec(1))
        })
    }
}
