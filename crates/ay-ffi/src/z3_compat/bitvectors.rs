// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible bitvector operation functions.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::c_uint;

use ay_dpll::api::Sort;

use super::{
    ffi_guard_ast, lookup_ast_sort, record_ast_sort, require_term_ast_or_return, term_to_ast,
    Z3Context, Z3_ast, Z3_context, MAX_FFI_BITVECTOR_WIDTH, Z3_INVALID_ARG,
};

fn accept_bv_width(ctx: &mut Z3Context, operation: &str, width: u32) -> bool {
    if width != 0 && width <= MAX_FFI_BITVECTOR_WIDTH {
        return true;
    }
    ctx.last_error = Z3_INVALID_ARG;
    ctx.error_msg = Some(format!(
        "{operation}: result width {width} is outside the supported range 1..={MAX_FFI_BITVECTOR_WIDTH}"
    ));
    false
}

fn require_bv_operand_width(ctx: &mut Z3Context, operation: &str, operand: Z3_ast) -> Option<u32> {
    if let Some(Sort::BitVec(bv)) = lookup_ast_sort(ctx, operand) {
        return Some(bv.width);
    }
    ctx.last_error = Z3_INVALID_ARG;
    ctx.error_msg = Some(format!("{operation}: operand is not a bit-vector"));
    None
}

// ---- BV binary operations ----

/// Helper macro for binary BV operations that return the same-width BV sort.
macro_rules! bv_binary_op {
    ($name:ident, $method:ident) => {
        /// # Safety
        /// `c` must be a valid context pointer.
        #[no_mangle]
        pub unsafe extern "C" fn $name(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
            // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on
            // this extern "C" function requires it to be a valid, non-aliased pointer (or
            // null). `ffi_guard_ast` handles the null case internally and catches any
            // unwinding panic so it cannot cross the FFI boundary.
            unsafe {
                ffi_guard_ast(c, |ctx| {
                    let t1_term =
                        require_term_ast_or_return!(ctx, t1, stringify!($name), "left operand", 0);
                    let t2_term =
                        require_term_ast_or_return!(ctx, t2, stringify!($name), "right operand", 0);
                    let t = ctx.solver.$method(t1_term, t2_term);
                    let a = term_to_ast(ctx, t);
                    if let Some(sort) = lookup_ast_sort(ctx, t1).cloned() {
                        record_ast_sort(ctx, a, sort);
                    }
                    a
                })
            }
        }
    };
}

bv_binary_op!(Z3_mk_bvand, bvand);
bv_binary_op!(Z3_mk_bvor, bvor);
bv_binary_op!(Z3_mk_bvxor, bvxor);
bv_binary_op!(Z3_mk_bvadd, bvadd);
bv_binary_op!(Z3_mk_bvsub, bvsub);
bv_binary_op!(Z3_mk_bvmul, bvmul);
bv_binary_op!(Z3_mk_bvudiv, bvudiv);
bv_binary_op!(Z3_mk_bvsdiv, bvsdiv);
bv_binary_op!(Z3_mk_bvurem, bvurem);
bv_binary_op!(Z3_mk_bvsrem, bvsrem);
bv_binary_op!(Z3_mk_bvsmod, bvsmod);
bv_binary_op!(Z3_mk_bvshl, bvshl);
bv_binary_op!(Z3_mk_bvlshr, bvlshr);
bv_binary_op!(Z3_mk_bvashr, bvashr);

// ---- BV derived binary operations (NAND, NOR, XNOR) ----

/// Create bitwise NAND: `bvnand(t1, t2) = bvnot(bvand(t1, t2))`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvnand(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t1_term = require_term_ast_or_return!(ctx, t1, "Z3_mk_bvnand", "left operand", 0);
            let t2_term = require_term_ast_or_return!(ctx, t2, "Z3_mk_bvnand", "right operand", 0);
            let and_t = ctx.solver.bvand(t1_term, t2_term);
            let t = ctx.solver.bvnot(and_t);
            let a = term_to_ast(ctx, t);
            if let Some(sort) = lookup_ast_sort(ctx, t1).cloned() {
                record_ast_sort(ctx, a, sort);
            }
            a
        })
    }
}

/// Create bitwise NOR: `bvnor(t1, t2) = bvnot(bvor(t1, t2))`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvnor(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t1_term = require_term_ast_or_return!(ctx, t1, "Z3_mk_bvnor", "left operand", 0);
            let t2_term = require_term_ast_or_return!(ctx, t2, "Z3_mk_bvnor", "right operand", 0);
            let or_t = ctx.solver.bvor(t1_term, t2_term);
            let t = ctx.solver.bvnot(or_t);
            let a = term_to_ast(ctx, t);
            if let Some(sort) = lookup_ast_sort(ctx, t1).cloned() {
                record_ast_sort(ctx, a, sort);
            }
            a
        })
    }
}

/// Create bitwise XNOR: `bvxnor(t1, t2) = bvnot(bvxor(t1, t2))`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvxnor(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t1_term = require_term_ast_or_return!(ctx, t1, "Z3_mk_bvxnor", "left operand", 0);
            let t2_term = require_term_ast_or_return!(ctx, t2, "Z3_mk_bvxnor", "right operand", 0);
            let xor_t = ctx.solver.bvxor(t1_term, t2_term);
            let t = ctx.solver.bvnot(xor_t);
            let a = term_to_ast(ctx, t);
            if let Some(sort) = lookup_ast_sort(ctx, t1).cloned() {
                record_ast_sort(ctx, a, sort);
            }
            a
        })
    }
}

// ---- BV comparison operations ----

/// Helper macro for BV comparison operations that return Bool sort.
macro_rules! bv_compare_op {
    ($name:ident, $method:ident) => {
        /// # Safety
        /// `c` must be a valid context pointer.
        #[no_mangle]
        pub unsafe extern "C" fn $name(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
            // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on
            // this extern "C" function requires it to be a valid, non-aliased pointer (or
            // null). `ffi_guard_ast` handles the null case internally and catches any
            // unwinding panic so it cannot cross the FFI boundary.
            unsafe {
                ffi_guard_ast(c, |ctx| {
                    let t1 =
                        require_term_ast_or_return!(ctx, t1, stringify!($name), "left operand", 0);
                    let t2 =
                        require_term_ast_or_return!(ctx, t2, stringify!($name), "right operand", 0);
                    let t = ctx.solver.$method(t1, t2);
                    let a = term_to_ast(ctx, t);
                    record_ast_sort(ctx, a, Sort::Bool);
                    a
                })
            }
        }
    };
}

bv_compare_op!(Z3_mk_bvult, bvult);
bv_compare_op!(Z3_mk_bvslt, bvslt);
bv_compare_op!(Z3_mk_bvule, bvule);
bv_compare_op!(Z3_mk_bvsle, bvsle);
bv_compare_op!(Z3_mk_bvuge, bvuge);
bv_compare_op!(Z3_mk_bvsge, bvsge);
bv_compare_op!(Z3_mk_bvugt, bvugt);
bv_compare_op!(Z3_mk_bvsgt, bvsgt);

// ---- BV unary operations ----

/// Create bitwise NOT.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvnot(c: Z3_context, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t1_term = require_term_ast_or_return!(ctx, t1, "Z3_mk_bvnot", "operand", 0);
            let t = ctx.solver.bvnot(t1_term);
            let a = term_to_ast(ctx, t);
            if let Some(sort) = lookup_ast_sort(ctx, t1).cloned() {
                record_ast_sort(ctx, a, sort);
            }
            a
        })
    }
}

/// Create two's complement negation.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvneg(c: Z3_context, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t1_term = require_term_ast_or_return!(ctx, t1, "Z3_mk_bvneg", "operand", 0);
            let t = ctx.solver.bvneg(t1_term);
            let a = term_to_ast(ctx, t);
            if let Some(sort) = lookup_ast_sort(ctx, t1).cloned() {
                record_ast_sort(ctx, a, sort);
            }
            a
        })
    }
}

// ---- BV concat and width-changing operations ----

/// Concatenate two bitvectors (high bits first).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_concat(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some(left_width) = require_bv_operand_width(ctx, "Z3_mk_concat", t1) else {
                return 0;
            };
            let Some(right_width) = require_bv_operand_width(ctx, "Z3_mk_concat", t2) else {
                return 0;
            };
            let Some(result_width) = left_width.checked_add(right_width) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_concat: result width overflows".to_string());
                return 0;
            };
            if !accept_bv_width(ctx, "Z3_mk_concat", result_width) {
                return 0;
            }
            let t1_term = require_term_ast_or_return!(ctx, t1, "Z3_mk_concat", "left operand", 0);
            let t2_term = require_term_ast_or_return!(ctx, t2, "Z3_mk_concat", "right operand", 0);
            let t = ctx.solver.bvconcat(t1_term, t2_term);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::bitvec(result_width));
            a
        })
    }
}

/// Extract bits `[high:low]` from a bitvector.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_extract(
    c: Z3_context,
    high: c_uint,
    low: c_uint,
    t1: Z3_ast,
) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if high < low {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_mk_extract: high index {high} is below low index {low}"
                ));
                return 0;
            }
            let Some(operand_width) = require_bv_operand_width(ctx, "Z3_mk_extract", t1) else {
                return 0;
            };
            if high >= operand_width {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_mk_extract: high index {high} is out of range for width {operand_width}"
                ));
                return 0;
            }
            let Some(width) = high.checked_sub(low).and_then(|width| width.checked_add(1)) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_extract: result width overflows".to_string());
                return 0;
            };
            if !accept_bv_width(ctx, "Z3_mk_extract", width) {
                return 0;
            }
            let t1 = require_term_ast_or_return!(ctx, t1, "Z3_mk_extract", "operand", 0);
            let t = ctx.solver.bvextract(t1, high, low);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::bitvec(width));
            a
        })
    }
}

/// Sign-extend a bitvector by `i` bits.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_sign_ext(c: Z3_context, i: c_uint, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some(operand_width) = require_bv_operand_width(ctx, "Z3_mk_sign_ext", t1) else {
                return 0;
            };
            let Some(result_width) = operand_width.checked_add(i) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_sign_ext: result width overflows".to_string());
                return 0;
            };
            if !accept_bv_width(ctx, "Z3_mk_sign_ext", result_width) {
                return 0;
            }
            let t1 = require_term_ast_or_return!(ctx, t1, "Z3_mk_sign_ext", "operand", 0);
            let t = ctx.solver.bvsignext(t1, i);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::bitvec(result_width));
            a
        })
    }
}

/// Zero-extend a bitvector by `i` bits.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_zero_ext(c: Z3_context, i: c_uint, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some(operand_width) = require_bv_operand_width(ctx, "Z3_mk_zero_ext", t1) else {
                return 0;
            };
            let Some(result_width) = operand_width.checked_add(i) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_zero_ext: result width overflows".to_string());
                return 0;
            };
            if !accept_bv_width(ctx, "Z3_mk_zero_ext", result_width) {
                return 0;
            }
            let t1 = require_term_ast_or_return!(ctx, t1, "Z3_mk_zero_ext", "operand", 0);
            let t = ctx.solver.bvzeroext(t1, i);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::bitvec(result_width));
            a
        })
    }
}

/// Repeat a bitvector `i` times.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_repeat(c: Z3_context, i: c_uint, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some(operand_width) = require_bv_operand_width(ctx, "Z3_mk_repeat", t1) else {
                return 0;
            };
            let Some(result_width) = operand_width.checked_mul(i) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_repeat: result width overflows".to_string());
                return 0;
            };
            if !accept_bv_width(ctx, "Z3_mk_repeat", result_width) {
                return 0;
            }
            let t1 = require_term_ast_or_return!(ctx, t1, "Z3_mk_repeat", "operand", 0);
            let t = ctx.solver.bvrepeat(t1, i);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::bitvec(result_width));
            a
        })
    }
}

/// Rotate bitvector left by `i` bits.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_rotate_left(c: Z3_context, i: c_uint, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t1_term = require_term_ast_or_return!(ctx, t1, "Z3_mk_rotate_left", "operand", 0);
            let t = ctx.solver.bvrotl(t1_term, i);
            let a = term_to_ast(ctx, t);
            if let Some(sort) = lookup_ast_sort(ctx, t1).cloned() {
                record_ast_sort(ctx, a, sort);
            }
            a
        })
    }
}

/// Rotate bitvector right by `i` bits.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_rotate_right(c: Z3_context, i: c_uint, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t1_term = require_term_ast_or_return!(ctx, t1, "Z3_mk_rotate_right", "operand", 0);
            let t = ctx.solver.bvrotr(t1_term, i);
            let a = term_to_ast(ctx, t);
            if let Some(sort) = lookup_ast_sort(ctx, t1).cloned() {
                record_ast_sort(ctx, a, sort);
            }
            a
        })
    }
}

/// Create BV comparison: returns 1-bit BV with `#b1` if `t1 == t2`, `#b0` otherwise.
///
/// Equivalent to `(ite (= t1 t2) #b1 #b0)`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvcomp(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t1 = require_term_ast_or_return!(ctx, t1, "Z3_mk_bvcomp", "left operand", 0);
            let t2 = require_term_ast_or_return!(ctx, t2, "Z3_mk_bvcomp", "right operand", 0);
            let eq_term = ctx.solver.eq(t1, t2);
            let one = ctx.solver.bv_const(1, 1);
            let zero = ctx.solver.bv_const(0, 1);
            let t = ctx.solver.ite(eq_term, one, zero);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::bitvec(1));
            a
        })
    }
}

// ---- BV-Int conversion operations ----

/// Convert bitvector to integer.
///
/// If `is_signed` is true, interprets the BV as a signed value.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bv2int(c: Z3_context, t1: Z3_ast, is_signed: bool) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t1 = require_term_ast_or_return!(ctx, t1, "Z3_mk_bv2int", "operand", 0);
            let t = if is_signed {
                ctx.solver.bv2int_signed(t1)
            } else {
                ctx.solver.bv2int(t1)
            };
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Int);
            a
        })
    }
}

/// Convert integer to bitvector of width `n`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_int2bv(c: Z3_context, n: c_uint, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if !accept_bv_width(ctx, "Z3_mk_int2bv", n) {
                return 0;
            }
            let t1 = require_term_ast_or_return!(ctx, t1, "Z3_mk_int2bv", "operand", 0);
            let t = ctx.solver.int2bv(t1, n);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::bitvec(n));
            a
        })
    }
}
