// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible arithmetic, comparison, conversion, array, and AST inspection functions.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::c_uint;

use ay_dpll::api::Sort;

use super::{
    alloc_sort, ast_to_term, ffi_count_within_limit, ffi_guard_ast, ffi_guard_ptr, lookup_ast_sort,
    record_ast_sort, term_to_ast, Z3_ast, Z3_context, Z3_sort,
};

// ---- Arithmetic operations ----

/// Helper for n-ary arithmetic operations that inherit sort from first arg.
macro_rules! arith_nary_op {
    ($name:ident, $method:ident) => {
        /// # Safety
        /// All pointers must be valid. `args` must point to `num_args` elements.
        #[no_mangle]
        pub unsafe extern "C" fn $name(
            c: Z3_context,
            num_args: c_uint,
            args: *const Z3_ast,
        ) -> Z3_ast {
            // SAFETY: this public entry point requires `c` to be null or a live,
            // exclusively borrowed context; the bound checker only updates its error state.
            if !unsafe { ffi_count_within_limit(c, stringify!($name), num_args) } {
                return 0;
            }
            if num_args == 0 || args.is_null() {
                return 0;
            }
            let terms: Vec<_> = (0..num_args as usize)
                // SAFETY: The caller's `# Safety` contract guarantees `args` points to at
                // least the declared number of elements. The count was range-checked above,
                // and null-checked before entering this block, so `args.add(i)` stays within
                // the caller's allocation.
                .map(|i| ast_to_term(unsafe { *args.add(i) }))
                .collect();
            // SAFETY: All raw pointers used inside this block were validated (null-checked
            // and/or bounds-checked) above, and the caller's `# Safety` contract on this
            // extern "C" function guarantees they remain valid for the duration of the call.
            let first_ast = unsafe { *args };

            // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on
            // this extern "C" function requires it to be a valid, non-aliased pointer (or
            // null). `ffi_guard_ast` handles the null case internally and catches any
            // unwinding panic so it cannot cross the FFI boundary.
            unsafe {
                ffi_guard_ast(c, |ctx| {
                    let t = ctx.solver.$method(&terms);
                    let a = term_to_ast(t);
                    if let Some(sort) = lookup_ast_sort(ctx, first_ast).cloned() {
                        record_ast_sort(ctx, a, sort);
                    }
                    a
                })
            }
        }
    };
}

arith_nary_op!(Z3_mk_add, add_many);
arith_nary_op!(Z3_mk_mul, mul_many);

/// Create subtraction (left-associative).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_sub(c: Z3_context, num_args: c_uint, args: *const Z3_ast) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_sub", num_args) } {
        return 0;
    }
    if num_args < 2 || args.is_null() {
        return 0;
    }
    let terms: Vec<_> = (0..num_args as usize)
        // SAFETY: The caller's `# Safety` contract guarantees `args` points to at least the
        // declared number of elements. The count was range-checked above, and null-checked
        // before entering this block, so `args.add(i)` stays within the caller's allocation.
        .map(|i| ast_to_term(unsafe { *args.add(i) }))
        .collect();
    // SAFETY: All raw pointers used inside this block were validated (null-checked and/or
    // bounds-checked) above, and the caller's `# Safety` contract on this extern "C" function
    // guarantees they remain valid for the duration of the call.
    let first_ast = unsafe { *args };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let mut result = terms[0];
            for &t in &terms[1..] {
                result = ctx.solver.sub(result, t);
            }
            let a = term_to_ast(result);
            if let Some(sort) = lookup_ast_sort(ctx, first_ast).cloned() {
                record_ast_sort(ctx, a, sort);
            }
            a
        })
    }
}

/// Create unary minus.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_unary_minus(c: Z3_context, arg: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.neg(ast_to_term(arg));
            let a = term_to_ast(t);
            if let Some(sort) = lookup_ast_sort(ctx, arg).cloned() {
                record_ast_sort(ctx, a, sort);
            }
            a
        })
    }
}

/// Create division (integer or real based on argument sort).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_div(c: Z3_context, arg1: Z3_ast, arg2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let is_int = lookup_ast_sort(ctx, arg1).is_some_and(|s| matches!(s, Sort::Int));
            let t = if is_int {
                ctx.solver.int_div(ast_to_term(arg1), ast_to_term(arg2))
            } else {
                ctx.solver.div(ast_to_term(arg1), ast_to_term(arg2))
            };
            let a = term_to_ast(t);
            if let Some(sort) = lookup_ast_sort(ctx, arg1).cloned() {
                record_ast_sort(ctx, a, sort);
            }
            a
        })
    }
}

/// Create integer modulo.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_mod(c: Z3_context, arg1: Z3_ast, arg2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.modulo(ast_to_term(arg1), ast_to_term(arg2));
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Int);
            a
        })
    }
}

/// Create integer remainder (truncation remainder).
///
/// Unlike `mod` (Euclidean, always non-negative), `rem` has the same sign as
/// the dividend `a`. Defined as:
/// ```text
/// rem(a, b) = ite(a mod b = 0, 0, ite(a >= 0, a mod b, (a mod b) - |b|))
/// ```
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_rem(c: Z3_context, arg1: Z3_ast, arg2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let a = ast_to_term(arg1);
            let b = ast_to_term(arg2);
            let zero = ctx.solver.int_const(0);
            // a mod b is Euclidean (always >= 0) in SMT-LIB
            let a_mod_b = ctx.solver.modulo(a, b);
            let mod_is_zero = ctx.solver.eq(a_mod_b, zero);
            let a_ge_zero = ctx.solver.ge(a, zero);
            let abs_b = ctx.solver.abs(b);
            // When a < 0 and mod != 0: rem = (a mod b) - |b| (makes result negative)
            let neg_case = ctx.solver.sub(a_mod_b, abs_b);
            let nonzero_case = ctx.solver.ite(a_ge_zero, a_mod_b, neg_case);
            let t = ctx.solver.ite(mod_is_zero, zero, nonzero_case);
            let ast = term_to_ast(t);
            record_ast_sort(ctx, ast, Sort::Int);
            ast
        })
    }
}

/// Helper for binary comparison operations (result is Bool).
macro_rules! arith_cmp_op {
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
                    let t = ctx.solver.$method(ast_to_term(t1), ast_to_term(t2));
                    let a = term_to_ast(t);
                    record_ast_sort(ctx, a, Sort::Bool);
                    a
                })
            }
        }
    };
}

arith_cmp_op!(Z3_mk_lt, lt);
arith_cmp_op!(Z3_mk_le, le);
arith_cmp_op!(Z3_mk_gt, gt);
arith_cmp_op!(Z3_mk_ge, ge);

/// Convert int to real.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_int2real(c: Z3_context, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.int_to_real(ast_to_term(t1));
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Real);
            a
        })
    }
}

/// Convert real to int (floor).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_real2int(c: Z3_context, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.real_to_int(ast_to_term(t1));
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Int);
            a
        })
    }
}

/// Check if a real is an integer.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_is_int(c: Z3_context, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.is_int(ast_to_term(t1));
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create absolute value.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_abs(c: Z3_context, arg: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.abs(ast_to_term(arg));
            let a = term_to_ast(t);
            if let Some(sort) = lookup_ast_sort(ctx, arg).cloned() {
                record_ast_sort(ctx, a, sort);
            }
            a
        })
    }
}

/// Create exponentiation (arg1 ^ arg2).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_power(c: Z3_context, arg1: Z3_ast, arg2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.power(ast_to_term(arg1), ast_to_term(arg2));
            let a = term_to_ast(t);
            if let Some(sort) = lookup_ast_sort(ctx, arg1).cloned() {
                record_ast_sort(ctx, a, sort);
            }
            a
        })
    }
}

// ---- Array operations ----

/// Create array select (read).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_select(c: Z3_context, a: Z3_ast, i: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.select(ast_to_term(a), ast_to_term(i));
            let r = term_to_ast(t);
            if let Some(Sort::Array(arr)) = lookup_ast_sort(ctx, a) {
                record_ast_sort(ctx, r, arr.element_sort.clone());
            }
            r
        })
    }
}

/// Create array store (write).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_store(c: Z3_context, a: Z3_ast, i: Z3_ast, v: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx
                .solver
                .store(ast_to_term(a), ast_to_term(i), ast_to_term(v));
            let r = term_to_ast(t);
            if let Some(sort) = lookup_ast_sort(ctx, a).cloned() {
                record_ast_sort(ctx, r, sort);
            }
            r
        })
    }
}

/// Create a constant array.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_const_array(c: Z3_context, domain: Z3_sort, v: Z3_ast) -> Z3_ast {
    if domain.is_null() {
        return 0;
    }
    // SAFETY: `domain` was null-checked above and originates from a prior AY FFI allocation
    // whose handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`).
    // Reading `.sort` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let domain_sort = unsafe { (*domain).sort.clone() };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.const_array(domain_sort.clone(), ast_to_term(v));
            let r = term_to_ast(t);
            if let Some(elem_sort) = lookup_ast_sort(ctx, v).cloned() {
                record_ast_sort(ctx, r, Sort::array(domain_sort, elem_sort));
            }
            r
        })
    }
}

// ---- AST inspection ----

/// Get the sort of an AST.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_sort(c: Z3_context, a: Z3_ast) -> Z3_sort {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| match lookup_ast_sort(ctx, a) {
            Some(sort) => alloc_sort(ctx, sort.clone()),
            None => {
                // The side-table only covers handles minted through the mk_*
                // constructors. Terms surfaced from INSIDE the engine (e.g.
                // normalized consequence clauses from Z3_solver_get_consequences,
                // units/trail literals) were never recorded there, which used to
                // make this return null (observed as Z3_UNKNOWN_SORT downstream).
                // Fall back to the solver's own sort for the term — the ground
                // truth — and record it so subsequent lookups hit the table.
                let sort = ctx.solver.term_sort(ast_to_term(a)).clone();
                record_ast_sort(ctx, a, sort.clone());
                alloc_sort(ctx, sort)
            }
        })
    }
}
