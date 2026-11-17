// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Native bounded prime-field C ABI. Unsupported sizes fail explicitly.
use super::*;
use ay_core::FiniteFieldSort;
use ay_dpll::api::{Sort, Term};
use std::{
    ffi::{c_char, c_uint},
    ptr,
};

/// A C declaration's public name can differ from its private engine identity.
pub(super) fn format_public_term_in_context(ctx: &Z3Context, term: Term) -> Option<String> {
    ctx.solver
        .format_term_checked_with_bindings(term, |name| ctx.ffi_used_decl_names.contains(name))
}

pub(super) fn format_public_term(ctx: &mut Z3Context, term: Term) -> Option<String> {
    let text = format_public_term_in_context(ctx, term);
    if text.is_none() {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some("term rendering refused".into());
    }
    text
}

pub(super) fn format_public_assertions(ctx: &mut Z3Context, assertions: &[Term]) -> Option<String> {
    let text = ctx
        .solver
        .assertions_sexpr_with_bindings(assertions, |name| ctx.ffi_used_decl_names.contains(name));
    if text.is_none() {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some("assertion rendering refused".into());
    }
    text
}

/// Create a prime-field sort, for prime cardinalities fitting in u32.
/// # Safety
/// Context is live or null; `prime` is a readable NUL-terminated string.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_finite_field_sort(c: Z3_context, prime: *const c_char) -> Z3_sort {
    // SAFETY: caller supplies the context/string; guard handles null context.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(text) = ffi_read_bounded_numeral_text(ctx, "Z3_mk_finite_field_sort", prime)
            else {
                return ptr::null_mut();
            };
            let Some(field) = text.parse().ok().and_then(FiniteFieldSort::new) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(
                    "finite field requires a prime cardinality from 2 through 4294967291".into(),
                );
                return ptr::null_mut();
            };
            alloc_sort(ctx, Sort::FiniteField(field))
        })
    }
}
/// Return the exact decimal cardinality of a prime-field sort.
/// # Safety
/// Context and sort must be live and belong to the same context.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_finite_field_sort_size(
    c: Z3_context,
    sort: Z3_sort,
) -> *const c_char {
    // SAFETY: the caller guarantees the sort allocation; null is checked.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            if !sort.is_null() {
                if let Sort::FiniteField(f) = (*sort).sort {
                    return cache_string(ctx, f.modulus().to_string());
                }
            }
            ctx.last_error = Z3_INVALID_ARG;
            ctx.error_msg = Some("expected finite-field sort".into());
            ptr::null()
        })
    }
}
unsafe fn field_app(
    c: Z3_context,
    operation: &'static str,
    count: c_uint,
    args: *const Z3_ast,
) -> Z3_ast {
    // SAFETY: forwarded context contract; admission precedes allocation/dereference.
    if !unsafe { ffi_count_within_limit(c, operation, count) } {
        return 0;
    }
    // SAFETY: context is live or null, and args is readable for count elements.
    unsafe {
        ffi_guard_mk(c, operation, |ctx| {
            if args.is_null()
                || (if operation == "ff.neg" {
                    count != 1
                } else {
                    count < 2
                })
            {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("wrong field operator arity".into());
                return 0;
            }
            let asts = std::slice::from_raw_parts(args, count as usize);
            let operands = require_asts_or_return!(ctx, asts, operation, 0);
            let terms: Vec<_> = operands.iter().map(|a| a.term).collect();
            if operands
                .iter()
                .any(|a| public_sort(ctx, *a) != public_sort(ctx, operands[0]))
            {
                ctx.last_error = Z3_SORT_ERROR;
                return 0;
            }
            let sort = public_sort(ctx, operands[0]);
            match ctx.solver.try_finite_field_app(operation, &terms) {
                Ok(t) => mk_ast(ctx, t, sort),
                Err(e) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(e.to_string());
                    0
                }
            }
        })
    }
}
/// Construct a same-field addition application.
/// # Safety
/// Context is live or null; args points to count live AST handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_ff_add(c: Z3_context, count: c_uint, args: *const Z3_ast) -> Z3_ast {
    // SAFETY: caller supplies the count-bounded operand array and context.
    unsafe { field_app(c, "ff.add", count, args) }
}
/// Construct a same-field multiplication application.
/// # Safety
/// Context is live or null; args points to count live AST handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_ff_mul(c: Z3_context, count: c_uint, args: *const Z3_ast) -> Z3_ast {
    // SAFETY: caller supplies the count-bounded operand array and context.
    unsafe { field_app(c, "ff.mul", count, args) }
}
/// Construct a same-field positional weighted bitsum application.
/// # Safety
/// Context is live or null; args points to count live AST handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_ff_bitsum(
    c: Z3_context,
    count: c_uint,
    args: *const Z3_ast,
) -> Z3_ast {
    // SAFETY: caller supplies the count-bounded operand array and context.
    unsafe { field_app(c, "ff.bitsum", count, args) }
}
/// Construct finite-field additive inverse.
/// # Safety
/// Context is live or null and arg is a live AST from that context.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_ff_neg(c: Z3_context, arg: Z3_ast) -> Z3_ast {
    // SAFETY: a one-element stack array remains live for the complete call.
    unsafe { field_app(c, "ff.neg", 1, &raw const arg) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CStr;
    #[test]
    fn finite_field_c_model_refuses_exhausted_literal_names() {
        // SAFETY: local text and arrays remain live during every call; this
        // test exclusively owns and ultimately destroys the context.
        unsafe {
            let config = Z3_mk_config();
            let c = Z3_mk_context(config);
            Z3_del_config(config);
            let f = Z3_mk_finite_field_sort(c, c"7".as_ptr());
            Z3_mk_const(c, Z3_mk_string_symbol(c, c"ff1".as_ptr()), f);
            for k in 0..1024 {
                let name = CString::new(format!("#f{}m7", 1 + 7 * k))
                    .expect("generated finite-field literal name cannot contain an interior NUL");
                Z3_mk_const(c, Z3_mk_string_symbol(c, name.as_ptr()), f);
            }
            let solver = Z3_mk_solver(c);
            Z3_solver_inc_ref(c, solver);
            let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"witness".as_ptr()), f);
            let one = Z3_mk_numeral(c, c"1".as_ptr(), f);
            Z3_solver_assert(c, solver, Z3_mk_eq(c, x, one));
            assert_eq!(Z3_solver_check(c, solver), Z3_L_TRUE);
            let model = Z3_solver_get_model(c, solver);
            assert!(!model.is_null());
            assert!(Z3_model_to_string(c, model).is_null());
            assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
            assert_eq!(Z3_solver_check(c, solver), Z3_L_TRUE);
            assert!(Z3_ast_to_string(c, one).is_null());
            assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
            assert_eq!(Z3_solver_check(c, solver), Z3_L_TRUE);
            assert!(Z3_ast_to_string(c, Z3_mk_eq(c, x, one)).is_null());
            assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
            assert_eq!(Z3_solver_check(c, solver), Z3_L_TRUE);
            assert!(Z3_solver_to_string(c, solver).is_null());
            assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
            Z3_solver_dec_ref(c, solver);
            Z3_del_context(c);
        }
    }
    #[test]
    fn finite_field_c_api_has_exact_arithmetic_and_typed_refusals() {
        // SAFETY: this test owns a live context; each pointer references local
        // NUL-terminated text or count-sized arrays throughout the call.
        unsafe {
            let config = Z3_mk_config();
            let c = Z3_mk_context(config);
            Z3_del_config(config);
            let f = Z3_mk_finite_field_sort(c, c"7".as_ptr());
            assert!(!f.is_null());
            assert_eq!(Z3_get_sort_kind(c, f), Z3_FINITE_FIELD_SORT);
            assert_eq!(
                CStr::from_ptr(Z3_get_finite_field_sort_size(c, f))
                    .to_str()
                    .expect("finite-field sort size must be valid UTF-8"),
                "7"
            );
            let one = Z3_mk_numeral(c, c"1".as_ptr(), f);
            let two = Z3_mk_numeral(c, c"2".as_ptr(), f);
            let three = Z3_mk_numeral(c, c"3".as_ptr(), f);
            let sum = Z3_mk_ff_bitsum(c, 3, [one, two, three].as_ptr());
            assert_ne!(sum, 0);
            let x = Z3_mk_const(c, Z3_mk_string_symbol(c, c"x".as_ptr()), f);
            let solver = Z3_mk_solver(c);
            Z3_solver_inc_ref(c, solver);
            Z3_solver_assert(c, solver, Z3_mk_eq(c, sum, three));
            Z3_solver_assert(c, solver, Z3_mk_eq(c, x, three));
            for name in [c"ff3", c"#f3m7"] {
                let shadow = Z3_mk_const(c, Z3_mk_string_symbol(c, name.as_ptr()), f);
                Z3_solver_assert(c, solver, Z3_mk_eq(c, shadow, two));
            }
            assert_eq!(CStr::from_ptr(Z3_ast_to_string(c, three)), c"#f10m7");
            assert!(CStr::from_ptr(Z3_ast_to_string(c, sum))
                .to_str()
                .expect("finite-field AST rendering must be valid UTF-8")
                .contains("#f10m7"));
            let product = Z3_mk_ff_mul(c, 2, [two, three].as_ptr());
            let neg = Z3_mk_ff_neg(c, one);
            Z3_solver_assert(c, solver, Z3_mk_eq(c, product, neg));
            let add = Z3_mk_ff_add(c, 2, [one, neg].as_ptr());
            let zero = Z3_mk_numeral(c, c"0".as_ptr(), f);
            Z3_solver_assert(c, solver, Z3_mk_eq(c, add, zero));
            assert_eq!(Z3_solver_check(c, solver), Z3_L_TRUE);
            assert!(CStr::from_ptr(Z3_solver_to_string(c, solver))
                .to_str()
                .expect("finite-field solver rendering must be valid UTF-8")
                .contains("#f10m7"));
            let model = Z3_solver_get_model(c, solver);
            assert!(!model.is_null());
            let text = CStr::from_ptr(Z3_model_to_string(c, model))
                .to_str()
                .expect("finite-field model rendering must be valid UTF-8");
            assert!(text.contains("#f10m7"), "{text}");
            let mut value = 0;
            assert!(Z3_model_eval(c, model, x, false, &raw mut value));
            assert_eq!(CStr::from_ptr(Z3_get_numeral_string(c, value)), c"3");
            for (term, expected) in [(sum, c"3"), (product, c"6"), (neg, c"6"), (add, c"0")] {
                assert!(Z3_model_eval(c, model, term, false, &raw mut value));
                assert_eq!(CStr::from_ptr(Z3_get_numeral_string(c, value)), expected);
            }
            assert_eq!(
                Z3_get_sort_kind(c, Z3_get_sort(c, value)),
                Z3_FINITE_FIELD_SORT
            );
            assert!(Z3_get_numeral_string(c, neg).is_null());
            assert_eq!(Z3_get_decl_kind(c, Z3_get_app_decl(c, three)), Z3_OP_FF_NUM);
            let decl = Z3_get_app_decl(c, three);
            assert_eq!(Z3_get_decl_num_parameters(c, decl), 1);
            assert_eq!(
                Z3_get_decl_parameter_kind(c, decl, 0),
                Z3_PARAMETER_RATIONAL
            );
            assert_eq!(
                Z3_get_decl_kind(c, Z3_get_app_decl(c, sum)),
                Z3_OP_FF_BITSUM
            );
            Z3_solver_assert(c, solver, Z3_mk_not(c, Z3_mk_eq(c, sum, three)));
            assert_eq!(Z3_solver_check(c, solver), Z3_L_FALSE);
            assert_eq!(Z3_mk_ff_add(c, 1, [one].as_ptr()), 0);
            let other = Z3_mk_finite_field_sort(c, c"5".as_ptr());
            let foreign = Z3_mk_numeral(c, c"1".as_ptr(), other);
            assert_eq!(Z3_mk_ff_mul(c, 2, [one, foreign].as_ptr()), 0);
            assert!(Z3_mk_finite_field_sort(c, c"9".as_ptr()).is_null());
            assert!(!Z3_mk_finite_field_sort(c, c"257".as_ptr()).is_null());
            assert!(!Z3_mk_finite_field_sort(c, c"4294967291".as_ptr()).is_null());
            assert!(Z3_mk_finite_field_sort(c, c"4294967295".as_ptr()).is_null());
            Z3_solver_dec_ref(c, solver);
            Z3_del_context(c);
        }
    }
}
