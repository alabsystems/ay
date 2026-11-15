// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FFI panic guards (#6192): `catch_unwind` wrappers for extern "C" functions.
//!
//! Panics unwinding across `extern "C"` boundaries are undefined behavior.
//! These guards catch panics, record the error in the Z3Context, and return
//! a type-appropriate sentinel value.

use std::ffi::{c_char, c_int, c_uint};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::ptr;

use super::{Z3Context, Z3_ast, Z3_context, Z3_EXCEPTION, Z3_OK};

/// Extract a human-readable message from a panic payload.
pub(crate) fn panic_payload_to_string(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "unknown panic".to_string()
    }
}

/// Clear the per-context error state on entry to an API call.
///
/// libz3 resets the error code at the start of EVERY API entry point except the
/// error accessors themselves, so `Z3_get_error_code` always reports the outcome
/// of the most recent call rather than a stale error from an earlier one. These
/// guards are AY's equivalent chokepoint. Without this, one recoverable error
/// latches forever and every later `Z3_get_error_code` check fails spuriously —
/// which breaks any consumer (z3py included) that error-checks after each call.
///
/// The accessors use the `_keep_error` variants below so that reading the error
/// does not destroy it.
fn reset_error_state(ctx: &mut Z3Context) {
    ctx.last_error = Z3_OK;
    ctx.error_msg = None;
}

/// Invoke the caller's error handler (`Z3_set_error_handler`) once for the
/// error state the just-finished API call left behind, mirroring libz3,
/// which calls the handler from its error-raising path. Called only from
/// the error-RESETTING guards (never the `_keep_error` accessor guards, so
/// a handler that queries `Z3_get_error_code`/`Z3_get_error_msg` does not
/// re-trigger itself); the `error_handler_active` latch additionally
/// suppresses reentrant invocation while the handler runs.
///
/// # Safety
/// `ctx_ptr` must be a live context with no live `&mut` reference; the
/// handler receives the raw context pointer and may re-enter the API.
unsafe fn invoke_error_handler(ctx_ptr: *mut Z3Context) {
    // SAFETY: caller guarantees no live &mut to *ctx_ptr (see above).
    let (handler, code) = unsafe {
        let ctx = &*ctx_ptr;
        (ctx.error_handler, ctx.last_error)
    };
    let Some(handler) = handler else { return };
    if code == Z3_OK {
        return;
    }
    // SAFETY: same no-live-&mut guarantee; single-field write through ptr.
    unsafe {
        if (*ctx_ptr).error_handler_active {
            return;
        }
        (*ctx_ptr).error_handler_active = true;
    }
    // SAFETY: `handler` is the caller-supplied C callback registered via
    // `Z3_set_error_handler`; invoking it with the context pointer and the
    // Z3 error code is exactly its documented contract.
    unsafe { handler(ctx_ptr, code) };
    // SAFETY: same as the latch set above.
    unsafe { (*ctx_ptr).error_handler_active = false };
}

/// Guard an FFI function body that needs a context pointer and returns void.
/// On panic, sets `last_error = Z3_EXCEPTION` and records the panic message.
///
/// # Safety
/// - `c` must point to a valid, initialized `Z3Context` if non-null.
/// - No other mutable reference to `*c` may exist for the duration of `f`.
/// - The Z3 C API is single-threaded per context, so concurrent access is
///   ruled out by API contract.
pub(crate) unsafe fn ffi_guard_void(c: Z3_context, f: impl FnOnce(&mut Z3Context)) {
    // SAFETY: `c.as_mut()` is sound because the caller guarantees `c` is
    // either null or a valid, non-aliased pointer. The mutable reference
    // is passed into `f` and does not escape this function.
    let Some(ctx) = (unsafe { c.as_mut() }) else {
        return;
    };
    reset_error_state(ctx);
    let ctx_ptr = ptr::from_mut::<Z3Context>(ctx);
    if let Err(panic) = catch_unwind(AssertUnwindSafe(|| f(ctx))) {
        // SAFETY: The closure consumed `ctx`. On panic, the reference is
        // dead, so re-deriving from `ctx_ptr` does not create aliasing.
        let ctx = unsafe { &mut *ctx_ptr };
        ctx.last_error = Z3_EXCEPTION;
        ctx.error_msg = Some(format!(
            "panic in FFI: {}",
            panic_payload_to_string(&*panic)
        ));
    }
    // SAFETY: no &mut to *ctx_ptr is live past the closure/panic handling.
    unsafe { invoke_error_handler(ctx_ptr) };
}

/// Guard an FFI function body that needs a context pointer and returns `c_int`.
/// On panic, sets error state and returns `default_val`.
///
/// # Safety
/// Same invariants as [`ffi_guard_void`].
pub(crate) unsafe fn ffi_guard_int(
    c: Z3_context,
    default_val: c_int,
    f: impl FnOnce(&mut Z3Context) -> c_int,
) -> c_int {
    // SAFETY: the caller guarantees `c` is null or a live, non-aliased context;
    // `as_mut` checks for null before creating the unique reference.
    let Some(ctx) = (unsafe { c.as_mut() }) else {
        return default_val;
    };
    reset_error_state(ctx);
    let ctx_ptr = ptr::from_mut::<Z3Context>(ctx);
    let val = match catch_unwind(AssertUnwindSafe(|| f(ctx))) {
        Ok(val) => val,
        Err(panic) => {
            // SAFETY: closure consumed `ctx`; re-derive is non-aliasing.
            let ctx = unsafe { &mut *ctx_ptr };
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!(
                "panic in FFI: {}",
                panic_payload_to_string(&*panic)
            ));
            default_val
        }
    };
    // SAFETY: no &mut to *ctx_ptr is live past the closure/panic handling.
    unsafe { invoke_error_handler(ctx_ptr) };
    val
}

/// Guard an FFI function body that needs a context pointer and returns a pointer.
/// On panic, sets error state and returns null.
///
/// # Safety
/// Same invariants as [`ffi_guard_void`].
pub(crate) unsafe fn ffi_guard_ptr<T>(
    c: Z3_context,
    f: impl FnOnce(&mut Z3Context) -> *mut T,
) -> *mut T {
    // SAFETY: the caller guarantees `c` is null or a live, non-aliased context;
    // `as_mut` checks for null before creating the unique reference.
    let Some(ctx) = (unsafe { c.as_mut() }) else {
        return ptr::null_mut();
    };
    reset_error_state(ctx);
    let ctx_ptr = ptr::from_mut::<Z3Context>(ctx);
    let val = match catch_unwind(AssertUnwindSafe(|| f(ctx))) {
        Ok(val) => val,
        Err(panic) => {
            // SAFETY: closure consumed `ctx`; re-derive is non-aliasing.
            let ctx = unsafe { &mut *ctx_ptr };
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!(
                "panic in FFI: {}",
                panic_payload_to_string(&*panic)
            ));
            ptr::null_mut()
        }
    };
    // SAFETY: no &mut to *ctx_ptr is live past the closure/panic handling.
    unsafe { invoke_error_handler(ctx_ptr) };
    val
}

/// Guard an FFI function body that needs a context pointer and returns `*const c_char`.
/// On panic, sets error state and returns null.
///
/// # Safety
/// Same invariants as [`ffi_guard_void`].
pub(crate) unsafe fn ffi_guard_const_ptr(
    c: Z3_context,
    f: impl FnOnce(&mut Z3Context) -> *const c_char,
) -> *const c_char {
    // SAFETY: see ffi_guard_void; the reset is the only added behavior.
    let val = unsafe {
        ffi_guard_const_ptr_keep_error(c, |ctx| {
            reset_error_state(ctx);
            f(ctx)
        })
    };
    if !c.is_null() {
        // SAFETY: the inner guard's &mut is dead; `c` is a live context.
        unsafe { invoke_error_handler(c) };
    }
    val
}

/// [`ffi_guard_const_ptr`] without the entry reset, for `Z3_get_error_msg`:
/// reading the error state must not clear it.
///
/// # Safety
/// Same invariants as [`ffi_guard_void`].
pub(crate) unsafe fn ffi_guard_const_ptr_keep_error(
    c: Z3_context,
    f: impl FnOnce(&mut Z3Context) -> *const c_char,
) -> *const c_char {
    // SAFETY: the caller guarantees `c` is null or a live, non-aliased context;
    // `as_mut` checks for null before creating the unique reference.
    let Some(ctx) = (unsafe { c.as_mut() }) else {
        return ptr::null();
    };
    let ctx_ptr = ptr::from_mut::<Z3Context>(ctx);
    match catch_unwind(AssertUnwindSafe(|| f(ctx))) {
        Ok(val) => val,
        Err(panic) => {
            // SAFETY: closure consumed `ctx`; re-derive is non-aliasing.
            let ctx = unsafe { &mut *ctx_ptr };
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!(
                "panic in FFI: {}",
                panic_payload_to_string(&*panic)
            ));
            ptr::null()
        }
    }
}

/// Guard an FFI function body that needs a context pointer and returns `Z3_ast` (u64).
/// On panic, sets error state and returns 0 (null AST).
///
/// # Safety
/// Same invariants as [`ffi_guard_void`].
pub(crate) unsafe fn ffi_guard_ast(
    c: Z3_context,
    f: impl FnOnce(&mut Z3Context) -> Z3_ast,
) -> Z3_ast {
    // SAFETY: the caller guarantees `c` is null or a live, non-aliased context;
    // `as_mut` checks for null before creating the unique reference.
    let Some(ctx) = (unsafe { c.as_mut() }) else {
        return 0;
    };
    reset_error_state(ctx);
    let ctx_ptr = ptr::from_mut::<Z3Context>(ctx);
    let val = match catch_unwind(AssertUnwindSafe(|| f(ctx))) {
        Ok(val) => val,
        Err(panic) => {
            // SAFETY: closure consumed `ctx`; re-derive is non-aliasing.
            let ctx = unsafe { &mut *ctx_ptr };
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!(
                "panic in FFI: {}",
                panic_payload_to_string(&*panic)
            ));
            0
        }
    };
    // SAFETY: no &mut to *ctx_ptr is live past the closure/panic handling.
    unsafe { invoke_error_handler(ctx_ptr) };
    val
}

/// [`ffi_guard_ast`] for a `Z3_mk_*` entry named `entry`: also records
/// whether the term it returns is exactly the application the caller built
/// (see `provenance.rs`), which `Z3_substitute` and `Z3_update_term` rely on.
///
/// # Safety
/// Same invariants as [`ffi_guard_void`].
pub(crate) unsafe fn ffi_guard_mk(
    c: Z3_context,
    entry: &'static str,
    f: impl FnOnce(&mut Z3Context) -> Z3_ast,
) -> Z3_ast {
    // SAFETY: the caller guarantees `c` is null or a live, non-aliased
    // context; the reference ends before `ffi_guard_ast` re-derives one.
    let Some(ctx) = (unsafe { c.as_mut() }) else {
        return 0;
    };
    let token = ctx.provenance.begin(entry);
    // SAFETY: forwarded from this function's contract.
    let ast = unsafe { ffi_guard_ast(c, f) };
    // SAFETY: `c` is non-null (checked above) and live per this function's
    // contract; `ffi_guard_ast` no longer holds a reference.
    let ctx = unsafe { &mut *c };
    // Recording never fails the call: a panic here would only lose evidence.
    let recorded = catch_unwind(AssertUnwindSafe(|| {
        super::provenance::end_mk(ctx, token, ast);
        super::zstring::refuse_under_non_unicode_encoding(ctx, ast)
    }));
    match recorded {
        Ok(false) => ast,
        Ok(true) => 0,
        Err(_) => {
            // SAFETY: `c` is non-null (checked at entry) and live per this
            // function's contract; the closure that borrowed it has returned.
            let ctx = unsafe { &mut *c };
            let result = super::checked_ast_to_pub(ctx, ast).map(|built| built.term);
            ctx.provenance.abandon(result);
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!("{entry}: internal error while checking the result"));
            0
        }
    }
}

/// Arithmetic constructor whose retained original request also covers the
/// existing provenance finish. Capturing it inside the body and dropping it
/// before end_mk would release its prepaid scratch too early.
///
/// # Safety
/// Same live, exclusive context contract as ffi_guard_mk.
pub(crate) unsafe fn ffi_guard_arithmetic_owned(
    c: Z3_context,
    entry: &'static str,
    arguments: usize,
    f: impl FnOnce(&mut Z3Context, &ay_dpll::api::TacticOperation) -> Z3_ast,
) -> Z3_ast {
    let mut operation = None;
    // SAFETY: forwarded exclusive-context contract; the original guard catches
    // unwinding and restores/poisons its provenance scope as before.
    let result = unsafe {
        ffi_guard_mk(c, entry, |ctx| {
            let captured = match ctx.solver.begin_tactic_operation() {
                Ok(captured) => captured,
                Err(error) => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(error.to_string());
                    return 0;
                }
            };
            operation = Some(captured);
            let Some(captured) = operation.as_ref() else {
                return 0;
            };
            if ctx
                .provenance
                .prepare_arithmetic_owned(arguments, captured.admission())
                .is_err()
                || !captured.validate(&ctx.solver)
            {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some("arithmetic constructor original owner refused".into());
                return 0;
            }
            let result = f(ctx, captured);
            if result != 0 && ctx.last_error == Z3_OK {
                let actual = super::checked_ast_to_pub(ctx, result)
                    .and_then(|node| ctx.solver.try_term_child_count(node.term).ok())
                    .and_then(|count| ctx.provenance.arithmetic_comparison_work(count));
                if actual.is_none_or(|work| captured.admission().admit(work, 0).is_err())
                    || !captured.validate(&ctx.solver)
                {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some("constructor provenance comparison refused".into());
                    return 0;
                }
            }
            result
        })
    };
    if let Some(operation) = operation.as_ref() {
        // SAFETY: ffi_guard_mk has released its borrow; c is live/exclusive
        // under the same forwarded contract and is checked for null.
        if let Some(ctx) = unsafe { c.as_mut() } {
            if !operation.validate(&ctx.solver) {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some("arithmetic constructor publication refused".into());
                return 0;
            }
        }
    }
    result
}

/// [`ffi_guard_ast`] for an entry that returns a term produced by AY's own
/// rewriting (simplifier, model, goal, quantifier elimination, ...): the
/// result is marked as possibly standing for a differently structured z3 term
/// (see `provenance.rs`).
///
/// # Safety
/// Same invariants as [`ffi_guard_void`].
pub(crate) unsafe fn ffi_guard_produced(
    c: Z3_context,
    f: impl FnOnce(&mut Z3Context) -> Z3_ast,
) -> Z3_ast {
    // SAFETY: forwarded from this function's contract.
    let ast = unsafe { ffi_guard_ast(c, f) };
    // SAFETY: the caller guarantees `c` is null or a live, non-aliased
    // context; `ffi_guard_ast` no longer holds a reference.
    if let Some(ctx) = unsafe { c.as_mut() } {
        if catch_unwind(AssertUnwindSafe(|| {
            super::provenance::mark_produced(ctx, ast)
        }))
        .is_err()
        {
            // SAFETY: `c` is non-null (`as_mut` succeeded) and live per this
            // function's contract; the closure that borrowed it has returned.
            let ctx = unsafe { &mut *c };
            ctx.provenance.taint_all();
        }
    }
    ast
}

/// Guard an FFI function body that needs a context pointer and returns `f64`.
/// On panic, sets error state and returns `default_val`.
///
/// # Safety
/// Same invariants as [`ffi_guard_void`].
pub(crate) unsafe fn ffi_guard_double(
    c: Z3_context,
    default_val: f64,
    f: impl FnOnce(&mut Z3Context) -> f64,
) -> f64 {
    // SAFETY: the caller guarantees `c` is null or a live, non-aliased context;
    // `as_mut` checks for null before creating the unique reference.
    let Some(ctx) = (unsafe { c.as_mut() }) else {
        return default_val;
    };
    reset_error_state(ctx);
    let ctx_ptr = ptr::from_mut::<Z3Context>(ctx);
    let val = match catch_unwind(AssertUnwindSafe(|| f(ctx))) {
        Ok(val) => val,
        Err(panic) => {
            // SAFETY: closure consumed `ctx`; re-derive is non-aliasing.
            let ctx = unsafe { &mut *ctx_ptr };
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!(
                "panic in FFI: {}",
                panic_payload_to_string(&*panic)
            ));
            default_val
        }
    };
    // SAFETY: no &mut to *ctx_ptr is live past the closure/panic handling.
    unsafe { invoke_error_handler(ctx_ptr) };
    val
}

/// Guard an FFI function body that needs a context pointer and returns `c_uint`.
/// On panic, sets error state and returns `default_val`.
///
/// # Safety
/// Same invariants as [`ffi_guard_void`].
pub(crate) unsafe fn ffi_guard_uint(
    c: Z3_context,
    default_val: c_uint,
    f: impl FnOnce(&mut Z3Context) -> c_uint,
) -> c_uint {
    // SAFETY: see ffi_guard_void; the reset is the only added behavior.
    let val = unsafe {
        ffi_guard_uint_keep_error(c, default_val, |ctx| {
            reset_error_state(ctx);
            f(ctx)
        })
    };
    if !c.is_null() {
        // SAFETY: the inner guard's &mut is dead; `c` is a live context.
        unsafe { invoke_error_handler(c) };
    }
    val
}

/// [`ffi_guard_uint`] without the entry reset, for `Z3_get_error_code`: reading
/// the error code must not clear it.
///
/// # Safety
/// Same invariants as [`ffi_guard_void`].
pub(crate) unsafe fn ffi_guard_uint_keep_error(
    c: Z3_context,
    default_val: c_uint,
    f: impl FnOnce(&mut Z3Context) -> c_uint,
) -> c_uint {
    // SAFETY: the caller guarantees `c` is null or a live, non-aliased context;
    // `as_mut` checks for null before creating the unique reference.
    let Some(ctx) = (unsafe { c.as_mut() }) else {
        return default_val;
    };
    let ctx_ptr = ptr::from_mut::<Z3Context>(ctx);
    match catch_unwind(AssertUnwindSafe(|| f(ctx))) {
        Ok(val) => val,
        Err(panic) => {
            // SAFETY: closure consumed `ctx`; re-derive is non-aliasing.
            let ctx = unsafe { &mut *ctx_ptr };
            ctx.last_error = Z3_EXCEPTION;
            ctx.error_msg = Some(format!(
                "panic in FFI: {}",
                panic_payload_to_string(&*panic)
            ));
            default_val
        }
    }
}
