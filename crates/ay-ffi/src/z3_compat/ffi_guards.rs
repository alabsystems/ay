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
            ptr::null_mut()
        }
    }
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
    unsafe {
        ffi_guard_const_ptr_keep_error(c, |ctx| {
            reset_error_state(ctx);
            f(ctx)
        })
    }
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
            0
        }
    }
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
    unsafe {
        ffi_guard_uint_keep_error(c, default_val, |ctx| {
            reset_error_state(ctx);
            f(ctx)
        })
    }
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
