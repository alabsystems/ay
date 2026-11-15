// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof callbacks run between short context borrows, never inside an FFI guard.
use super::{
    eval_session::{EvalSession, ProofEvent},
    *,
};
use ay_dpll::{api::NativeProofInputBinding, Executor};
use std::{
    ffi::{c_void, CStr},
    panic::{catch_unwind, AssertUnwindSafe},
};

#[allow(non_camel_case_types)]
pub type Z3_proof_check_eh =
    Option<unsafe extern "C" fn(*mut c_void, Z3_context, Z3_ast, Z3_ast_vector) -> Z3_string>;

/// Replace or unregister the client checker. Registration survives script reset.
///
/// # Safety
/// `c` is live; callback/user storage lives until replacement or destruction.
/// The callback must not delete c, reenter evaluation on c, or unwind across C.
#[no_mangle]
pub unsafe extern "C" fn Z3_set_proof_check_callback(
    c: Z3_context,
    user: *mut c_void,
    callback: Z3_proof_check_eh,
) {
    // SAFETY: caller provides the live context; the guard catches Rust panics.
    unsafe {
        ffi_guard_void(c, |ctx| {
            ctx.proof_check_callback = callback;
            ctx.proof_check_user_context = if callback.is_some() {
                user
            } else {
                std::ptr::null_mut()
            };
        })
    }
}

struct EvalLease {
    context: Z3_context,
    session: Option<EvalSession>,
}

impl Drop for EvalLease {
    fn drop(&mut self) {
        if self.session.is_none() {
            return;
        }
        // SAFETY: the evaluator owns this live context's session. Client code
        // may not delete it; no context reference survives between guards.
        unsafe {
            ffi_guard_void(self.context, |ctx| {
                ctx.eval_session = self.session.take();
                ctx.eval_active = false;
            })
        }
    }
}

#[derive(Clone, Copy)]
struct Invocation {
    callback: unsafe extern "C" fn(*mut c_void, Z3_context, Z3_ast, Z3_ast_vector) -> Z3_string,
    user: *mut c_void,
    proof: Z3_ast,
    inputs: Z3_ast_vector,
}

/// c is live and exclusively used by this thread, except permitted callback
/// reentry. No Rust reference into c exists when foreign code runs.
unsafe fn proof_event(
    c: Z3_context,
    source: &Executor,
    bindings: &[NativeProofInputBinding],
    event: ProofEvent,
    ready: bool,
) -> Result<Option<String>, String> {
    let mut invocation = None;
    let mut view = None;
    let mut error = None;
    // SAFETY: each guard is a separate context borrow; it ends before callback.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if matches!(event, ProofEvent::UnsatCheck) && ctx.proof_check_callback.is_none() {
                return;
            }
            if matches!(event, ProofEvent::UnsatCheck) && (!ready || !source.is_producing_proofs())
            {
                error = Some(
                    "proof checking callback requires proof production before assertions"
                        .to_owned(),
                );
                return;
            }
            let Some((dag, inputs)) = ctx.solver.import_executor_proof_dag_with_tracking(
                source,
                bindings,
                &mut ctx.proof_tracking,
            ) else {
                if matches!(event, ProofEvent::UnsatCheck) {
                    error = Some("proof is not available for the proof checking callback (unsupported native fragment or premise binding)".to_owned());
                }
                return;
            };
            let Some(proof) = super::proof_dag::materialize(ctx, &dag) else {
                if matches!(event, ProofEvent::UnsatCheck) {
                    error =
                        Some("proof is not available for the proof checking callback".to_owned());
                }
                return;
            };
            match event {
                ProofEvent::GetProof => {
                    view = super::proofs::proof_text_for_ast(ctx, proof).map(str::to_owned)
                }
                ProofEvent::UnsatCheck => {
                    let Some(callback) = ctx.proof_check_callback else {
                        return;
                    };
                    let inputs = inputs
                        .into_iter()
                        .map(|term| term_to_ast(ctx, term))
                        .collect();
                    let inputs = cache_ast_vector(ctx, inputs);
                    invocation = Some(Invocation {
                        callback,
                        user: ctx.proof_check_user_context,
                        proof,
                        inputs,
                    });
                }
            }
        })
    }
    if let Some(error) = error {
        return Err(error);
    }
    let Some(call) = invocation else {
        return Ok(view);
    };
    // SAFETY: registered C callback and data are live by the registration
    // contract. Proof and vector are pinned by the context-owned arenas. The
    // context guard and all references derived from it have ended above.
    let report = unsafe { (call.callback)(call.user, c, call.proof, call.inputs) };
    if report.is_null() {
        return Err("proof checking callback returned null".to_owned());
    }
    // SAFETY: client promises NUL-terminated storage valid immediately after
    // callback return. Copy before any further callback can reuse that storage.
    let report = unsafe { CStr::from_ptr(report) }
        .to_str()
        .map_err(|_| "proof checking callback report is not UTF-8".to_owned())?
        .to_owned();
    Ok(Some(report))
}

/// # Safety
/// c is null or live; input was decoded and bounded at the public ABI boundary.
pub(super) unsafe fn evaluate(c: Z3_context, input: &str) -> Z3_string {
    let mut lease = None;
    // SAFETY: the initial borrow ends before command execution or client code.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if ctx.eval_active {
                ctx.last_error = Z3_INVALID_USAGE;
                ctx.error_msg = Some("recursive SMT-LIB evaluation is not permitted".to_owned());
                return;
            }
            ctx.eval_active = true;
            let session = ctx
                .eval_session
                .take()
                .unwrap_or_else(|| EvalSession::with_proofs(ctx.solver.is_producing_proofs()));
            lease = Some(EvalLease {
                context: c,
                session: Some(session),
            });
        })
    }
    let Some(mut lease) = lease else {
        // SAFETY: preserve the recursive-eval error established above.
        return unsafe {
            ffi_guard_const_ptr_keep_error(c, |ctx| {
                cache_string(
                    ctx,
                    "(error \"recursive SMT-LIB evaluation is not permitted\")\n".to_owned(),
                )
            })
        };
    };
    let result = catch_unwind(AssertUnwindSafe(|| {
        lease.session.as_mut().map(|session| {
            session.evaluate_with_proof_view(input, |source, bindings, event, ready| {
                // SAFETY: source is owned outside c; proof_event borrows c only in
                // separate guards and releases every borrow before invoking C.
                unsafe { proof_event(c, source, bindings, event, ready) }
            })
        })
    }));
    // SAFETY: command execution/callback is finished; no context refs survive.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            ctx.eval_session = lease.session.take();
            ctx.eval_active = false;
            match result {
                Ok(Some(reply)) => {
                    ctx.last_error = if reply.error.is_some() {
                        Z3_PARSER_ERROR
                    } else {
                        Z3_OK
                    };
                    ctx.error_msg = reply.error;
                    cache_string(ctx, reply.text)
                }
                _ => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some("panic during SMT-LIB evaluation".to_owned());
                    cache_string(
                        ctx,
                        "(error \"panic during SMT-LIB evaluation\")\n".to_owned(),
                    )
                }
            }
        })
    }
}
