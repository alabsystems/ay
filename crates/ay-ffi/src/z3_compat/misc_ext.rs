// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible miscellaneous C-API surface.
//!
//! Implements the assorted "utility" corner of the Z3 C API that does not fit a
//! dedicated module: AST/sort/func_decl casts, the error/print-mode setters, the
//! per-context parameter-value update, cross-context AST translation, recursive
//! function definitions, the process-global interaction-log surface
//! (`Z3_open_log`/`Z3_append_log`/`Z3_close_log`), the trace/memory/concurrency
//! no-ops, params/pattern/apply-result stringification, the `simplify` parameter
//! surface, benchmark emission, and SMT-LIB2 file parsing / string evaluation.
//!
//! # Honesty
//!
//! Where AY lacks a Z3 capability, the function sets a Z3 error code and returns
//! a SOUND sentinel (`0` / `false` / null) rather than fabricating a value; each
//! such case is flagged with a `DIVERGENCE:` note in its doc comment. Nothing
//! here manufactures a term, sort, or verdict AY did not actually compute.

use std::ffi::c_uint;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::ptr;
use std::sync::Mutex;

use ay_dpll::api::{Sort, Term, TermKind};
use ay_dpll::Executor;
use ay_frontend::parse;

use super::model_params::eval_term_under_model;
use super::{
    apply_supported_params, cache_ast_vector, cache_string, checked_ast_to_term,
    ensure_cross_context_translation_semantics, ffi_count_within_limit, ffi_guard_ast,
    ffi_guard_const_ptr, ffi_guard_ptr, ffi_guard_uint, ffi_guard_void,
    ffi_read_bounded_parser_file, ffi_read_bounded_parser_text, ffi_read_bounded_text,
    record_ast_sort, require_term_ast_or_return, require_term_asts_or_return, sort_handle_to_ast,
    term_to_ast, transfer_cross_context_ffi_metadata, ModelHandle, ParamDescr, ParamDescrsHandle,
    Z3Context, Z3_apply_result, Z3_ast, Z3_ast_vector, Z3_constructor, Z3_context, Z3_func_decl,
    Z3_model, Z3_param_descrs, Z3_params, Z3_pattern, Z3_sort, Z3_string, Z3_symbol,
    HANDLE_TAG_MASK, Z3_EXCEPTION, Z3_INVALID_ARG, Z3_OK, Z3_PK_BOOL,
};

// ============================================================================
// Small local helper.
// ============================================================================

/// Decode a `Z3_string` argument into an owned `String`.
///
/// Returns `None` for a null pointer or non-UTF-8 contents (callers treat both
/// as "absent/invalid").
///
/// # Safety
/// `s`, when non-null, must point to a valid null-terminated C string owned by
/// the caller for the duration of this call.
unsafe fn cstr_opt(s: Z3_string) -> Option<String> {
    if s.is_null() {
        return None;
    }
    // SAFETY: `s` is non-null (checked above) and valid per this fn's contract;
    // the shared helper bounds the scan and clone.
    unsafe { ffi_read_bounded_text(s) }.ok()
}

// ============================================================================
// AST / sort / func_decl casts.
// ============================================================================

/// Convert an `app` node to an AST (Z3's `Z3_app_to_ast`).
///
/// In AY, `Z3_app`, `Z3_ast`, and the internal term id are all the same `u64`
/// handle (see `Z3_to_app` in `accessors.rs`), so this is a pure identity cast:
/// `a` is returned unchanged. No solver call.
///
/// # Safety
/// `c` must be a valid context pointer (unused).
#[no_mangle]
pub unsafe extern "C" fn Z3_app_to_ast(_c: Z3_context, a: Z3_ast) -> Z3_ast {
    a
}

/// Convert a sort to an AST (Z3's `Z3_sort_to_ast`).
///
/// Returns a value-canonical, context-salted tagged handle: the same semantic
/// `Sort` in one context always yields the SAME `Z3_ast`, so `Z3_is_eq_ast`,
/// `Z3_get_ast_id`, and dict/hash use through z3py behave exactly like z3's
/// hash-consed sort asts. The tag keeps the handle disjoint from every term
/// (see `HANDLE_TAG_MASK`); a tagged handle leaking into a term-consuming entry
/// point fails closed via authenticated term-handle decoding. A null sort or a
/// sort owned by another context returns the null AST (`0`).
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid sort
/// handle owned by `c`.
#[no_mangle]
pub unsafe extern "C" fn Z3_sort_to_ast(c: Z3_context, s: Z3_sort) -> Z3_ast {
    if s.is_null() {
        return 0;
    }
    // SAFETY: `c` is the caller-supplied context pointer; `ffi_guard_ast`
    // handles the null case and catches panics. `s` is null-checked above and
    // owned by the context arena per the safety contract.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if !ctx.sort_cache.contains(&s) {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_sort_to_ast: sort handle belongs to a different context".to_string());
                return 0;
            }
            ctx.last_error = Z3_OK;
            sort_handle_to_ast(ctx, s)
        })
    }
}

/// Convert an AST back to a func_decl (Z3's `Z3_to_func_decl`).
///
/// A FUNC-DECL-AST handle (from `Z3_func_decl_to_ast`) decodes to the
/// CANONICAL `Z3_func_decl` for that declaration — usable in `Z3_mk_app` etc.
/// It may differ pointer-wise from the handle the ast was minted from (AY does
/// not hash-cons `Z3_mk_func_decl`); `Z3_is_eq_func_decl` value-compares, and
/// no z3py flow compares decl pointers raw. Anything else — including a TERM
/// ast, where z3 performs an unchecked identity cast (UB we refuse to copy) —
/// sets `Z3_INVALID_ARG` and returns null: a strictly-safer documented
/// divergence.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_to_func_decl(c: Z3_context, a: Z3_ast) -> Z3_func_decl {
    // SAFETY: `c` is the caller-supplied context pointer; `ffi_guard_ptr` handles
    // the null case and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let handle = super::func_decl_ast_to_handle(ctx, a);
            if !handle.is_null() {
                return handle;
            }
            ctx.last_error = Z3_INVALID_ARG;
            ctx.error_msg = Some(
                "Z3_to_func_decl: argument is not a func_decl AST (AY refuses z3's \
                 unchecked identity cast on non-decl ASTs)"
                    .to_string(),
            );
            ptr::null_mut()
        })
    }
}

// ============================================================================
// Error / print-mode / parameter setters.
// ============================================================================

/// Set the context's current error code (Z3's `Z3_set_error`).
///
/// Directly assigns `ctx.last_error = e`. Used by callers to inject an error code
/// (including `Z3_OK` to clear a prior error).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_set_error(c: Z3_context, e: c_uint) {
    // SAFETY: `ffi_guard_void` handles a null context and catches panics.
    unsafe {
        ffi_guard_void(c, |ctx| {
            ctx.last_error = e;
        });
    }
}

/// Set the AST pretty-printing mode (Z3's `Z3_set_ast_print_mode`).
///
/// Documented no-op: AY's term formatter always emits SMT-LIB2 syntax (the
/// `Z3_PRINT_SMTLIB2_COMPLIANT` shape), so the requested `mode` cannot change the
/// rendering. Accepted for API compatibility and ignored — it never affects a
/// verdict or a stringification's meaning.
///
/// # Safety
/// `c` must be a valid context pointer (unused).
#[no_mangle]
pub unsafe extern "C" fn Z3_set_ast_print_mode(_c: Z3_context, _mode: c_uint) {}

/// Update a configuration parameter on an existing context (Z3's
/// `Z3_update_param_value`).
///
/// Unlike `Z3_global_param_set` (process-global), this targets THIS context's
/// solver. Runtime controls (`timeout`, proof production) are applied through
/// the same typed path as solver/optimize params, while the normalized option
/// is also installed in the frontend (for example `opt.priority`). Successful
/// updates retire all copied solver/optimize decision artifacts.
///
/// # Safety
/// `c` must be a valid context pointer; `param_id`/`param_value`, when non-null,
/// must be valid null-terminated C strings.
#[no_mangle]
pub unsafe extern "C" fn Z3_update_param_value(
    c: Z3_context,
    param_id: Z3_string,
    param_value: Z3_string,
) {
    // Decode both strings outside the guard (raw-pointer derefs).
    // SAFETY: each pointer, when non-null, is a valid C string per the contract.
    let (key, value) = unsafe { (cstr_opt(param_id), cstr_opt(param_value)) };
    // SAFETY: `ffi_guard_void` handles a null context and catches panics.
    unsafe {
        ffi_guard_void(c, |ctx| match (key, value) {
            (Some(k), Some(v)) => {
                if !ctx.decision_engine_is_usable("Z3_update_param_value") {
                    return;
                }
                let normalized = k.trim().trim_start_matches(':');
                if normalized.is_empty() {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some("Z3_update_param_value: empty param id".to_string());
                    return;
                }
                let frontend_key = format!(":{normalized}");
                if let Err(e) = ctx.solver.try_set_option(&frontend_key, &v) {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("Z3_update_param_value: {e}"));
                    return;
                }
                apply_supported_params(&mut ctx.solver, &[(normalized.to_string(), v)]);
                ctx.clear_decision_check_artifacts();
                ctx.last_error = Z3_OK;
                ctx.error_msg = None;
            }
            _ => {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_update_param_value: null/invalid param id or value".to_string());
            }
        });
    }
}

// ============================================================================
// Cross-context AST translation.
// ============================================================================

/// Translate AST `a` from context `source` into context `target` (Z3's
/// `Z3_translate`).
///
/// When `source == target` the handle is already valid in `target`, so `a` is
/// returned unchanged. Across DISTINCT contexts a `Z3_ast` from `source` is
/// meaningless in `target`, so the term's whole DAG is re-interned into
/// `target`'s term store via `Solver::translate_terms_from` — a faithful deep
/// copy, never a fabricated term. The operation is refused when source
/// context-resident semantic metadata cannot be represented by that DAG copy.
///
/// # Safety
/// `source`/`target` must be valid context pointers; `a` is a `u64` handle valid
/// in `source`.
#[no_mangle]
pub unsafe extern "C" fn Z3_translate(source: Z3_context, a: Z3_ast, target: Z3_context) -> Z3_ast {
    // SAFETY: `target` is the destination context; `ffi_guard_ast` handles a null
    // context and catches panics, returning `0` (null AST) on failure.
    unsafe {
        ffi_guard_ast(target, |tgt| {
            // Tagged non-term handle (proof / algebraic / sort-ast /
            // func-decl-ast): not a translatable term DAG. Fail closed rather
            // than let the poison id reach the copier.
            if a & HANDLE_TAG_MASK != 0 {
                tgt.last_error = Z3_INVALID_ARG;
                tgt.error_msg = Some("Z3_translate: argument is not a term AST".to_string());
                return 0;
            }
            // Same context: authenticate before returning the identity handle;
            // otherwise this API would launder a colliding foreign handle.
            if source == target {
                if checked_ast_to_term(tgt, a).is_none() {
                    tgt.last_error = Z3_INVALID_ARG;
                    tgt.error_msg = Some(
                        "Z3_translate: argument is invalid or belongs to a different context"
                            .to_string(),
                    );
                    return 0;
                }
                tgt.last_error = Z3_OK;
                return a;
            }
            // Cross-context: re-intern the term DAG into `target`'s store.
            // SAFETY: `source != target`, so this shared borrow does not alias
            // `tgt`; dereferenced under the enclosing `unsafe`.
            let Some(src) = source.as_ref() else {
                tgt.last_error = Z3_INVALID_ARG;
                tgt.error_msg = Some("Z3_translate: null source context".to_string());
                return 0;
            };
            let Some(src_term) = checked_ast_to_term(src, a) else {
                tgt.last_error = Z3_INVALID_ARG;
                tgt.error_msg = Some(
                    "Z3_translate: argument is invalid or belongs to a different source context"
                        .to_string(),
                );
                return 0;
            };
            if !ensure_cross_context_translation_semantics(src, tgt, "Z3_translate") {
                return 0;
            }
            let new_terms = tgt.solver.translate_terms_from(&src.solver, &[src_term]);
            let Some(&new_term) = new_terms.first() else {
                tgt.last_error = Z3_EXCEPTION;
                tgt.error_msg =
                    Some("Z3_translate: term translation produced no result".to_string());
                return 0;
            };
            if !transfer_cross_context_ffi_metadata(
                src,
                tgt,
                &[src_term],
                &[new_term],
                "Z3_translate",
            ) {
                return 0;
            }
            let ast = term_to_ast(tgt, new_term);
            let sort = src.solver.term_sort(src_term);
            record_ast_sort(tgt, ast, sort);
            tgt.last_error = Z3_OK;
            ast
        })
    }
}

// ============================================================================
// Recursive function definition.
// ============================================================================

/// Attach a recursive definition to the func_decl `f` (Z3's `Z3_add_rec_def`).
///
/// Installs the defining axiom `(forall (args...) (= (f args...) body))` as
/// durable context semantics, built from real engine primitives: `Solver::try_apply`
/// constructs the uninterpreted application `f(args)` (AY does NOT register `f`
/// in `defined_funs`, so the application is genuinely symbolic, not inlined),
/// `try_eq` builds the equation, and `try_forall` universally closes it over the
/// bound argument variables. A ground definition (`n == 0`) asserts the bare
/// equation.
///
/// It ALSO registers the definition in `ctx.rec_fun_defs` for check-time
/// bounded expansion (P1.1, the Term-level twin of the SMT-LIB `fun_defs`
/// machinery): a goal whose `f`-applications fully expand is solved without
/// the quantified axiom (this is what lets `fact(5) == 120` decide `sat`),
/// while any expansion failure keeps the axiom and demotes an engine `sat`
/// to `unknown` — fail-closed, never a plain-UF `sat`.
///
/// Two argument classes are rejected outright (error, nothing registered):
/// a name AY matches structurally as a BUILTIN operator (`+`, `and`, `ite`,
/// …) — splicing a user body into builtin nodes is a confirmed wrong-verdict
/// class — and a RE-definition of an already-defined name (z3 parity:
/// "function ... has already been given a definition"; add-only registries
/// are also what keeps live model handles' stale-eval protection sound).
///
/// This is a SOUND axiom: it states exactly what the recursive definition means.
/// If the arguments are not proper bound variables (so `try_forall` cannot
/// universally close soundly), or an argument/sort is invalid, the function sets
/// an honest error and asserts NOTHING — it never asserts a formula with dangling
/// free variables or a fabricated axiom.
///
/// # Safety
/// `c` must be a valid context pointer; `f`, when non-null, a valid func_decl
/// handle; `args`, when `n > 0`, must point to `n` valid `Z3_ast` handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_add_rec_def(
    c: Z3_context,
    f: Z3_func_decl,
    n: c_uint,
    args: *const Z3_ast,
    body: Z3_ast,
) {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the helper only mutates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_add_rec_def", n) } {
        return;
    }
    // Pre-extract the decl and argument handles outside the guard (raw derefs).
    // SAFETY: `f`, when non-null, is a live `FuncDeclHandle`; `as_ref` null-checks.
    let decl_handle = unsafe { f.as_ref() };
    let decl = decl_handle.map(|h| h.decl.clone());
    let api_name = decl_handle.and_then(|h| h.symbol.as_ref().map(super::SymbolKey::display_name));
    let mut arg_asts: Vec<Z3_ast> = Vec::new();
    if n > 0 && !args.is_null() {
        for i in 0..n as usize {
            // SAFETY: `args` points to at least `n` elements per the contract; the
            // count was range-checked and the pointer null-checked above.
            arg_asts.push(unsafe { *args.add(i) });
        }
    }

    // SAFETY: `ffi_guard_void` handles a null context and catches panics.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if n > 0 && args.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_add_rec_def: null args array for non-zero count".to_string());
                return;
            }
            let Some(decl) = decl else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_add_rec_def: null func_decl handle".to_string());
                return;
            };
            let arg_terms = require_term_asts_or_return!(ctx, &arg_asts, "Z3_add_rec_def");
            let body_term =
                require_term_ast_or_return!(ctx, body, "Z3_add_rec_def", "definition body");
            // Recursive definitions are declaration semantics consumed by both
            // Solver and Optimize. They do not select one family, but a context
            // already poisoned by a partial transaction must remain unusable.
            if !ctx.decision_engine_is_usable("Z3_add_rec_def") {
                return;
            }
            let name = decl.name().to_string();
            let display_name = api_name.as_deref().unwrap_or(&name);
            // BUILTIN-NAME GUARD (skeptic finding: '+' := '*' made 2+3==6 sat
            // with an invalid model). AY represents builtin operators as
            // `App(Symbol::Named("+"), ..)`, so BOTH the defining axiom
            // (`∀x,y. x+y = body`) and the check-time expander would rewrite
            // builtin semantics. Registering NOTHING and erroring honestly is
            // the only sound option (z3 accepts these names because its decls
            // are nominal objects; AY's are name-matched).
            if ay_dpll::api::rec_def_name_conflates_with_builtin(display_name) {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_add_rec_def: '{display_name}' is a builtin operator name in AY; a recursive \
                     definition of it would rewrite builtin semantics and is rejected"
                ));
                return;
            }
            // REDEFINITION GUARD (z3 parity: "function ... has already been
            // given a definition"). Rejecting keeps the registry
            // add-only, which is what makes live model handles' stale-eval
            // protection (`ModelHandle::rec_def_count`) sound: a model can
            // never outlive a definition CHANGE, only predate an addition.
            if ctx.rec_fun_defs.contains_key(&name) || ctx.rec_def_axiom_index.contains_key(&name) {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_add_rec_def: function '{name}' has already been given a definition"
                ));
                return;
            }
            // lhs = f(args...)
            let lhs = match ctx.solver.try_apply(&decl, &arg_terms) {
                Ok(t) => t,
                Err(e) => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("Z3_add_rec_def: {e}"));
                    return;
                }
            };
            // eq = (= (f args...) body)
            let eq = match ctx.solver.try_eq(lhs, body_term) {
                Ok(t) => t,
                Err(e) => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("Z3_add_rec_def: {e}"));
                    return;
                }
            };
            // Universally close over the bound variables (if any).
            let axiom = if arg_terms.is_empty() {
                eq
            } else {
                match ctx.solver.try_forall(&arg_terms, eq) {
                    Ok(t) => t,
                    Err(e) => {
                        // Cannot build the quantified definition soundly (args are
                        // not proper bound variables). Do NOT assert a free-var
                        // formula — report honestly and assert nothing.
                        ctx.last_error = Z3_INVALID_ARG;
                        ctx.error_msg = Some(format!(
                            "Z3_add_rec_def: cannot universally close definition ({e}); \
                             arguments must be bound variables"
                        ));
                        return;
                    }
                }
            };
            // Register the definition for check-time expansion (P1.1). The
            // builder computes the capture-relevant name sets; a body whose
            // binders shadow a parameter is registered NON-expandable, so its
            // uses are still detected at every solve site (residual mode:
            // axiom-only, `sat` demoted) without ever being mis-substituted.
            let def = ctx.solver.make_rec_fun_def(&arg_terms, body_term);
            // First (and, per the redefinition guard above, ONLY) definition
            // of this name: the registry and axiom list are add-only.
            ctx.rec_def_axiom_index
                .insert(name.clone(), ctx.global_definition_axioms.len());
            ctx.global_definition_axioms.push(axiom);
            ctx.rec_fun_defs.insert(name, def);
            // A new definition changes every handle's semantic problem. Models,
            // cores, reasons, proofs, bounds, and statistics copied before this
            // point are no longer authoritative.
            ctx.clear_decision_check_artifacts();
            ctx.last_error = Z3_OK;
            ctx.error_msg = None;
        });
    }
}

// ============================================================================
// Interaction log (process-global; matches Z3's stateless log surface).
// ============================================================================

/// The one process-global interaction log, matching Z3's global `Z3_open_log` /
/// `Z3_append_log` / `Z3_close_log` (none of which take a context). Guarded by a
/// `Mutex` so concurrent callers cannot corrupt the buffered writer.
static LOG: Mutex<Option<BufWriter<File>>> = Mutex::new(None);

/// Open the interaction log, writing to `filename` (Z3's `Z3_open_log`).
///
/// Creates/truncates the file and installs a buffered writer into the shared
/// `LOG`. Returns `true` on success, `false` if the file cannot be created (or on
/// a null/invalid filename) — an honest result, never a faked success. No context
/// argument (the log is process-global).
///
/// # Safety
/// `filename`, when non-null, must be a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn Z3_open_log(filename: Z3_string) -> bool {
    // SAFETY: `filename`, when non-null, is a valid C string per the contract.
    let Some(path) = (unsafe { cstr_opt(filename) }) else {
        return false;
    };
    match File::create(&path) {
        Ok(file) => match LOG.lock() {
            Ok(mut guard) => {
                *guard = Some(BufWriter::new(file));
                true
            }
            Err(_) => false,
        },
        Err(_) => false,
    }
}

/// Append a string (plus a newline) to the interaction log (Z3's
/// `Z3_append_log`).
///
/// A no-op if the log is not open or the string is null/invalid. No context
/// argument (the log is process-global).
///
/// # Safety
/// `string`, when non-null, must be a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn Z3_append_log(string: Z3_string) {
    // SAFETY: `string`, when non-null, is a valid C string per the contract.
    let Some(s) = (unsafe { cstr_opt(string) }) else {
        return;
    };
    if let Ok(mut guard) = LOG.lock() {
        if let Some(writer) = guard.as_mut() {
            // Best-effort: a write error to the log must not abort the caller.
            let _ = writeln!(writer, "{s}");
        }
    }
}

/// Close the interaction log, flushing and dropping the writer (Z3's
/// `Z3_close_log`). A no-op if no log is open. No context argument.
#[no_mangle]
pub extern "C" fn Z3_close_log() {
    if let Ok(mut guard) = LOG.lock() {
        if let Some(mut writer) = guard.take() {
            let _ = writer.flush();
            // `writer` is dropped here, closing the underlying file.
        }
    }
}

// ============================================================================
// Trace / memory / concurrency no-ops (documented; never fake state).
// ============================================================================

/// Enable a low-level trace tag (Z3's `Z3_enable_trace`). Documented no-op: AY
/// has no libz3-style internal trace subsystem, so there is nothing to toggle.
/// `tag` is ignored (never dereferenced).
#[no_mangle]
pub extern "C" fn Z3_enable_trace(_tag: Z3_string) {}

/// Disable a low-level trace tag (Z3's `Z3_disable_trace`). Documented no-op (see
/// `Z3_enable_trace`). `tag` is ignored (never dereferenced).
#[no_mangle]
pub extern "C" fn Z3_disable_trace(_tag: Z3_string) {}

/// Toggle warning-message printing (Z3's `Z3_toggle_warning_messages`).
/// Documented no-op: AY emits no libz3-style warning stream.
#[no_mangle]
pub extern "C" fn Z3_toggle_warning_messages(_enabled: bool) {}

/// Finalize Z3's memory manager (Z3's `Z3_finalize_memory`). Documented no-op:
/// AY frees all state through normal Rust `Drop` (per-context arenas), so there
/// is no global pool to finalize.
#[no_mangle]
pub extern "C" fn Z3_finalize_memory() {}

/// Reset Z3's memory manager (Z3's `Z3_reset_memory`). Documented no-op: AY keeps
/// no global memory pool to reset (see `Z3_finalize_memory`).
#[no_mangle]
pub extern "C" fn Z3_reset_memory() {}

/// Enable concurrent `dec_ref` (Z3's `Z3_enable_concurrent_dec_ref`). Documented
/// no-op: AY's reference counting is bookkeeping-only and the C API is
/// single-threaded per context, so there is no concurrent-free path to enable.
///
/// # Safety
/// `c` may be any pointer; it is ignored.
#[no_mangle]
pub unsafe extern "C" fn Z3_enable_concurrent_dec_ref(_c: Z3_context) {}

// `Z3_global_param_get` moved to `global_params.rs` (real store + measured
// z3 4.15.4 registry defaults, alongside `Z3_global_param_set`/`_reset_all`).

// ============================================================================
// Params / param-descrs stringification & validation.
// ============================================================================

/// Render a params set as an s-expression (Z3's `Z3_params_to_string`): `(params
/// k1 v1 k2 v2 ...)` over the stored `(key, value)` pairs. Cached in the context.
///
/// # Safety
/// `c` must be a valid context pointer; `p`, when non-null, a valid params handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_params_to_string(c: Z3_context, p: Z3_params) -> Z3_string {
    // Pre-extract the pairs outside the guard (raw deref).
    // SAFETY: `p`, when non-null, is a live `ParamsHandle`; `as_ref` null-checks.
    let pairs = unsafe { p.as_ref() }.map(|h| h.params.clone());
    // SAFETY: `ffi_guard_const_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let Some(pairs) = pairs else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_params_to_string: null params handle".to_string());
                return ptr::null();
            };
            let mut s = String::from("(params");
            for (k, v) in &pairs {
                s.push(' ');
                s.push_str(k);
                s.push(' ');
                s.push_str(v);
            }
            s.push(')');
            ctx.last_error = Z3_OK;
            cache_string(ctx, s)
        })
    }
}

/// Validate a params set against a parameter-descriptor set (Z3's
/// `Z3_params_validate`).
///
/// Each key in `p` is checked against the descriptor names in `d`; an unknown key
/// sets `Z3_INVALID_ARG` with a diagnostic and stops. When every key is
/// recognized (or `p` is empty), it is a no-op with `Z3_OK`.
///
/// # Safety
/// `c` must be a valid context pointer; `p`/`d`, when non-null, valid handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_params_validate(c: Z3_context, p: Z3_params, d: Z3_param_descrs) {
    // Pre-extract keys and descriptor names outside the guard (raw derefs).
    // SAFETY: `p`/`d`, when non-null, are live handles; `as_ref` null-checks.
    let (keys, names) = unsafe {
        (
            p.as_ref()
                .map(|h| h.params.iter().map(|(k, _)| k.clone()).collect::<Vec<_>>()),
            d.as_ref()
                .map(|h| h.entries.iter().map(|e| e.name.clone()).collect::<Vec<_>>()),
        )
    };
    // SAFETY: `ffi_guard_void` handles a null context and catches panics.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let (Some(keys), Some(names)) = (keys, names) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_params_validate: null params or descriptor set".to_string());
                return;
            };
            for k in &keys {
                if !names.iter().any(|n| n == k) {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!("Z3_params_validate: unknown parameter '{k}'"));
                    return;
                }
            }
            ctx.last_error = Z3_OK;
        });
    }
}

// ============================================================================
// Constructor field count.
// ============================================================================

/// Return the number of fields of a datatype constructor (Z3's
/// `Z3_constructor_num_fields`).
///
/// # Safety
/// `c` must be a valid context pointer; `constr`, when non-null, a valid handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_constructor_num_fields(
    c: Z3_context,
    constr: Z3_constructor,
) -> c_uint {
    // SAFETY: `constr`, when non-null, is a live `ConstructorHandle`; `as_ref`
    // null-checks.
    let count = unsafe { constr.as_ref() }.map(|h| h.field_names.len() as c_uint);
    // SAFETY: `ffi_guard_uint` handles a null context and catches panics.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| match count {
            Some(n) => {
                ctx.last_error = Z3_OK;
                n
            }
            None => {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_constructor_num_fields: null constructor handle".to_string());
                0
            }
        })
    }
}

// ============================================================================
// Model extrapolation (model-based generalization).
// ============================================================================

/// Evaluate `t` under the model to a definite Boolean, when possible.
fn eval_bool_under_model(ctx: &mut Z3Context, handle: &ModelHandle, t: Term) -> Option<bool> {
    let reduced = eval_term_under_model(ctx, handle, t, true)?;
    ctx.solver.bool_value(reduced)
}

/// Collect a SOUND implicant of `fml` under the model into `out`: subformulas,
/// each satisfied by the model, whose conjunction IMPLIES `fml` (structural
/// recursion: all conjuncts of an `and`, one satisfied disjunct of an `or`,
/// the taken branch (plus its guard literal) of an `ite`, the discharging side
/// of an `=>`; anything else is treated as a literal and kept whole iff it
/// evaluates to true). Returns `false` — leaving `out`'s new suffix rolled
/// back by the caller — when the model does not (determinably) satisfy `fml`.
fn model_implicant(
    ctx: &mut Z3Context,
    handle: &ModelHandle,
    t: Term,
    out: &mut Vec<Term>,
) -> bool {
    match ctx.solver.term_kind(t) {
        TermKind::App { ref name, .. } if name == "and" => {
            for child in ctx.solver.term_children(t) {
                if !model_implicant(ctx, handle, child, out) {
                    return false;
                }
            }
            true
        }
        TermKind::App { ref name, .. } if name == "or" => {
            for child in ctx.solver.term_children(t) {
                let mark = out.len();
                if model_implicant(ctx, handle, child, out) {
                    return true; // one satisfied disjunct implies the or
                }
                out.truncate(mark);
            }
            false
        }
        TermKind::App { ref name, num_args } if name == "=>" && num_args == 2 => {
            let children = ctx.solver.term_children(t);
            let (lhs, rhs) = (children[0], children[1]);
            let mark = out.len();
            // A satisfied consequent implies the implication ...
            if model_implicant(ctx, handle, rhs, out) {
                return true;
            }
            out.truncate(mark);
            // ... as does a falsified antecedent (kept as the literal ¬lhs).
            if eval_bool_under_model(ctx, handle, lhs) == Some(false) {
                let neg = ctx.solver.not(lhs);
                out.push(neg);
                return true;
            }
            false
        }
        TermKind::Ite => {
            let children = ctx.solver.term_children(t);
            if children.len() != 3 || ctx.solver.term_sort(t) != Sort::Bool {
                // Non-Boolean ite (or malformed): treat as a literal below.
                return match eval_bool_under_model(ctx, handle, t) {
                    Some(true) => {
                        out.push(t);
                        true
                    }
                    _ => false,
                };
            }
            let (cond, then_b, else_b) = (children[0], children[1], children[2]);
            match eval_bool_under_model(ctx, handle, cond) {
                Some(true) => {
                    // cond ∧ then-branch ⇒ ite
                    model_implicant(ctx, handle, cond, out)
                        && model_implicant(ctx, handle, then_b, out)
                }
                Some(false) => {
                    let neg = ctx.solver.not(cond);
                    out.push(neg);
                    model_implicant(ctx, handle, else_b, out)
                }
                None => false,
            }
        }
        // Everything else — atoms, negations, quantified subformulas — is a
        // LITERAL: kept whole iff the model satisfies it.
        _ => match eval_bool_under_model(ctx, handle, t) {
            Some(true) => {
                out.push(t);
                true
            }
            _ => false,
        },
    }
}

/// Extrapolate a model of a formula (Z3's `Z3_model_extrapolate`).
///
/// REAL (model-based generalization): evaluates `fml`'s Boolean structure
/// under the model and returns the conjunction of `fml`'s satisfied literals —
/// a SOUND implicant (each returned conjunct is satisfied by the model, and
/// their conjunction implies `fml`; libz3-cross-checked, e.g. under `x = 5`,
/// `(or (> x 2) (< x 0))` extrapolates to `(> x 2)`). A single literal is
/// returned unwrapped; conjunct ORDER may differ from libz3's (semantically
/// irrelevant).
///
/// Documented deliberate divergence: when the model does NOT satisfy `fml`
/// (a violation of the function's precondition), AY returns `false` — the
/// sound "empty implicant" (`false ⇒ fml` vacuously, and it signals
/// unsatisfaction) — where libz3 4.16 returns the UNSOUND `true` (its
/// implicant collector silently drops the falsified fact; `true` does not
/// imply `fml`). AY never returns a formula that fails to imply `fml`.
///
/// # Safety
/// `c` must be a valid context pointer; `m`, when non-null, a valid model.
#[no_mangle]
pub unsafe extern "C" fn Z3_model_extrapolate(c: Z3_context, m: Z3_model, fml: Z3_ast) -> Z3_ast {
    // SAFETY: `ffi_guard_ast` handles a null context and catches panics; `m`
    // is a separate live allocation owned by the context arena, null-checked
    // below.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if m.is_null() || fml == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_model_extrapolate: null model or formula".to_string());
                return 0;
            }
            let handle = &*m;
            let t = require_term_ast_or_return!(ctx, fml, "Z3_model_extrapolate", "formula", 0);
            let mut lits: Vec<Term> = Vec::new();
            let result = if model_implicant(ctx, handle, t, &mut lits) {
                match lits.len() {
                    0 => ctx.solver.bool_const(true),
                    1 => lits[0],
                    _ => ctx.solver.and_many(&lits),
                }
            } else {
                // m ⊭ fml (or undeterminable): the sound empty implicant.
                ctx.solver.bool_const(false)
            };
            let ast = term_to_ast(ctx, result);
            record_ast_sort(ctx, ast, Sort::Bool);
            ast
        })
    }
}

// ============================================================================
// Apply-result stringification.
// ============================================================================

/// Render an apply-result as text (Z3's `Z3_apply_result_to_string`): each
/// subgoal is rendered like `Z3_goal_to_string` (`(goal` then each formula on its
/// own indented line, closed by `)`), and the subgoals are joined by newlines.
///
/// # Safety
/// `c` must be a valid context pointer; `r`, when non-null, a valid handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_apply_result_to_string(c: Z3_context, r: Z3_apply_result) -> Z3_string {
    // Pre-extract each subgoal's formulas outside the guard (raw derefs). Each
    // subgoal is a `Z3_goal` owned by the context's `goal_cache`.
    // SAFETY: `r`/each `g`, when non-null, are live handles; `as_ref` null-checks.
    let subgoals: Option<Vec<Vec<Z3_ast>>> = unsafe { r.as_ref() }.map(|h| {
        h.subgoals
            .iter()
            .map(|&g| {
                // SAFETY: every non-null subgoal handle is owned by the same
                // context cache as `r`; `as_ref` handles a defensive null.
                unsafe { g.as_ref() }
                    .map(|gh| gh.formulas.clone())
                    .unwrap_or_default()
            })
            .collect()
    });
    // SAFETY: `ffi_guard_const_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let Some(subgoals) = subgoals else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_apply_result_to_string: null apply-result handle".to_string());
                return ptr::null();
            };
            let mut parts: Vec<String> = Vec::with_capacity(subgoals.len());
            for formulas in &subgoals {
                let mut s = String::from("(goal");
                for &a in formulas {
                    let rendered = if a == 0 {
                        "?".to_string()
                    } else {
                        let term = require_term_ast_or_return!(
                            ctx,
                            a,
                            "Z3_apply_result_to_string",
                            "subgoal formula",
                            ptr::null()
                        );
                        ctx.solver
                            .format_term_checked(term)
                            .unwrap_or_else(|| "?".to_string())
                    };
                    s.push_str("\n  ");
                    s.push_str(&rendered);
                }
                s.push(')');
                parts.push(s);
            }
            ctx.last_error = Z3_OK;
            let rendered = super::ffi_surface_text(ctx, &parts.join("\n"));
            cache_string(ctx, rendered)
        })
    }
}

// ============================================================================
// Pattern conversion & stringification.
// ============================================================================

/// Convert a pattern to an AST (Z3's `Z3_pattern_to_ast`).
///
/// REAL: Z3 represents a pattern as an application of an internal decl named
/// `pattern` over the trigger terms, at sort Bool (libz3-cross-checked:
/// `Z3_get_ast_kind` = APP, decl name `pattern`, sort Bool, decl kind
/// `Z3_OP_UNINTERPRETED`). A multi-trigger pattern is returned as exactly that
/// grouping node (`Solver::pattern_term`) — an INERT term used only for
/// introspection (patterns are instantiation hints; the node is never asserted
/// or consulted by the solver, so it cannot affect any verdict).
///
/// A single-trigger pattern returns its sole trigger term directly (AY's
/// established convention; libz3 wraps even single triggers in the `pattern`
/// node — a shape-only, semantics-free difference, documented here).
///
/// # Safety
/// `c` must be a valid context pointer; `p`, when non-null, a valid pattern handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_pattern_to_ast(c: Z3_context, p: Z3_pattern) -> Z3_ast {
    // SAFETY: `p`, when non-null, is a live `PatternHandle`; `as_ref` null-checks.
    let pattern = unsafe { p.as_ref() }.map(|h| (h.owner_salt, h.terms.clone()));
    // SAFETY: `ffi_guard_ast` handles a null context and catches panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some(pattern) = pattern else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_pattern_to_ast: null pattern handle".to_string());
                return 0;
            };
            let Some(mut slices) = super::quantifiers::checked_pattern_slices(
                ctx,
                std::slice::from_ref(&pattern),
                "Z3_pattern_to_ast",
            ) else {
                return 0;
            };
            let terms = slices.pop().unwrap_or_default();
            if terms.len() == 1 {
                ctx.last_error = Z3_OK;
                term_to_ast(ctx, terms[0])
            } else {
                // Multi-trigger: the real `(pattern t1 t2 ...)` grouping node.
                let t = ctx.solver.pattern_term(&terms);
                let ast = term_to_ast(ctx, t);
                record_ast_sort(ctx, ast, Sort::Bool);
                ctx.last_error = Z3_OK;
                ast
            }
        })
    }
}

/// Render a pattern as an s-expression (Z3's `Z3_pattern_to_string`): `(pattern
/// t1 t2 ...)` over the trigger terms, each rendered by the solver's real term
/// formatter. Cached in the context.
///
/// # Safety
/// `c` must be a valid context pointer; `p`, when non-null, a valid pattern handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_pattern_to_string(c: Z3_context, p: Z3_pattern) -> Z3_string {
    // SAFETY: `p`, when non-null, is a live `PatternHandle`; `as_ref` null-checks.
    let pattern = unsafe { p.as_ref() }.map(|h| (h.owner_salt, h.terms.clone()));
    // SAFETY: `ffi_guard_const_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let Some(pattern) = pattern else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_pattern_to_string: null pattern handle".to_string());
                return ptr::null();
            };
            let Some(mut slices) = super::quantifiers::checked_pattern_slices(
                ctx,
                std::slice::from_ref(&pattern),
                "Z3_pattern_to_string",
            ) else {
                return ptr::null();
            };
            let terms = slices.pop().unwrap_or_default();
            let mut s = String::from("(pattern");
            for &t in &terms {
                let rendered = ctx
                    .solver
                    .format_term_checked(t)
                    .unwrap_or_else(|| "?".to_string());
                s.push(' ');
                s.push_str(&rendered);
            }
            s.push(')');
            ctx.last_error = Z3_OK;
            let s = super::ffi_surface_text(ctx, &s);
            cache_string(ctx, s)
        })
    }
}

// ============================================================================
// Simplify parameter surface.
// ============================================================================

/// Return help text describing the parameters `Z3_simplify_ex` accepts (Z3's
/// `Z3_simplify_get_help`). Honest: it documents exactly what AY's simplifier
/// honors. Mirrors `Z3_optimize_get_help`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_simplify_get_help(c: Z3_context) -> Z3_string {
    // SAFETY: `ffi_guard_const_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let help = "\
Parameters honored by the AY simplifier:
  elim_and (bool)         rewrite (and a b) as (not (or (not a) (not b)))
  local_ctx (bool)        use local context simplification
  som (bool)              put polynomials in sum-of-monomials form
Other z3 simplify parameters are accepted for API compatibility but ignored;
they never change the simplified term's meaning (equivalence is preserved).\n";
            ctx.last_error = Z3_OK;
            cache_string(ctx, help.to_string())
        })
    }
}

/// Return the parameter-descriptor set the simplifier recognizes (Z3's
/// `Z3_simplify_get_param_descrs`).
///
/// A REAL, queryable list (name + `Z3_param_kind` + documentation), never a
/// fake/empty stub disguised as z3's full set. Mirrors
/// `Z3_optimize_get_param_descrs`: the handle is arena-owned by the context and
/// freed at `Z3_del_context`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_simplify_get_param_descrs(c: Z3_context) -> Z3_param_descrs {
    // SAFETY: `ffi_guard_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let entries = vec![
                ParamDescr {
                    name: "elim_and".to_string(),
                    kind: Z3_PK_BOOL,
                    doc: "rewrite (and a b) as (not (or (not a) (not b)))".to_string(),
                },
                ParamDescr {
                    name: "local_ctx".to_string(),
                    kind: Z3_PK_BOOL,
                    doc: "use local context simplification".to_string(),
                },
                ParamDescr {
                    name: "som".to_string(),
                    kind: Z3_PK_BOOL,
                    doc: "put polynomials in sum-of-monomials form".to_string(),
                },
                ParamDescr {
                    name: "sort_sums".to_string(),
                    kind: Z3_PK_BOOL,
                    doc: "sort the arguments of + application; accepted for compatibility"
                        .to_string(),
                },
            ];
            let handle = Box::into_raw(Box::new(ParamDescrsHandle { entries }));
            ctx.param_descrs_cache.push(handle);
            ctx.last_error = Z3_OK;
            handle
        })
    }
}

// ============================================================================
// Benchmark emission.
// ============================================================================

/// Emit an SMT-LIB2 benchmark string for the given assumptions and formula (Z3's
/// `Z3_benchmark_to_smtlib_string`).
///
/// Builds a self-contained benchmark: a `; <name>` comment, `(set-logic ...)`,
/// `(set-info :status ...)`, any `attributes` verbatim, then the declarations and
/// assertions for exactly the passed `assumptions` + `formula` (rendered by the
/// solver's real serializer, `Solver::assertions_sexpr`), closed by
/// `(check-sat)`. Only the passed terms are dumped — matching Z3's standalone
/// benchmark semantics (there is no solver argument) — so the context's own
/// assertion stack is neither read nor mutated. Cached in the context.
///
/// # Safety
/// `c` must be a valid context pointer; the string arguments, when non-null, must
/// be valid C strings; `assumptions`, when `num_assumptions > 0`, must point to
/// `num_assumptions` valid `Z3_ast` handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_benchmark_to_smtlib_string(
    c: Z3_context,
    name: Z3_string,
    logic: Z3_string,
    status: Z3_string,
    attributes: Z3_string,
    num_assumptions: c_uint,
    assumptions: *const Z3_ast,
    formula: Z3_ast,
) -> Z3_string {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the helper only mutates its error state.
    if !unsafe {
        ffi_count_within_limit(
            c,
            "Z3_benchmark_to_smtlib_string assumptions",
            num_assumptions,
        )
    } {
        return ptr::null();
    }
    // Decode the header strings and collect the assertion handles outside the guard.
    // SAFETY: each string, when non-null, is a valid C string per the contract.
    let (name, logic, status, attributes) = unsafe {
        (
            cstr_opt(name).unwrap_or_default(),
            cstr_opt(logic).unwrap_or_default(),
            cstr_opt(status).unwrap_or_default(),
            cstr_opt(attributes).unwrap_or_default(),
        )
    };

    let mut all_asts: Vec<Z3_ast> = Vec::new();
    if num_assumptions > 0 && !assumptions.is_null() {
        for i in 0..num_assumptions as usize {
            // SAFETY: `assumptions` points to at least `num_assumptions` elements
            // per the contract; range/null checked above.
            let a = unsafe { *assumptions.add(i) };
            if a != 0 {
                all_asts.push(a);
            }
        }
    }
    if formula != 0 {
        all_asts.push(formula);
    }

    // SAFETY: `ffi_guard_const_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            if num_assumptions > 0 && assumptions.is_null() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(
                    "Z3_benchmark_to_smtlib_string: null assumptions array for non-zero count"
                        .to_string(),
                );
                return ptr::null();
            }
            let all_terms = require_term_asts_or_return!(
                ctx,
                &all_asts,
                "Z3_benchmark_to_smtlib_string",
                ptr::null()
            );
            // Real serialization of exactly these assertions (decls + asserts, no
            // script wrapper) — never fabricated.
            let body = ctx.solver.assertions_sexpr(&all_terms);

            let mut out = String::new();
            if !name.is_empty() {
                out.push_str(&format!("; {name}\n"));
            }
            if !logic.is_empty() {
                out.push_str(&format!("(set-logic {logic})\n"));
            }
            if !status.is_empty() {
                out.push_str(&format!("(set-info :status {status})\n"));
            }
            if !attributes.is_empty() {
                out.push_str(&attributes);
                out.push('\n');
            }
            out.push_str(&body);
            if !out.ends_with('\n') {
                out.push('\n');
            }
            out.push_str("(check-sat)\n");

            ctx.last_error = Z3_OK;
            let out = super::ffi_surface_text(ctx, &out);
            cache_string(ctx, out)
        })
    }
}

// ============================================================================
// SMT-LIB2 file parsing / string evaluation.
// ============================================================================

/// Parse an SMT-LIB2 file, returning its assertions as an AST vector (Z3's
/// `Z3_parse_smtlib2_file`).
///
/// Reads the file and follows the same path as `Z3_parse_smtlib2_string`:
/// declarations and assertions are parsed into the context's solver and returned
/// as an AST vector; query commands (`check-sat`, `get-model`, ...) are ignored.
/// State-control commands are rejected before execution. A late semantic error
/// permanently fails the shared decision engine closed because declarations and
/// options cannot yet be fully rolled back.
/// The `sort_names`/`sorts` and `decl_names`/`decls` pre-declaration arrays are
/// accepted for signature compatibility and ignored (all declarations must be in
/// the file). A file-read failure sets `Z3_EXCEPTION` and returns an empty vector.
///
/// # Safety
/// `c` must be a valid context pointer; `file_name`, when non-null, a valid C
/// string; the array pointers are unused.
#[no_mangle]
pub unsafe extern "C" fn Z3_parse_smtlib2_file(
    c: Z3_context,
    file_name: Z3_string,
    _num_sorts: c_uint,
    _sort_names: *const Z3_symbol,
    _sorts: *const Z3_sort,
    _num_decls: c_uint,
    _decl_names: *const Z3_symbol,
    _decls: *const Z3_func_decl,
) -> Z3_ast_vector {
    // Decode the path outside the guard (raw deref).
    // SAFETY: `file_name`, when non-null, is a valid C string per the contract.
    let path = unsafe { cstr_opt(file_name) };
    // SAFETY: `ffi_guard_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(path) = path else {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some("Z3_parse_smtlib2_file: null/invalid file name".to_string());
                return cache_ast_vector(ctx, Vec::new());
            };
            let content = match ffi_read_bounded_parser_file(&path) {
                Ok(text) => text,
                Err(e) => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg =
                        Some(format!("Z3_parse_smtlib2_file: cannot read '{path}': {e}"));
                    return cache_ast_vector(ctx, Vec::new());
                }
            };
            let terms =
                super::solver::parse_solver_transaction(ctx, &content, "Z3_parse_smtlib2_file")
                    .unwrap_or_default();
            let asts = terms
                .into_iter()
                .map(|term| term_to_ast(ctx, term))
                .collect();
            cache_ast_vector(ctx, asts)
        })
    }
}

/// Parse and evaluate an SMT-LIB2 command sequence, returning the concatenated
/// command output (Z3's `Z3_eval_smtlib2_string`).
///
/// Parses `str` into commands and runs them through a fresh `ay_dpll::Executor`
/// (the same engine the `ay` CLI drives), joining each command's output with
/// newlines. Parse/execution errors set `Z3_EXCEPTION` and the return value is an
/// `(error "...")` string.
///
/// DIVERGENCE: Z3 keeps the evaluation state across successive
/// `Z3_eval_smtlib2_string` calls (each builds on the previous). AY runs each
/// call on a FRESH executor, so state does NOT persist across calls — every call
/// is self-contained. Results for a single self-contained script are exact; a
/// multi-call script relying on carried-over declarations must pass them in each
/// call. This is documented, not faked.
///
/// # Safety
/// `c` must be a valid context pointer; `str`, when non-null, a valid C string.
#[no_mangle]
pub unsafe extern "C" fn Z3_eval_smtlib2_string(c: Z3_context, str: Z3_string) -> Z3_string {
    // Decode the input outside the guard (raw deref).
    // SAFETY: `str`, when non-null, is a valid C string per the contract.
    let input = if str.is_null() {
        None
    } else {
        // SAFETY: `str` is a valid NUL-terminated parser source per the caller
        // contract; the parser helper enforces the larger explicit source cap.
        unsafe { ffi_read_bounded_parser_text(str) }.ok()
    };
    // SAFETY: `ffi_guard_const_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let Some(input) = input else {
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg =
                    Some("Z3_eval_smtlib2_string: null/invalid input string".to_string());
                return cache_string(ctx, "(error \"null input\")".to_string());
            };
            // Fail-close reserved `map[...]` symbol capture before the text
            // reaches the core parser/executor (where a quoted `|map[f]|`
            // declaration silently acquires internal array-map semantics — a
            // measured wrong-verdict channel). See `smtlib2_reserved_error`.
            if let Some(msg) = super::smtlib2_reserved_error(&input) {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!("Z3_eval_smtlib2_string: {msg}"));
                return cache_string(ctx, format!("(error \"{msg}\")"));
            }
            match parse(&input) {
                Ok(commands) => {
                    let mut executor = Executor::new();
                    match executor.execute_all(&commands) {
                        Ok(outputs) => {
                            ctx.last_error = Z3_OK;
                            cache_string(ctx, outputs.join("\n"))
                        }
                        Err(e) => {
                            ctx.last_error = Z3_EXCEPTION;
                            ctx.error_msg = Some(format!("{e}"));
                            cache_string(ctx, format!("(error \"{e}\")"))
                        }
                    }
                }
                Err(e) => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(format!("{e}"));
                    cache_string(ctx, format!("(error \"{e}\")"))
                }
            }
        })
    }
}

#[cfg(test)]
#[path = "batch1_tests.rs"]
mod batch1_tests;

#[cfg(test)]
#[path = "capi_handle_tests.rs"]
mod capi_handle_tests;
