// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible context, config, and symbol lifecycle functions.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_char, c_int, c_uint};
use std::ptr;

use ay_dpll::api::{Logic, Solver};

use super::handle_params::ParamSet;
use super::{
    apply_supported_params, cache_int_symbol, cache_string, cache_symbol, ffi_guard_const_ptr,
    ffi_guard_ptr, ffi_guard_void, ffi_read_bounded_text, require_term_ast_or_return, Z3Config,
    Z3Context, Z3_ast, Z3_config, Z3_context, Z3_symbol, Z3_DEC_REF_ERROR, Z3_OK,
};

/// Create a new configuration object.
#[no_mangle]
pub extern "C" fn Z3_mk_config() -> Z3_config {
    Box::into_raw(Box::new(Z3Config { params: Vec::new() }))
}

/// Delete a configuration object.
///
/// # Safety
/// `c` must be a valid config pointer or null.
#[no_mangle]
pub unsafe extern "C" fn Z3_del_config(c: Z3_config) {
    if c.is_null() {
        return;
    }
    // SAFETY: `c` is non-null and was returned by `Box::into_raw` in
    // `Z3_mk_config`; the caller transfers exclusive ownership and this
    // function consumes that allocation exactly once.
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
        let _ = Box::from_raw(c);
    }));
}

/// Set a configuration parameter.
///
/// Only `timeout` is currently honored by AY.
///
/// # Safety
/// `c` must point to a live config that is not concurrently accessed. Both
/// string pointers must remain readable through their NUL terminators for this
/// call.
#[no_mangle]
pub unsafe extern "C" fn Z3_set_param_value(
    c: Z3_config,
    param_id: *const c_char,
    param_value: *const c_char,
) {
    if c.is_null() || param_id.is_null() || param_value.is_null() {
        return;
    }
    let key = {
        // SAFETY: `param_id` was null-checked above and the caller guarantees it
        // remains a valid NUL-terminated string while the bounded helper clones it.
        unsafe { ffi_read_bounded_text(param_id) }
    };
    let value = {
        // SAFETY: `param_value` was null-checked above and the caller guarantees it
        // remains a valid NUL-terminated string while the bounded helper clones it.
        unsafe { ffi_read_bounded_text(param_value) }
    };
    let (Ok(key), Ok(value)) = (key, value) else {
        return;
    };
    // SAFETY: `c` was null-checked above and points to a live `Z3Config` that
    // the single-threaded C API gives this call exclusive access to.
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
        let cfg = &mut *c;
        cfg.params.push((key, value));
    }));
}

/// Install the process-wide `--z3-mode` transcript flag once, when a context
/// is created: the z3 C API library writes nothing to the host's
/// stderr (z3 does not). The posture only silences the CLI diagnostics (the
/// partial-model note, MODEL-UNCONFIRMED, the unbounded-objective warning)
/// and changes no verdict. A no-op when the process already installed its
/// flags.
fn install_z3_transcript_posture() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        let _ = std::panic::catch_unwind(|| {
            ay_core::set_global_misc_cli_flags_with(|flags| flags.z3_transcript = true)
        });
    });
}

/// The engine of a new context with the configuration `c`'s recognized
/// parameters applied, and those parameters as the context defaults every
/// handle's own parameters override (see `handle_params`).
///
/// # Safety
/// `c` must be a valid config pointer or null.
unsafe fn configured_engine(c: Z3_config) -> (Solver, ParamSet) {
    let mut solver = Solver::new(Logic::All);
    let mut defaults = ParamSet::default();
    // SAFETY: `c` is null-checked by `as_ref` and otherwise a live
    // configuration handle the caller owns (single-threaded shared read).
    if let Some(config) = unsafe { c.as_ref() } {
        apply_supported_params(&mut solver, &config.params);
        defaults.record(&config.params);
    }
    (solver, defaults)
}

/// Shared constructor for both `Z3_mk_context` and `Z3_mk_context_rc`.
///
/// `ref_counted` records whether the caller opted into z3py-style reference
/// counting. It controls only the BOOKKEEPING behavior of `Z3_inc_ref`/
/// `Z3_dec_ref`; it never changes how (or whether) terms are freed — terms are
/// arena-interned and live until `Z3_del_context`.
///
/// # Safety
/// `c` must be a valid config pointer or null.
unsafe fn mk_context_inner(c: Z3_config, ref_counted: bool) -> Z3_context {
    // Solver::new could panic, and there is no context yet for ffi_guard.
    match std::panic::catch_unwind(|| {
        // SAFETY: `c` is null or a live configuration handle per this
        // function's contract, read once while the context is built.
        let (solver, default_params) = unsafe { configured_engine(c) };
        Box::into_raw(Box::new(Z3Context {
            solver,
            eval_session: None,
            eval_active: false,
            proof_check_callback: None,
            proof_check_user_context: ptr::null_mut(),
            proof_tracking: Default::default(),
            last_error: Z3_OK,
            error_msg: None,
            decision_owner: None,
            decision_engine_poisoned: None,
            optimize_engine_displaced: false,
            optimize_engine_owner: ptr::null(),
            text_datatypes: Default::default(),
            string_cache: Vec::new(),
            symbol_cache: Vec::new(),
            ffi_const_cache: std::collections::HashMap::new(),
            ffi_const_metadata: std::collections::HashMap::new(),
            ffi_const_terms_by_identity: std::collections::HashMap::new(),
            ffi_func_names: std::collections::HashMap::new(),
            ffi_func_decls: std::collections::HashMap::new(),
            ffi_rec_func_decls: std::collections::HashMap::new(),
            wf_guards: std::collections::HashMap::new(),
            uninterpreted_sort_names: std::collections::HashSet::new(),
            bounded_sort_lost: std::collections::HashSet::new(),
            default_params,
            ffi_decl_symbols: std::collections::HashMap::new(),
            ffi_dt_recognizers: std::collections::HashMap::new(),
            ffi_sort_symbols: std::collections::HashMap::new(),
            ffi_used_decl_names: std::collections::HashSet::new(),
            next_ffi_fresh_id: 0,
            pub_ast: super::pub_ast::PubStore::default(),
            provenance: super::provenance::Provenance::default(),
            dt_decl_index: std::collections::HashMap::new(),
            func_decl_intern: std::collections::HashMap::new(),
            error_handler: None,
            error_handler_active: false,
            finite_set_sorts: std::collections::HashMap::new(),
            finite_set_sorts_by_basis: std::collections::HashMap::new(),
            finite_set_term_provenance: std::collections::HashMap::new(),
            finite_set_reachable_axioms: std::collections::HashMap::new(),
            quantifier_public_bound_terms: std::collections::HashMap::new(),
            parsed_quantifier_public_bound_sorts: std::collections::HashMap::new(),
            quantifier_weights: std::collections::HashMap::new(),
            quantifier_no_patterns: std::collections::HashMap::new(),
            quantifier_ffi_metadata: std::collections::HashMap::new(),
            finite_set_apps: std::collections::HashMap::new(),
            finite_set_app_cache: std::collections::HashMap::new(),
            finite_set_decl_signatures: std::collections::HashMap::new(),
            sort_cache: Vec::new(),
            func_decl_cache: Vec::new(),
            solver_handle_cache: Vec::new(),
            optimize_handle_cache: Vec::new(),
            fixedpoint_handle_cache: Vec::new(),
            tactic_handle_cache: Vec::new(),
            simplifier_handle_cache: Vec::new(),
            stats_handle_cache: Vec::new(),
            model_cache: Vec::new(),
            func_interp_cache: Vec::new(),
            func_entry_cache: Vec::new(),
            params_cache: Vec::new(),
            param_descrs_cache: Vec::new(),
            ast_vector_cache: Vec::new(),
            ast_map_cache: Vec::new(),
            pattern_cache: Vec::new(),
            goal_cache: Vec::new(),
            apply_result_cache: Vec::new(),
            probe_cache: Vec::new(),
            parser_context_cache: Vec::new(),
            handle_salt: super::next_handle_salt(),
            sort_ast_handles: Vec::new(),
            decl_ast_ids: std::collections::HashMap::new(),
            decl_ast_handles: Vec::new(),
            map_fn_sigs: std::collections::HashMap::new(),
            next_decl_id: 1,
            ref_counted,
            ast_refcounts: std::collections::HashMap::new(),
            proof_texts: Vec::new(),
            proof_applications: Default::default(),
            proof_application_intern: Default::default(),
            proof_declarations: Default::default(),
            rcf_num_cache: Vec::new(),
            algebraic_values: Vec::new(),
            background_axioms: Vec::new(),
            global_definition_axioms: Vec::new(),
            rec_fun_defs: std::collections::HashMap::new(),
            rec_declared_names: std::collections::HashSet::new(),
            rec_def_axiom_index: std::collections::HashMap::new(),
            range_bounded: std::collections::HashSet::new(),
            bounded_array_ext_lemmas: std::collections::HashMap::new(),
            array_ext_cache: std::collections::HashMap::new(),
            char_to_bv_cache: std::collections::HashMap::new(),
            special_relation_cache: std::collections::HashMap::new(),
            poly_decl_instances: std::collections::HashMap::new(),
            transitive_closure_regs: Vec::new(),
        }))
    }) {
        Ok(ctx) => ctx,
        Err(_) => ptr::null_mut(),
    }
}

/// Create a new context with the given configuration.
///
/// Uses `Logic::All` since Z3 contexts are logic-agnostic. Recognized config
/// parameters are copied onto the new solver during construction.
///
/// Reference counting is NOT enabled: `Z3_inc_ref`/`Z3_dec_ref` are no-ops on
/// contexts created this way (matching Z3, where RC is only active on RC
/// contexts). Use `Z3_mk_context_rc` for z3py-style reference-count discipline.
///
/// # Safety
/// `c` must be a valid config pointer or null.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_context(c: Z3_config) -> Z3_context {
    install_z3_transcript_posture();
    // SAFETY: forwards the caller's `# Safety` contract to `mk_context_inner`.
    unsafe { mk_context_inner(c, false) }
}

/// Create a new context with reference counting enabled (z3py-style).
///
/// Distinct from `Z3_mk_context`: on the returned context `Z3_inc_ref`/
/// `Z3_dec_ref` perform real validity/ownership BOOKKEEPING — they maintain
/// per-AST counts and report `Z3_DEC_REF_ERROR` on an unbalanced `dec_ref`.
/// This is bookkeeping only: ASTs are hash-consed and arena-interned, so no
/// term is ever freed by reference counting; everything lives until
/// `Z3_del_context`.
///
/// # Safety
/// `c` must be a valid config pointer or null.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_context_rc(c: Z3_config) -> Z3_context {
    install_z3_transcript_posture();
    // SAFETY: forwards the caller's `# Safety` contract to `mk_context_inner`.
    unsafe { mk_context_inner(c, true) }
}

/// Delete a context and all associated resources.
///
/// # Safety
/// `c` must be a valid context pointer or null.
#[no_mangle]
pub unsafe extern "C" fn Z3_del_context(c: Z3_context) {
    if c.is_null() {
        return;
    }
    // Drop of Z3Context runs drain_arena on all cached handles; catch any panic
    // to prevent UB across the FFI boundary.
    // SAFETY: The pointer was produced by a matching `Box::into_raw` in the corresponding
    // `Z3_mk_*`/cache-add path and stored in the context's handle cache. We own it exclusively
    // here because the Z3 C API is single-threaded per context.
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
        let _ = Box::from_raw(c);
    }));
}

/// Increment the reference count for an AST.
///
/// Bookkeeping only: ASTs are hash-consed and arena-interned, so they live
/// until `Z3_del_context` and are NEVER freed by reference counting. On an
/// RC context (`Z3_mk_context_rc`) this records one more outstanding reference
/// to the term, which lets `Z3_dec_ref` detect dec-below-zero
/// (`Z3_DEC_REF_ERROR`) and supports z3py-style RC-context discipline. On a
/// non-RC context (`Z3_mk_context`) it is a no-op. A null AST (`a == 0`) is a
/// no-op.
///
/// # Safety
/// `c` must be a valid context pointer or null.
#[no_mangle]
pub unsafe extern "C" fn Z3_inc_ref(c: Z3_context, a: Z3_ast) {
    if a == 0 {
        return;
    }
    // A tagged non-term handle (proof / algebraic / sort-ast / func-decl-ast)
    // is arena-owned and never freed by reference counting; z3py's
    // `AstRef.__init__` inc-refs `as_ast()` of every SortRef/FuncDeclRef on RC
    // contexts, so this must be a balanced no-op — never term-refcount
    // bookkeeping keyed off a truncated alias.
    if a & super::HANDLE_TAG_MASK != 0 {
        return;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if ctx.ref_counted {
                // Track the count; NEVER allocate/free the underlying term.
                let term = require_term_ast_or_return!(ctx, a, "Z3_inc_ref", "AST");
                *ctx.ast_refcounts.entry(term).or_insert(0) += 1;
            }
            // Non-RC contexts: no-op (Z3 only ref-counts on RC contexts).
        });
    }
}

/// Decrement the reference count for an AST.
///
/// Bookkeeping only: ASTs are hash-consed and arena-interned, so NO term is
/// ever freed here — the model is preserved and everything lives until
/// `Z3_del_context`. On an RC context (`Z3_mk_context_rc`), decrementing a
/// term whose count is absent or already zero is an unbalanced `dec_ref` and
/// sets `last_error = Z3_DEC_REF_ERROR`; otherwise the count is decremented
/// (the entry is removed at zero). On a non-RC context (`Z3_mk_context`) it is
/// a no-op, so an unbalanced `dec_ref` leaves the error code at `Z3_OK`. A
/// null AST (`a == 0`) is a no-op.
///
/// # Safety
/// `c` must be a valid context pointer or null.
#[no_mangle]
pub unsafe extern "C" fn Z3_dec_ref(c: Z3_context, a: Z3_ast) {
    if a == 0 {
        return;
    }
    // Tagged non-term handle: balanced no-op, matching `Z3_inc_ref` — a
    // `Z3_DEC_REF_ERROR` here would make every z3py `SortRef`/`FuncDeclRef`
    // destructor on an RC context report a spurious error.
    if a & super::HANDLE_TAG_MASK != 0 {
        return;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_void(c, |ctx| {
            if !ctx.ref_counted {
                // Non-RC contexts: no-op (no counts are tracked).
                return;
            }
            let term = require_term_ast_or_return!(ctx, a, "Z3_dec_ref", "AST");
            match ctx.ast_refcounts.get_mut(&term) {
                Some(count) if *count > 1 => {
                    *count -= 1;
                }
                Some(_) => {
                    // Count is exactly 1 → drop to 0. Remove the bookkeeping
                    // entry; the term itself is arena-interned and NOT freed.
                    ctx.ast_refcounts.remove(&term);
                }
                None => {
                    // Unbalanced dec_ref: count is absent (== 0). Report the
                    // error; never touch the arena.
                    ctx.last_error = Z3_DEC_REF_ERROR;
                }
            }
        });
    }
}

/// Interrupt the context (cancel ongoing computation).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_interrupt(c: Z3_context) {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_void(c, |ctx| {
            ctx.solver.interrupt();
        });
    }
}

/// Create an integer symbol.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_int_symbol(c: Z3_context, i: c_int) -> Z3_symbol {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| cache_int_symbol(ctx, i)) }
}

/// Create a string symbol.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_string_symbol(c: Z3_context, s: *const c_char) -> Z3_symbol {
    if s.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `s` is non-null and a valid NUL-terminated string per the caller
    // contract; the helper bounds the scan and clone.
    let name = match unsafe { ffi_read_bounded_text(s) } {
        Ok(name) => name,
        Err(_) => return ptr::null_mut(),
    };
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| cache_symbol(ctx, name.clone())) }
}

/// Get the string representation of a symbol.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_symbol_string(c: Z3_context, s: Z3_symbol) -> *const c_char {
    if s.is_null() {
        return ptr::null();
    }
    // SAFETY: All raw pointers used inside this block were validated (null-checked and/or
    // bounds-checked) above, and the caller's `# Safety` contract on this extern "C" function
    // guarantees they remain valid for the duration of the call.
    let sym = unsafe { &*s };
    let name = sym.display_name();
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_const_ptr` handles the null case internally and catches any unwinding panic
    // so it cannot cross the FFI boundary.
    unsafe { ffi_guard_const_ptr(c, |ctx| cache_string(ctx, name.clone())) }
}

/// Get Z3 version numbers.
/// Reports AY's version as the Z3 compatibility version.
///
/// # Safety
/// All pointers must be valid or null.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_version(
    major: *mut c_uint,
    minor: *mut c_uint,
    build_number: *mut c_uint,
    revision_number: *mut c_uint,
) {
    // SAFETY: All raw pointers used inside this block were validated (null-checked and/or
    // bounds-checked) above, and the caller's `# Safety` contract on this extern "C" function
    // guarantees they remain valid for the duration of the call.
    unsafe {
        // Report the pinned Z3 API compatibility version 5.1.0.0.
        if !major.is_null() {
            *major = 5;
        }
        if !minor.is_null() {
            *minor = 1;
        }
        if !build_number.is_null() {
            *build_number = 0;
        }
        if !revision_number.is_null() {
            *revision_number = 0;
        }
    }
}
