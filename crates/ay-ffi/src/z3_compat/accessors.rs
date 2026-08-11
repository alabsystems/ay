// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible AST and FuncDecl accessor functions.
//!
//! Implements the subset of z3_api.h "Accessors" section needed for
//! external consumers: AST kind queries, app introspection, func_decl
//! introspection, and boolean value retrieval.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_int, c_uint};
use std::ptr;

use ay_dpll::api::{Term, TermKind};

use super::{
    alloc_sort, cache_func_decl_with_params, cache_func_decl_with_symbol, cache_symbol_key,
    ffi_guard_ast, ffi_guard_int, ffi_guard_ptr, ffi_guard_uint, finite_set_app_for_ast,
    finite_set_decl_for_ast, finite_set_empty_decl_parameter, lookup_ast_sort, parse_indexed_name,
    public_ast_sort, require_term_ast_or_return, term_to_ast, Z3_ast, Z3_context, Z3_func_decl,
    Z3_sort, Z3_symbol, Z3_APP_AST, Z3_IOB, Z3_L_FALSE, Z3_L_TRUE, Z3_L_UNDEF, Z3_NUMERAL_AST,
    Z3_PARAMETER_INT, Z3_PARAMETER_SORT, Z3_QUANTIFIER_AST, Z3_UNKNOWN_AST, Z3_VAR_AST,
};

// ============================================================================
// AST kind and classification
// ============================================================================

/// True iff `name` is AY's C-API encoding of a de-Bruijn BOUND variable —
/// `__db<index>`, as produced by [`Z3_mk_bound`] and consumed throughout the
/// quantifier machinery (see `ay_dpll::api::compat_ext`).
///
/// A declared CONSTANT (`Z3_mk_const`) and a bound variable are both stored as a
/// core `Var`, but z3 exposes them differently: a declared constant is a nullary
/// APPLICATION (`Z3_APP_AST`) — the shape stock z3py relies on for `to_app`,
/// `decl()`, `children()`, `ForAll`/`Exists` over constants, `m[x]` — while a
/// bound variable is the genuine `Z3_VAR_AST`. The `__db` marker is the only
/// thing that distinguishes them at the C-API boundary, so it is the pivot for
/// every classifier below.
fn is_debruijn_bound_var_name(name: &str) -> bool {
    name.strip_prefix("__db")
        .is_some_and(|rest| !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()))
}

/// The name of a declared constant (a core `Var` that is NOT a `__db` bound
/// variable), or `None` for anything else. A declared constant is a nullary
/// application in z3 terms.
fn declared_const_name(ctx: &super::Z3Context, term: Term) -> Option<String> {
    match ctx.solver.term_kind(term) {
        TermKind::Var { name } if !is_debruijn_bound_var_name(&name) => Some(name),
        _ => None,
    }
}

fn lookup_public_term_sort(ctx: &super::Z3Context, ast: Z3_ast, term: Term) -> ay_dpll::api::Sort {
    lookup_ast_sort(ctx, ast)
        .cloned()
        .unwrap_or_else(|| ctx.solver.term_sort(term))
}

/// Get the kind of an AST node.
///
/// Returns one of `Z3_NUMERAL_AST`, `Z3_APP_AST`, `Z3_VAR_AST`,
/// `Z3_QUANTIFIER_AST`, or `Z3_UNKNOWN_AST`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_ast_kind(c: Z3_context, a: Z3_ast) -> c_uint {
    if a == 0 {
        return Z3_UNKNOWN_AST;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_uint(c, Z3_UNKNOWN_AST, |ctx| {
            // Tagged non-term handles never reach the term arena. Authenticate
            // each arena lookup before reporting even its kind: otherwise a
            // foreign sort/decl handle would be accepted as a local object.
            match a & super::HANDLE_TAG_MASK {
                super::SORT_AST_TAG => {
                    if super::sort_ast_to_handle(ctx, a).is_null() {
                        ctx.last_error = super::Z3_INVALID_ARG;
                        ctx.error_msg =
                            Some("Z3_get_ast_kind: invalid or foreign sort AST handle".to_string());
                        return Z3_UNKNOWN_AST;
                    }
                    ctx.last_error = super::Z3_OK;
                    return super::Z3_SORT_AST;
                }
                super::FUNC_DECL_AST_TAG => {
                    if super::func_decl_ast_to_handle(ctx, a).is_null() {
                        ctx.last_error = super::Z3_INVALID_ARG;
                        ctx.error_msg = Some(
                            "Z3_get_ast_kind: invalid or foreign func-decl AST handle".to_string(),
                        );
                        return Z3_UNKNOWN_AST;
                    }
                    ctx.last_error = super::Z3_OK;
                    return super::Z3_FUNC_DECL_AST;
                }
                super::PROOF_AST_TAG => {
                    if super::proof_text_for_ast(ctx, a).is_none() {
                        ctx.last_error = super::Z3_INVALID_ARG;
                        ctx.error_msg = Some(
                            "Z3_get_ast_kind: invalid or foreign proof AST handle".to_string(),
                        );
                    } else {
                        ctx.last_error = super::Z3_OK;
                    }
                    // AY's proof handle has no faithful term kind.
                    return Z3_UNKNOWN_AST;
                }
                super::ALGEBRAIC_AST_TAG => {
                    if super::algebraic::ast_as_scalar(ctx, a).is_none() {
                        ctx.last_error = super::Z3_INVALID_ARG;
                        ctx.error_msg = Some(
                            "Z3_get_ast_kind: invalid or foreign algebraic AST handle".to_string(),
                        );
                    } else {
                        ctx.last_error = super::Z3_OK;
                    }
                    // AY's opaque algebraic handle has no faithful term kind.
                    return Z3_UNKNOWN_AST;
                }
                0 => {}
                _ => {
                    ctx.last_error = super::Z3_INVALID_ARG;
                    ctx.error_msg = Some("Z3_get_ast_kind: malformed AST tag".to_string());
                    return Z3_UNKNOWN_AST;
                }
            }
            if finite_set_app_for_ast(ctx, a).is_some() {
                return Z3_APP_AST;
            }
            let term =
                require_term_ast_or_return!(ctx, a, "Z3_get_ast_kind", "AST", Z3_UNKNOWN_AST);
            match ctx.solver.term_kind(term) {
                TermKind::Const => Z3_NUMERAL_AST,
                TermKind::App { .. } | TermKind::Not | TermKind::Ite => Z3_APP_AST,
                // A declared constant (`Z3_mk_const`) is a NULLARY APPLICATION in
                // z3 (`Z3_APP_AST`); only a `__db` de-Bruijn bound variable is a
                // true `Z3_VAR_AST`. Reporting VAR for a declared constant made
                // `Z3_to_app` return NULL and broke stock z3py (`m[x]`, `decl()`,
                // `ForAll`/`Exists` over consts).
                TermKind::Var { name } if is_debruijn_bound_var_name(&name) => Z3_VAR_AST,
                TermKind::Var { .. } => Z3_APP_AST,
                TermKind::Forall | TermKind::Exists => Z3_QUANTIFIER_AST,
                TermKind::Let | _ => Z3_UNKNOWN_AST,
            }
        })
    }
}

/// Return true if the AST is a numeral.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_numeral_ast(c: Z3_context, a: Z3_ast) -> bool {
    if a == 0 {
        return false;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = require_term_ast_or_return!(ctx, a, "Z3_is_numeral_ast", "AST", 0);
            i32::from(ctx.solver.is_numeral(term))
        }) != 0
    }
}

/// Return true if the AST is an application node.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_app(c: Z3_context, a: Z3_ast) -> bool {
    if a == 0 {
        return false;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = require_term_ast_or_return!(ctx, a, "Z3_is_app", "AST", 0);
            // A declared constant is a nullary application; the core stores it as
            // a `Var`, so `solver.is_app` alone would miss it (breaking z3py's
            // `is_app`/`to_app`). A numeral is also an application in z3.
            let is_app = finite_set_app_for_ast(ctx, a).is_some()
                || ctx.solver.is_app(term)
                || ctx.solver.is_numeral(term)
                || declared_const_name(ctx, term).is_some();
            i32::from(is_app)
        }) != 0
    }
}

/// Convert an AST to an application node.
///
/// In Z3, `Z3_app` is a typedef for `Z3_ast`. This function is a type-checked
/// identity cast: returns the AST unchanged if it represents an application,
/// or 0 (null) if it does not.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_to_app(c: Z3_context, a: Z3_ast) -> Z3_ast {
    if a == 0 {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            // A tagged non-term handle (proof/algebraic/sort/func-decl AST) is
            // not an application. z3's identity-cast leniency here is UB we
            // refuse to copy: fail closed with INVALID_ARG.
            if a & super::HANDLE_TAG_MASK != 0 {
                ctx.last_error = super::Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_to_app: argument is not an application AST".to_string());
                return 0;
            }
            let term = require_term_ast_or_return!(ctx, a, "Z3_to_app", "AST", 0);
            if finite_set_app_for_ast(ctx, a).is_some()
                || ctx.solver.is_app(term)
                || ctx.solver.is_numeral(term)
                // A declared constant is a nullary application: z3's `Z3_to_app`
                // is a type-checked identity cast that succeeds on it, and stock
                // z3py depends on that (`m[x]`, `decl()`, quantifier construction).
                || declared_const_name(ctx, term).is_some()
            {
                a
            } else {
                0
            }
        })
    }
}

// ============================================================================
// Application introspection
// ============================================================================

/// Get the number of arguments of an application AST.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_app_num_args(c: Z3_context, a: Z3_ast) -> c_uint {
    if a == 0 {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            if let Some(app) = finite_set_app_for_ast(ctx, a) {
                return app.args.len() as c_uint;
            }
            let term = require_term_ast_or_return!(ctx, a, "Z3_get_app_num_args", "application", 0);
            ctx.solver.app_num_args(term) as c_uint
        })
    }
}

/// Get the i-th argument of an application AST.
///
/// Returns 0 (null AST) if `a` is not an application or `i` is out of bounds.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_app_arg(c: Z3_context, a: Z3_ast, i: c_uint) -> Z3_ast {
    if a == 0 {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if let Some(app) = finite_set_app_for_ast(ctx, a) {
                return app.args.get(i as usize).copied().unwrap_or(0);
            }
            let term = require_term_ast_or_return!(ctx, a, "Z3_get_app_arg", "application", 0);
            match ctx.solver.app_arg(term, i as usize) {
                Some(t) => term_to_ast(ctx, t),
                None => 0,
            }
        })
    }
}

/// Get the function declaration of an application AST.
///
/// For built-in operators (and, or, not, +, -, etc.) this returns a synthetic
/// func_decl with the operator name.
///
/// Returns null if `a` is not an application.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_app_decl(c: Z3_context, a: Z3_ast) -> Z3_func_decl {
    if a == 0 {
        return ptr::null_mut();
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if let Some(decl) = finite_set_decl_for_ast(ctx, a) {
                return decl;
            }
            let term = require_term_ast_or_return!(
                ctx,
                a,
                "Z3_get_app_decl",
                "application",
                ptr::null_mut()
            );
            // A declared constant is a nullary application; its decl is a 0-arity
            // function named after the constant, ranging over its sort. z3py's
            // `x.decl()` returns exactly this, so it must not be NULL.
            if let Some(const_name) = declared_const_name(ctx, term) {
                let range = lookup_public_term_sort(ctx, a, term);
                if let Some((identity, symbol)) = ctx.ffi_const_metadata.get(&term).cloned() {
                    return cache_func_decl_with_symbol(
                        ctx,
                        ay_dpll::api::FuncDecl::new(identity, Vec::new(), range),
                        symbol,
                    );
                }
                return cache_func_decl_with_params(
                    ctx,
                    ay_dpll::api::FuncDecl::new(const_name, Vec::new(), range),
                    Vec::new(),
                );
            }
            let name = match ctx.solver.app_symbol_name(term) {
                Some(n) => n,
                None => return ptr::null_mut(),
            };
            let num_args = ctx.solver.app_num_args(term);
            // Parse indexed operator name and extract parameters (#6580 F2).
            let (base_name, params) = parse_indexed_name(&name);
            // z3py reports the if-then-else operator's canonical decl name as
            // "if" (its native syntax), while AY's core / SMT-LIB symbol is
            // "ite". Canonicalize here so `decl().name()` matches z3py exactly;
            // the decl kind stays Z3_OP_ITE (operator_name_to_decl_kind maps
            // both spellings). The core's SMT-LIB printing is untouched.
            let base_name = if base_name == "ite" {
                "if".to_string()
            } else {
                base_name
            };
            // Reconstruct real domain sorts from the application's children (#6580 F3).
            // Falls back to null if any child lookup fails.
            let domain: Option<Vec<_>> = (0..num_args)
                .map(|i| {
                    ctx.solver
                        .app_arg(term, i)
                        .map(|arg| public_ast_sort(ctx, term_to_ast(ctx, arg), arg))
                })
                .collect();
            let domain = match domain {
                Some(d) => d,
                None => return ptr::null_mut(),
            };
            let (domain, range) =
                if let Some((domain, range)) = ctx.finite_set_decl_signatures.get(&name).cloned() {
                    (domain, range)
                } else {
                    (domain, lookup_public_term_sort(ctx, a, term))
                };
            cache_func_decl_with_params(
                ctx,
                ay_dpll::api::FuncDecl::new(base_name, domain, range),
                params,
            )
        })
    }
}

// ============================================================================
// FuncDecl introspection
// ============================================================================

/// Get the name of a function declaration as a symbol.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_name(c: Z3_context, d: Z3_func_decl) -> Z3_symbol {
    if d.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `d` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.decl` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let handle = unsafe { &*d };
    let symbol = handle
        .symbol
        .clone()
        .unwrap_or_else(|| super::SymbolKey::String(handle.decl.name().to_string()));
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| cache_symbol_key(ctx, symbol.clone())) }
}

/// Get the number of arguments (arity) of a function declaration.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_arity(_c: Z3_context, d: Z3_func_decl) -> c_uint {
    if d.is_null() {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_uint(_c, 0, |_ctx| {
            let decl = &(*d).decl;
            decl.arity() as c_uint
        })
    }
}

/// Get the number of parameters in a function declaration (always 0 for AY).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_domain_size(_c: Z3_context, d: Z3_func_decl) -> c_uint {
    if d.is_null() {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_uint(_c, 0, |_ctx| {
            let decl = &(*d).decl;
            decl.arity() as c_uint
        })
    }
}

/// Get the i-th domain sort of a function declaration.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_domain(c: Z3_context, d: Z3_func_decl, i: c_uint) -> Z3_sort {
    if d.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `d` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.decl` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let decl = unsafe { &(*d).decl };
    let public_signature = unsafe {
        c.as_ref()
            .and_then(|ctx| ctx.finite_set_decl_signatures.get(decl.name()))
    };
    let sort = match public_signature
        .map(|(domain, _)| domain.as_slice())
        .unwrap_or_else(|| decl.domain())
        .get(i as usize)
    {
        Some(s) => s.clone(),
        None => return ptr::null_mut(),
    };
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, sort.clone())) }
}

/// Get the range (return) sort of a function declaration.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_range(c: Z3_context, d: Z3_func_decl) -> Z3_sort {
    if d.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `d` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.decl` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let decl = unsafe { &(*d).decl };
    let sort = unsafe {
        c.as_ref()
            .and_then(|ctx| ctx.finite_set_decl_signatures.get(decl.name()))
            .map_or_else(|| decl.range().clone(), |(_, range)| range.clone())
    };
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, sort.clone())) }
}

// ============================================================================
// Boolean value
// ============================================================================

/// Get the boolean value of a constant AST.
///
/// Returns `Z3_L_TRUE`, `Z3_L_FALSE`, or `Z3_L_UNDEF` if not a boolean constant.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_bool_value(c: Z3_context, a: Z3_ast) -> c_int {
    if a == 0 {
        return Z3_L_UNDEF;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, Z3_L_UNDEF, |ctx| {
            let term = require_term_ast_or_return!(
                ctx,
                a,
                "Z3_get_bool_value",
                "Boolean term",
                Z3_L_UNDEF
            );
            match ctx.solver.bool_value(term) {
                Some(true) => Z3_L_TRUE,
                Some(false) => Z3_L_FALSE,
                None => Z3_L_UNDEF,
            }
        })
    }
}

// ============================================================================
// Numeral extraction
// ============================================================================

/// Try to extract an i32 value from a numeral AST.
///
/// Returns true and writes to `*v` if successful, false otherwise.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_int(c: Z3_context, a: Z3_ast, v: *mut c_int) -> bool {
    if a == 0 || v.is_null() {
        return false;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = require_term_ast_or_return!(ctx, a, "Z3_get_numeral_int", "numeral", 0);
            if let Some(s) = ctx.solver.numeral_string(term) {
                if let Ok(val) = s.parse::<c_int>() {
                    *v = val;
                    return 1;
                }
            }
            0
        }) != 0
    }
}

/// Try to extract a u32 value from a numeral AST.
///
/// Returns true and writes to `*v` if successful, false otherwise.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_uint(c: Z3_context, a: Z3_ast, v: *mut c_uint) -> bool {
    if a == 0 || v.is_null() {
        return false;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = require_term_ast_or_return!(ctx, a, "Z3_get_numeral_uint", "numeral", 0);
            if let Some(s) = ctx.solver.numeral_string(term) {
                if let Ok(val) = s.parse::<c_uint>() {
                    *v = val;
                    return 1;
                }
            }
            0
        }) != 0
    }
}

/// Try to extract an i64 value from a numeral AST.
///
/// Returns true and writes to `*v` if successful, false otherwise.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_int64(c: Z3_context, a: Z3_ast, v: *mut i64) -> bool {
    if a == 0 || v.is_null() {
        return false;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = require_term_ast_or_return!(ctx, a, "Z3_get_numeral_int64", "numeral", 0);
            if let Some(s) = ctx.solver.numeral_string(term) {
                if let Ok(val) = s.parse::<i64>() {
                    *v = val;
                    return 1;
                }
            }
            0
        }) != 0
    }
}

/// Try to extract a u64 value from a numeral AST.
///
/// Returns true and writes to `*v` if successful, false otherwise.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_uint64(c: Z3_context, a: Z3_ast, v: *mut u64) -> bool {
    if a == 0 || v.is_null() {
        return false;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_int` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = require_term_ast_or_return!(ctx, a, "Z3_get_numeral_uint64", "numeral", 0);
            if let Some(s) = ctx.solver.numeral_string(term) {
                if let Ok(val) = s.parse::<u64>() {
                    *v = val;
                    return 1;
                }
            }
            0
        }) != 0
    }
}

// ============================================================================
// Function declaration parameter introspection
// ============================================================================

/// Get the number of parameters associated with a function declaration.
///
/// For indexed operators like `(_ extract 7 4)`, returns the number of
/// integer parameters (2 in that case). For non-indexed operators, returns 0.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_num_parameters(_c: Z3_context, d: Z3_func_decl) -> c_uint {
    if d.is_null() {
        return 0;
    }
    // SAFETY: the context guard catches panics and `d` is a context-owned,
    // null-checked declaration handle under the C API contract.
    unsafe {
        ffi_guard_uint(_c, 0, |ctx| {
            if finite_set_empty_decl_parameter(ctx, &(*d).decl).is_some() {
                1
            } else {
                (*d).params.len() as c_uint
            }
        })
    }
}

/// Get an integer parameter from a function declaration.
///
/// For indexed operators, returns the parameter at `idx`. For example,
/// `(_ extract 7 4)` has parameter 0 = 7 and parameter 1 = 4.
/// Returns 0 if `idx` is out of bounds or the decl has no parameters.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_int_parameter(
    _c: Z3_context,
    d: Z3_func_decl,
    idx: c_uint,
) -> c_int {
    if d.is_null() {
        return 0;
    }
    // SAFETY: `d` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.params` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    unsafe {
        let params = &(*d).params;
        params.get(idx as usize).copied().unwrap_or(0)
    }
}

/// Get the `Z3_parameter_kind` of a function declaration's `idx`-th parameter.
///
/// AY's indexed operators — `(_ extract h l)`, `(_ sign_extend n)`,
/// `(_ zero_extend n)`, `(_ repeat n)`, `(_ rotate_left n)`, … — report
/// `Z3_PARAMETER_INT`; Z3 5.0.0 finite-set `set.empty` reports one
/// `Z3_PARAMETER_SORT`. Read values through the corresponding typed getter.
///
/// For `idx >= Z3_get_decl_num_parameters(c, d)` this sets `Z3_IOB` (index out of
/// bounds) and returns `Z3_PARAMETER_INT` (`0`) as a benign default — the caller
/// should honor the `idx < num_parameters` precondition and check the error code.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_parameter_kind(
    c: Z3_context,
    d: Z3_func_decl,
    idx: c_uint,
) -> c_uint {
    if d.is_null() {
        return Z3_PARAMETER_INT;
    }
    // SAFETY: `c` is guarded by `ffi_guard_uint`; `d` is a valid, non-aliasing
    // func_decl handle owned by the context (single-threaded read of `.params`).
    unsafe {
        ffi_guard_uint(c, Z3_PARAMETER_INT, |ctx| {
            if finite_set_empty_decl_parameter(ctx, &(*d).decl).is_some() {
                if idx == 0 {
                    return Z3_PARAMETER_SORT;
                }
                ctx.last_error = Z3_IOB;
                ctx.error_msg = Some(format!(
                    "Z3_get_decl_parameter_kind: index {idx} out of bounds (1 parameter)"
                ));
                return Z3_PARAMETER_INT;
            }
            let params = &(*d).params;
            if (idx as usize) < params.len() {
                // AY's only decl parameters are integers (indexed BV operators).
                Z3_PARAMETER_INT
            } else {
                ctx.last_error = Z3_IOB;
                ctx.error_msg = Some(format!(
                    "Z3_get_decl_parameter_kind: index {idx} out of bounds ({} parameter(s))",
                    params.len()
                ));
                Z3_PARAMETER_INT
            }
        })
    }
}
