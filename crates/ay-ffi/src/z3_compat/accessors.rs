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

use ay_dpll::api::TermKind;

use super::{
    alloc_sort, ast_to_term, cache_func_decl_with_params, cache_func_decl_with_symbol,
    cache_symbol_key, ffi_guard_ast, ffi_guard_int, ffi_guard_ptr, ffi_guard_uint,
    parse_indexed_name, term_to_ast, Z3_ast, Z3_context, Z3_func_decl, Z3_sort, Z3_symbol,
    Z3_APP_AST, Z3_IOB, Z3_L_FALSE, Z3_L_TRUE, Z3_L_UNDEF, Z3_NUMERAL_AST, Z3_PARAMETER_INT,
    Z3_QUANTIFIER_AST, Z3_UNKNOWN_AST, Z3_VAR_AST,
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
fn declared_const_name(ctx: &super::Z3Context, a: Z3_ast) -> Option<String> {
    match ctx.solver.term_kind(ast_to_term(a)) {
        TermKind::Var { name } if !is_debruijn_bound_var_name(&name) => Some(name),
        _ => None,
    }
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
    // Tagged non-term handles never reach the term arena (the `ast_to_term`
    // poison guard would fail the call closed); report their kind directly.
    // Dispatch order: bit 63 (proof), bit 62 (algebraic), bit 61 (sort),
    // bit 60 (func_decl).
    match a & super::HANDLE_TAG_MASK {
        0 => {}
        super::SORT_AST_TAG => return super::Z3_SORT_AST,
        super::FUNC_DECL_AST_TAG => return super::Z3_FUNC_DECL_AST,
        // Proof / algebraic handles have no faithful term kind in AY
        // (z3 renders both as apps, but AY's are opaque text/value handles);
        // report UNKNOWN honestly rather than fabricate. Before the poison
        // guard these truncation-aliased onto an arbitrary term's kind.
        _ => return Z3_UNKNOWN_AST,
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_uint(c, Z3_UNKNOWN_AST, |ctx| {
            match ctx.solver.term_kind(ast_to_term(a)) {
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
    unsafe { ffi_guard_int(c, 0, |ctx| i32::from(ctx.solver.is_numeral(ast_to_term(a)))) != 0 }
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
            // A declared constant is a nullary application; the core stores it as
            // a `Var`, so `solver.is_app` alone would miss it (breaking z3py's
            // `is_app`/`to_app`). A numeral is also an application in z3.
            let is_app = ctx.solver.is_app(ast_to_term(a))
                || ctx.solver.is_numeral(ast_to_term(a))
                || declared_const_name(ctx, a).is_some();
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
            if ctx.solver.is_app(ast_to_term(a))
                || ctx.solver.is_numeral(ast_to_term(a))
                // A declared constant is a nullary application: z3's `Z3_to_app`
                // is a type-checked identity cast that succeeds on it, and stock
                // z3py depends on that (`m[x]`, `decl()`, quantifier construction).
                || declared_const_name(ctx, a).is_some()
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
            ctx.solver.app_num_args(ast_to_term(a)) as c_uint
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
            match ctx.solver.app_arg(ast_to_term(a), i as usize) {
                Some(t) => term_to_ast(t),
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
            let term = ast_to_term(a);
            // A declared constant is a nullary application; its decl is a 0-arity
            // function named after the constant, ranging over its sort. z3py's
            // `x.decl()` returns exactly this, so it must not be NULL.
            if let Some(const_name) = declared_const_name(ctx, a) {
                let range = ctx.solver.term_sort(term);
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
                        .map(|arg| ctx.solver.term_sort(arg))
                })
                .collect();
            let domain = match domain {
                Some(d) => d,
                None => return ptr::null_mut(),
            };
            let range = ctx.solver.term_sort(term);
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
    let sort = match decl.domain().get(i as usize) {
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
    let sort = decl.range().clone();
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
            match ctx.solver.bool_value(ast_to_term(a)) {
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
            if let Some(s) = ctx.solver.numeral_string(ast_to_term(a)) {
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
            if let Some(s) = ctx.solver.numeral_string(ast_to_term(a)) {
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
            if let Some(s) = ctx.solver.numeral_string(ast_to_term(a)) {
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
            if let Some(s) = ctx.solver.numeral_string(ast_to_term(a)) {
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
    // SAFETY: `d` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.params` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    unsafe { (*d).params.len() as c_uint }
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
/// `(_ zero_extend n)`, `(_ repeat n)`, `(_ rotate_left n)`, … — carry only
/// INTEGER parameters, so every in-range parameter reports `Z3_PARAMETER_INT`
/// (matching libz3, which reports `Z3_PARAMETER_INT` for these too). Read the
/// value itself with `Z3_get_decl_int_parameter`.
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
