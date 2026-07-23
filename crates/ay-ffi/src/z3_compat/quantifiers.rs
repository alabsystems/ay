// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible quantifier construction: forall, exists, patterns, bound variables.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::c_uint;
use std::ptr;

use ay_dpll::api::{Sort, Term};

use super::{
    bounded_sort_hi, ffi_count_within_limit, ffi_counts_within_limit, ffi_guard_ast, ffi_guard_ptr,
    lookup_ast_sort, range_guard_term, record_ast_sort, require_term_ast_or_return,
    require_term_asts_or_return, term_to_ast, Z3Context, Z3_ast, Z3_context, Z3_sort, Z3_symbol,
    MAX_FFI_CONTAINER_ELEMENTS, Z3_INVALID_ARG,
};

// ============================================================================
// Pattern (Trigger) Handle
// ============================================================================

/// Opaque pattern handle (wraps a list of trigger terms).
pub type Z3_pattern = *mut PatternHandle;

pub struct PatternHandle {
    pub(crate) terms: Vec<Term>,
    pub(crate) owner_salt: u32,
}

/// Validate that pre-extracted trigger patterns came from `ctx` and that every
/// stored term is still live before a quantifier builder mutates the term arena.
pub(crate) fn checked_pattern_slices(
    ctx: &mut Z3Context,
    patterns: &[(u32, Vec<Term>)],
    operation: &str,
) -> Option<Vec<Vec<Term>>> {
    if patterns.iter().any(|(owner_salt, terms)| {
        *owner_salt != ctx.handle_salt || terms.iter().any(|&term| !ctx.solver.is_valid_term(term))
    }) {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some(format!(
            "{operation}: trigger pattern is stale or belongs to a different context"
        ));
        return None;
    }
    Some(patterns.iter().map(|(_, terms)| terms.clone()).collect())
}

// ============================================================================
// Z3_mk_pattern
// ============================================================================

/// Create a pattern (trigger) from a set of terms.
///
/// Patterns guide quantifier instantiation via E-matching. Each pattern
/// is a multi-trigger: all terms must match for the quantifier to be
/// instantiated.
///
/// # Safety
/// All pointers must be valid. `terms` must point to `num_patterns` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_pattern(
    c: Z3_context,
    num_patterns: c_uint,
    terms: *const Z3_ast,
) -> Z3_pattern {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_pattern", num_patterns) } {
        return ptr::null_mut();
    }
    if num_patterns == 0 || terms.is_null() {
        // Need context to set error — guard handles null context
        // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
        // extern "C" function requires it to be a valid, non-aliased pointer (or null).
        // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so
        // it cannot cross the FFI boundary.
        unsafe {
            return ffi_guard_ptr(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_pattern: num_patterns must be > 0".to_string());
                ptr::null_mut()
            });
        }
    }
    let pattern_asts: Vec<Z3_ast> = (0..num_patterns as usize)
        // SAFETY: The caller's `# Safety` contract guarantees `terms` points to at least the
        // declared number of elements. The count was range-checked above, and null-checked
        // before entering this block, so `terms.add(i)` stays within the caller's allocation.
        .map(|i| unsafe { *terms.add(i) })
        .collect();
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let pattern_terms =
                require_term_asts_or_return!(ctx, &pattern_asts, "Z3_mk_pattern", ptr::null_mut());
            let handle = Box::into_raw(Box::new(PatternHandle {
                terms: pattern_terms,
                owner_salt: ctx.handle_salt,
            }));
            ctx.pattern_cache.push(handle);
            handle
        })
    }
}

// ============================================================================
// Z3_mk_bound
// ============================================================================

/// Create a de Bruijn indexed bound variable.
///
/// AY uses named variables internally, so this creates a fresh variable
/// named `__db<index>` with the given sort. The index is stored for
/// later use by `Z3_mk_forall`/`Z3_mk_exists` which map de Bruijn
/// indices to the corresponding bound declarations.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bound(c: Z3_context, index: c_uint, ty: Z3_sort) -> Z3_ast {
    if ty.is_null() {
        return 0;
    }
    // SAFETY: `ty` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.sort` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let sort = unsafe { (*ty).sort.clone() };
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            // Create a named variable that encodes the de Bruijn index.
            let name = format!("__db{index}");
            let term = ctx.solver.declare_const(&name, sort.clone());
            let ast = term_to_ast(ctx, term);
            record_ast_sort(ctx, ast, sort.clone());
            ast
        })
    }
}

/// Guard a quantifier body for bounded-Int-lowered bound variables.
///
/// A `Char` / finite-domain bound variable lowers to an `Int`, which is
/// otherwise UNBOUNDED under the quantifier — `forall c:Char. φ` would wrongly
/// range over all integers (e.g. `forall c:Char. code(c) <= 196607` is VALID in
/// Z3 but would be falsified by an unbounded Int = a wrong verdict). Given the
/// per-variable range bounds, this rewrites the body to
///   * forall: `(range(x1) ∧ …) => body`
///   * exists: `range(x1) ∧ … ∧ body`
/// which is EXACTLY relativization of the quantifier to the sort's finite
/// carrier — the standard, semantics-preserving encoding. Variables of
/// unbounded sorts contribute no guard (body unchanged when none apply).
fn guard_bounded_quantifier_body(
    ctx: &mut Z3Context,
    is_forall: bool,
    var_bounds: &[(Term, i64)],
    body: Term,
) -> Term {
    if var_bounds.is_empty() {
        return body;
    }
    let guards: Vec<Term> = var_bounds
        .iter()
        .map(|&(v, hi)| range_guard_term(ctx, v, hi))
        .collect();
    let all = ctx.solver.and_many(&guards);
    if is_forall {
        ctx.solver.implies(all, body)
    } else {
        let mut parts = guards;
        parts.push(body);
        ctx.solver.and_many(&parts)
    }
}

// ============================================================================
// Z3_mk_forall_const / Z3_mk_exists_const
// ============================================================================

/// Create a universally quantified formula using constants.
///
/// `bound` contains the constants to bind. `patterns` contains
/// optional trigger patterns. `weight` is a priority hint (lower = higher
/// priority); AY ignores it.
///
/// # Safety
/// All pointers must be valid. `bound` must point to `num_bound` elements.
/// `patterns` must point to `num_patterns` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_forall_const(
    c: Z3_context,
    _weight: c_uint,
    num_bound: c_uint,
    bound: *const Z3_ast,
    num_patterns: c_uint,
    patterns: *const Z3_pattern,
    body: Z3_ast,
) -> Z3_ast {
    // SAFETY: every caller of this unsafe helper forwards a null or live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe {
        ffi_counts_within_limit(
            c,
            "quantifier bound variables and patterns",
            &[num_bound, num_patterns],
        )
    } {
        return 0;
    }
    // SAFETY: caller guarantees pointer validity per function contract
    unsafe { mk_quantifier_const(c, true, num_bound, bound, num_patterns, patterns, body) }
}

/// Create an existentially quantified formula using constants.
///
/// See [`Z3_mk_forall_const`] for parameter descriptions.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_exists_const(
    c: Z3_context,
    _weight: c_uint,
    num_bound: c_uint,
    bound: *const Z3_ast,
    num_patterns: c_uint,
    patterns: *const Z3_pattern,
    body: Z3_ast,
) -> Z3_ast {
    // SAFETY: every caller of this unsafe helper forwards a null or live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe {
        ffi_counts_within_limit(
            c,
            "quantifier bound variables and patterns",
            &[num_bound, num_patterns],
        )
    } {
        return 0;
    }
    // SAFETY: caller guarantees pointer validity per function contract
    unsafe { mk_quantifier_const(c, false, num_bound, bound, num_patterns, patterns, body) }
}

/// Shared implementation for `Z3_mk_forall_const` and `Z3_mk_exists_const`.
///
/// # Safety
/// All pointers must be valid.
unsafe fn mk_quantifier_const(
    c: Z3_context,
    is_forall: bool,
    num_bound: c_uint,
    bound: *const Z3_ast,
    num_patterns: c_uint,
    patterns: *const Z3_pattern,
    body: Z3_ast,
) -> Z3_ast {
    if num_bound == 0 || bound.is_null() {
        // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
        // extern "C" function requires it to be a valid, non-aliased pointer (or null).
        // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so
        // it cannot cross the FFI boundary.
        unsafe {
            return ffi_guard_ast(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("quantifier requires at least one bound variable".to_string());
                0
            });
        }
    }

    let bound_asts: Vec<Z3_ast> = (0..num_bound as usize)
        // SAFETY: The caller's `# Safety` contract guarantees `bound` points to at least the
        // declared number of elements. The count was range-checked above, and null-checked
        // before entering this block, so `bound.add(i)` stays within the caller's allocation.
        .map(|i| unsafe { *bound.add(i) })
        .collect();

    // Collect trigger patterns before entering the guard
    let trigger_data: Option<Vec<(u32, Vec<Term>)>> = if num_patterns > 0 && !patterns.is_null() {
        let mut slices = Vec::new();
        let mut total_terms = (num_bound as usize).saturating_add(num_patterns as usize);
        for i in 0..num_patterns as usize {
            // SAFETY: The caller's `# Safety` contract guarantees `patterns` points to at
            // least the declared number of elements. The count was range-checked above, and
            // null-checked before entering this block, so `patterns.add(i)` stays within the
            // caller's allocation.
            let pat = unsafe { *patterns.add(i) };
            if !pat.is_null() {
                // SAFETY: All raw pointers used inside this block were validated (null-checked
                // and/or bounds-checked) above, and the caller's `# Safety` contract on this
                // extern "C" function guarantees they remain valid for the duration of the
                // call.
                let handle = unsafe { &*pat };
                total_terms = total_terms.saturating_add(handle.terms.len());
                if total_terms > MAX_FFI_CONTAINER_ELEMENTS as usize {
                    // SAFETY: this public entry point requires `c` to be null or a live,
                    // exclusively borrowed context; the bound checker only updates its error state.
                    unsafe {
                        ffi_count_within_limit(
                            c,
                            "quantifier trigger terms",
                            MAX_FFI_CONTAINER_ELEMENTS + 1,
                        );
                    }
                    return 0;
                }
                slices.push((handle.owner_salt, handle.terms.clone()));
            }
        }
        Some(slices)
    } else {
        None
    };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let vars = require_term_asts_or_return!(ctx, &bound_asts, "quantifier construction", 0);
            let body_term =
                require_term_ast_or_return!(ctx, body, "quantifier construction", "body", 0);
            let trigger_slices = match trigger_data.as_deref() {
                Some(patterns) => {
                    let Some(slices) =
                        checked_pattern_slices(ctx, patterns, "quantifier construction")
                    else {
                        return 0;
                    };
                    Some(slices)
                }
                None => None,
            };
            // Relativize bounded-Int-lowered bound vars (Char / finite-domain)
            // to their carrier range — see `guard_bounded_quantifier_body`.
            let var_bounds: Vec<(Term, i64)> = vars
                .iter()
                .filter_map(|&v| {
                    lookup_ast_sort(ctx, term_to_ast(ctx, v))
                        .and_then(bounded_sort_hi)
                        .map(|hi| (v, hi))
                })
                .collect();
            let body_term = guard_bounded_quantifier_body(ctx, is_forall, &var_bounds, body_term);
            let result = if let Some(ref trigger_slices) = trigger_slices {
                let trigger_refs: Vec<&[Term]> = trigger_slices.iter().map(Vec::as_slice).collect();
                if is_forall {
                    ctx.solver
                        .try_forall_with_triggers(&vars, body_term, &trigger_refs)
                } else {
                    ctx.solver
                        .try_exists_with_triggers(&vars, body_term, &trigger_refs)
                }
            } else if is_forall {
                ctx.solver.try_forall(&vars, body_term)
            } else {
                ctx.solver.try_exists(&vars, body_term)
            };

            match result {
                Ok(term) => {
                    let ast = term_to_ast(ctx, term);
                    record_ast_sort(ctx, ast, Sort::Bool);
                    ast
                }
                Err(e) => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!("{e}"));
                    0
                }
            }
        })
    }
}

// ============================================================================
// Z3_mk_forall / Z3_mk_exists (de Bruijn style)
// ============================================================================

/// Create a universally quantified formula using de Bruijn indices.
///
/// `sorts` and `decl_names` specify the bound variables (innermost = index 0).
/// `patterns` contains optional triggers. `weight` is a priority hint (ignored).
///
/// The body should reference bound variables created via [`Z3_mk_bound`].
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_forall(
    c: Z3_context,
    _weight: c_uint,
    num_patterns: c_uint,
    patterns: *const Z3_pattern,
    num_decls: c_uint,
    sorts: *const Z3_sort,
    decl_names: *const Z3_symbol,
    body: Z3_ast,
) -> Z3_ast {
    // SAFETY: caller guarantees pointer validity per function contract
    unsafe {
        mk_quantifier_db(
            c,
            true,
            num_patterns,
            patterns,
            num_decls,
            sorts,
            decl_names,
            body,
        )
    }
}

/// Create an existentially quantified formula using de Bruijn indices.
///
/// See [`Z3_mk_forall`] for parameter descriptions.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_exists(
    c: Z3_context,
    _weight: c_uint,
    num_patterns: c_uint,
    patterns: *const Z3_pattern,
    num_decls: c_uint,
    sorts: *const Z3_sort,
    decl_names: *const Z3_symbol,
    body: Z3_ast,
) -> Z3_ast {
    // SAFETY: caller guarantees pointer validity per function contract
    unsafe {
        mk_quantifier_db(
            c,
            false,
            num_patterns,
            patterns,
            num_decls,
            sorts,
            decl_names,
            body,
        )
    }
}

/// Shared implementation for de Bruijn-style quantifiers.
///
/// Creates fresh named variables for each de Bruijn index, then delegates
/// to the const-style quantifier construction.
///
/// # Safety
/// All pointers must be valid.
unsafe fn mk_quantifier_db(
    c: Z3_context,
    is_forall: bool,
    num_patterns: c_uint,
    patterns: *const Z3_pattern,
    num_decls: c_uint,
    sorts: *const Z3_sort,
    decl_names: *const Z3_symbol,
    body: Z3_ast,
) -> Z3_ast {
    // SAFETY: every caller of this unsafe helper forwards a null or live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe {
        ffi_counts_within_limit(
            c,
            "quantifier declaration arrays and patterns",
            &[num_decls, num_decls, num_patterns],
        )
    } {
        return 0;
    }
    if num_decls == 0 || sorts.is_null() || decl_names.is_null() {
        // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
        // extern "C" function requires it to be a valid, non-aliased pointer (or null).
        // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so
        // it cannot cross the FFI boundary.
        unsafe {
            return ffi_guard_ast(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("quantifier requires at least one bound variable".to_string());
                0
            });
        }
    }

    // Pre-extract sort/name data from raw pointers before entering the guard
    let mut decl_data: Vec<(Sort, String)> = Vec::with_capacity(num_decls as usize);
    for i in 0..num_decls as usize {
        // SAFETY: The caller's `# Safety` contract guarantees `sorts` points to at least the
        // declared number of elements. The count was range-checked above, and null-checked
        // before entering this block, so `sorts.add(i)` stays within the caller's allocation.
        let sort_ptr = unsafe { *sorts.add(i) };
        // SAFETY: The caller's `# Safety` contract guarantees `decl_names` points to at least
        // the declared number of elements. The count was range-checked above, and null-checked
        // before entering this block, so `decl_names.add(i)` stays within the caller's
        // allocation.
        let sym_ptr = unsafe { *decl_names.add(i) };
        if sort_ptr.is_null() || sym_ptr.is_null() {
            // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on
            // this extern "C" function requires it to be a valid, non-aliased pointer (or
            // null). `ffi_guard_ast` handles the null case internally and catches any
            // unwinding panic so it cannot cross the FFI boundary.
            unsafe {
                return ffi_guard_ast(c, |ctx| {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some("null sort or name in quantifier declaration".to_string());
                    0
                });
            }
        }
        // SAFETY: `sort_ptr` was null-checked above and originates from a prior AY FFI
        // allocation whose handle is kept alive by the owning `Z3Context` (see handle caches
        // in `mod.rs`). Reading `.sort` is a shared-read with no concurrent mutation because
        // the Z3 C API is single-threaded per context.
        let sort = unsafe { (*sort_ptr).sort.clone() };
        // SAFETY: `sym_ptr` was null-checked above and originates from a prior AY FFI
        // allocation whose handle is kept alive by the owning `Z3Context` (see handle caches
        // in `mod.rs`). Reading the symbol key is a shared-read with no concurrent mutation because
        // the Z3 C API is single-threaded per context.
        let name = unsafe { (*sym_ptr).semantic_name() };
        decl_data.push((sort, name));
    }

    // Create bound variables + quantifier in a single guard closure
    // (can't split into two guards since both need &mut ctx)
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            // Authenticate every caller-provided term/pattern before declaring
            // bound variables, so a rejected call leaves the solver unchanged.
            let body_term =
                require_term_ast_or_return!(ctx, body, "quantifier construction", "body", 0);
            let trigger_slices: Option<Vec<Vec<Term>>> = if num_patterns > 0 && !patterns.is_null()
            {
                let mut pattern_data = Vec::new();
                let mut total_terms = (num_decls as usize)
                    .saturating_mul(2)
                    .saturating_add(num_patterns as usize);
                for i in 0..num_patterns as usize {
                    // SAFETY: the aggregate count was checked before this pointer
                    // walk and the caller supplies `num_patterns` live entries.
                    let pat = *patterns.add(i);
                    if !pat.is_null() {
                        // SAFETY: non-null pattern handles are live for this call
                        // under the entry point's ownership contract.
                        let handle = &*pat;
                        total_terms = total_terms.saturating_add(handle.terms.len());
                        if total_terms > MAX_FFI_CONTAINER_ELEMENTS as usize {
                            ctx.last_error = Z3_INVALID_ARG;
                            ctx.error_msg = Some(format!(
                                    "quantifier trigger terms: element count exceeds the supported maximum {MAX_FFI_CONTAINER_ELEMENTS}"
                                ));
                            return 0;
                        }
                        pattern_data.push((handle.owner_salt, handle.terms.clone()));
                    }
                }
                let Some(slices) =
                    checked_pattern_slices(ctx, &pattern_data, "quantifier construction")
                else {
                    return 0;
                };
                Some(slices)
            } else {
                None
            };

            let mut vars: Vec<Term> = Vec::with_capacity(decl_data.len());
            for (sort, name) in &decl_data {
                let term = ctx.solver.declare_const(name, sort.clone());
                let ast = term_to_ast(ctx, term);
                record_ast_sort(ctx, ast, sort.clone());
                vars.push(term);
            }

            // Relativize bounded-Int-lowered bound vars (Char / finite-domain)
            // to their carrier range — see `guard_bounded_quantifier_body`.
            let var_bounds: Vec<(Term, i64)> = decl_data
                .iter()
                .zip(vars.iter())
                .filter_map(|((sort, _), &v)| bounded_sort_hi(sort).map(|hi| (v, hi)))
                .collect();
            let body_term = guard_bounded_quantifier_body(ctx, is_forall, &var_bounds, body_term);

            let result = if let Some(ref trigger_slices) = trigger_slices {
                let trigger_refs: Vec<&[Term]> = trigger_slices.iter().map(Vec::as_slice).collect();
                if is_forall {
                    ctx.solver
                        .try_forall_with_triggers(&vars, body_term, &trigger_refs)
                } else {
                    ctx.solver
                        .try_exists_with_triggers(&vars, body_term, &trigger_refs)
                }
            } else if is_forall {
                ctx.solver.try_forall(&vars, body_term)
            } else {
                ctx.solver.try_exists(&vars, body_term)
            };

            match result {
                Ok(term) => {
                    let ast = term_to_ast(ctx, term);
                    record_ast_sort(ctx, ast, Sort::Bool);
                    ast
                }
                Err(e) => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!("{e}"));
                    0
                }
            }
        })
    }
}
