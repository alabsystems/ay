// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Engine-backed extensions to the Z3-compatible C API.
//!
//! These 22 entry points broaden the C ABI toward `z3_api.h` while staying
//! sound-by-construction: each lowers directly onto an existing, semantically
//! identical `ay_dpll::api::Solver` primitive (added in `api/compat_ext.rs`) —
//! term traversal/rebuild (`is_ground`, `substitute_vars`, `substitute_funs`,
//! `update_term`), the `TermArena` array/lambda/map builders
//! (`array_default`/`as_array`/`lambda_array`/`array_map`, which also underlie
//! the pointwise set operations), recognized-builtin named applications
//! (`str.<=`, `str.<`, `str.from_code`, `str.to_code`, `seq.last_indexof`,
//! `str.replace_re`, `str.replace_re_all`), the empty-`Model` constructor, and
//! the `qe-light` equality-elimination core.
//!
//! None of them introduces a new "decide" path, so none can make AY emit a
//! wrong verdict. Building a recognized theory atom is sound regardless of
//! whether the executor can DECIDE it (an undecided atom yields `unknown`,
//! never a wrong answer). Where a well-sorted result cannot be formed (e.g. a
//! zero-argument set union, whose element sort is unknowable), the function
//! sets an error and returns the sound null sentinel rather than fabricating a
//! term.
//!
//! Every function calling into the solver is wrapped via the `ffi_guard_*`
//! helpers so a panic can never unwind across the `extern "C"` boundary.

use std::ffi::c_uint;

use ay_dpll::api::{FuncDecl, Model, SolverError, Sort, Term};

use super::{
    activate_finite_set_quantifier_gate, activate_finite_set_sat_gate, checked_ast_to_term,
    ffi_count_within_limit, ffi_counts_within_limit, ffi_guard_ast, ffi_guard_ptr, ffi_guard_uint,
    finite_set_engine_public_sort, lookup_ast_sort, public_ast_sort, record_ast_sort,
    require_term_ast_or_return, require_term_asts_or_return, sort_mentions_finite_set,
    term_ast_belongs_to, term_to_ast, ModelHandle, Z3Context, Z3_ast, Z3_ast_vector, Z3_context,
    Z3_func_decl, Z3_model, Z3_sort, Z3_symbol, HANDLE_TAG_MASK, TERM_AST_PAYLOAD_MASK,
    Z3_EXCEPTION, Z3_INVALID_ARG, Z3_IOB, Z3_SORT_ERROR,
};

// ============================================================================
// Term predicates / traversal
// ============================================================================

/// Return `true` iff `a` is ground (contains no free/quantifier-bound variable).
///
/// A declared constant is ground (0-arity app, matching Z3); an unregistered
/// quantifier-bound variable is not. Delegates to `Solver::is_ground`.
///
/// # Safety
/// `c` must be a valid context pointer (or null, which yields `false`).
#[no_mangle]
pub unsafe extern "C" fn Z3_is_ground(c: Z3_context, a: Z3_ast) -> bool {
    if a == 0 {
        return false;
    }
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_uint` null-checks it
    // and catches panics so none cross the FFI boundary. Bool encoded as 0/1.
    let r = unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            let term = require_term_ast_or_return!(ctx, a, "Z3_is_ground", "AST", 0);
            u32::from(ctx.solver.is_ground(term))
        })
    };
    r != 0
}

// ============================================================================
// Substitution
// ============================================================================

/// Replace de Bruijn bound variable `i` (AY's `__db<i>` var) with `to[i]`.
///
/// Guard: `num_exprs == 0` or null `to` returns `a` unchanged. Delegates to
/// `Solver::substitute_vars`.
///
/// # Safety
/// `c` must be a valid context pointer; `to`, when non-null, must point to
/// `num_exprs` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_substitute_vars(
    c: Z3_context,
    a: Z3_ast,
    num_exprs: c_uint,
    to: *const Z3_ast,
) -> Z3_ast {
    if a == 0 {
        return 0;
    }
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_substitute_vars", num_exprs) } {
        return 0;
    }
    if num_exprs == 0 || to.is_null() {
        return a;
    }
    let to_asts: Vec<Z3_ast> = (0..num_exprs as usize)
        // SAFETY: caller's contract guarantees `to` points to `num_exprs` elements;
        // count range-checked and null-checked above.
        .map(|i| unsafe { *to.add(i) })
        .collect();
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let source = require_term_ast_or_return!(ctx, a, "Z3_substitute_vars", "input", a);
            let to_terms = require_term_asts_or_return!(ctx, &to_asts, "Z3_substitute_vars", a);
            let result = ctx.solver.substitute_vars(source, &to_terms);
            let r = term_to_ast(ctx, result);
            let sort = ctx.solver.term_sort(result);
            record_ast_sort(ctx, r, sort);
            r
        })
    }
}

/// Macro/beta-expand each application of `from[i]` in `a` using the template
/// `to[i]` (a body over the de Bruijn params `__db0..`). Delegates to
/// `Solver::substitute_funs`.
///
/// Guard: `num_funs == 0` or null `from`/`to` returns `a` unchanged; a null
/// decl in `from` sets `Z3_INVALID_ARG` and returns `0`.
///
/// # Safety
/// `c` must be a valid context pointer; `from`/`to`, when non-null, must point
/// to `num_funs` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_substitute_funs(
    c: Z3_context,
    a: Z3_ast,
    num_funs: c_uint,
    from: *const Z3_func_decl,
    to: *const Z3_ast,
) -> Z3_ast {
    if a == 0 {
        return 0;
    }
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe {
        ffi_counts_within_limit(
            c,
            "Z3_substitute_funs declaration and replacement arrays",
            &[num_funs, num_funs],
        )
    } {
        return 0;
    }
    if num_funs == 0 || from.is_null() || to.is_null() {
        return a;
    }
    // Pre-extract the decls and replacement terms from raw pointers.
    let mut from_decls: Vec<FuncDecl> = Vec::with_capacity(num_funs as usize);
    for i in 0..num_funs as usize {
        // SAFETY: caller's contract guarantees `from` points to `num_funs` elements;
        // count range-checked and null-checked above.
        let d = unsafe { *from.add(i) };
        if d.is_null() {
            // SAFETY: `c` is the caller's context pointer; guard null-checks it.
            return unsafe {
                ffi_guard_ast(c, |ctx| {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some("null func_decl in substitute_funs".to_string());
                    0
                })
            };
        }
        // SAFETY: `d` null-checked above; a valid AY func_decl handle kept alive by
        // the owning context (single-threaded per context).
        from_decls.push(unsafe { (*d).decl.clone() });
    }
    let to_asts: Vec<Z3_ast> = (0..num_funs as usize)
        // SAFETY: caller's contract guarantees `to` points to `num_funs` elements.
        .map(|i| unsafe { *to.add(i) })
        .collect();
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let source = require_term_ast_or_return!(ctx, a, "Z3_substitute_funs", "input", a);
            let to_terms = require_term_asts_or_return!(ctx, &to_asts, "Z3_substitute_funs", a);
            let result = ctx.solver.substitute_funs(source, &from_decls, &to_terms);
            let r = term_to_ast(ctx, result);
            let sort = ctx.solver.term_sort(result);
            record_ast_sort(ctx, r, sort);
            r
        })
    }
}

/// Decode one raw term handle only after authenticating its representation and
/// membership in this context's term store.
fn checked_update_term_ast(ctx: &Z3Context, ast: Z3_ast, role: &str) -> Result<Term, SolverError> {
    if ast == 0 {
        return Err(SolverError::InvalidArgument {
            operation: "update_term",
            message: format!("{role} AST handle is null"),
        });
    }
    if ast & HANDLE_TAG_MASK != 0 {
        return Err(SolverError::InvalidArgument {
            operation: "update_term",
            message: format!("{role} AST handle {ast} is tagged and does not denote a term"),
        });
    }
    if !term_ast_belongs_to(ctx, ast) {
        return Err(SolverError::InvalidArgument {
            operation: "update_term",
            message: format!("{role} AST handle {ast} belongs to a different context"),
        });
    }
    let payload = ast & TERM_AST_PAYLOAD_MASK;
    let max_term_ast = u64::from(u32::MAX) + 1;
    if payload > max_term_ast {
        return Err(SolverError::InvalidArgument {
            operation: "update_term",
            message: format!(
                "{role} AST handle {ast} exceeds the maximum term payload {max_term_ast}"
            ),
        });
    }
    let Some(term) = checked_ast_to_term(ctx, ast) else {
        return Err(SolverError::InvalidArgument {
            operation: "update_term",
            message: format!("{role} AST handle {ast} is not live in this context"),
        });
    };
    Ok(term)
}

/// Rebuild `a` keeping its operator/binder but swapping in `args` as children.
///
/// Arg-count mismatch (against the node's child count) sets `Z3_IOB` and returns
/// `a` unchanged. Invalid handles, replacement-sort mismatches, and other
/// checked rebuild failures set `Z3_EXCEPTION`, preserve the complete
/// `SolverError` diagnostic, and likewise return `a` unchanged. Delegates to
/// `Solver::try_update_term`; no unchecked term-store access occurs here.
///
/// # Safety
/// `c` must be a valid context pointer; `args`, when non-null, must point to
/// `num_args` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_update_term(
    c: Z3_context,
    a: Z3_ast,
    num_args: c_uint,
    args: *const Z3_ast,
) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_update_term", num_args) } {
        return a;
    }
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let source = match checked_update_term_ast(ctx, a, "source") {
                Ok(source) => source,
                Err(error) => {
                    ctx.last_error = Z3_EXCEPTION;
                    ctx.error_msg = Some(error.to_string());
                    return a;
                }
            };
            if num_args > 0 && args.is_null() {
                let error = SolverError::InvalidArgument {
                    operation: "update_term",
                    message: "replacement AST array is null for a nonzero argument count"
                        .to_string(),
                };
                ctx.last_error = Z3_EXCEPTION;
                ctx.error_msg = Some(error.to_string());
                return a;
            }
            let mut arg_terms = Vec::with_capacity(num_args as usize);
            for position in 0..num_args as usize {
                // SAFETY: the public function contract requires `args` to point
                // to `num_args` elements; the count is capped above and the
                // nonzero-count null case was rejected before this dereference.
                let raw = *args.add(position);
                let role = format!("replacement at position {position}");
                match checked_update_term_ast(ctx, raw, &role) {
                    Ok(term) => arg_terms.push(term),
                    Err(error) => {
                        ctx.last_error = Z3_EXCEPTION;
                        ctx.error_msg = Some(error.to_string());
                        return a;
                    }
                }
            }

            match ctx.solver.try_update_term(source, &arg_terms) {
                Ok(result) => {
                    let r = term_to_ast(ctx, result);
                    let sort = ctx.solver.term_sort(result);
                    record_ast_sort(ctx, r, sort);
                    r
                }
                Err(error) => {
                    let is_count_mismatch = matches!(
                        &error,
                        SolverError::InvalidArgument { operation, message }
                            if *operation == "update_term"
                                && message.starts_with("term expects ")
                                && message.contains(" immediate children, got ")
                    );
                    ctx.last_error = if is_count_mismatch {
                        Z3_IOB
                    } else {
                        Z3_EXCEPTION
                    };
                    ctx.error_msg = Some(error.to_string());
                    a
                }
            }
        })
    }
}

// ============================================================================
// Array / lambda / map (and the pointwise set operations)
// ============================================================================

/// `(default a)` — the else-case value of array `a`; result sort is `a`'s
/// element sort. Delegates to `Solver::array_default`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_array_default(c: Z3_context, array: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let array_term =
                require_term_ast_or_return!(ctx, array, "Z3_mk_array_default", "array", 0);
            let public_sort = public_ast_sort(ctx, array, array_term);
            let Sort::Array(public_array) = public_sort else {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg =
                    Some("Z3_mk_array_default: public operand sort is not an Array".to_string());
                return 0;
            };
            let t = ctx.solver.array_default(array_term);
            let r = term_to_ast(ctx, t);
            record_ast_sort(ctx, r, public_array.element_sort);
            r
        })
    }
}

/// `(as-array f)` for the UNARY function `f` — an array with
/// `select(as-array f, i) = f(i)` and sort `(Array dom range)`. Rejects a
/// non-unary `f` with `Z3_INVALID_ARG`. Delegates to `Solver::as_array`.
///
/// # Safety
/// `c` must be a valid context pointer; `f`, when non-null, a valid func_decl.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_as_array(c: Z3_context, f: Z3_func_decl) -> Z3_ast {
    if f.is_null() {
        return 0;
    }
    // SAFETY: `f` null-checked above; a valid AY func_decl handle kept alive by the
    // owning context (single-threaded per context).
    let decl = unsafe { &(*f).decl };
    let arity = decl.arity();
    let dom0 = decl.domain().first().cloned();
    let range = decl.range().clone();
    let name = decl.name().to_string();
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let (public_domain, public_range) = ctx
                .finite_set_decl_signatures
                .get(&name)
                .cloned()
                .unwrap_or_else(|| (dom0.clone().into_iter().collect::<Vec<_>>(), range.clone()));
            let [public_domain] = public_domain.as_slice() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_mk_as_array requires a unary (arity 1) function".to_string());
                return 0;
            };
            if arity != 1 || dom0.is_none() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_mk_as_array requires a unary (arity 1) function".to_string());
                return 0;
            }
            let public_array_sort = Sort::array(public_domain.clone(), public_range);
            let engine_array_sort = finite_set_engine_public_sort(ctx, &public_array_sort);
            let t = ctx.solver.as_array(&name, engine_array_sort);
            let r = term_to_ast(ctx, t);
            if sort_mentions_finite_set(ctx, &public_array_sort) {
                activate_finite_set_sat_gate(ctx, t, "Z3_mk_as_array");
            }
            record_ast_sort(ctx, r, public_array_sort);
            r
        })
    }
}

/// `(lambda ((x0 S0) ..) body)` over de Bruijn decls — curried into nested
/// single-variable lambda arrays `lambda(x0, lambda(x1, .. body))` with nested
/// `Array` sorts. Mirrors the de Bruijn quantifier path (`Z3_mk_forall`):
/// declares one bound constant per `(sort, name)` and builds the lambda over
/// them. Delegates to `Solver::lambda_array`.
///
/// # Safety
/// `c` must be a valid context pointer; `sorts`/`decl_names`, when non-null,
/// must point to `num_decls` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_lambda(
    c: Z3_context,
    num_decls: c_uint,
    sorts: *const Z3_sort,
    decl_names: *const Z3_symbol,
    body: Z3_ast,
) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe {
        ffi_counts_within_limit(
            c,
            "Z3_mk_lambda sort and name arrays",
            &[num_decls, num_decls],
        )
    } {
        return 0;
    }
    if num_decls == 0 || sorts.is_null() || decl_names.is_null() || body == 0 {
        // SAFETY: `c` is the caller's context pointer; guard null-checks it.
        return unsafe {
            ffi_guard_ast(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_lambda requires >=1 bound variable".to_string());
                0
            })
        };
    }
    // Pre-extract (sort, name) data from raw pointers before the guard.
    let mut decl_data: Vec<(Sort, String)> = Vec::with_capacity(num_decls as usize);
    for i in 0..num_decls as usize {
        // SAFETY: caller's contract guarantees `sorts`/`decl_names` point to
        // `num_decls` elements; count range-checked and null-checked above.
        let sort_ptr = unsafe { *sorts.add(i) };
        let sym_ptr = unsafe { *decl_names.add(i) };
        if sort_ptr.is_null() || sym_ptr.is_null() {
            // SAFETY: `c` is the caller's context pointer; guard null-checks it.
            return unsafe {
                ffi_guard_ast(c, |ctx| {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some("null sort or name in Z3_mk_lambda".to_string());
                    0
                })
            };
        }
        // SAFETY: pointers null-checked above; valid AY handles kept alive by the
        // owning context (single-threaded per context).
        let sort = unsafe { (*sort_ptr).sort.clone() };
        let name = unsafe { (*sym_ptr).semantic_name() };
        decl_data.push((sort, name));
    }
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let body_term = require_term_ast_or_return!(ctx, body, "Z3_mk_lambda", "body", 0);
            let body_public_sort = public_ast_sort(ctx, body, body_term);
            let has_finite_set_binder = decl_data
                .iter()
                .any(|(sort, _)| sort_mentions_finite_set(ctx, sort));
            let vars: Vec<Term> = decl_data
                .iter()
                .map(|(sort, name)| {
                    let engine_sort = finite_set_engine_public_sort(ctx, sort);
                    let v = ctx.solver.declare_const(name, engine_sort);
                    let ast = term_to_ast(ctx, v);
                    record_ast_sort(ctx, ast, sort.clone());
                    v
                })
                .collect();
            // Resolve the body's de Bruijn `__db{k}` occurrences into the
            // named bound vars (index 0 = last decl) and re-anchor surviving
            // indices to the enclosing scope — otherwise `__db{k}` leaks into
            // the lambda as a free variable and `select` beta-reduction
            // produces an OPEN term (a wrong value).
            let mut acc = ctx.solver.bind_de_bruijn(&vars, body_term);
            // Curry: lambda(x0, lambda(x1, .. lambda(x_{n-1}, body))).
            for &var in vars.iter().rev() {
                acc = ctx.solver.lambda_array(var, acc);
            }
            let mut public_sort = body_public_sort;
            for (sort, _) in decl_data.iter().rev() {
                public_sort = Sort::array(sort.clone(), public_sort);
            }
            let expected_engine_sort = finite_set_engine_public_sort(ctx, &public_sort);
            if ctx.solver.term_sort(acc) != expected_engine_sort {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(
                    "Z3_mk_lambda: engine result sort does not match its public signature"
                        .to_string(),
                );
                return 0;
            }
            let r = term_to_ast(ctx, acc);
            if has_finite_set_binder {
                activate_finite_set_quantifier_gate(ctx, acc, "Z3_mk_lambda");
            }
            record_ast_sort(ctx, r, public_sort);
            r
        })
    }
}

/// `(lambda ((x0 ..) ..) body)` where the bound variables are given as
/// app-constants `bound[i]` (`Z3_app == Z3_ast`). Curried into nested lambda
/// arrays `lambda(bound[0], lambda(bound[1], .. body))`. Mirrors
/// `Z3_mk_forall_const` bound-const handling. Delegates to
/// `Solver::lambda_array`.
///
/// # Safety
/// `c` must be a valid context pointer; `bound`, when non-null, must point to
/// `num_bound` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_lambda_const(
    c: Z3_context,
    num_bound: c_uint,
    bound: *const Z3_ast,
    body: Z3_ast,
) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_lambda_const bounds", num_bound) } {
        return 0;
    }
    if num_bound == 0 || bound.is_null() || body == 0 {
        // SAFETY: `c` is the caller's context pointer; guard null-checks it.
        return unsafe {
            ffi_guard_ast(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_lambda_const requires >=1 bound variable".to_string());
                0
            })
        };
    }
    let bound_asts: Vec<Z3_ast> = (0..num_bound as usize)
        // SAFETY: caller's contract guarantees `bound` points to `num_bound`
        // elements; count range-checked and null-checked above.
        .map(|i| unsafe { *bound.add(i) })
        .collect();
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let vars =
                require_term_asts_or_return!(ctx, &bound_asts, "Z3_mk_lambda_const bounds", 0);
            let public_bound_sorts: Vec<Sort> = bound_asts
                .iter()
                .zip(&vars)
                .map(|(&ast, &term)| public_ast_sort(ctx, ast, term))
                .collect();
            let has_finite_set_binder = public_bound_sorts
                .iter()
                .any(|sort| sort_mentions_finite_set(ctx, sort));
            let body_term = require_term_ast_or_return!(ctx, body, "Z3_mk_lambda_const", "body", 0);
            let body_public_sort = public_ast_sort(ctx, body, body_term);
            let mut acc = body_term;
            for &var in vars.iter().rev() {
                acc = ctx.solver.lambda_array(var, acc);
            }
            let mut public_sort = body_public_sort;
            for sort in public_bound_sorts.iter().rev() {
                public_sort = Sort::array(sort.clone(), public_sort);
            }
            let expected_engine_sort = finite_set_engine_public_sort(ctx, &public_sort);
            if ctx.solver.term_sort(acc) != expected_engine_sort {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(
                    "Z3_mk_lambda_const: engine result sort does not match its public signature"
                        .to_string(),
                );
                return 0;
            }
            let r = term_to_ast(ctx, acc);
            if has_finite_set_binder {
                activate_finite_set_quantifier_gate(ctx, acc, "Z3_mk_lambda_const");
            }
            record_ast_sort(ctx, r, public_sort);
            r
        })
    }
}

/// `((_ map f) a0 .. a{n-1})` — pointwise application of `f` over the `n`
/// arrays `args`; result sort `(Array index range_of_f)`. Delegates to
/// `Solver::array_map`.
///
/// # Safety
/// `c` must be a valid context pointer; `f`, when non-null, a valid func_decl;
/// `args`, when non-null, must point to `n` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_map(
    c: Z3_context,
    f: Z3_func_decl,
    n: c_uint,
    args: *const Z3_ast,
) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_map arrays", n) } {
        return 0;
    }
    if f.is_null() || n == 0 || args.is_null() {
        return 0;
    }
    // SAFETY: `f` null-checked above; a valid AY func_decl handle kept alive by the
    // owning context (single-threaded per context).
    let decl = unsafe { (*f).decl.clone() };
    let arg_asts: Vec<Z3_ast> = (0..n as usize)
        // SAFETY: caller's contract guarantees `args` points to `n` elements;
        // count range-checked and null-checked above.
        .map(|i| unsafe { *args.add(i) })
        .collect();
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let arg_terms = require_term_asts_or_return!(ctx, &arg_asts, "Z3_mk_map arrays", 0);
            // Full sort gate (z3's checked builder; AY's map term captures `f`
            // by NAME only, so an ill-sorted map could silently conflate
            // functions — refuse up front instead).
            if decl.arity() != n as usize {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(format!(
                    "Z3_mk_map: function {} has arity {}, got {} array(s)",
                    decl.name(),
                    decl.arity(),
                    n
                ));
                return 0;
            }
            let (public_domain, public_range) = ctx
                .finite_set_decl_signatures
                .get(decl.name())
                .cloned()
                .unwrap_or_else(|| (decl.domain().to_vec(), decl.range().clone()));
            let mut idx_sort: Option<Sort> = None;
            for (i, (&a, &term)) in arg_asts.iter().zip(&arg_terms).enumerate() {
                let sort = public_ast_sort(ctx, a, term);
                let Sort::Array(arr) = &sort else {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some("Z3_mk_map: argument is not an array".to_string());
                    return 0;
                };
                // All arg arrays share ONE index sort.
                match &idx_sort {
                    None => idx_sort = Some(arr.index_sort.clone()),
                    Some(prev) if *prev != arr.index_sort => {
                        ctx.last_error = Z3_SORT_ERROR;
                        ctx.error_msg = Some(format!(
                            "Z3_mk_map: array index sorts differ ({prev} vs {})",
                            arr.index_sort
                        ));
                        return 0;
                    }
                    Some(_) => {}
                }
                // Element sort must match the function's i-th domain sort.
                if arr.element_sort != public_domain[i] {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!(
                        "Z3_mk_map: array {} has element sort {} but {} expects {}",
                        i,
                        arr.element_sort,
                        decl.name(),
                        public_domain[i]
                    ));
                    return 0;
                }
            }
            let Some(idx_sort) = idx_sort else {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some("Z3_mk_map: no array arguments".to_string());
                return 0;
            };
            // SOUNDNESS (name-capture guard): the map term is
            // `App("map[<name>]", ..)` and the eager select rewrite emits `f`
            // by NAME — two different-signature decls both named `f` would
            // alias onto one symbol and conflate two functions (a
            // wrong-verdict channel). Refuse a second map under the same name
            // at a different signature; fail-close, honest error.
            match ctx.map_fn_sigs.get(decl.name()) {
                Some(prev) if *prev != decl => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!(
                        "Z3_mk_map: a function named {} with a different signature was \
                         already mapped in this context; AY's map term captures the \
                         function by name and cannot distinguish them",
                        decl.name()
                    ));
                    return 0;
                }
                Some(_) => {}
                None => {
                    ctx.map_fn_sigs
                        .insert(decl.name().to_string(), decl.clone());
                }
            }
            let result_sort = Sort::array(idx_sort, public_range);
            let engine_result_sort = finite_set_engine_public_sort(ctx, &result_sort);
            let t = ctx
                .solver
                .array_map(decl.name(), &arg_terms, engine_result_sort);
            let r = term_to_ast(ctx, t);
            if sort_mentions_finite_set(ctx, &result_sort) {
                activate_finite_set_sat_gate(ctx, t, "Z3_mk_map result");
            }
            record_ast_sort(ctx, r, result_sort);
            r
        })
    }
}

/// Read the set (array) sort of `set_ast`, falling back to the solver's own
/// term sort when the side table has no record.
fn set_sort_of(ctx: &Z3Context, set_ast: Z3_ast, set_term: Term) -> Sort {
    match lookup_ast_sort(ctx, set_ast).cloned() {
        Some(s) => s,
        None => ctx.solver.term_sort(set_term),
    }
}

/// Set union `((_ map or) args..)` over `(Array elem Bool)`. `num_args == 1`
/// returns the single arg. `num_args == 0` cannot form a well-sorted set (the
/// element sort is unknowable) and sets `Z3_INVALID_ARG`. Delegates to
/// `Solver::array_map`.
///
/// # Safety
/// `c` must be a valid context pointer; `args`, when non-null, must point to
/// `num_args` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_set_union(
    c: Z3_context,
    num_args: c_uint,
    args: *const Z3_ast,
) -> Z3_ast {
    // SAFETY: caller's contract guarantees validity; `mk_set_nary` documents its
    // own invariants and null-checks internally.
    unsafe { mk_set_nary(c, "or", num_args, args) }
}

/// Set intersection `((_ map and) args..)` over `(Array elem Bool)`.
/// `num_args == 1` returns the single arg. `num_args == 0` sets
/// `Z3_INVALID_ARG` (element sort unknowable). Delegates to
/// `Solver::array_map`.
///
/// # Safety
/// `c` must be a valid context pointer; `args`, when non-null, must point to
/// `num_args` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_set_intersect(
    c: Z3_context,
    num_args: c_uint,
    args: *const Z3_ast,
) -> Z3_ast {
    // SAFETY: see `Z3_mk_set_union`.
    unsafe { mk_set_nary(c, "and", num_args, args) }
}

/// Shared n-ary set combinator: `((_ map <combinator>) args..)`.
///
/// # Safety
/// `c` must be a valid context pointer; `args`, when non-null, must point to
/// `num_args` elements.
unsafe fn mk_set_nary(
    c: Z3_context,
    combinator: &'static str,
    num_args: c_uint,
    args: *const Z3_ast,
) -> Z3_ast {
    // SAFETY: every caller of this unsafe helper forwards a null or live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "set combinator arguments", num_args) } {
        return 0;
    }
    if num_args == 0 || args.is_null() {
        // SAFETY: `c` is the caller's context pointer; guard null-checks it.
        return unsafe {
            ffi_guard_ast(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("empty set union/intersect has no inferable element sort".to_string());
                0
            })
        };
    }
    // SAFETY: `args` null-checked and `num_args >= 1`, so `*args` is in bounds.
    let first = unsafe { *args };
    let arg_asts: Vec<Z3_ast> = (0..num_args as usize)
        // SAFETY: caller's contract guarantees `args` points to `num_args` elements.
        .map(|i| unsafe { *args.add(i) })
        .collect();
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let arg_terms =
                require_term_asts_or_return!(ctx, &arg_asts, "set combinator arguments", 0);
            let expected = set_sort_of(ctx, first, arg_terms[0]);
            let Sort::Array(expected_array) = &expected else {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(
                    "set combinator argument must have public legacy (Array T Bool) sort"
                        .to_string(),
                );
                return 0;
            };
            if expected_array.element_sort != Sort::Bool {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(
                    "set combinator argument must have public legacy (Array T Bool) sort"
                        .to_string(),
                );
                return 0;
            }
            for (&ast, &term) in arg_asts.iter().zip(&arg_terms).skip(1) {
                if set_sort_of(ctx, ast, term) != expected {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some("set combinator public set sorts differ".to_string());
                    return 0;
                }
            }
            if num_args == 1 {
                return term_to_ast(ctx, arg_terms[0]);
            }
            let t = ctx.solver.array_map(
                combinator,
                &arg_terms,
                finite_set_engine_public_sort(ctx, &expected),
            );
            let r = term_to_ast(ctx, t);
            record_ast_sort(ctx, r, expected);
            r
        })
    }
}

/// Set difference `arg1 \ arg2` = `((_ map and) arg1 ((_ map not) arg2))` over
/// `(Array elem Bool)`; result is `arg1`'s set sort. Delegates to
/// `Solver::array_map`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_set_difference(c: Z3_context, arg1: Z3_ast, arg2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let arg1_term =
                require_term_ast_or_return!(ctx, arg1, "Z3_mk_set_difference", "left set", 0);
            let arg2_term =
                require_term_ast_or_return!(ctx, arg2, "Z3_mk_set_difference", "right set", 0);
            let set_sort = set_sort_of(ctx, arg1, arg1_term);
            let Sort::Array(array) = &set_sort else {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(
                    "Z3_mk_set_difference: expected public legacy (Array T Bool) sort".to_string(),
                );
                return 0;
            };
            if array.element_sort != Sort::Bool || set_sort_of(ctx, arg2, arg2_term) != set_sort {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg =
                    Some("Z3_mk_set_difference: public legacy set sorts differ".to_string());
                return 0;
            }
            let engine_sort = finite_set_engine_public_sort(ctx, &set_sort);
            let not_arg2 = ctx
                .solver
                .array_map("not", &[arg2_term], engine_sort.clone());
            let t = ctx
                .solver
                .array_map("and", &[arg1_term, not_arg2], engine_sort);
            let r = term_to_ast(ctx, t);
            record_ast_sort(ctx, r, set_sort);
            r
        })
    }
}

/// Set complement `((_ map not) arg)` over `(Array elem Bool)`; result is
/// `arg`'s set sort. Delegates to `Solver::array_map`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_set_complement(c: Z3_context, arg: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let arg_term = require_term_ast_or_return!(ctx, arg, "Z3_mk_set_complement", "set", 0);
            let set_sort = set_sort_of(ctx, arg, arg_term);
            let Sort::Array(array) = &set_sort else {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(
                    "Z3_mk_set_complement: expected public legacy (Array T Bool) sort".to_string(),
                );
                return 0;
            };
            if array.element_sort != Sort::Bool {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(
                    "Z3_mk_set_complement: expected public legacy (Array T Bool) sort".to_string(),
                );
                return 0;
            }
            let engine_sort = finite_set_engine_public_sort(ctx, &set_sort);
            let t = ctx.solver.array_map("not", &[arg_term], engine_sort);
            let r = term_to_ast(ctx, t);
            record_ast_sort(ctx, r, set_sort);
            r
        })
    }
}

// ============================================================================
// Recognized-builtin named applications (sequences / strings)
// ============================================================================

/// Lexicographic string `<=`: `(str.<= prefix s)` → Bool. Delegates to
/// `Solver::str_le`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_str_le(c: Z3_context, prefix: Z3_ast, s: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let prefix = require_term_ast_or_return!(ctx, prefix, "Z3_mk_str_le", "prefix", 0);
            let s = require_term_ast_or_return!(ctx, s, "Z3_mk_str_le", "string", 0);
            let t = ctx.solver.str_le(prefix, s);
            let r = term_to_ast(ctx, t);
            record_ast_sort(ctx, r, Sort::Bool);
            r
        })
    }
}

/// Lexicographic string `<`: `(str.< prefix s)` → Bool. Delegates to
/// `Solver::str_lt`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_str_lt(c: Z3_context, prefix: Z3_ast, s: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let prefix = require_term_ast_or_return!(ctx, prefix, "Z3_mk_str_lt", "prefix", 0);
            let s = require_term_ast_or_return!(ctx, s, "Z3_mk_str_lt", "string", 0);
            let t = ctx.solver.str_lt(prefix, s);
            let r = term_to_ast(ctx, t);
            record_ast_sort(ctx, r, Sort::Bool);
            r
        })
    }
}

/// Int codepoint → single-char string: `(str.from_code a)` → String. Delegates
/// to `Solver::string_from_code`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_string_from_code(c: Z3_context, a: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let a = require_term_ast_or_return!(ctx, a, "Z3_mk_string_from_code", "code", 0);
            let t = ctx.solver.string_from_code(a);
            let r = term_to_ast(ctx, t);
            record_ast_sort(ctx, r, Sort::String);
            r
        })
    }
}

/// Single-char string → Int codepoint (`-1` if not length 1):
/// `(str.to_code a)` → Int. Delegates to `Solver::string_to_code`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_string_to_code(c: Z3_context, a: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let a = require_term_ast_or_return!(ctx, a, "Z3_mk_string_to_code", "string", 0);
            let t = ctx.solver.string_to_code(a);
            let r = term_to_ast(ctx, t);
            record_ast_sort(ctx, r, Sort::Int);
            r
        })
    }
}

/// Last index of `substr` in `s`: `(seq.last_indexof s substr)` → Int.
/// Delegates to `Solver::seq_last_index`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_last_index(c: Z3_context, s: Z3_ast, substr: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let s = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_last_index", "sequence", 0);
            let substr =
                require_term_ast_or_return!(ctx, substr, "Z3_mk_seq_last_index", "substring", 0);
            let t = ctx.solver.seq_last_index(s, substr);
            let r = term_to_ast(ctx, t);
            record_ast_sort(ctx, r, Sort::Int);
            r
        })
    }
}

/// Replace the first regex match of `re` in `s` with `dst`:
/// `(str.replace_re s re dst)` → String. Delegates to
/// `Solver::seq_replace_re`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_replace_re(
    c: Z3_context,
    s: Z3_ast,
    re: Z3_ast,
    dst: Z3_ast,
) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let s = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_replace_re", "string", 0);
            let re = require_term_ast_or_return!(ctx, re, "Z3_mk_seq_replace_re", "regex", 0);
            let dst =
                require_term_ast_or_return!(ctx, dst, "Z3_mk_seq_replace_re", "replacement", 0);
            let t = ctx.solver.seq_replace_re(s, re, dst);
            let r = term_to_ast(ctx, t);
            record_ast_sort(ctx, r, Sort::String);
            r
        })
    }
}

/// Replace ALL regex matches of `re` in `s` with `dst`:
/// `(str.replace_re_all s re dst)` → String. Delegates to
/// `Solver::seq_replace_re_all`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_replace_re_all(
    c: Z3_context,
    s: Z3_ast,
    re: Z3_ast,
    dst: Z3_ast,
) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let s = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_replace_re_all", "string", 0);
            let re = require_term_ast_or_return!(ctx, re, "Z3_mk_seq_replace_re_all", "regex", 0);
            let dst =
                require_term_ast_or_return!(ctx, dst, "Z3_mk_seq_replace_re_all", "replacement", 0);
            let t = ctx.solver.seq_replace_re_all(s, re, dst);
            let r = term_to_ast(ctx, t);
            record_ast_sort(ctx, r, Sort::String);
            r
        })
    }
}

// ============================================================================
// Empty model
// ============================================================================

/// Create an empty, caller-owned model (to be populated with
/// `Z3_add_const_interp` / `Z3_add_func_interp`). Wraps [`Model::empty`] in an
/// arena-owned [`ModelHandle`].
///
/// # Safety
/// `c` must be a valid context pointer (or null, which yields null).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_model(c: Z3_context) -> Z3_model {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ptr` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let handle = Box::into_raw(Box::new(ModelHandle {
                model: Model::empty(),
                func_interps: Vec::new(),
                user_const_interps: Vec::new(),
                user_func_interps: Vec::new(),
                rec_def_count: ctx.rec_fun_defs.len(),
                _ctx: c,
            }));
            ctx.model_cache.push(handle);
            handle
        })
    }
}

// ============================================================================
// Light quantifier elimination
// ============================================================================

/// Best-effort light quantifier elimination of `vars` from `body`.
///
/// Eliminates each listed variable that falls in the sound `qe-light` (Cooper)
/// fragment via `Solver::qe_lite`; a variable outside the fragment simply
/// REMAINS (the identity fallback is always logically valid — `qe_lite` is
/// best-effort by contract). A null `vars` vector is treated as empty, so the
/// body is returned unchanged.
///
/// # Safety
/// `c` must be a valid context pointer; `vars`, when non-null, a valid AST
/// vector handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_qe_lite(c: Z3_context, vars: Z3_ast_vector, body: Z3_ast) -> Z3_ast {
    if body == 0 {
        return 0;
    }
    // SAFETY: `vars`, when non-null, is a live `AstVectorHandle`; `as_ref` null-checks.
    let var_asts = unsafe { vars.as_ref() }
        .map(|h| h.asts.clone())
        .unwrap_or_default();
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let var_terms = require_term_asts_or_return!(ctx, &var_asts, "Z3_qe_lite variables", 0);
            let body = require_term_ast_or_return!(ctx, body, "Z3_qe_lite", "body", 0);
            let result = ctx.solver.qe_lite(body, &var_terms);
            let r = term_to_ast(ctx, result);
            let sort = ctx.solver.term_sort(result);
            record_ast_sort(ctx, r, sort);
            r
        })
    }
}

#[cfg(test)]
#[path = "engine_ext_tests.rs"]
mod engine_ext_tests;
