// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible term construction: function decls and boolean operations.
//! Numeral constructors are in `numerals.rs`.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_char, c_int, c_uint, CStr};
use std::ptr;

use ay_dpll::api::{Sort, Term};
use num_bigint::BigInt;

use super::{
    ast_to_term, cache_func_decl_with_symbol, ffi_function_semantic_name, ffi_guard_ast,
    ffi_guard_ptr, lookup_ast_sort, record_ast_sort, term_to_ast, DatatypeOp, SymbolKey, Z3_ast,
    Z3_context, Z3_func_decl, Z3_params, Z3_sort, Z3_symbol, Z3_INVALID_ARG, Z3_SORT_ERROR,
};

// ---- Function declarations and constants ----

/// Declare an uninterpreted function.
///
/// # Safety
/// All pointers must be valid. `domain` must point to `domain_size` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_func_decl(
    c: Z3_context,
    s: Z3_symbol,
    domain_size: c_uint,
    domain: *const Z3_sort,
    range: Z3_sort,
) -> Z3_func_decl {
    if s.is_null() || range.is_null() {
        return ptr::null_mut();
    }
    if domain_size > 0 && domain.is_null() {
        return ptr::null_mut();
    }

    // Pre-extract data from raw pointers before entering the guard
    // SAFETY: `s` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.key` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let symbol = unsafe { (*s).key.clone() };
    let display_name = symbol.display_name();
    let mut dom_sorts = Vec::with_capacity(domain_size as usize);
    for i in 0..domain_size as usize {
        // SAFETY: The caller's `# Safety` contract guarantees `domain` points to at least the
        // declared number of elements. The count was range-checked above, and null-checked
        // before entering this block, so `domain.add(i)` stays within the caller's allocation.
        let sort_ptr = unsafe { *domain.add(i) };
        if sort_ptr.is_null() {
            return ptr::null_mut();
        }
        // SAFETY: `sort_ptr` was null-checked above and originates from a prior AY FFI
        // allocation whose handle is kept alive by the owning `Z3Context` (see handle caches
        // in `mod.rs`). Reading `.sort` is a shared-read with no concurrent mutation because
        // the Z3 C API is single-threaded per context.
        dom_sorts.push(unsafe { (*sort_ptr).sort.clone() });
    }
    // SAFETY: `range` was null-checked above and originates from a prior AY FFI allocation
    // whose handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`).
    // Reading `.sort` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let range_sort = unsafe { (*range).sort.clone() };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            // Fail-close reserved-namespace capture (`map[...]` / `!ay.*`):
            // an ordinary decl with such a name silently acquires internal
            // array-map semantics in the core rewriter — a measured
            // wrong-verdict channel. See `reserved_name_error`.
            if matches!(&symbol, SymbolKey::String(_)) {
                if let Some(msg) = super::reserved_name_error(&display_name) {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(msg);
                    return ptr::null_mut();
                }
            }
            ctx.ffi_used_decl_names.insert(display_name.clone());
            let semantic_name = ffi_function_semantic_name(ctx, &symbol, &dom_sorts, &range_sort);
            match ctx
                .solver
                .try_declare_fun(&semantic_name, &dom_sorts, range_sort)
            {
                Ok(decl) => cache_func_decl_with_symbol(ctx, decl, symbol.clone()),
                Err(e) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!("{e}"));
                    ptr::null_mut()
                }
            }
        })
    }
}

/// Create a constant (0-arity function application).
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_const(c: Z3_context, s: Z3_symbol, ty: Z3_sort) -> Z3_ast {
    if s.is_null() || ty.is_null() {
        return 0;
    }
    // SAFETY: `s` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.key` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let symbol = unsafe { (*s).key.clone() };
    let display_name = symbol.display_name();
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
            // Fail-close reserved-namespace capture — see `reserved_name_error`
            // (a `!ay.*` constant can alias an internal engine witness).
            if matches!(&symbol, SymbolKey::String(_)) {
                if let Some(msg) = super::reserved_name_error(&display_name) {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(msg);
                    return 0;
                }
            }
            let cache_key = (symbol.clone(), sort.clone());
            if let Some(term) = ctx.ffi_const_cache.get(&cache_key).copied() {
                let ast = term_to_ast(term);
                record_ast_sort(ctx, ast, sort.clone());
                return ast;
            }
            let identity = format!("!ay.z3-const!{}", ctx.next_ffi_fresh_id);
            ctx.next_ffi_fresh_id += 1;
            let term = ctx.solver.declare_const_with_fresh_identity(
                &display_name,
                &identity,
                sort.clone(),
            );
            ctx.ffi_const_cache.insert(cache_key, term);
            ctx.ffi_const_metadata
                .insert(term, (identity.clone(), symbol.clone()));
            ctx.ffi_const_terms_by_identity.insert(identity, term);
            ctx.ffi_used_decl_names.insert(display_name.clone());
            let ast = term_to_ast(term);
            record_ast_sort(ctx, ast, sort);
            ast
        })
    }
}

/// Create a fresh constant with a unique name.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fresh_const(
    c: Z3_context,
    prefix: *const c_char,
    ty: Z3_sort,
) -> Z3_ast {
    if ty.is_null() {
        return 0;
    }
    let pfx = if prefix.is_null() {
        "fresh".to_string()
    } else {
        // SAFETY: The caller's `# Safety` contract requires the C string pointer to be
        // non-null and to point to a valid, null-terminated sequence of bytes owned by the
        // caller for the duration of this call. The pointer was null-checked before entering
        // this block.
        unsafe { CStr::from_ptr(prefix) }
            .to_str()
            .unwrap_or("fresh")
            .to_string()
    };
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
            // Fail-close reserved-namespace capture — a `!ay.`-prefixed fresh
            // prefix could collide with an internal engine witness name.
            if let Some(msg) = super::reserved_name_error(&pfx) {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(msg);
                return 0;
            }
            let (fresh_id, fresh_name) = loop {
                let fresh_id = ctx.next_ffi_fresh_id;
                ctx.next_ffi_fresh_id += 1;
                let candidate = format!("{pfx}!{fresh_id}");
                if ctx.ffi_used_decl_names.insert(candidate.clone()) {
                    break (fresh_id, candidate);
                }
            };
            let identity = format!("!ay.z3-fresh-const!{fresh_id}");
            let term =
                ctx.solver
                    .declare_const_with_fresh_identity(&fresh_name, &identity, sort.clone());
            let symbol = SymbolKey::String(fresh_name.clone());
            ctx.ffi_const_metadata
                .insert(term, (identity.clone(), symbol));
            ctx.ffi_const_terms_by_identity.insert(identity, term);
            let ast = term_to_ast(term);
            record_ast_sort(ctx, ast, sort);
            ast
        })
    }
}

/// Apply a function declaration to arguments.
///
/// # Safety
/// All pointers must be valid. `args` must point to `num_args` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_app(
    c: Z3_context,
    d: Z3_func_decl,
    num_args: c_uint,
    args: *const Z3_ast,
) -> Z3_ast {
    if d.is_null() {
        return 0;
    }
    if num_args > 0 && args.is_null() {
        return 0;
    }

    // Pre-extract data from raw pointers
    // SAFETY: `d` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.decl`/`.dt_op` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let decl = unsafe { (*d).decl.clone() };
    let dt_op = unsafe { (*d).dt_op.clone() };
    let term_args: Vec<_> = (0..num_args as usize)
        // SAFETY: The caller's `# Safety` contract guarantees `args` points to at least the
        // declared number of elements. The count was range-checked above, and null-checked
        // before entering this block, so `args.add(i)` stays within the caller's allocation.
        .map(|i| ast_to_term(unsafe { *args.add(i) }))
        .collect();

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            // Datatype constructor/recognizer/accessor applications route through
            // AY's verified datatype builders so the resulting term matches the
            // SMT-LIB elaborator exactly (e.g. nullary constructors resolve to the
            // registered constant, not a generic 0-arg UF application) (#phase3-dt).
            let result = match dt_op {
                Some(DatatypeOp::Constructor { dt, ctor }) => {
                    match ctx.solver.try_datatype_constructor(&dt, &ctor, &term_args) {
                        Ok(t) => t,
                        Err(e) => {
                            ctx.last_error = Z3_SORT_ERROR;
                            ctx.error_msg = Some(format!("{e}"));
                            return 0;
                        }
                    }
                }
                Some(DatatypeOp::Recognizer { ctor }) => {
                    let Some(arg) = term_args.first().copied() else {
                        ctx.last_error = Z3_SORT_ERROR;
                        ctx.error_msg = Some("recognizer expects 1 argument".to_string());
                        return 0;
                    };
                    match ctx.solver.try_datatype_tester(&ctor, arg) {
                        Ok(t) => t,
                        Err(e) => {
                            ctx.last_error = Z3_SORT_ERROR;
                            ctx.error_msg = Some(format!("{e}"));
                            return 0;
                        }
                    }
                }
                Some(DatatypeOp::Accessor { field, result_sort }) => {
                    let Some(arg) = term_args.first().copied() else {
                        ctx.last_error = Z3_SORT_ERROR;
                        ctx.error_msg = Some("accessor expects 1 argument".to_string());
                        return 0;
                    };
                    match ctx.solver.try_datatype_selector(&field, arg, result_sort) {
                        Ok(t) => t,
                        Err(e) => {
                            ctx.last_error = Z3_SORT_ERROR;
                            ctx.error_msg = Some(format!("{e}"));
                            return 0;
                        }
                    }
                }
                None => {
                    // Apply-time polymorphic instantiation (#poly-inst): a decl
                    // whose signature mentions a type variable is unified against
                    // the actual argument sorts and applied as its monomorphic
                    // instance (libz3 parity: `f : α → α` at an Int argument
                    // yields an Int-sorted application). Mismatched unification
                    // stays an honest sort error.
                    if decl_mentions_type_var(&decl) {
                        match instantiate_poly_decl(ctx, &decl, &term_args) {
                            Ok(inst) => {
                                let range = inst.range().clone();
                                match ctx.solver.try_apply(&inst, &term_args) {
                                    Ok(t) => {
                                        let ast = term_to_ast(t);
                                        record_ast_sort(ctx, ast, range);
                                        return ast;
                                    }
                                    Err(e) => {
                                        ctx.last_error = Z3_SORT_ERROR;
                                        ctx.error_msg = Some(format!("{e}"));
                                        return 0;
                                    }
                                }
                            }
                            Err(msg) => {
                                ctx.last_error = Z3_SORT_ERROR;
                                ctx.error_msg = Some(msg);
                                return 0;
                            }
                        }
                    }
                    ctx.solver.apply(&decl, &term_args)
                }
            };
            let ast = term_to_ast(result);
            record_ast_sort(ctx, ast, decl.range().clone());
            ast
        })
    }
}

// ---- Polymorphic declaration instantiation (#poly-inst) ----

/// Does `sort` mention a [`Sort::TypeVar`] anywhere (through the parametric
/// Array/Seq constructors)?
fn sort_mentions_type_var(sort: &Sort) -> bool {
    match sort {
        Sort::TypeVar(_) => true,
        Sort::Array(arr) => {
            sort_mentions_type_var(&arr.index_sort) || sort_mentions_type_var(&arr.element_sort)
        }
        Sort::Seq(elem) => sort_mentions_type_var(elem),
        _ => false,
    }
}

/// Does the decl's signature (domain or range) mention a type variable?
fn decl_mentions_type_var(decl: &ay_dpll::api::FuncDecl) -> bool {
    decl.domain().iter().any(sort_mentions_type_var) || sort_mentions_type_var(decl.range())
}

/// Unify a signature `pattern` sort against a concrete `actual` sort,
/// extending `bindings` (type-var name → concrete sort). A variable already
/// bound must re-unify to the SAME sort (`f : (α, α) → α` at `(Int, Bool)` is
/// a sort error, exactly as before this feature existed).
fn unify_sorts(
    pattern: &Sort,
    actual: &Sort,
    bindings: &mut std::collections::HashMap<String, Sort>,
) -> bool {
    match (pattern, actual) {
        (Sort::TypeVar(name), _) => match bindings.get(name) {
            Some(bound) => bound == actual,
            None => {
                bindings.insert(name.clone(), actual.clone());
                true
            }
        },
        (Sort::Array(p), Sort::Array(a)) => {
            unify_sorts(&p.index_sort, &a.index_sort, bindings)
                && unify_sorts(&p.element_sort, &a.element_sort, bindings)
        }
        (Sort::Seq(p), Sort::Seq(a)) => unify_sorts(p, a, bindings),
        (p, a) => p == a,
    }
}

/// Substitute `bindings` into `sort`. `None` iff an UNBOUND type variable
/// remains (e.g. a range-only variable no argument sort determines).
fn substitute_sort(
    sort: &Sort,
    bindings: &std::collections::HashMap<String, Sort>,
) -> Option<Sort> {
    match sort {
        Sort::TypeVar(name) => bindings.get(name).cloned(),
        Sort::Array(arr) => Some(Sort::array(
            substitute_sort(&arr.index_sort, bindings)?,
            substitute_sort(&arr.element_sort, bindings)?,
        )),
        Sort::Seq(elem) => Some(Sort::seq(substitute_sort(elem, bindings)?)),
        other => Some(other.clone()),
    }
}

/// Unify the polymorphic `decl`'s domain against the actual argument sorts and
/// return the cached monomorphic instance decl (same name, concrete
/// signature). `Err(message)` on arity mismatch, failed unification, or an
/// undetermined range variable — the caller reports `Z3_SORT_ERROR`.
fn instantiate_poly_decl(
    ctx: &mut super::Z3Context,
    decl: &ay_dpll::api::FuncDecl,
    args: &[Term],
) -> Result<ay_dpll::api::FuncDecl, String> {
    let name = decl.name();
    if args.len() != decl.domain().len() {
        return Err(format!(
            "Z3_mk_app: polymorphic function {name} expects {} args, got {}",
            decl.domain().len(),
            args.len()
        ));
    }
    let arg_sorts: Vec<Sort> = args.iter().map(|&t| ctx.solver.sort_of(t)).collect();
    let mut bindings = std::collections::HashMap::new();
    for (pattern, actual) in decl.domain().iter().zip(arg_sorts.iter()) {
        if !unify_sorts(pattern, actual, &mut bindings) {
            return Err(format!(
                "Z3_mk_app: cannot instantiate polymorphic {name}: domain {pattern} \
                 does not unify with argument sort {actual}"
            ));
        }
    }
    let key = (name.to_string(), arg_sorts.clone());
    if let Some(inst) = ctx.poly_decl_instances.get(&key) {
        return Ok(inst.clone());
    }
    let Some(range) = substitute_sort(decl.range(), &bindings) else {
        return Err(format!(
            "Z3_mk_app: cannot instantiate polymorphic {name}: range {} mentions a \
             type variable not determined by any argument",
            decl.range()
        ));
    };
    let inst = ay_dpll::api::FuncDecl::new(name.to_string(), arg_sorts, range);
    ctx.poly_decl_instances.insert(key, inst.clone());
    Ok(inst)
}

// ---- Boolean operations ----

/// Create the `true` constant.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_true(c: Z3_context) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.bool_const(true);
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create the `false` constant.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_false(c: Z3_context) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.bool_const(false);
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create an equality.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_eq(c: Z3_context, l: Z3_ast, r: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.eq(ast_to_term(l), ast_to_term(r));
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create a distinct constraint.
///
/// # Safety
/// All pointers must be valid. `args` must point to `num_args` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_distinct(
    c: Z3_context,
    num_args: c_uint,
    args: *const Z3_ast,
) -> Z3_ast {
    if num_args == 0 || args.is_null() {
        return 0;
    }
    let terms: Vec<_> = (0..num_args as usize)
        // SAFETY: The caller's `# Safety` contract guarantees `args` points to at least the
        // declared number of elements. The count was range-checked above, and null-checked
        // before entering this block, so `args.add(i)` stays within the caller's allocation.
        .map(|i| ast_to_term(unsafe { *args.add(i) }))
        .collect();

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.distinct(&terms);
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create boolean NOT.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_not(c: Z3_context, a: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.not(ast_to_term(a));
            let r = term_to_ast(t);
            record_ast_sort(ctx, r, Sort::Bool);
            r
        })
    }
}

/// Create if-then-else.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_ite(c: Z3_context, t1: Z3_ast, t2: Z3_ast, t3: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx
                .solver
                .ite(ast_to_term(t1), ast_to_term(t2), ast_to_term(t3));
            let r = term_to_ast(t);
            if let Some(sort) = lookup_ast_sort(ctx, t2).cloned() {
                record_ast_sort(ctx, r, sort);
            }
            r
        })
    }
}

/// Create boolean iff.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_iff(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.eq(ast_to_term(t1), ast_to_term(t2));
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create boolean implication.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_implies(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.implies(ast_to_term(t1), ast_to_term(t2));
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create boolean XOR.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_xor(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.xor(ast_to_term(t1), ast_to_term(t2));
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create boolean AND.
///
/// # Safety
/// All pointers must be valid. `args` must point to `num_args` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_and(c: Z3_context, num_args: c_uint, args: *const Z3_ast) -> Z3_ast {
    let terms: Vec<_> = if num_args == 0 || args.is_null() {
        Vec::new()
    } else {
        (0..num_args as usize)
            // SAFETY: The caller's `# Safety` contract guarantees `args` points to at least
            // the declared number of elements. The count was range-checked above, and
            // null-checked before entering this block, so `args.add(i)` stays within the
            // caller's allocation.
            .map(|i| ast_to_term(unsafe { *args.add(i) }))
            .collect()
    };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if terms.is_empty() {
                let t = ctx.solver.bool_const(true);
                return term_to_ast(t);
            }
            let t = ctx.solver.and_many(&terms);
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create boolean OR.
///
/// # Safety
/// All pointers must be valid. `args` must point to `num_args` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_or(c: Z3_context, num_args: c_uint, args: *const Z3_ast) -> Z3_ast {
    let terms: Vec<_> = if num_args == 0 || args.is_null() {
        Vec::new()
    } else {
        (0..num_args as usize)
            // SAFETY: The caller's `# Safety` contract guarantees `args` points to at least
            // the declared number of elements. The count was range-checked above, and
            // null-checked before entering this block, so `args.add(i)` stays within the
            // caller's allocation.
            .map(|i| ast_to_term(unsafe { *args.add(i) }))
            .collect()
    };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if terms.is_empty() {
                let t = ctx.solver.bool_const(false);
                return term_to_ast(t);
            }
            let t = ctx.solver.or_many(&terms);
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

// ---- Pseudo-boolean / cardinality constraints ----

/// Comparison operator for a pseudo-boolean / cardinality constraint.
#[derive(Clone, Copy)]
enum PbCmp {
    Le,
    Ge,
    Eq,
}

/// Build `(cmp (Σ coeff_i · [arg_i]) k)` — the exact integer-arithmetic
/// semantics of Z3's PB / cardinality operators — over the 0/1 indicators of the
/// Bool literals `terms`. Each summand is `(ite arg_i coeff_i 0)`, so the result
/// is decided by AY's audited LIA path (equisatisfiable, no new soundness
/// surface). Mirrors the frontend elaborator's `build_pb_constraint`.
///
/// # Safety
/// `c` must be a valid context pointer (or null; handled by the guard).
unsafe fn mk_pb_ast(
    c: Z3_context,
    terms: Vec<Term>,
    coeffs: Vec<BigInt>,
    k: BigInt,
    cmp: PbCmp,
) -> Z3_ast {
    debug_assert_eq!(terms.len(), coeffs.len());
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; `ffi_guard_ast`
    // handles the null case internally and catches any unwinding panic so it cannot
    // cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let zero = ctx.solver.int_const(0);
            let summands: Vec<Term> = terms
                .iter()
                .zip(&coeffs)
                .map(|(&t, coeff)| {
                    let coeff_term = ctx.solver.int_const_bigint(coeff);
                    ctx.solver.ite(t, coeff_term, zero)
                })
                .collect();
            let sum = if summands.is_empty() {
                ctx.solver.int_const(0)
            } else {
                ctx.solver.add_many(&summands)
            };
            let bound = ctx.solver.int_const_bigint(&k);
            let t = match cmp {
                PbCmp::Le => ctx.solver.le(sum, bound),
                PbCmp::Ge => ctx.solver.ge(sum, bound),
                PbCmp::Eq => ctx.solver.eq(sum, bound),
            };
            let a = term_to_ast(t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Read `num_args` `Z3_ast` handles into a `Vec<Term>`.
///
/// # Safety
/// `args` must point to at least `num_args` valid elements (or be null when
/// `num_args == 0`).
unsafe fn read_ast_args(num_args: c_uint, args: *const Z3_ast) -> Vec<Term> {
    if num_args == 0 || args.is_null() {
        return Vec::new();
    }
    (0..num_args as usize)
        // SAFETY: caller guarantees `args` points to at least `num_args` elements;
        // `add(i)` stays in bounds.
        .map(|i| ast_to_term(unsafe { *args.add(i) }))
        .collect()
}

/// Create a cardinality "at most k" constraint: at most `k` of `args` are true.
///
/// Real Z3 C signature:
/// `Z3_ast Z3_mk_atmost(Z3_context c, unsigned num_args, Z3_ast const args[], unsigned k)`.
///
/// # Safety
/// `c` must be a valid context pointer. `args` must point to `num_args` valid
/// Bool `Z3_ast` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_atmost(
    c: Z3_context,
    num_args: c_uint,
    args: *const Z3_ast,
    k: c_uint,
) -> Z3_ast {
    // SAFETY: caller contract on `args`/`num_args`; see `read_ast_args`.
    let terms = unsafe { read_ast_args(num_args, args) };
    let coeffs = vec![BigInt::from(1); terms.len()];
    // SAFETY: `c` validity is the caller's contract; forwarded to the guard.
    unsafe { mk_pb_ast(c, terms, coeffs, BigInt::from(k), PbCmp::Le) }
}

/// Create a cardinality "at least k" constraint: at least `k` of `args` are true.
///
/// Real Z3 C signature:
/// `Z3_ast Z3_mk_atleast(Z3_context c, unsigned num_args, Z3_ast const args[], unsigned k)`.
///
/// # Safety
/// `c` must be a valid context pointer. `args` must point to `num_args` valid
/// Bool `Z3_ast` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_atleast(
    c: Z3_context,
    num_args: c_uint,
    args: *const Z3_ast,
    k: c_uint,
) -> Z3_ast {
    // SAFETY: caller contract on `args`/`num_args`; see `read_ast_args`.
    let terms = unsafe { read_ast_args(num_args, args) };
    let coeffs = vec![BigInt::from(1); terms.len()];
    // SAFETY: `c` validity is the caller's contract; forwarded to the guard.
    unsafe { mk_pb_ast(c, terms, coeffs, BigInt::from(k), PbCmp::Ge) }
}

/// Read `num_args` signed coefficients into a `Vec<BigInt>`.
///
/// # Safety
/// `coeffs` must point to at least `num_args` valid `int` elements (or be null
/// when `num_args == 0`).
unsafe fn read_int_coeffs(num_args: c_uint, coeffs: *const c_int) -> Vec<BigInt> {
    if num_args == 0 || coeffs.is_null() {
        return Vec::new();
    }
    (0..num_args as usize)
        // SAFETY: caller guarantees `coeffs` points to at least `num_args`
        // elements; `add(i)` stays in bounds.
        .map(|i| BigInt::from(unsafe { *coeffs.add(i) }))
        .collect()
}

/// Create a pseudo-boolean `<= k` constraint: `Σ coeffs_i·args_i <= k`.
///
/// Real Z3 C signature:
/// `Z3_ast Z3_mk_pble(Z3_context c, unsigned num_args, Z3_ast const args[], int const coeffs[], int k)`.
///
/// # Safety
/// `c` must be a valid context pointer. `args` and `coeffs` must each point to
/// `num_args` valid elements (`args` Bool `Z3_ast`, `coeffs` `int`).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_pble(
    c: Z3_context,
    num_args: c_uint,
    args: *const Z3_ast,
    coeffs: *const c_int,
    k: c_int,
) -> Z3_ast {
    // SAFETY: caller contract on the two arrays; see the readers' contracts.
    let terms = unsafe { read_ast_args(num_args, args) };
    let cs = unsafe { read_int_coeffs(num_args, coeffs) };
    if terms.len() != cs.len() {
        return 0;
    }
    // SAFETY: `c` validity is the caller's contract; forwarded to the guard.
    unsafe { mk_pb_ast(c, terms, cs, BigInt::from(k), PbCmp::Le) }
}

/// Create a pseudo-boolean `>= k` constraint: `Σ coeffs_i·args_i >= k`.
///
/// Real Z3 C signature:
/// `Z3_ast Z3_mk_pbge(Z3_context c, unsigned num_args, Z3_ast const args[], int const coeffs[], int k)`.
///
/// # Safety
/// `c` must be a valid context pointer. `args` and `coeffs` must each point to
/// `num_args` valid elements (`args` Bool `Z3_ast`, `coeffs` `int`).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_pbge(
    c: Z3_context,
    num_args: c_uint,
    args: *const Z3_ast,
    coeffs: *const c_int,
    k: c_int,
) -> Z3_ast {
    // SAFETY: caller contract on the two arrays; see the readers' contracts.
    let terms = unsafe { read_ast_args(num_args, args) };
    let cs = unsafe { read_int_coeffs(num_args, coeffs) };
    if terms.len() != cs.len() {
        return 0;
    }
    // SAFETY: `c` validity is the caller's contract; forwarded to the guard.
    unsafe { mk_pb_ast(c, terms, cs, BigInt::from(k), PbCmp::Ge) }
}

/// Create a pseudo-boolean `= k` constraint: `Σ coeffs_i·args_i = k`.
///
/// Real Z3 C signature:
/// `Z3_ast Z3_mk_pbeq(Z3_context c, unsigned num_args, Z3_ast const args[], int const coeffs[], int k)`.
///
/// # Safety
/// `c` must be a valid context pointer. `args` and `coeffs` must each point to
/// `num_args` valid elements (`args` Bool `Z3_ast`, `coeffs` `int`).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_pbeq(
    c: Z3_context,
    num_args: c_uint,
    args: *const Z3_ast,
    coeffs: *const c_int,
    k: c_int,
) -> Z3_ast {
    // SAFETY: caller contract on the two arrays; see the readers' contracts.
    let terms = unsafe { read_ast_args(num_args, args) };
    let cs = unsafe { read_int_coeffs(num_args, coeffs) };
    if terms.len() != cs.len() {
        return 0;
    }
    // SAFETY: `c` validity is the caller's contract; forwarded to the guard.
    unsafe { mk_pb_ast(c, terms, cs, BigInt::from(k), PbCmp::Eq) }
}

// ---- Simplification ----

/// Simplify an AST, returning a logically equivalent simplified term.
///
/// Rebuilds `a` bottom-up through AY's simplifying constructors, re-applying
/// AY's eager constant-folding and identity simplification to every node. AY
/// already folds eagerly during term construction, so a term assembled entirely
/// through the `Z3_mk_*` API is a fixpoint of this rewrite (the result is the
/// same interned term). The value-add is for terms whose constant/identity
/// subexpressions were not folded at build time (e.g. parser-built terms, or
/// terms a consumer assembled through a path that bypassed the folding builders):
/// `(+ 2 3)` -> `5`, `(and true p)` -> `p`, `(+ x 0)` -> `x`,
/// `(ite true a b)` -> `a`, `(select (store a i v) i)` -> `v`, etc.
///
/// The result is **logically equivalent** to `a`: every step is a
/// semantics-preserving simplification, so `simplify(a)` denotes the same
/// value/relation as `a`.
///
/// # Safety
/// `c` must be a valid context pointer. `a` must be a valid `Z3_ast` produced
/// by this context (or null/0, which is returned unchanged).
#[no_mangle]
pub unsafe extern "C" fn Z3_simplify(c: Z3_context, a: Z3_ast) -> Z3_ast {
    if a == 0 {
        return a;
    }
    let target = ast_to_term(a);

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety`
    // on this extern "C" function requires it to be a valid, non-aliased pointer
    // (or null). `ffi_guard_ast` handles the null case internally and catches any
    // unwinding panic so it cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let result = ctx.solver.simplify(target);
            term_to_ast(result)
        })
    }
}

/// Simplify an AST with simplifier parameters; equivalent to [`Z3_simplify`].
///
/// AY's simplifier is parameter-free (it applies the same eager folding used at
/// term construction), so the `Z3_params` argument is accepted for API
/// compatibility and ignored. The result is logically equivalent to `a`, the
/// same as [`Z3_simplify`].
///
/// # Safety
/// `c` must be a valid context pointer. `a` must be a valid `Z3_ast` produced by
/// this context (or null/0, returned unchanged). `p` is ignored and may be null.
#[no_mangle]
pub unsafe extern "C" fn Z3_simplify_ex(c: Z3_context, a: Z3_ast, _p: Z3_params) -> Z3_ast {
    // SAFETY: forwards to Z3_simplify under the same caller contract on `c`/`a`.
    unsafe { Z3_simplify(c, a) }
}

// ---- Substitution ----

/// Substitute every occurrence of `from[i]` in `a` with `to[i]`, simultaneously.
///
/// Z3 semantics: simultaneous replacement of subterms matched by structural
/// (hash-consed) identity. The common consumer use (KLEE/SeaHorn/angr-style
/// symbolic execution) is replacing uninterpreted constants with concrete
/// terms. Each `from[i]` and `to[i]` must have the same sort; a mismatch sets
/// `Z3_SORT_ERROR` and returns `a` unchanged.
///
/// Guards: a null `from`/`to` array or `num_exprs == 0` returns `a` unchanged.
///
/// # Safety
/// `c` must be a valid context pointer. When `num_exprs > 0`, `from` and `to`
/// must each point to at least `num_exprs` valid `Z3_ast` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_substitute(
    c: Z3_context,
    a: Z3_ast,
    num_exprs: c_uint,
    from: *const Z3_ast,
    to: *const Z3_ast,
) -> Z3_ast {
    // No-op guards: nothing to do → return the input unchanged.
    if a == 0 || num_exprs == 0 || from.is_null() || to.is_null() {
        return a;
    }

    let n = num_exprs as usize;
    // Pre-extract the from/to arrays from raw pointers before entering the guard.
    // SAFETY: The caller's `# Safety` contract guarantees `from`/`to` each point
    // to at least `num_exprs` elements. Both were null-checked above, so
    // `from.add(i)`/`to.add(i)` stay within the caller's allocation.
    let from_terms: Vec<_> = (0..n)
        .map(|i| ast_to_term(unsafe { *from.add(i) }))
        .collect();
    let to_terms: Vec<_> = (0..n).map(|i| ast_to_term(unsafe { *to.add(i) })).collect();
    let target = ast_to_term(a);

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            // Z3 requires from[i] and to[i] to share a sort. A mismatch is a
            // Z3_SORT_ERROR; report it honestly and leave `a` unchanged rather
            // than fabricating an ill-sorted term.
            for (f, t) in from_terms.iter().zip(to_terms.iter()) {
                if ctx.solver.sort_of(*f) != ctx.solver.sort_of(*t) {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some("Z3_substitute: from/to sort mismatch".to_string());
                    return a;
                }
            }
            let result = ctx.solver.substitute(target, &from_terms, &to_terms);
            term_to_ast(result)
        })
    }
}
