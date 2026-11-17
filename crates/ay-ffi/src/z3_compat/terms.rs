// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible term construction: function decls and boolean operations.
//! Numeral constructors are in `numerals.rs`.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_char, c_int, c_uint};
use std::ptr;

use ay_dpll::api::{Sort, Term};
use num_bigint::BigInt;

use super::arithmetic::coerce_mixed_int_real;
use super::provenance::StructuralRefusal;
use super::{
    activate_finite_set_sat_gate, cache_func_decl_with_symbol, ffi_count_within_limit,
    ffi_counts_within_limit, ffi_guard_ast, ffi_guard_mk, ffi_guard_ptr, ffi_read_bounded_text,
    ffi_try_declare_function, finite_set_engine_public_sort,
    has_unsupported_finite_set_datatype_embedding, public_ast_sort, record_ast_sort,
    require_term_ast, require_term_asts, sort_mentions_finite_set, term_to_ast, DatatypeOp,
    SymbolKey, Z3_ast, Z3_context, Z3_func_decl, Z3_params, Z3_sort, Z3_symbol, Z3_INVALID_ARG,
    Z3_SORT_ERROR,
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
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_func_decl", domain_size) } {
        return ptr::null_mut();
    }
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
            match ffi_try_declare_function(ctx, &symbol, &dom_sorts, &range_sort) {
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
        ffi_guard_mk(c, "Z3_mk_const", |ctx| {
            // Fail-close reserved-namespace capture — see `reserved_name_error`
            // (a `!ay.*` constant can alias an internal engine witness).
            if matches!(&symbol, SymbolKey::String(_)) {
                if let Some(msg) = super::reserved_name_error(&display_name) {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(msg);
                    return 0;
                }
            }
            let Some(term) = ffi_api_constant(ctx, &symbol, &sort) else {
                return 0;
            };
            let ast = term_to_ast(ctx, term);
            record_ast_sort(ctx, ast, sort)
        })
    }
}

/// The context's constant for `symbol` at `sort`, declaring it on first use
/// (the core of [`Z3_mk_const`]). z3 identifies a constant by its name and
/// sort, so every request for the same pair returns the same term. `None`
/// (with the context error set) when the sort cannot be lowered.
pub(crate) fn ffi_api_constant(
    ctx: &mut super::Z3Context,
    symbol: &SymbolKey,
    sort: &Sort,
) -> Option<Term> {
    let display_name = symbol.display_name();
    let cache_key = (symbol.clone(), sort.clone());
    if let Some(term) = ctx.ffi_const_cache.get(&cache_key).copied() {
        return Some(term);
    }
    if has_unsupported_finite_set_datatype_embedding(ctx, sort) {
        ctx.last_error = Z3_SORT_ERROR;
        ctx.error_msg = Some(
            "Z3_mk_const: a datatype containing FiniteSet fields cannot be lowered \
             without changing the datatype identity"
                .to_string(),
        );
        return None;
    }
    let identity = format!("!ay.z3-const!{}", ctx.next_ffi_fresh_id);
    ctx.next_ffi_fresh_id += 1;
    let needs_finite_set_gate = sort_mentions_finite_set(ctx, sort);
    let engine_sort = finite_set_engine_public_sort(ctx, sort);
    let term = ctx
        .solver
        .declare_const_with_fresh_identity(&display_name, &identity, engine_sort);
    if needs_finite_set_gate {
        activate_finite_set_sat_gate(ctx, term, "Z3_mk_const");
        ctx.finite_set_decl_signatures
            .insert(identity.clone(), (Vec::new(), sort.clone()));
    }
    ctx.ffi_const_cache.insert(cache_key, term);
    ctx.ffi_const_metadata
        .insert(term, (identity.clone(), symbol.clone()));
    ctx.ffi_const_terms_by_identity.insert(identity, term);
    ctx.ffi_used_decl_names.insert(display_name);
    Some(term)
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
        Ok("fresh".to_string())
    } else {
        // SAFETY: The caller's `# Safety` contract requires the C string pointer to be
        // non-null and to point to a valid, null-terminated sequence of bytes owned by the
        // caller for the duration of this call. The pointer was null-checked before entering
        // this block.
        unsafe { ffi_read_bounded_text(prefix) }
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
        ffi_guard_mk(c, "Z3_mk_fresh_const", |ctx| {
            let pfx = match &pfx {
                Ok(pfx) => pfx,
                Err(error) => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!("Z3_mk_fresh_const: {error}"));
                    return 0;
                }
            };
            // Fail-close reserved-namespace capture — a `!ay.`-prefixed fresh
            // prefix could collide with an internal engine witness name.
            if let Some(msg) = super::reserved_name_error(pfx) {
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
            if has_unsupported_finite_set_datatype_embedding(ctx, &sort) {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(
                    "Z3_mk_fresh_const: a datatype containing FiniteSet fields cannot be \
                     lowered without changing the datatype identity"
                        .to_string(),
                );
                return 0;
            }
            let needs_finite_set_gate = sort_mentions_finite_set(ctx, &sort);
            let engine_sort = finite_set_engine_public_sort(ctx, &sort);
            let term =
                ctx.solver
                    .declare_const_with_fresh_identity(&fresh_name, &identity, engine_sort);
            if needs_finite_set_gate {
                activate_finite_set_sat_gate(ctx, term, "Z3_mk_fresh_const");
                ctx.finite_set_decl_signatures
                    .insert(identity.clone(), (Vec::new(), sort.clone()));
            }
            let symbol = SymbolKey::String(fresh_name.clone());
            ctx.ffi_const_metadata
                .insert(term, (identity.clone(), symbol));
            ctx.ffi_const_terms_by_identity.insert(identity, term);
            let ast = term_to_ast(ctx, term);
            record_ast_sort(ctx, ast, sort)
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
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_app", num_args) } {
        return 0;
    }
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
    let (decl, dt_op, value) = unsafe { ((*d).decl.clone(), (*d).dt_op.clone(), (*d).value) };
    let arg_asts: Vec<_> = (0..num_args as usize)
        // SAFETY: The caller's `# Safety` contract guarantees `args` points to at least the
        // declared number of elements. The count was range-checked above, and null-checked
        // before entering this block, so `args.add(i)` stays within the caller's allocation.
        .map(|i| unsafe { *args.add(i) })
        .collect();

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_app", |ctx| {
            if ctx.proof_declarations.contains_key(&d) {
                ctx.last_error = super::Z3_INVALID_USAGE;
                ctx.error_msg =
                    Some("Z3_mk_app: proof applications require a native derivation".to_owned());
                return 0;
            }
            let Some(term_args) = require_term_asts(ctx, &arg_asts, "Z3_mk_app") else {
                return 0;
            };
            let (public_domain, public_range) = ctx
                .finite_set_decl_signatures
                .get(decl.name())
                .cloned()
                .unwrap_or_else(|| (decl.domain().to_vec(), decl.range().clone()));
            if term_args.len() != public_domain.len() {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_mk_app: declaration expects {} argument(s), got {}",
                    public_domain.len(),
                    term_args.len()
                ));
                return 0;
            }
            // A POLYMORPHIC declaration's domain is a signature SCHEMA, not a
            // concrete sort list: `f : α → α` legitimately accepts an Int
            // argument. Equality against the schema would reject every
            // instantiation, so the per-argument check below is skipped for
            // such decls and `instantiate_poly_decl` (which unifies, and keeps
            // one variable bound to ONE sort) reports the sort error instead
            // (#poly-inst).
            let polymorphic = decl_mentions_type_var(&decl);
            if !polymorphic {
                for (index, ((&arg_ast, &arg_term), expected)) in arg_asts
                    .iter()
                    .zip(&term_args)
                    .zip(&public_domain)
                    .enumerate()
                {
                    let actual = public_ast_sort(ctx, arg_ast, arg_term);
                    if actual != *expected {
                        ctx.last_error = Z3_SORT_ERROR;
                        ctx.error_msg = Some(format!(
                            "Z3_mk_app: argument {index} has public sort {actual}, expected {expected}"
                        ));
                        return 0;
                    }
                }
            }
            // The decl of a literal (`Z3_get_app_decl` on a value) applied to
            // no arguments is that literal, as in z3.
            if let Some(value) = value {
                let ast = term_to_ast(ctx, value.term);
                let ast = record_ast_sort(ctx, ast, public_range);
                return ast;
            }
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
                    if polymorphic {
                        match instantiate_poly_decl(ctx, &decl, &term_args) {
                            Ok(inst) => {
                                let range = inst.range().clone();
                                match ctx.solver.try_apply(&inst, &term_args) {
                                    Ok(t) => {
                                        let ast = term_to_ast(ctx, t);
                                        let ast = record_ast_sort(ctx, ast, range);
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
                    if term_args.is_empty() {
                        if let Some(ast) = declared_const_for_decl(ctx, &decl, &public_range) {
                            return ast;
                        }
                    }
                    match ctx.solver.try_apply(&decl, &term_args) {
                        Ok(t) => t,
                        Err(e) => {
                            ctx.last_error = Z3_INVALID_ARG;
                            ctx.error_msg = Some(format!("Z3_mk_app: {e}"));
                            return 0;
                        }
                    }
                }
            };
            let ast = term_to_ast(ctx, result);
            if sort_mentions_finite_set(ctx, &public_range) {
                activate_finite_set_sat_gate(ctx, result, "Z3_mk_app result");
            }
            record_ast_sort(ctx, ast, public_range)
        })
    }
}

/// The constant a nullary decl names when the decl came back from AY rather
/// than from `Z3_mk_func_decl`: `Z3_get_app_decl` of a `Z3_mk_const` constant
/// and `Z3_model_get_const_decl` both name the constant by its internal
/// identity (`!ay.z3-const!N`, a reserved name no user declaration can take).
/// Applying such a decl is the constant itself, as in z3 (z3py's model
/// enumeration builds `d() != m[d]`); before this, `Z3_mk_app` panicked on it
/// as an unregistered declaration. `Some(0)` with `Z3_SORT_ERROR` when the
/// decl's range is not the constant's sort.
fn declared_const_for_decl(
    ctx: &mut super::Z3Context,
    decl: &ay_dpll::api::FuncDecl,
    range: &Sort,
) -> Option<Z3_ast> {
    let term = ctx.ffi_const_terms_by_identity.get(decl.name()).copied()?;
    let ast = term_to_ast(ctx, term);
    let sort = public_ast_sort(ctx, ast, term);
    if sort != *range {
        ctx.last_error = Z3_SORT_ERROR;
        ctx.error_msg = Some(format!(
            "Z3_mk_app: declaration '{}' ranges over {range}, but that constant has sort {sort}",
            decl.name()
        ));
        return Some(0);
    }
    Some(ast)
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
    let inst = decl.with_instantiated_signature(arg_sorts, range);
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
        ffi_guard_mk(c, "Z3_mk_true", |ctx| {
            let t = ctx.solver.bool_const(true);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Bool)
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
        ffi_guard_mk(c, "Z3_mk_false", |ctx| {
            let t = ctx.solver.bool_const(false);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Bool)
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
    unsafe { ffi_guard_mk(c, "Z3_mk_eq", |ctx| mk_equality(ctx, "Z3_mk_eq", l, r)) }
}

/// `(= l r)` for `Z3_mk_eq` and `Z3_mk_iff` (z3's iff is `=`, also over
/// non-Bool operands: `Z3_mk_iff(x:Int, y:Int)` is `(= x y)`, measured). The
/// public operand sorts must agree, except Int beside Real, which z3 coerces
/// to `(= (to_real x) y)` (measured; T5 P0.2 Q4). Every refusal is
/// `Z3_SORT_ERROR`, never a panic.
fn mk_equality(ctx: &mut super::Z3Context, entry: &str, l_ast: Z3_ast, r_ast: Z3_ast) -> Z3_ast {
    let Some(l) = require_term_ast(ctx, l_ast, entry, "left operand") else {
        return 0;
    };
    let Some(r) = require_term_ast(ctx, r_ast, entry, "right operand") else {
        return 0;
    };
    let left_sort = public_ast_sort(ctx, l_ast, l);
    let right_sort = public_ast_sort(ctx, r_ast, r);
    let (l, r) = match coerce_mixed_int_real(
        ctx,
        entry,
        &[l, r],
        &[left_sort.clone(), right_sort.clone()],
    ) {
        Some(Ok(lifted)) => match lifted.as_slice() {
            [l, r] => (*l, *r),
            _ => return 0,
        },
        Some(Err(())) => return 0,
        None if left_sort != right_sort => {
            ctx.last_error = Z3_SORT_ERROR;
            ctx.error_msg = Some(format!(
                "{entry}: public operand sorts differ ({left_sort} vs {right_sort})"
            ));
            return 0;
        }
        None => (l, r),
    };
    let t = match ctx.solver.try_eq(l, r) {
        Ok(t) => t,
        Err(e) => {
            ctx.last_error = Z3_SORT_ERROR;
            ctx.error_msg = Some(format!("{entry}: {e}"));
            return 0;
        }
    };
    let a = term_to_ast(ctx, t);
    record_ast_sort(ctx, a, Sort::Bool)
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
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_distinct", num_args) } {
        return 0;
    }
    if num_args == 0 || args.is_null() {
        return 0;
    }
    let arg_asts: Vec<_> = (0..num_args as usize)
        // SAFETY: The caller's `# Safety` contract guarantees `args` points to at least the
        // declared number of elements. The count was range-checked above, and null-checked
        // before entering this block, so `args.add(i)` stays within the caller's allocation.
        .map(|i| unsafe { *args.add(i) })
        .collect();

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_distinct", |ctx| {
            let Some(terms) = require_term_asts(ctx, &arg_asts, "Z3_mk_distinct") else {
                return 0;
            };
            let sorts: Vec<Sort> = arg_asts
                .iter()
                .zip(&terms)
                .map(|(&arg_ast, &term)| public_ast_sort(ctx, arg_ast, term))
                .collect();
            // Int beside Real: z3's `(distinct (to_real x) y)` (measured).
            let terms = match coerce_mixed_int_real(ctx, "Z3_mk_distinct", &terms, &sorts) {
                Some(Ok(lifted)) => lifted,
                Some(Err(())) => return 0,
                None => {
                    let Some(expected) = sorts.first() else {
                        return 0;
                    };
                    if let Some(actual) = sorts.iter().find(|sort| *sort != expected) {
                        ctx.last_error = Z3_SORT_ERROR;
                        ctx.error_msg = Some(format!(
                            "Z3_mk_distinct: public operand sorts differ ({expected} vs {actual})"
                        ));
                        return 0;
                    }
                    terms
                }
            };
            let t = match ctx.solver.try_distinct(&terms) {
                Ok(t) => t,
                Err(e) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!("Z3_mk_distinct: {e}"));
                    return 0;
                }
            };
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Bool)
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
        ffi_guard_mk(c, "Z3_mk_not", |ctx| {
            let Some(a) = require_term_ast(ctx, a, "Z3_mk_not", "operand") else {
                return 0;
            };
            let t = match ctx.solver.try_not(a) {
                Ok(t) => t,
                Err(e) => return bool_operand_error(ctx, "Z3_mk_not", &e),
            };
            let r = term_to_ast(ctx, t);
            record_ast_sort(ctx, r, Sort::Bool)
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
        ffi_guard_mk(c, "Z3_mk_ite", |ctx| {
            let condition_ast = t1;
            let then_ast = t2;
            let else_ast = t3;
            let Some(t1) = require_term_ast(ctx, condition_ast, "Z3_mk_ite", "condition") else {
                return 0;
            };
            let Some(t2_term) = require_term_ast(ctx, then_ast, "Z3_mk_ite", "then operand") else {
                return 0;
            };
            let Some(t3) = require_term_ast(ctx, else_ast, "Z3_mk_ite", "else operand") else {
                return 0;
            };
            if public_ast_sort(ctx, condition_ast, t1) != Sort::Bool {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some("Z3_mk_ite: condition must have public Bool sort".to_string());
                return 0;
            }
            let then_sort = public_ast_sort(ctx, then_ast, t2_term);
            let else_sort = public_ast_sort(ctx, else_ast, t3);
            // Int beside Real: z3's `(ite c (to_real x) y)`, of sort Real
            // (measured).
            let (t2_term, t3, result_sort) = match coerce_mixed_int_real(
                ctx,
                "Z3_mk_ite",
                &[t2_term, t3],
                &[then_sort.clone(), else_sort.clone()],
            ) {
                Some(Ok(lifted)) => match lifted.as_slice() {
                    [t2, t3] => (*t2, *t3, Sort::Real),
                    _ => return 0,
                },
                Some(Err(())) => return 0,
                None if then_sort != else_sort => {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!(
                        "Z3_mk_ite: branch public sorts differ ({then_sort} vs {else_sort})"
                    ));
                    return 0;
                }
                None => (t2_term, t3, then_sort),
            };
            let t = match ctx.solver.try_ite(t1, t2_term, t3) {
                Ok(t) => t,
                Err(e) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!("Z3_mk_ite: {e}"));
                    return 0;
                }
            };
            let r = term_to_ast(ctx, t);
            record_ast_sort(ctx, r, result_sort)
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
    unsafe { ffi_guard_mk(c, "Z3_mk_iff", |ctx| mk_equality(ctx, "Z3_mk_iff", t1, t2)) }
}

/// Report a non-Bool operand of a Boolean connective as z3 does
/// (`Z3_SORT_ERROR`; measured on libz3 5.1.0, `q4_bool_pins.py`: "Sort
/// mismatch at argument #1 for function (declare-fun not (Bool) Bool)").
/// AY's builders used to panic on it ("panic in FFI").
fn bool_operand_error(
    ctx: &mut super::Z3Context,
    entry: &str,
    error: &ay_dpll::api::SolverError,
) -> Z3_ast {
    ctx.last_error = Z3_SORT_ERROR;
    ctx.error_msg = Some(format!("{entry}: {error}"));
    0
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
        ffi_guard_mk(c, "Z3_mk_implies", |ctx| {
            let Some(t1) = require_term_ast(ctx, t1, "Z3_mk_implies", "antecedent") else {
                return 0;
            };
            let Some(t2) = require_term_ast(ctx, t2, "Z3_mk_implies", "consequent") else {
                return 0;
            };
            let t = match ctx.solver.try_implies(t1, t2) {
                Ok(t) => t,
                Err(e) => return bool_operand_error(ctx, "Z3_mk_implies", &e),
            };
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Bool)
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
        ffi_guard_mk(c, "Z3_mk_xor", |ctx| {
            let Some(t1) = require_term_ast(ctx, t1, "Z3_mk_xor", "left operand") else {
                return 0;
            };
            let Some(t2) = require_term_ast(ctx, t2, "Z3_mk_xor", "right operand") else {
                return 0;
            };
            let t = match ctx.solver.try_xor(t1, t2) {
                Ok(t) => t,
                Err(e) => return bool_operand_error(ctx, "Z3_mk_xor", &e),
            };
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Bool)
        })
    }
}

/// Create boolean AND.
///
/// # Safety
/// All pointers must be valid. `args` must point to `num_args` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_and(c: Z3_context, num_args: c_uint, args: *const Z3_ast) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_and", num_args) } {
        return 0;
    }
    let arg_asts: Vec<_> = if num_args == 0 || args.is_null() {
        Vec::new()
    } else {
        (0..num_args as usize)
            // SAFETY: The caller's `# Safety` contract guarantees `args` points to at least
            // the declared number of elements. The count was range-checked above, and
            // null-checked before entering this block, so `args.add(i)` stays within the
            // caller's allocation.
            .map(|i| unsafe { *args.add(i) })
            .collect()
    };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_and", |ctx| {
            let Some(terms) = require_term_asts(ctx, &arg_asts, "Z3_mk_and") else {
                return 0;
            };
            if terms.is_empty() {
                let t = ctx.solver.bool_const(true);
                return term_to_ast(ctx, t);
            }
            let t = match ctx.solver.try_and_many(&terms) {
                Ok(t) => t,
                Err(e) => return bool_operand_error(ctx, "Z3_mk_and", &e),
            };
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Bool)
        })
    }
}

/// Create boolean OR.
///
/// # Safety
/// All pointers must be valid. `args` must point to `num_args` elements.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_or(c: Z3_context, num_args: c_uint, args: *const Z3_ast) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_or", num_args) } {
        return 0;
    }
    let arg_asts: Vec<_> = if num_args == 0 || args.is_null() {
        Vec::new()
    } else {
        (0..num_args as usize)
            // SAFETY: The caller's `# Safety` contract guarantees `args` points to at least
            // the declared number of elements. The count was range-checked above, and
            // null-checked before entering this block, so `args.add(i)` stays within the
            // caller's allocation.
            .map(|i| unsafe { *args.add(i) })
            .collect()
    };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_or", |ctx| {
            let Some(terms) = require_term_asts(ctx, &arg_asts, "Z3_mk_or") else {
                return 0;
            };
            if terms.is_empty() {
                let t = ctx.solver.bool_const(false);
                return term_to_ast(ctx, t);
            }
            let t = match ctx.solver.try_or_many(&terms) {
                Ok(t) => t,
                Err(e) => return bool_operand_error(ctx, "Z3_mk_or", &e),
            };
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Bool)
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
    term_asts: Vec<Z3_ast>,
    coeffs: Vec<BigInt>,
    k: BigInt,
    cmp: PbCmp,
) -> Z3_ast {
    debug_assert_eq!(term_asts.len(), coeffs.len());
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; `ffi_guard_ast`
    // handles the null case internally and catches any unwinding panic so it cannot
    // cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "mk_pb_ast", |ctx| {
            let Some(terms) = require_term_asts(ctx, &term_asts, "pseudo-Boolean constructor")
            else {
                return 0;
            };
            let zero = ctx.solver.int_const(0);
            let mut summands: Vec<Term> = Vec::with_capacity(terms.len());
            for (&t, coeff) in terms.iter().zip(&coeffs) {
                let coeff_term = ctx.solver.int_const_bigint(coeff);
                match ctx.solver.try_ite(t, coeff_term, zero) {
                    Ok(summand) => summands.push(summand),
                    Err(e) => return bool_operand_error(ctx, "pseudo-Boolean constructor", &e),
                }
            }
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
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Bool)
        })
    }
}

/// Read `num_args` raw `Z3_ast` handles for later context-aware decoding.
///
/// # Safety
/// `args` must point to at least `num_args` valid elements (or be null when
/// `num_args == 0`).
unsafe fn read_ast_args(num_args: c_uint, args: *const Z3_ast) -> Vec<Z3_ast> {
    if num_args == 0 || args.is_null() {
        return Vec::new();
    }
    (0..num_args as usize)
        // SAFETY: caller guarantees `args` points to at least `num_args` elements;
        // `add(i)` stays in bounds.
        .map(|i| unsafe { *args.add(i) })
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
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_atmost", num_args) } {
        return 0;
    }
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
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_atleast", num_args) } {
        return 0;
    }
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
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe {
        ffi_counts_within_limit(
            c,
            "Z3_mk_pble argument and coefficient arrays",
            &[num_args, num_args],
        )
    } {
        return 0;
    }
    // SAFETY: caller contract on the two arrays; see the readers' contracts.
    let (terms, cs) = unsafe {
        (
            read_ast_args(num_args, args),
            read_int_coeffs(num_args, coeffs),
        )
    };
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
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe {
        ffi_counts_within_limit(
            c,
            "Z3_mk_pbge argument and coefficient arrays",
            &[num_args, num_args],
        )
    } {
        return 0;
    }
    // SAFETY: caller contract on the two arrays; see the readers' contracts.
    let (terms, cs) = unsafe {
        (
            read_ast_args(num_args, args),
            read_int_coeffs(num_args, coeffs),
        )
    };
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
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe {
        ffi_counts_within_limit(
            c,
            "Z3_mk_pbeq argument and coefficient arrays",
            &[num_args, num_args],
        )
    } {
        return 0;
    }
    // SAFETY: caller contract on the two arrays; see the readers' contracts.
    let (terms, cs) = unsafe {
        (
            read_ast_args(num_args, args),
            read_int_coeffs(num_args, coeffs),
        )
    };
    if terms.len() != cs.len() {
        return 0;
    }
    // SAFETY: `c` validity is the caller's contract; forwarded to the guard.
    unsafe { mk_pb_ast(c, terms, cs, BigInt::from(k), PbCmp::Eq) }
}

// ---- Simplification ----

/// Simplify an AST, returning a logically equivalent simplified term.
///
/// Runs the shared counted word and fact-free expression rewrites under one
/// retained operation. Supported closed expressions are evaluated independently;
/// unsupported expressions remain unchanged. Global word-expansion settings
/// apply here as they do in the owned tactic path. Resource refusal returns null
/// with an exception instead of publishing a partial rewrite.
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

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety`
    // on this extern "C" function requires it to be a valid, non-aliased pointer
    // (or null). `ffi_guard_ast` handles the null case internally and catches any
    // unwinding panic so it cannot cross the FFI boundary.
    unsafe { ffi_guard_ast(c, |ctx| simplify_owned(ctx, a, ptr::null_mut())) }
}

/// Simplify an AST with supported local settings under the same original
/// source/counter/output operation as plain simplification. Local settings
/// override actual globals; unsupported settings explicitly refuse.
///
/// # Safety
/// `c` must be a valid context pointer. `a` must be a valid `Z3_ast` produced by
/// this context (or null/0, returned unchanged). `p` may be null for defaults.
#[no_mangle]
pub unsafe extern "C" fn Z3_simplify_ex(c: Z3_context, a: Z3_ast, p: Z3_params) -> Z3_ast {
    if a == 0 {
        return 0;
    }
    // SAFETY: caller supplies this live non-aliased context; the guard catches
    // panics and the owned body authenticates input/parameter handles.
    unsafe { ffi_guard_ast(c, |ctx| simplify_owned(ctx, a, p)) }
}

fn simplify_owned(ctx: &mut super::Z3Context, a: Z3_ast, p: Z3_params) -> Z3_ast {
    let operation = match ctx.solver.begin_tactic_operation_for_check() {
        Ok(operation) => operation,
        Err(error) => {
            ctx.last_error = super::Z3_EXCEPTION;
            ctx.error_msg = Some(error.to_string());
            return 0;
        }
    };
    let result = (|| -> Result<Z3_ast, ay_dpll::api::SolverError> {
        let target = require_term_ast(ctx, a, "Z3_simplify", "input").ok_or_else(|| {
            ay_dpll::api::SolverError::TacticFailed("invalid simplifier input".into())
        })?;
        let mut parameters = ay_dpll::api::SimplifyParameters::default();
        if !p.is_null() {
            super::tactics::visit_parameters(ctx, p, &operation, &mut |name, value| {
                parameters.set(name, value).map_err(|e| e.to_string())
            })
            .map_err(ay_dpll::api::SolverError::TacticFailed)?;
        }
        let global = super::global_params::sequence_power_expansion(operation.admission())
            .map_err(|e| ay_dpll::api::SolverError::TacticFailed(e.into()))?;
        parameters = parameters.with_global_sequence_power(global);
        parameters = parameters.with_global_polynomial(
            super::global_params::polynomial_parameters(operation.admission())
                .map_err(|e| ay_dpll::api::SolverError::TacticFailed(e.into()))?,
        );
        let value = ctx
            .solver
            .simplify_in_operation(&operation, target, parameters)?;
        let owner = operation.admission();
        // A source public sort can differ from its engine carrier (Char/FD/
        // native sets). Keep the exact handle on identity; never reinterpret
        // a changed carrier as a newly minted ordinary engine-sorted AST.
        let output = if value == target {
            a
        } else {
            if let Some(stated) = super::lookup_ast_sort(ctx, a) {
                if !ctx
                    .solver
                    .term_has_sort_in_operation(&operation, value, stated)?
                {
                    return Err(ay_dpll::api::SolverError::TacticFailed(
                        "changed aliased public sort is unsupported".into(),
                    ));
                }
            }
            let id = ctx
                .pub_ast
                .engine_node_owned(value, Some(owner))
                .ok_or_else(|| {
                    ay_dpll::api::SolverError::TacticFailed("simplifier public AST refused".into())
                })?;
            super::pub_id_to_ast(ctx, id)
        };
        owner
            .admit(1, 0)
            .map_err(|e| ay_dpll::api::SolverError::TacticFailed(e.to_string()))?;
        if !matches!(ctx.solver.term_kind(value), ay_dpll::api::TermKind::Const) {
            ctx.provenance
                .mark_ambiguous_owned(value, owner)
                .map_err(|e| ay_dpll::api::SolverError::TacticFailed(e.into()))?;
        }
        if !operation.validate(&ctx.solver) {
            return Err(ay_dpll::api::SolverError::TacticFailed(
                "simplifier publication source changed".into(),
            ));
        }
        Ok(output)
    })();
    match result {
        Ok(ast) => {
            ctx.last_error = super::Z3_OK;
            ast
        }
        Err(error) => {
            let message = error.to_string();
            operation.publish_failure(&mut ctx.solver, &error);
            ctx.last_error = super::Z3_EXCEPTION;
            ctx.error_msg = Some(message);
            0
        }
    }
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
/// Unless every `from[i]` is an uninterpreted constant, or `a` and every
/// `from[i]` are stored exactly as the caller built them, sets
/// `Z3_INVALID_ARG` and returns null: AY's construction-time rewrites would
/// otherwise make the structural match differ from z3's (see `provenance.rs`).
/// It is refused the same way when a `from`/`to` term mentions a variable the
/// input binds, or the input contains a `let`: AY binds by name, so the
/// substitution would rewrite bound occurrences or capture free ones
/// (`provenance::check_binders`).
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
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe {
        ffi_counts_within_limit(
            c,
            "Z3_substitute source and replacement arrays",
            &[num_exprs, num_exprs],
        )
    } {
        return a;
    }

    let n = num_exprs as usize;
    // Pre-extract the from/to arrays from raw pointers before entering the guard.
    // SAFETY: The caller's `# Safety` contract guarantees `from`/`to` each point
    // to at least `num_exprs` elements. Both were null-checked above, so
    // `from.add(i)`/`to.add(i)` stay within the caller's allocation.
    let (from_asts, to_asts): (Vec<_>, Vec<_>) = unsafe {
        (
            (0..n).map(|i| *from.add(i)).collect(),
            (0..n).map(|i| *to.add(i)).collect(),
        )
    };

    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let Some(target) = require_term_ast(ctx, a, "Z3_substitute", "input") else {
                return a;
            };
            let Some(from_terms) = require_term_asts(ctx, &from_asts, "Z3_substitute from") else {
                return a;
            };
            let Some(to_terms) = require_term_asts(ctx, &to_asts, "Z3_substitute to") else {
                return a;
            };
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
            if let Err(refusal) = super::provenance::check_substitution(ctx, target, &from_terms) {
                let which = match refusal {
                    StructuralRefusal::Input => "the input".to_string(),
                    StructuralRefusal::Pattern(i) => format!("from[{i}]"),
                };
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_substitute: {which} may not be the term the caller built. AY rewrites \
                     terms at construction (Not(Not(p)) is stored as p, (x + 1) + 1 as x + 2, \
                     x > y as y < x), and z3 substitutes by structure, so AY substitutes only \
                     uninterpreted constants (Z3_mk_const) or terms it stores exactly as built; \
                     refusing rather than returning a formula z3 would not"
                ));
                return 0;
            }
            if let Err(refusal) =
                super::provenance::check_binders(ctx, target, &from_terms, &to_terms)
            {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(super::provenance::binder_refusal_message(
                    ctx,
                    "Z3_substitute",
                    refusal,
                ));
                return 0;
            }
            let result = ctx.solver.substitute(target, &from_terms, &to_terms);
            // AY rebuilt the changed nodes through its rewriting constructors;
            // z3 rebuilt them as written. Unchanged input or an exact
            // replacement is the same term in both.
            if result != target && !to_terms.contains(&result) {
                ctx.provenance.mark_ambiguous(result);
            }
            term_to_ast(ctx, result)
        })
    }
}
