// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible extended (non-FPA) `Z3_mk_*` constructors.
//!
//! This module rounds out the `z3_api.h` `mk_*` surface with the constructors
//! that were not already covered by the theory-specific modules (`sorts.rs`,
//! `terms.rs`, `numerals.rs`, `bitvectors.rs`, `sequences.rs`, `sets_regex.rs`,
//! `datatypes.rs`, `quantifiers.rs`). Everything here is either
//!
//!   * a **real** builder that lowers onto an existing, semantically-identical
//!     `ay_dpll::api::Solver` primitive (currying array sorts, de-Bruijn/const
//!     quantifiers dispatched to the shared forall/exists builder, datatype /
//!     list / enumeration / tuple sorts reusing the `Z3_mk_datatype`
//!     machinery, BV/regex/string lowerings), or
//!
//!   * an **honest divergence**: where AY's IR has no sound representation
//!     (parametric datatypes) the function sets `Z3_INVALID_ARG` (or
//!     `Z3_SORT_ERROR`) and returns the sound null sentinel (`0` / null)
//!     rather than fabricating a wrong term. Each such case carries a
//!     `DIVERGENCE:` doc line explaining why an opaque placeholder would be
//!     UNSOUND (it would drop axioms and flip a Z3-unsat into an AY-sat =
//!     wrong answer).
//!
//!   Formerly-divergent surfaces now REAL here: the char theory
//!   (`Sort::Char`), the full char↔BV bridge (width 18, pinned empirically
//!   against libz3 4.16.0), the four special-relation orders,
//!   `Z3_mk_transitive_closure` (reflexive-transitive-closure axioms + a
//!   model-check gate at `Z3_solver_check`), `finite_domain` cardinality
//!   sorts (`Sort::FiniteDomain`, bounded-Int lowering), type variables
//!   (`Sort::TypeVar`, monomorphic), the array-extensionality witness
//!   (`Z3_mk_array_ext`, cached witness + background axiom), and the
//!   higher-order sequence combinators (real `seq.map`/`seq.mapi`/`seq.foldl`/
//!   `seq.foldli` terms; solving is honestly incomplete).
//!
//! All functions calling into the solver are wrapped via the `ffi_guard_*`
//! helpers (#6192) so a panic can never unwind across the `extern "C"` boundary.

use std::ffi::c_uint;
use std::ptr;
use std::slice;

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, FuncDecl, Sort, Term};
use num_bigint::BigInt;

use super::quantifiers::{mk_quantifier_const, mk_quantifier_db, QuantifierMetadataInput};

use super::{
    activate_finite_set_sat_gate, alloc_sort, cache_dt_func_decl_with_symbol, cache_func_decl,
    cache_func_decl_with_symbol, ffi_count_within_limit, ffi_counts_within_limit, ffi_guard_ast,
    ffi_guard_ptr, ffi_read_bounded_text, ffi_try_declare_function, finite_set_engine_public_sort,
    public_ast_sort, record_ast_sort, record_reachable_finite_set_axiom,
    require_term_ast_or_return, require_term_asts_or_return, sort_mentions_finite_set, term_to_ast,
    DatatypeOp, SymbolKey, Z3Context, Z3_ast, Z3_constructor, Z3_context, Z3_func_decl,
    Z3_mk_solver, Z3_pattern, Z3_solver, Z3_sort, Z3_string, Z3_symbol, AY_MAX_CHAR,
    MAX_FFI_BITVECTOR_WIDTH, Z3_INVALID_ARG, Z3_SORT_ERROR,
};

// ============================================================================
// Shared helpers
// ============================================================================

/// Read the exact caller-visible symbol identity.
///
/// # Safety
/// `s` must be null or a valid symbol handle from a prior AY FFI allocation.
unsafe fn read_symbol_key(s: Z3_symbol) -> Option<SymbolKey> {
    if s.is_null() {
        return None;
    }
    // SAFETY: `s` null-checked above; a valid AY symbol handle kept alive by the
    // owning context (single-threaded per context).
    Some(unsafe { (*s).key.clone() })
}

/// Declare a datatype on the solver and allocate its sort handle.
///
/// Returns null (after setting `last_error`) if the solver rejects the
/// definition. Mirrors `datatypes.rs::declare_and_fill`'s declaration step.
fn declare_datatype_and_alloc(
    ctx: &mut Z3Context,
    dt: &DatatypeSort,
    symbol: &SymbolKey,
) -> Z3_sort {
    if let Err(e) = ctx.solver.try_declare_datatype(dt) {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some(format!("{e}"));
        return ptr::null_mut();
    }
    let sort = Sort::Datatype(dt.clone());
    ctx.ffi_sort_symbols.insert(sort.clone(), symbol.clone());
    alloc_sort(ctx, sort)
}

/// Build a constructor func_decl (`(field sorts...) -> DT`) tagged so
/// `Z3_mk_app` routes through AY's verified datatype constructor builder.
fn make_constructor_decl(
    ctx: &mut Z3Context,
    dt: &DatatypeSort,
    ctor: &DatatypeConstructor,
    dt_sort: &Sort,
    symbol: SymbolKey,
) -> Z3_func_decl {
    cache_dt_func_decl_with_symbol(
        ctx,
        FuncDecl::new(
            ctor.name.clone(),
            ctor.fields.iter().map(|f| f.sort.clone()).collect(),
            dt_sort.clone(),
        ),
        DatatypeOp::Constructor {
            dt: dt.clone(),
            ctor: ctor.name.clone(),
        },
        symbol,
    )
}

/// Build a recognizer func_decl (`DT -> Bool`, named `is-<ctor>`) tagged for
/// AY's datatype tester builder.
fn make_recognizer_decl(
    ctx: &mut Z3Context,
    ctor_name: &str,
    dt_sort: &Sort,
    symbol: SymbolKey,
) -> Z3_func_decl {
    cache_dt_func_decl_with_symbol(
        ctx,
        FuncDecl::new(format!("is-{ctor_name}"), vec![dt_sort.clone()], Sort::Bool),
        DatatypeOp::Recognizer {
            ctor: ctor_name.to_string(),
        },
        symbol,
    )
}

/// Build an accessor (selector) func_decl (`DT -> field_sort`) tagged for AY's
/// datatype selector builder.
fn make_accessor_decl(
    ctx: &mut Z3Context,
    field_name: &str,
    field_sort: Sort,
    dt_sort: &Sort,
    symbol: SymbolKey,
) -> Z3_func_decl {
    cache_dt_func_decl_with_symbol(
        ctx,
        FuncDecl::new(
            field_name.to_string(),
            vec![dt_sort.clone()],
            field_sort.clone(),
        ),
        DatatypeOp::Accessor {
            field: field_name.to_string(),
            result_sort: field_sort,
        },
        symbol,
    )
}

// ============================================================================
// Array sorts and n-ary select/store (curried)
// ============================================================================

/// Create an `n`-dimensional array sort `(Array d0 d1 ... range)`.
///
/// AY has no native flat n-index array sort, so this curries over the existing
/// binary [`Sort::array`]: `(Array d0 (Array d1 ... (Array d_{n-1} range)))`.
/// This is functionally equivalent under the array axioms provided
/// `Z3_mk_select_n` / `Z3_mk_store_n` curry consistently (they do). Mirrors
/// `Z3_mk_array_sort`.
///
/// # Safety
/// `c` must be valid; `domain` must point to `n` valid `Z3_sort` handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_array_sort_n(
    c: Z3_context,
    n: c_uint,
    domain: *const Z3_sort,
    range: Z3_sort,
) -> Z3_sort {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_array_sort_n domains", n) } {
        return ptr::null_mut();
    }
    if n == 0 || domain.is_null() || range.is_null() {
        return ptr::null_mut();
    }
    // Pre-extract domain + range sorts before entering the guard.
    let mut dom = Vec::with_capacity(n as usize);
    for i in 0..n as usize {
        // SAFETY: `domain` points to `n` elements (checked); `add(i)` in bounds.
        let sp = unsafe { *domain.add(i) };
        if sp.is_null() {
            return ptr::null_mut();
        }
        // SAFETY: `sp` is a valid AY sort handle from a prior alloc.
        dom.push(unsafe { (*sp).sort.clone() });
    }
    // SAFETY: `range` null-checked above; valid AY sort handle.
    let range_sort = unsafe { (*range).sort.clone() };
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ptr` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            // Curry innermost-first: acc = range; acc = (Array d_i acc).
            let mut acc = range_sort.clone();
            for d in dom.iter().rev() {
                acc = Sort::array(d.clone(), acc);
            }
            alloc_sort(ctx, acc)
        })
    }
}

/// `n`-ary array read: `select(select(...select(a, idxs[0])..., idxs[n-1]))`.
///
/// Consistent with the curried representation of [`Z3_mk_array_sort_n`].
///
/// # Safety
/// `c` must be valid; `idxs` must point to `n` valid `Z3_ast` values (`n >= 1`).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_select_n(
    c: Z3_context,
    a: Z3_ast,
    n: c_uint,
    idxs: *const Z3_ast,
) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_select_n indices", n) } {
        return 0;
    }
    if n == 0 || idxs.is_null() {
        // SAFETY: guard null-checks `c`.
        unsafe {
            return ffi_guard_ast(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_select_n: n must be >= 1".to_string());
                0
            });
        }
    }
    // SAFETY: `idxs` points to `n` elements (checked); `add(i)` in bounds.
    let index_asts: Vec<Z3_ast> = (0..n as usize).map(|i| unsafe { *idxs.add(i) }).collect();
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let mut acc = require_term_ast_or_return!(ctx, a, "Z3_mk_select_n", "array", 0);
            let indices =
                require_term_asts_or_return!(ctx, &index_asts, "Z3_mk_select_n indices", 0);
            let mut public_sort = public_ast_sort(ctx, a, acc);
            for (&index_ast, idx) in index_asts.iter().zip(indices) {
                let Sort::Array(array_sort) = &public_sort else {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg =
                        Some("Z3_mk_select_n: public operand sort is not an Array".to_string());
                    return 0;
                };
                let index_sort = public_ast_sort(ctx, index_ast, idx);
                if index_sort != array_sort.index_sort {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!(
                        "Z3_mk_select_n: public index sort {index_sort} differs from array domain {}",
                        array_sort.index_sort
                    ));
                    return 0;
                }
                let next_sort = array_sort.element_sort.clone();
                acc = ctx.solver.select(acc, idx);
                public_sort = next_sort;
            }
            let out = term_to_ast(ctx, acc);
            record_ast_sort(ctx, out, public_sort);
            out
        })
    }
}

/// `n`-ary array write. The curried multi-index store:
/// `store(a, i0, store(select(a,i0), i1, ... store(select..., i_{n-1}, v)...))`.
///
/// Sound under the array axioms; consistent with [`Z3_mk_array_sort_n`] /
/// [`Z3_mk_select_n`].
///
/// # Safety
/// `c` must be valid; `idxs` must point to `n` valid `Z3_ast` values (`n >= 1`).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_store_n(
    c: Z3_context,
    a: Z3_ast,
    n: c_uint,
    idxs: *const Z3_ast,
    v: Z3_ast,
) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_store_n indices", n) } {
        return 0;
    }
    if n == 0 || idxs.is_null() {
        // SAFETY: guard null-checks `c`.
        unsafe {
            return ffi_guard_ast(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_store_n: n must be >= 1".to_string());
                0
            });
        }
    }
    // SAFETY: `idxs` points to `n` elements (checked); `add(i)` in bounds.
    let index_asts: Vec<Z3_ast> = (0..n as usize).map(|i| unsafe { *idxs.add(i) }).collect();
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let base = require_term_ast_or_return!(ctx, a, "Z3_mk_store_n", "array", 0);
            let indices =
                require_term_asts_or_return!(ctx, &index_asts, "Z3_mk_store_n indices", 0);
            let mut val = require_term_ast_or_return!(ctx, v, "Z3_mk_store_n", "value", 0);
            let base_public_sort = public_ast_sort(ctx, a, base);
            let mut selected_public_sort = base_public_sort.clone();
            // prefix[k] = select(...select(a, i0)..., i_{k-1}); prefix[0] = a.
            let mut prefix = Vec::with_capacity(indices.len() + 1);
            prefix.push(base);
            for (&index_ast, &idx) in index_asts.iter().zip(&indices) {
                let Sort::Array(array_sort) = &selected_public_sort else {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg =
                        Some("Z3_mk_store_n: public operand sort is not an Array".to_string());
                    return 0;
                };
                let index_sort = public_ast_sort(ctx, index_ast, idx);
                if index_sort != array_sort.index_sort {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!(
                        "Z3_mk_store_n: public index sort {index_sort} differs from array domain {}",
                        array_sort.index_sort
                    ));
                    return 0;
                }
                let next_sort = array_sort.element_sort.clone();
                let sel = ctx.solver.select(prefix[prefix.len() - 1], idx);
                prefix.push(sel);
                selected_public_sort = next_sort;
            }
            let value_public_sort = public_ast_sort(ctx, v, val);
            if value_public_sort != selected_public_sort {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(format!(
                    "Z3_mk_store_n: public value sort {value_public_sort} differs from array range {selected_public_sort}"
                ));
                return 0;
            }
            // Build inside-out: val_{n} = v; val_k = store(prefix[k], i_k, val_{k+1}).
            for k in (0..indices.len()).rev() {
                val = ctx.solver.store(prefix[k], indices[k], val);
            }
            let out = term_to_ast(ctx, val);
            record_ast_sort(ctx, out, base_public_sort);
            out
        })
    }
}

/// Array extensionality skolem index.
///
/// REAL: returns a witness index `k(a, b)` of the arrays' index sort together
/// with the context-global background axiom
/// `(distinct a b) => (distinct (select a k) (select b k))`
/// (see [`Z3Context::background_axioms`]), which is EXACTLY the semantics Z3
/// gives `ext(a, b)` (libz3-cross-checked: `a != b && a[k] == b[k]` is UNSAT).
/// Repeated calls on the identical `(a, b)` pair return the identical witness
/// AST with the axiom injected once (matching Z3's hash-consed `ext`).
///
/// SOUNDNESS: the witness is a FRESH constant and the axiom only ADDS a
/// constraint over it, so it can only shrink the model set (never a Z3-unsat →
/// AY-sat flip); and the axiom is satisfiable for every pair (pick any index
/// where the arrays differ, or any index at all when `a = b`), so it introduces
/// no spurious unsat.
///
/// Documented residual divergence (introspection-only): AY's witness is a
/// fresh CONSTANT (`!ay.array-ext!<n>`), not an application of an internal
/// `ext` operator, so `Z3_get_app_decl` on it differs from libz3's node shape.
/// All SAT/UNSAT behavior matches.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_array_ext(c: Z3_context, arg1: Z3_ast, arg2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if arg1 == 0 || arg2 == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_array_ext: null AST argument".to_string());
                return 0;
            }
            let a = require_term_ast_or_return!(ctx, arg1, "Z3_mk_array_ext", "left array", 0);
            let b = require_term_ast_or_return!(ctx, arg2, "Z3_mk_array_ext", "right array", 0);
            // Both arguments must be arrays of the SAME sort (Z3 contract).
            let (public_a, public_b) =
                (public_ast_sort(ctx, arg1, a), public_ast_sort(ctx, arg2, b));
            let Sort::Array(public_array) = &public_a else {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(format!(
                    "Z3_mk_array_ext: expected public Array operands, got {public_a}"
                ));
                return 0;
            };
            if public_a != public_b {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(format!(
                    "Z3_mk_array_ext: public array sorts differ ({public_a} vs {public_b})"
                ));
                return 0;
            }
            let engine_sort = finite_set_engine_public_sort(ctx, &public_a);
            if ctx.solver.sort_of(a) != engine_sort || ctx.solver.sort_of(b) != engine_sort {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(
                    "Z3_mk_array_ext: engine array sort does not match the public signature"
                        .to_string(),
                );
                return 0;
            }
            let index_sort = public_array.index_sort.clone();
            if let Some(&cached) = ctx.array_ext_cache.get(&(a, b)) {
                return cached; // same pair → identical witness (Z3 parity)
            }
            // Fresh witness index, registered so it carries a model value.
            let name = format!("!ay.array-ext!{}", ctx.array_ext_cache.len());
            let engine_index_sort = finite_set_engine_public_sort(ctx, &index_sort);
            let k = ctx.solver.declare_const(&name, engine_index_sort);
            // Background axiom: a != b => select(a,k) != select(b,k).
            let sel_a = ctx.solver.select(a, k);
            let sel_b = ctx.solver.select(b, k);
            let a_eq_b = ctx.solver.eq(a, b);
            let sel_eq = ctx.solver.eq(sel_a, sel_b);
            let a_ne_b = ctx.solver.not(a_eq_b);
            let sel_ne = ctx.solver.not(sel_eq);
            let axiom = ctx.solver.implies(a_ne_b, sel_ne);
            let ast = term_to_ast(ctx, k);
            record_reachable_finite_set_axiom(ctx, k, axiom);
            if sort_mentions_finite_set(ctx, &index_sort) {
                activate_finite_set_sat_gate(ctx, k, "Z3_mk_array_ext");
            }
            record_ast_sort(ctx, ast, index_sort);
            ctx.array_ext_cache.insert((a, b), ast);
            ast
        })
    }
}

// ============================================================================
// Bitvector constructors
// ============================================================================

/// Extract bit `i` of `t1` as a Bool: `(= ((_ extract i i) t1) #b1)`.
///
/// Lowers to the existing `bvextract` + `eq` primitives (analogous to the
/// `Z3_mk_bvcomp` lowering). The result sort is Bool.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bit2bool(c: Z3_context, i: c_uint, t1: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let bv = require_term_ast_or_return!(ctx, t1, "Z3_mk_bit2bool", "bit-vector", 0);
            let width = match ctx.solver.sort_of(bv) {
                Sort::BitVec(bvs) => bvs.width,
                other => {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!(
                        "Z3_mk_bit2bool: expected a bitvector, got {other:?}"
                    ));
                    return 0;
                }
            };
            if i >= width {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_mk_bit2bool: bit index {i} out of range for width {width}"
                ));
                return 0;
            }
            let bit = ctx.solver.bvextract(bv, i, i);
            let one = ctx.solver.bv_const(1, 1);
            let t = ctx.solver.eq(bit, one);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create a bitvector numeral from an explicit `sz`-length bit array.
///
/// Per Z3 convention `bits[0]` is the least-significant bit. Builds the value as
/// a `BigInt` and defers to the existing arbitrary-precision `bv_const_bigint`.
///
/// # Safety
/// `c` must be valid; `bits` must point to `sz` valid `bool` values (`sz >= 1`).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bv_numeral(c: Z3_context, sz: c_uint, bits: *const bool) -> Z3_ast {
    if bits.is_null() {
        return 0;
    }
    // SAFETY: `c` is valid per contract and `ffi_guard_ast` null-checks it and
    // isolates panics. The contract also guarantees that `bits` points to `sz`
    // initialized bools; the validated loop index remains in `0..sz`.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if sz == 0 || sz > MAX_FFI_BITVECTOR_WIDTH {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_mk_bv_numeral: width {sz} is outside the supported range 1..={MAX_FFI_BITVECTOR_WIDTH}"
                ));
                return 0;
            }
            // bits[0] = LSB: accumulate MSB-first so value = Σ bits[i]·2^i.
            let two = BigInt::from(2u32);
            let one = BigInt::from(1u32);
            let mut value = BigInt::from(0u32);
            for i in (0..sz as usize).rev() {
                value *= &two;
                if *bits.add(i) {
                    value += &one;
                }
            }
            let t = ctx.solver.bv_const_bigint(&value, sz);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::bitvec(sz));
            a
        })
    }
}

/// Variable-amount rotate left: rotate `t1` left by `t2 mod width` positions.
///
/// Lowered with existing engine BV primitives:
/// `rot = t2 urem width; (bvshl t1 rot) | (bvlshr t1 (width - rot))`. SMT
/// shift-by-`>= width` = 0 makes the `rot == 0` case correct. Same-width result.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_ext_rotate_left(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe { ext_rotate(c, t1, t2, true) }
}

/// Variable-amount rotate right: mirror of [`Z3_mk_ext_rotate_left`] with the
/// shift directions swapped: `(bvlshr t1 rot) | (bvshl t1 (width - rot))`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_ext_rotate_right(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe { ext_rotate(c, t1, t2, false) }
}

/// Shared variable-amount rotate lowering (see the two public entry points).
///
/// # Safety
/// `c` must be a valid context pointer.
unsafe fn ext_rotate(c: Z3_context, t1: Z3_ast, t2: Z3_ast, left: bool) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let x = require_term_ast_or_return!(ctx, t1, "ext_rotate", "bit-vector", 0);
            let amount = require_term_ast_or_return!(ctx, t2, "ext_rotate", "amount", 0);
            let width = match ctx.solver.sort_of(x) {
                Sort::BitVec(bvs) => bvs.width,
                other => {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg =
                        Some(format!("ext_rotate: expected a bitvector, got {other:?}"));
                    return 0;
                }
            };
            // width fits in `width` bits (2^w > w for w >= 1), so the modulus is
            // representable in the operand width.
            let w_const = ctx.solver.bv_const_u64(u64::from(width), width);
            let rot = ctx.solver.bvurem(amount, w_const);
            let complement = ctx.solver.bvsub(w_const, rot);
            let t = if left {
                let hi = ctx.solver.bvshl(x, rot);
                let lo = ctx.solver.bvlshr(x, complement);
                ctx.solver.bvor(hi, lo)
            } else {
                let lo = ctx.solver.bvlshr(x, rot);
                let hi = ctx.solver.bvshl(x, complement);
                ctx.solver.bvor(lo, hi)
            };
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::bitvec(width));
            a
        })
    }
}

/// Most-significant bit of a bitvector.
///
/// DIVERGENCE: `Z3_mk_bvmsb` is NOT present in the installed `z3_api.h` and is
/// not a known public Z3 C-API function, so its exact return type (Bool vs a
/// 1-bit BV) cannot be verified against upstream. Per this crate's rule — an
/// unverifiable builder diverges rather than guess a possibly ill-sorted term —
/// this sets `Z3_INVALID_ARG` and returns 0 instead of fabricating an
/// `(_ extract w-1 w-1)` term whose sort might mismatch the caller's
/// expectation. (Were the symbol confirmed upstream as a 1-bit-BV MSB extract,
/// the sound lowering is `bvextract(t, w-1, w-1)`.)
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bvmsb(c: Z3_context, t: Z3_ast) -> Z3_ast {
    let _ = t;
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            ctx.last_error = Z3_INVALID_ARG;
            ctx.error_msg = Some(
                "Z3_mk_bvmsb: symbol absent from the installed z3_api.h; return type \
                 unverifiable, so diverged rather than fabricate an ill-sorted term"
                    .to_string(),
            );
            0
        })
    }
}

// ============================================================================
// Arithmetic
// ============================================================================

/// Integer divisibility predicate `t1 | t2`, encoded as `(= (mod t2 t1) 0)`.
///
/// Note the argument order: `divides(t1, t2)` means "t1 divides t2", so the
/// modulus divisor is `t1`. Result sort is Bool.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_divides(c: Z3_context, t1: Z3_ast, t2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let divisor = require_term_ast_or_return!(ctx, t1, "Z3_mk_divides", "divisor", 0);
            let dividend = require_term_ast_or_return!(ctx, t2, "Z3_mk_divides", "dividend", 0);
            let m = ctx.solver.modulo(dividend, divisor);
            let zero = ctx.solver.int_const(0);
            let t = ctx.solver.eq(m, zero);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Create a Real numeral from an exact `num/den` pair of 64-bit integers.
///
/// Uses the exact arbitrary-precision rational builder (the same one backing
/// `Z3_mk_real`), NOT the lossy `f64` path.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_real_int64(c: Z3_context, num: i64, den: i64) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.rational_const(num, den);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Real);
            a
        })
    }
}

// ============================================================================
// Datatype / record / enumeration / list sorts
// ============================================================================

/// Forward-declared datatype sort placeholder (monomorphic).
///
/// For `num_params == 0` this returns an opaque `Sort::Uninterpreted(name)` —
/// exactly how AY models a (recursive) datatype sort before its constructors are
/// attached. The constructors are supplied separately (e.g. via the
/// `Z3_mk_constructor` / `Z3_mk_datatype` workflow).
///
/// DIVERGENCE: `num_params > 0` (a parametric datatype sort) is unsupported —
/// AY's `Sort::Datatype` is monomorphic — so it sets `Z3_INVALID_ARG` and
/// returns null.
///
/// # Safety
/// `c` must be valid; `name` a valid symbol handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_datatype_sort(
    c: Z3_context,
    name: Z3_symbol,
    num_params: c_uint,
    params: *const Z3_sort,
) -> Z3_sort {
    let _ = params;
    // SAFETY: `name` may be null; `read_symbol_key` null-checks it.
    let Some(dt_symbol) = (unsafe { read_symbol_key(name) }) else {
        return ptr::null_mut();
    };
    let dt_name = dt_symbol.semantic_name();
    // SAFETY: `c` valid per contract; `ffi_guard_ptr` null-checks + isolates panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if num_params != 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(
                    "Z3_mk_datatype_sort: parametric datatypes are unsupported (num_params > 0)"
                        .to_string(),
                );
                return ptr::null_mut();
            }
            let sort = Sort::Uninterpreted(dt_name.clone());
            ctx.ffi_sort_symbols.insert(sort.clone(), dt_symbol.clone());
            alloc_sort(ctx, sort)
        })
    }
}

/// Create an enumeration sort (a datatype of `n` nullary constructors) and
/// back-fill the constant/tester func_decls.
///
/// Reuses the `Z3_mk_datatype` machinery: builds a `DatatypeSort` of nullary
/// constructors, declares it, and writes each `enum_consts[i]` (nullary
/// constructor) and `enum_testers[i]` (`is-<name>` recognizer) func_decl.
///
/// # Safety
/// `c` must be valid; `name` a valid symbol; `enum_names` must point to `n`
/// valid symbols; `enum_consts`/`enum_testers`, when non-null, must have room
/// for `n` func_decl slots.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_enumeration_sort(
    c: Z3_context,
    name: Z3_symbol,
    n: c_uint,
    enum_names: *const Z3_symbol,
    enum_consts: *mut Z3_func_decl,
    enum_testers: *mut Z3_func_decl,
) -> Z3_sort {
    let output_arrays =
        c_uint::from(!enum_consts.is_null()) + c_uint::from(!enum_testers.is_null());
    let output_counts = match output_arrays {
        0 => [0, 0],
        1 => [n, 0],
        _ => [n, n],
    };
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe {
        ffi_counts_within_limit(
            c,
            "Z3_mk_enumeration_sort caller arrays",
            &[n, output_counts[0], output_counts[1]],
        )
    } {
        return ptr::null_mut();
    }
    // SAFETY: `name` may be null; `read_symbol_key` null-checks it.
    let Some(dt_symbol) = (unsafe { read_symbol_key(name) }) else {
        return ptr::null_mut();
    };
    let dt_name = dt_symbol.semantic_name();
    if n > 0 && enum_names.is_null() {
        return ptr::null_mut();
    }
    // Pre-extract element names.
    let mut ctors = Vec::with_capacity(n as usize);
    let mut ctor_symbols = Vec::with_capacity(n as usize);
    for i in 0..n as usize {
        // SAFETY: `enum_names` points to `n` elements (checked); `add(i)` in bounds.
        let sym = unsafe { *enum_names.add(i) };
        // SAFETY: `sym` is a valid AY symbol handle (or null -> reject).
        let Some(ctor_symbol) = (unsafe { read_symbol_key(sym) }) else {
            return ptr::null_mut();
        };
        ctors.push(DatatypeConstructor {
            name: ctor_symbol.semantic_name(),
            fields: Vec::new(),
        });
        ctor_symbols.push(ctor_symbol);
    }
    let dt = DatatypeSort {
        name: dt_name,
        constructors: ctors,
    };

    // SAFETY: `c` valid per contract; `ffi_guard_ptr` null-checks + isolates panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let sort_handle = declare_datatype_and_alloc(ctx, &dt, &dt_symbol);
            if sort_handle.is_null() {
                return ptr::null_mut();
            }
            let dt_sort = Sort::Datatype(dt.clone());
            for (i, (ctor, ctor_symbol)) in
                dt.constructors.iter().zip(ctor_symbols.iter()).enumerate()
            {
                let cdecl = make_constructor_decl(ctx, &dt, ctor, &dt_sort, ctor_symbol.clone());
                let tdecl = make_recognizer_decl(
                    ctx,
                    &ctor.name,
                    &dt_sort,
                    SymbolKey::String(format!("is-{}", ctor_symbol.display_name())),
                );
                if !enum_consts.is_null() {
                    // SAFETY: caller guarantees room for `n` slots; `i < n`.
                    // (already in the enclosing unsafe context)
                    *enum_consts.add(i) = cdecl;
                }
                if !enum_testers.is_null() {
                    // SAFETY: caller guarantees room for `n` slots; `i < n`.
                    // (already in the enclosing unsafe context)
                    *enum_testers.add(i) = tdecl;
                }
            }
            sort_handle
        })
    }
}

/// Create a (self-recursive) list sort over `elem_sort` and back-fill the six
/// constructor/tester/accessor func_decls.
///
/// Builds a 2-constructor recursive `DatatypeSort` — `nil` (nullary) and
/// `cons(head: elem_sort, tail: <self>)` — using the same self-reference model
/// (`Sort::Uninterpreted(name)`) as `datatypes.rs`, declares it, and fills the
/// out-pointers.
///
/// # Safety
/// `c` must be valid; `name` a valid symbol; `elem_sort` a valid sort; each
/// non-null out-pointer must be writable.
#[no_mangle]
#[allow(clippy::too_many_arguments)]
pub unsafe extern "C" fn Z3_mk_list_sort(
    c: Z3_context,
    name: Z3_symbol,
    elem_sort: Z3_sort,
    nil_decl: *mut Z3_func_decl,
    is_nil_decl: *mut Z3_func_decl,
    cons_decl: *mut Z3_func_decl,
    is_cons_decl: *mut Z3_func_decl,
    head_decl: *mut Z3_func_decl,
    tail_decl: *mut Z3_func_decl,
) -> Z3_sort {
    if elem_sort.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `name` may be null; `read_symbol_key` null-checks it.
    let Some(dt_symbol) = (unsafe { read_symbol_key(name) }) else {
        return ptr::null_mut();
    };
    let dt_name = dt_symbol.semantic_name();
    // SAFETY: `elem_sort` null-checked above; a valid AY sort handle.
    let elem = unsafe { (*elem_sort).sort.clone() };
    let self_sort = Sort::Uninterpreted(dt_name.clone());

    let dt = DatatypeSort {
        name: dt_name,
        constructors: vec![
            DatatypeConstructor {
                name: "nil".to_string(),
                fields: Vec::new(),
            },
            DatatypeConstructor {
                name: "cons".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "head".to_string(),
                        sort: elem.clone(),
                    },
                    DatatypeField {
                        name: "tail".to_string(),
                        sort: self_sort.clone(),
                    },
                ],
            },
        ],
    };

    // SAFETY: `c` valid per contract; `ffi_guard_ptr` null-checks + isolates panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let sort_handle = declare_datatype_and_alloc(ctx, &dt, &dt_symbol);
            if sort_handle.is_null() {
                return ptr::null_mut();
            }
            let dt_sort = Sort::Datatype(dt.clone());
            let nil = make_constructor_decl(
                ctx,
                &dt,
                &dt.constructors[0],
                &dt_sort,
                SymbolKey::String("nil".to_string()),
            );
            let is_nil = make_recognizer_decl(
                ctx,
                "nil",
                &dt_sort,
                SymbolKey::String("is-nil".to_string()),
            );
            let cons = make_constructor_decl(
                ctx,
                &dt,
                &dt.constructors[1],
                &dt_sort,
                SymbolKey::String("cons".to_string()),
            );
            let is_cons = make_recognizer_decl(
                ctx,
                "cons",
                &dt_sort,
                SymbolKey::String("is-cons".to_string()),
            );
            let head = make_accessor_decl(
                ctx,
                "head",
                elem.clone(),
                &dt_sort,
                SymbolKey::String("head".to_string()),
            );
            let tail = make_accessor_decl(
                ctx,
                "tail",
                self_sort.clone(),
                &dt_sort,
                SymbolKey::String("tail".to_string()),
            );
            // SAFETY: each out-pointer, when non-null, is writable per contract.
            // (already in the enclosing unsafe context)
            {
                if !nil_decl.is_null() {
                    *nil_decl = nil;
                }
                if !is_nil_decl.is_null() {
                    *is_nil_decl = is_nil;
                }
                if !cons_decl.is_null() {
                    *cons_decl = cons;
                }
                if !is_cons_decl.is_null() {
                    *is_cons_decl = is_cons;
                }
                if !head_decl.is_null() {
                    *head_decl = head;
                }
                if !tail_decl.is_null() {
                    *tail_decl = tail;
                }
            }
            sort_handle
        })
    }
}

/// Create a tuple (single-constructor record) sort and back-fill the
/// constructor + projection func_decls.
///
/// A tuple is a one-constructor datatype whose constructor is `mk_tuple_name`
/// and whose fields are `field_names[i] : field_sorts[i]`. Reuses the
/// `Z3_mk_datatype` machinery; the projections are the field accessors.
///
/// # Safety
/// `c` must be valid; `mk_tuple_name` a valid symbol; `field_names`/`field_sorts`
/// must point to `num_fields` valid handles; `mk_tuple_decl` (if non-null) and
/// `proj_decl` (if non-null, room for `num_fields`) must be writable.
#[no_mangle]
#[allow(clippy::too_many_arguments)]
pub unsafe extern "C" fn Z3_mk_tuple_sort(
    c: Z3_context,
    mk_tuple_name: Z3_symbol,
    num_fields: c_uint,
    field_names: *const Z3_symbol,
    field_sorts: *const Z3_sort,
    mk_tuple_decl: *mut Z3_func_decl,
    proj_decl: *mut Z3_func_decl,
) -> Z3_sort {
    let projection_count = if proj_decl.is_null() { 0 } else { num_fields };
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe {
        ffi_counts_within_limit(
            c,
            "Z3_mk_tuple_sort caller arrays",
            &[num_fields, num_fields, projection_count],
        )
    } {
        return ptr::null_mut();
    }
    // SAFETY: `mk_tuple_name` may be null; `read_symbol_key` null-checks it.
    let Some(tuple_symbol) = (unsafe { read_symbol_key(mk_tuple_name) }) else {
        return ptr::null_mut();
    };
    let tuple_name = tuple_symbol.semantic_name();
    if num_fields > 0 && (field_names.is_null() || field_sorts.is_null()) {
        return ptr::null_mut();
    }
    let mut fields = Vec::with_capacity(num_fields as usize);
    let mut field_symbols = Vec::with_capacity(num_fields as usize);
    for i in 0..num_fields as usize {
        // SAFETY: `field_names` points to `num_fields` elems (checked); in bounds.
        let fsym = unsafe { *field_names.add(i) };
        // SAFETY: `fsym` is a valid AY symbol handle (or null -> reject).
        let Some(field_symbol) = (unsafe { read_symbol_key(fsym) }) else {
            return ptr::null_mut();
        };
        // SAFETY: `field_sorts` points to `num_fields` elems (checked); in bounds.
        let fsort_ptr = unsafe { *field_sorts.add(i) };
        if fsort_ptr.is_null() {
            return ptr::null_mut();
        }
        // SAFETY: `fsort_ptr` null-checked; a valid AY sort handle.
        let fsort = unsafe { (*fsort_ptr).sort.clone() };
        fields.push(DatatypeField {
            name: field_symbol.semantic_name(),
            sort: fsort,
        });
        field_symbols.push(field_symbol);
    }
    // The tuple sort and its single constructor share `mk_tuple_name` (Z3
    // convention); sorts and functions live in disjoint namespaces.
    let dt = DatatypeSort {
        name: tuple_name.clone(),
        constructors: vec![DatatypeConstructor {
            name: tuple_name,
            fields,
        }],
    };

    // SAFETY: `c` valid per contract; `ffi_guard_ptr` null-checks + isolates panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let sort_handle = declare_datatype_and_alloc(ctx, &dt, &tuple_symbol);
            if sort_handle.is_null() {
                return ptr::null_mut();
            }
            let dt_sort = Sort::Datatype(dt.clone());
            let ctor = &dt.constructors[0];
            let ctor_decl = make_constructor_decl(ctx, &dt, ctor, &dt_sort, tuple_symbol.clone());
            if !mk_tuple_decl.is_null() {
                // SAFETY: `mk_tuple_decl` non-null and writable per contract.
                // (already in the enclosing unsafe context)
                *mk_tuple_decl = ctor_decl;
            }
            for (i, (field, field_symbol)) in
                ctor.fields.iter().zip(field_symbols.iter()).enumerate()
            {
                let acc = make_accessor_decl(
                    ctx,
                    &field.name,
                    field.sort.clone(),
                    &dt_sort,
                    field_symbol.clone(),
                );
                if !proj_decl.is_null() {
                    // SAFETY: caller guarantees room for `num_fields` slots; `i < num_fields`.
                    // (already in the enclosing unsafe context)
                    *proj_decl.add(i) = acc;
                }
            }
            sort_handle
        })
    }
}

/// Parametric / polymorphic datatype.
///
/// DIVERGENCE: AY has no parametric datatypes — `Sort::Datatype` is monomorphic
/// and type parameters cannot be represented or instantiated. (Monomorphic
/// datatypes work via `Z3_mk_datatype`.) Sets `Z3_INVALID_ARG`, returns null.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_polymorphic_datatype(
    c: Z3_context,
    name: Z3_symbol,
    num_parameters: c_uint,
    parameters: *const Z3_sort,
    num_constructors: c_uint,
    constructors: *mut Z3_constructor,
) -> Z3_sort {
    let _ = (
        name,
        num_parameters,
        parameters,
        num_constructors,
        constructors,
    );
    // SAFETY: `c` valid per contract; `ffi_guard_ptr` null-checks + isolates panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            ctx.last_error = Z3_INVALID_ARG;
            ctx.error_msg = Some(
                "Z3_mk_polymorphic_datatype: parametric datatypes are unsupported".to_string(),
            );
            ptr::null_mut()
        })
    }
}

/// Finite-domain sort of cardinality `size`.
///
/// REAL: creates a [`Sort::FiniteDomain`] whose carrier is `{0, ..., size-1}`.
/// Follows the `Sort::Char` pattern exactly — the value lowers to a bounded
/// `Int` in the engine and every finite-domain-sorted term carries the standing
/// background axiom `0 <= t <= size-1` (see `record_ast_sort`), so a
/// `size+1`-element pigeonhole (`distinct`) is UNSAT exactly as in Z3
/// (libz3-cross-checked). `Z3_get_sort_kind` reports `Z3_FINITE_DOMAIN_SORT`
/// and `Z3_get_finite_domain_sort_size` round-trips `size`.
///
/// `size == 0` is rejected with `Z3_INVALID_ARG` (libz3 4.16 errors with
/// "Domain size of sort ... may not be 0"; SMT sorts are non-empty).
///
/// Documented residual divergence (benign, verdict-safe): because the value
/// lowers to `Int`, AY ACCEPTS arithmetic/comparisons on finite-domain terms
/// (with the natural order on `{0..size-1}`) where libz3 raises a sort
/// mismatch; no program libz3 accepts gets a different verdict.
///
/// # Safety
/// `c` must be a valid context pointer; `name`, when non-null, a valid symbol.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_finite_domain_sort(
    c: Z3_context,
    name: Z3_symbol,
    size: u64,
) -> Z3_sort {
    // SAFETY: `name`, when non-null, is a live `SymbolHandle`; `as_ref` null-checks.
    let sort_symbol = unsafe { name.as_ref() }.map(|handle| handle.key.clone());
    // SAFETY: `c` valid per contract; `ffi_guard_ptr` null-checks + isolates panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(sort_symbol) = sort_symbol.clone() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_finite_domain_sort: null name symbol".to_string());
                return ptr::null_mut();
            };
            let sort_name = sort_symbol.semantic_name();
            if size == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_mk_finite_domain_sort: domain size of sort '{sort_name}' may not be 0"
                ));
                return ptr::null_mut();
            }
            let sort = Sort::FiniteDomain(sort_name, size);
            ctx.ffi_sort_symbols.insert(sort.clone(), sort_symbol);
            alloc_sort(ctx, sort)
        })
    }
}

/// Type variable (polymorphic type parameter).
///
/// REAL: creates a [`Sort::TypeVar`] that round-trips through the sort
/// accessors exactly like libz3 4.16 (`Z3_get_sort_kind` = `Z3_TYPE_VAR`,
/// `Z3_get_sort_name`/`Z3_sort_to_string` = the bare name) and is usable
/// MONOMORPHICALLY in declaration signatures, where it behaves as the
/// uninterpreted sort of the same name.
///
/// Polymorphic INSTANTIATION (#poly-inst): `Z3_mk_app` on a declaration whose
/// signature mentions the variable unifies it against the actual argument
/// sorts and applies a cached monomorphic instance decl (libz3 parity:
/// `f : α → α` at an Int numeral yields an Int-sorted application). A failed
/// unification — the same variable at two different sorts, or a range-only
/// variable no argument determines — stays an honest sort error.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid symbol.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_type_variable(c: Z3_context, s: Z3_symbol) -> Z3_sort {
    // SAFETY: `s`, when non-null, is a live `SymbolHandle`; `as_ref` null-checks.
    let var_symbol = unsafe { s.as_ref() }.map(|handle| handle.key.clone());
    // SAFETY: `c` valid per contract; `ffi_guard_ptr` null-checks + isolates panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(var_symbol) = var_symbol.clone() else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_type_variable: null name symbol".to_string());
                return ptr::null_mut();
            };
            let sort = Sort::TypeVar(var_symbol.semantic_name());
            ctx.ffi_sort_symbols.insert(sort.clone(), var_symbol);
            alloc_sort(ctx, sort)
        })
    }
}

// ============================================================================
// Function declarations
// ============================================================================

/// Declare a fresh uninterpreted function with a unique generated name.
///
/// Same as `Z3_mk_func_decl` but with an FFI-side fresh name
/// (`prefix!<counter>`) instead of a caller-supplied symbol.
///
/// # Safety
/// `c` must be valid; `domain` must point to `domain_size` valid sorts;
/// `range` a valid sort.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_fresh_func_decl(
    c: Z3_context,
    prefix: Z3_string,
    domain_size: c_uint,
    domain: *const Z3_sort,
    range: Z3_sort,
) -> Z3_func_decl {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_fresh_func_decl domain", domain_size) } {
        return ptr::null_mut();
    }
    if range.is_null() {
        return ptr::null_mut();
    }
    if domain_size > 0 && domain.is_null() {
        return ptr::null_mut();
    }
    let pfx = if prefix.is_null() {
        Ok("fresh".to_string())
    } else {
        // SAFETY: caller guarantees `prefix` is a valid null-terminated C string.
        unsafe { ffi_read_bounded_text(prefix) }
    };
    let mut dom_sorts = Vec::with_capacity(domain_size as usize);
    for i in 0..domain_size as usize {
        // SAFETY: `domain` points to `domain_size` elems (checked); in bounds.
        let sp = unsafe { *domain.add(i) };
        if sp.is_null() {
            return ptr::null_mut();
        }
        // SAFETY: `sp` is a valid AY sort handle from a prior alloc.
        dom_sorts.push(unsafe { (*sp).sort.clone() });
    }
    // SAFETY: `range` null-checked above; a valid AY sort handle.
    let range_sort = unsafe { (*range).sort.clone() };

    // SAFETY: `c` valid per contract; `ffi_guard_ptr` null-checks + isolates panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let pfx = match &pfx {
                Ok(pfx) => pfx,
                Err(error) => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!("Z3_mk_fresh_func_decl: {error}"));
                    return ptr::null_mut();
                }
            };
            // Fail-close reserved-namespace capture — see `reserved_name_error`.
            if let Some(msg) = super::reserved_name_error(pfx) {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(msg);
                return ptr::null_mut();
            }
            let (fresh_id, fresh_name) = loop {
                let fresh_id = ctx.next_ffi_fresh_id;
                ctx.next_ffi_fresh_id += 1;
                let candidate = format!("{pfx}!{fresh_id}");
                if ctx.ffi_used_decl_names.insert(candidate.clone()) {
                    break (fresh_id, candidate);
                }
            };
            let semantic_name = format!("!ay.z3-fresh-func!{fresh_id}");
            match ctx
                .solver
                .try_declare_fun(&semantic_name, &dom_sorts, range_sort.clone())
            {
                Ok(decl) => {
                    cache_func_decl_with_symbol(ctx, decl, SymbolKey::String(fresh_name.clone()))
                }
                Err(e) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!("{e}"));
                    ptr::null_mut()
                }
            }
        })
    }
}

/// Declare a recursive-function symbol.
///
/// Before its body is supplied by `Z3_add_rec_def` (a separate call), the
/// symbol is just an uninterpreted function — identical to `Z3_mk_func_decl`.
/// This is a sound over-approximation: with no body attached, the symbol is
/// unconstrained.
///
/// # Safety
/// `c` must be valid; `s` a valid symbol; `domain` must point to `domain_size`
/// valid sorts; `range` a valid sort.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_rec_func_decl(
    c: Z3_context,
    s: Z3_symbol,
    domain_size: c_uint,
    domain: *const Z3_sort,
    range: Z3_sort,
) -> Z3_func_decl {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_rec_func_decl domain", domain_size) } {
        return ptr::null_mut();
    }
    if s.is_null() || range.is_null() {
        return ptr::null_mut();
    }
    if domain_size > 0 && domain.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `s` null-checked above; a valid AY symbol handle.
    let symbol = unsafe { (*s).key.clone() };
    let display_name = symbol.display_name();
    let mut dom_sorts = Vec::with_capacity(domain_size as usize);
    for i in 0..domain_size as usize {
        // SAFETY: `domain` points to `domain_size` elems (checked); in bounds.
        let sp = unsafe { *domain.add(i) };
        if sp.is_null() {
            return ptr::null_mut();
        }
        // SAFETY: `sp` is a valid AY sort handle from a prior alloc.
        dom_sorts.push(unsafe { (*sp).sort.clone() });
    }
    // SAFETY: `range` null-checked above; a valid AY sort handle.
    let range_sort = unsafe { (*range).sort.clone() };

    // SAFETY: `c` valid per contract; `ffi_guard_ptr` null-checks + isolates panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            // Fail-close reserved-namespace capture — see `reserved_name_error`.
            if matches!(&symbol, SymbolKey::String(_)) {
                if let Some(msg) = super::reserved_name_error(&display_name) {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(msg);
                    return ptr::null_mut();
                }
            }
            match ffi_try_declare_function(ctx, &symbol, &dom_sorts, &range_sort) {
                Ok(decl) => {
                    // Record rec-DECLARED-ness: a rec-declared name that never
                    // receives a `Z3_add_rec_def` body must not be surfaced by
                    // the expansion of some OTHER definition's body (z3
                    // answers `unsat` in that window where the plain-UF
                    // reading says `sat`; AY fail-closes — see
                    // `solver::rec_defs_tainted_by_undefined`). Builtin-
                    // conflating names are NOT recorded: they can never be
                    // defined (`Z3_add_rec_def` rejects them) and their
                    // applications ARE the builtin operator.
                    if !ay_dpll::api::rec_def_name_conflates_with_builtin(&display_name) {
                        ctx.rec_declared_names.insert(decl.name().to_string());
                    }
                    ctx.ffi_used_decl_names.insert(display_name.clone());
                    cache_func_decl_with_symbol(ctx, decl, symbol.clone())
                }
                Err(e) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!("{e}"));
                    ptr::null_mut()
                }
            }
        })
    }
}

// ============================================================================
// Quantifiers (dispatch on is_forall to the shared forall/exists builders)
// ============================================================================

/// Create a universal or existential quantifier using de Bruijn indices.
///
/// Dispatches on `is_forall` to the existing `Z3_mk_forall` / `Z3_mk_exists`
/// de-Bruijn implementations (which drive `try_forall`/`try_exists` with
/// triggers). `weight` is a soundly-ignored instantiation-priority hint.
///
/// # Safety
/// All pointers must satisfy the `Z3_mk_forall`/`Z3_mk_exists` contracts.
#[no_mangle]
#[allow(clippy::too_many_arguments)]
pub unsafe extern "C" fn Z3_mk_quantifier(
    c: Z3_context,
    is_forall: bool,
    weight: c_uint,
    num_patterns: c_uint,
    patterns: *const Z3_pattern,
    num_decls: c_uint,
    sorts: *const Z3_sort,
    decl_names: *const Z3_symbol,
    body: Z3_ast,
) -> Z3_ast {
    // SAFETY: forwards the caller's pointers unchanged to the shared builder.
    unsafe {
        mk_quantifier_db(
            c,
            is_forall,
            QuantifierMetadataInput {
                weight,
                quantifier_id: None,
                skolem_id: None,
                no_pattern_asts: &[],
            },
            num_patterns,
            patterns,
            num_decls,
            sorts,
            decl_names,
            body,
        )
    }
}

/// De-Bruijn quantifier with extra E-matching hints.
///
/// Same de-Bruijn path as [`Z3_mk_quantifier`]; `quantifier_id`, `skolem_id`,
/// and `no_patterns` affect instantiation strategy/completeness, never the
/// asserted formula's logical semantics. AY retains them for introspection and
/// rejects hash-cons metadata conflicts fail-closed.
///
/// # Safety
/// All pointers must satisfy the `Z3_mk_forall`/`Z3_mk_exists` contracts.
#[no_mangle]
#[allow(clippy::too_many_arguments)]
pub unsafe extern "C" fn Z3_mk_quantifier_ex(
    c: Z3_context,
    is_forall: bool,
    weight: c_uint,
    quantifier_id: Z3_symbol,
    skolem_id: Z3_symbol,
    num_patterns: c_uint,
    patterns: *const Z3_pattern,
    num_no_patterns: c_uint,
    no_patterns: *const Z3_ast,
    num_decls: c_uint,
    sorts: *const Z3_sort,
    decl_names: *const Z3_symbol,
    body: Z3_ast,
) -> Z3_ast {
    // SAFETY: the bounded pointer copy and symbol reads follow this entry
    // point's caller contract; the shared builder authenticates every AST.
    unsafe {
        if !ffi_count_within_limit(c, "quantifier no-pattern expressions", num_no_patterns) {
            return 0;
        }
        if num_no_patterns > 0 && no_patterns.is_null() {
            return ffi_guard_ast(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("quantifier no-pattern array is null with a nonzero count".to_string());
                0
            });
        }
        let no_pattern_asts = if num_no_patterns == 0 {
            Vec::new()
        } else {
            slice::from_raw_parts(no_patterns, num_no_patterns as usize).to_vec()
        };
        mk_quantifier_db(
            c,
            is_forall,
            QuantifierMetadataInput {
                weight,
                quantifier_id: read_symbol_key(quantifier_id),
                skolem_id: read_symbol_key(skolem_id),
                no_pattern_asts: &no_pattern_asts,
            },
            num_patterns,
            patterns,
            num_decls,
            sorts,
            decl_names,
            body,
        )
    }
}

/// Create a universal or existential quantifier binding a list of constants.
///
/// Dispatches on `is_forall` to the existing `Z3_mk_forall_const` /
/// `Z3_mk_exists_const` (which drive `try_forall`/`try_exists` with triggers).
/// `weight` is a soundly-ignored hint. In AY a `Z3_app` bound constant is a
/// `Z3_ast`, so `bound` is a `*const Z3_ast` (matching `Z3_mk_forall_const`).
///
/// # Safety
/// All pointers must satisfy the `Z3_mk_forall_const`/`Z3_mk_exists_const`
/// contracts.
#[no_mangle]
#[allow(clippy::too_many_arguments)]
pub unsafe extern "C" fn Z3_mk_quantifier_const(
    c: Z3_context,
    is_forall: bool,
    weight: c_uint,
    num_bound: c_uint,
    bound: *const Z3_ast,
    num_patterns: c_uint,
    patterns: *const Z3_pattern,
    body: Z3_ast,
) -> Z3_ast {
    // SAFETY: forwards the caller's pointers unchanged to the shared builder.
    unsafe {
        mk_quantifier_const(
            c,
            is_forall,
            QuantifierMetadataInput {
                weight,
                quantifier_id: None,
                skolem_id: None,
                no_pattern_asts: &[],
            },
            num_bound,
            bound,
            num_patterns,
            patterns,
            body,
        )
    }
}

/// Constant-list quantifier with extra E-matching hints.
///
/// Same const-list path as [`Z3_mk_quantifier_const`]; `quantifier_id`,
/// `skolem_id`, and `no_patterns` are instantiation hints that never change the
/// asserted formula's semantics. AY retains them using the same constant-binder
/// terms as the body and rejects hash-cons metadata conflicts fail-closed.
///
/// # Safety
/// All pointers must satisfy the `Z3_mk_forall_const`/`Z3_mk_exists_const`
/// contracts.
#[no_mangle]
#[allow(clippy::too_many_arguments)]
pub unsafe extern "C" fn Z3_mk_quantifier_const_ex(
    c: Z3_context,
    is_forall: bool,
    weight: c_uint,
    quantifier_id: Z3_symbol,
    skolem_id: Z3_symbol,
    num_bound: c_uint,
    bound: *const Z3_ast,
    num_patterns: c_uint,
    patterns: *const Z3_pattern,
    num_no_patterns: c_uint,
    no_patterns: *const Z3_ast,
    body: Z3_ast,
) -> Z3_ast {
    // SAFETY: the bounded pointer copy and symbol reads follow this entry
    // point's caller contract; the shared builder authenticates every AST.
    unsafe {
        if !ffi_count_within_limit(c, "quantifier no-pattern expressions", num_no_patterns) {
            return 0;
        }
        if num_no_patterns > 0 && no_patterns.is_null() {
            return ffi_guard_ast(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("quantifier no-pattern array is null with a nonzero count".to_string());
                0
            });
        }
        let no_pattern_asts = if num_no_patterns == 0 {
            Vec::new()
        } else {
            slice::from_raw_parts(no_patterns, num_no_patterns as usize).to_vec()
        };
        mk_quantifier_const(
            c,
            is_forall,
            QuantifierMetadataInput {
                weight,
                quantifier_id: read_symbol_key(quantifier_id),
                skolem_id: read_symbol_key(skolem_id),
                no_pattern_asts: &no_pattern_asts,
            },
            num_bound,
            bound,
            num_patterns,
            patterns,
            body,
        )
    }
}

// ============================================================================
// Regular expressions
// ============================================================================

/// Regex difference `re.diff(re1, re2) = re.inter(re1, re.comp(re2))`.
///
/// Composed from the existing `try_re_comp` + `try_re_inter`. Result: RegLan.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_re_diff(c: Z3_context, re1: Z3_ast, re2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let re1 = require_term_ast_or_return!(ctx, re1, "Z3_mk_re_diff", "left regex", 0);
            let re2 = require_term_ast_or_return!(ctx, re2, "Z3_mk_re_diff", "right regex", 0);
            let comp = match ctx.solver.try_re_comp(re2) {
                Ok(t) => t,
                Err(_) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    return 0;
                }
            };
            match ctx.solver.try_re_inter(re1, comp) {
                Ok(t) => {
                    let a = term_to_ast(ctx, t);
                    record_ast_sort(ctx, a, Sort::RegLan);
                    a
                }
                Err(_) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    0
                }
            }
        })
    }
}

/// Regex power `re^n = ((_ re.loop n n) re)` — exactly `n` repetitions.
///
/// Backed by the existing `try_re_loop(re, n, n)`. Result: RegLan.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_re_power(c: Z3_context, re: Z3_ast, n: c_uint) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let re = require_term_ast_or_return!(ctx, re, "Z3_mk_re_power", "regex", 0);
            match ctx.solver.try_re_loop(re, n, n) {
                Ok(t) => {
                    let a = term_to_ast(ctx, t);
                    record_ast_sort(ctx, a, Sort::RegLan);
                    a
                }
                Err(_) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    0
                }
            }
        })
    }
}

// ============================================================================
// String constructors and BV<->string bridges
// ============================================================================

/// Create a String literal from the first `len` bytes of `s` (length-prefixed;
/// may contain embedded NUL).
///
/// The bytes are interpreted as UTF-8 for AY's Rust-backed string model. If the
/// slice is not valid UTF-8 (so it cannot round-trip in AY's string model) this
/// sets `Z3_INVALID_ARG` and returns 0 rather than lossily truncating.
///
/// # Safety
/// `c` must be valid; `s` must point to at least `len` readable bytes (or be
/// null only when `len == 0`).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_lstring(c: Z3_context, len: c_uint, s: Z3_string) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_lstring bytes", len) } {
        return 0;
    }
    if len == 0 {
        // SAFETY: guard null-checks `c`; empty string is the zero-length literal.
        return unsafe {
            ffi_guard_ast(c, |ctx| {
                let t = ctx.solver.string_const("");
                let a = term_to_ast(ctx, t);
                record_ast_sort(ctx, a, Sort::String);
                a
            })
        };
    }
    if s.is_null() {
        return 0;
    }
    // SAFETY: caller guarantees `s` points to at least `len` readable bytes.
    let bytes = unsafe { slice::from_raw_parts(s.cast::<u8>(), len as usize) };
    let value = match std::str::from_utf8(bytes) {
        Ok(v) => v.to_string(),
        Err(_) => {
            // SAFETY: guard null-checks `c`.
            return unsafe {
                ffi_guard_ast(c, |ctx| {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(
                        "Z3_mk_lstring: non-UTF-8 bytes cannot round-trip in AY's string model"
                            .to_string(),
                    );
                    0
                })
            };
        }
    };
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.string_const(&value);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::String);
            a
        })
    }
}

/// Create a String literal from `len` Unicode code points.
///
/// AY strings are Rust strings (Unicode scalar values), so each `chars[i]` must
/// be a valid scalar value (`char::from_u32`). An invalid code point (surrogate
/// or `> 0x10FFFF`) cannot be represented, so this sets `Z3_INVALID_ARG` and
/// returns 0 rather than lossily encoding it.
///
/// # Safety
/// `c` must be valid; `chars` must point to `len` `unsigned` values (or be null
/// only when `len == 0`).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_u32string(
    c: Z3_context,
    len: c_uint,
    chars: *const c_uint,
) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_u32string code points", len) } {
        return 0;
    }
    if len > 0 && chars.is_null() {
        return 0;
    }
    // Pre-extract + validate the code points before entering the guard.
    let mut value = String::with_capacity(len as usize);
    for i in 0..len as usize {
        // SAFETY: `chars` points to `len` elements (checked); `add(i)` in bounds.
        let cp = unsafe { *chars.add(i) };
        match char::from_u32(cp) {
            Some(ch) => value.push(ch),
            None => {
                // SAFETY: guard null-checks `c`.
                return unsafe {
                    ffi_guard_ast(c, |ctx| {
                        ctx.last_error = Z3_INVALID_ARG;
                        ctx.error_msg = Some(format!(
                            "Z3_mk_u32string: code point {cp:#x} is not a valid Unicode scalar value"
                        ));
                        0
                    })
                };
            }
        }
    }
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let t = ctx.solver.string_const(&value);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::String);
            a
        })
    }
}

/// Unsigned bitvector-to-decimal-string (`ubv.to_str`).
///
/// Backed by `try_bv_to_string`. On a non-BV operand sets `Z3_SORT_ERROR` and
/// returns 0. Result: String.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_ubv_to_str(c: Z3_context, s: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let s = require_term_ast_or_return!(ctx, s, "Z3_mk_ubv_to_str", "bit-vector", 0);
            match ctx.solver.try_bv_to_string(s) {
                Ok(t) => {
                    let a = term_to_ast(ctx, t);
                    record_ast_sort(ctx, a, Sort::String);
                    a
                }
                Err(_) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    0
                }
            }
        })
    }
}

/// Signed bitvector-to-decimal-string (`sbv.to_str`).
///
/// Backed by `try_bv_to_string_signed`. On a non-BV operand sets
/// `Z3_SORT_ERROR` and returns 0. Result: String.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_sbv_to_str(c: Z3_context, s: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let s = require_term_ast_or_return!(ctx, s, "Z3_mk_sbv_to_str", "bit-vector", 0);
            match ctx.solver.try_bv_to_string_signed(s) {
                Ok(t) => {
                    let a = term_to_ast(ctx, t);
                    record_ast_sort(ctx, a, Sort::String);
                    a
                }
                Err(_) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    0
                }
            }
        })
    }
}

/// Replace every occurrence of `src` in `s` with `dst` (`seq.replace_all`).
///
/// AY's replace-all is string-backed, so this requires String operands (backed
/// by `try_str_replace_all`). A non-String (general `Seq`) operand sets
/// `Z3_SORT_ERROR` and returns 0.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_replace_all(
    c: Z3_context,
    s: Z3_ast,
    src: Z3_ast,
    dst: Z3_ast,
) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let s = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_replace_all", "sequence", 0);
            let src = require_term_ast_or_return!(ctx, src, "Z3_mk_seq_replace_all", "source", 0);
            let dst =
                require_term_ast_or_return!(ctx, dst, "Z3_mk_seq_replace_all", "replacement", 0);
            match ctx.solver.try_str_replace_all(s, src, dst) {
                Ok(t) => {
                    let a = term_to_ast(ctx, t);
                    record_ast_sort(ctx, a, Sort::String);
                    a
                }
                Err(_) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(
                        "Z3_mk_seq_replace_all: only String operands are supported (AY seq \
                         replace-all is string-backed)"
                            .to_string(),
                    );
                    0
                }
            }
        })
    }
}

// ============================================================================
// Sets
// ============================================================================

/// Set subset predicate `(subset arg1 arg2)`, returning Bool.
///
/// A set is `(Array elem Bool)`. This uses the quantifier-free-in-spirit
/// encoding `forall x. (=> (select arg1 x) (select arg2 x))` over a fresh
/// index-sorted bound variable, using only existing engine primitives
/// (`select` / `implies` / `try_forall`). Unlike the other set ops (which return
/// arrays), subset is a predicate and returns Bool.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_set_subset(c: Z3_context, arg1: Z3_ast, arg2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let a = require_term_ast_or_return!(ctx, arg1, "Z3_mk_set_subset", "left set", 0);
            let b = require_term_ast_or_return!(ctx, arg2, "Z3_mk_set_subset", "right set", 0);
            let left_public = public_ast_sort(ctx, arg1, a);
            let right_public = public_ast_sort(ctx, arg2, b);
            let elem_sort = match &left_public {
                Sort::Array(arr)
                    if arr.element_sort == Sort::Bool && right_public == left_public =>
                {
                    match ctx.solver.sort_of(a) {
                        Sort::Array(engine_array) => engine_array.index_sort,
                        _ => {
                            ctx.last_error = Z3_SORT_ERROR;
                            ctx.error_msg =
                                Some("Z3_mk_set_subset: malformed lowered set backing".to_string());
                            return 0;
                        }
                    }
                }
                other => {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!(
                        "Z3_mk_set_subset: expected equal public legacy set sorts, got \
                         {other:?} and {right_public:?}"
                    ));
                    return 0;
                }
            };
            // Fresh, internally-named bound index variable (double-underscore
            // prefix avoids collision with user constants in the operands).
            let var_name = format!("__subset_idx!{}", ctx.ast_sorts.len());
            let x = ctx.solver.declare_const(&var_name, elem_sort);
            let in_a = ctx.solver.select(a, x);
            let in_b = ctx.solver.select(b, x);
            let body = ctx.solver.implies(in_a, in_b);
            match ctx.solver.try_forall(&[x], body) {
                Ok(t) => {
                    let out = term_to_ast(ctx, t);
                    record_ast_sort(ctx, out, Sort::Bool);
                    out
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
// Solvers
// ============================================================================

/// Create a "simple" solver.
///
/// In libz3 the only difference from `Z3_mk_solver` is a non-incremental tactic
/// default; AY's solver is uniform, so this aliases `Z3_mk_solver` (the
/// non-incremental-default nuance is not distinguished in AY).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_simple_solver(c: Z3_context) -> Z3_solver {
    // SAFETY: delegates to `Z3_mk_solver` under the same caller contract on `c`.
    unsafe { Z3_mk_solver(c) }
}

// ============================================================================
// Char theory — real over AY's bounded-Int code-point model
// ============================================================================
//
// AY models a character as an `Int` code point over the exact SMT-LIB Unicode
// alphabet `[0, 196607]` (`= 0x2FFFF = Z3's max_char`) — the same model AY's
// string theory already uses for `str.to_code`/`str.from_code`/`str.is_digit`.
// `Sort::Char` lowers to a single bounded `Int` (`Sort::as_term_sort` maps
// `Char → Int`), and every `Char`-sorted term carries the standing invariant
// `0 <= x <= 196607` as a background axiom (wired in `record_ast_sort` →
// `emit_char_range_axiom`). The sort/le/to_int/is_digit constructors are REAL
// and exact against that model, and so are the two BV bridges: the char
// bit-width is 18, pinned empirically against libz3 4.16.0 (see
// [`AY_CHAR_BV_WIDTH`]), so `char.to_bv` is `int2bv(code, 18)` and
// `char.from_bv` is the width-checked `bv2int` re-recorded at sort `Char`.

/// Create the character sort (Z3's `Z3_mk_char_sort`).
///
/// REAL: a fresh [`Sort::Char`] (`Z3_get_sort_kind` reports `Z3_CHAR_SORT`,
/// `Z3_is_char_sort` is true). It lowers to a bounded `Int` code point in the
/// engine; a `Char`-sorted constant automatically carries `0 <= x <= 196607`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_char_sort(c: Z3_context) -> Z3_sort {
    // SAFETY: `c` valid per contract; `ffi_guard_ptr` null-checks + isolates panics.
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, Sort::Char)) }
}

/// Create a character literal from a code point (Z3's `Z3_mk_char`).
///
/// REAL/exact: validates `ch <= 196607` (matching Z3's `max_char` check; else
/// `Z3_INVALID_ARG`, 0) and builds an `Int`-code-point literal recorded with sort
/// `Char`. In range by construction.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_char(c: Z3_context, ch: c_uint) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if i64::from(ch) > AY_MAX_CHAR {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_mk_char: code point {ch} exceeds max_char ({AY_MAX_CHAR})"
                ));
                return 0;
            }
            let t = ctx.solver.int_const(i64::from(ch));
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Char);
            a
        })
    }
}

/// Character `<=` on code points (Z3's `Z3_mk_char_le`); result Bool.
///
/// REAL/exact: `Int` order on the underlying code points IS Unicode code-point
/// order, matching Z3.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_char_le(c: Z3_context, ch1: Z3_ast, ch2: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let ch1 = require_term_ast_or_return!(ctx, ch1, "Z3_mk_char_le", "left character", 0);
            let ch2 = require_term_ast_or_return!(ctx, ch2, "Z3_mk_char_le", "right character", 0);
            let t = ctx.solver.le(ch1, ch2);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Coerce a character to its `Int` code point (Z3's `Z3_mk_char_to_int`).
///
/// REAL/exact: a genuine `Char` is a length-1 code point, so the coercion is the
/// IDENTITY on the underlying `Int` term — returns the same core term, now
/// reported as `Int`. (Deliberately NOT routed through `str.to_code`, which
/// yields `-1` for non-length-1 strings; a `Char` is never that case.)
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_char_to_int(c: Z3_context, ch: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let _ = require_term_ast_or_return!(ctx, ch, "Z3_mk_char_to_int", "character", 0);
            // The underlying term IS the code point; re-report it as Int. (The
            // Char range invariant for `ch` was already emitted when `ch` was
            // built, so the resulting Int inherits `0 <= . <= 196607`.)
            record_ast_sort(ctx, ch, Sort::Int);
            ch
        })
    }
}

/// Character digit test (Z3's `Z3_mk_char_is_digit`): `(and (<= 48 x)(<= x 57))`;
/// result Bool.
///
/// REAL/exact: agrees with AY's `str.is_digit` (ASCII `'0'..'9'` = code points
/// 48..57).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_char_is_digit(c: Z3_context, ch: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let x = require_term_ast_or_return!(ctx, ch, "Z3_mk_char_is_digit", "character", 0);
            let lo = ctx.solver.int_const(48);
            let hi = ctx.solver.int_const(57);
            let ge = ctx.solver.le(lo, x);
            let le = ctx.solver.le(x, hi);
            let t = ctx.solver.and_many(&[ge, le]);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Z3's char bit-vector width `W` (its internal `zstring::num_bits`), pinned
/// EMPIRICALLY against libz3 4.16.0 (2026-07-09): `Z3_mk_char_to_bv` on a char
/// literal yields a `(_ BitVec 18)` term, and `Z3_mk_char_from_bv` rejects any
/// other width with "expected bit-vector sort argument with 18". `2^18 =
/// 262144 > 196607 = max_char`, so every code point is exactly representable.
pub(crate) const AY_CHAR_BV_WIDTH: u32 = 18;

/// Char → BV (Z3's `Z3_mk_char_to_bv`).
///
/// REAL/exact: semantically `int2bv(code_point, 18)` — the width is libz3's
/// probed char bit-width [`AY_CHAR_BV_WIDTH`]. A `Char` code point is
/// `<= 196607 < 2^18`, so the conversion is lossless and agrees with libz3 on
/// every probe: `to_bv(c) = 65` is SAT with `c = 65`, `to_bv(c) = 196608` is
/// UNSAT, and `from_bv(to_bv(c)) = c` is valid (both libs, 2026-07-09).
///
/// ENCODING (a raw `int2bv` over a symbolic Int is outside the engine's
/// decidable fragment, so the lowering avoids it):
///
///   * a LITERAL char (the overwhelmingly common case, and libz3's own probe
///     case) folds to the exact BV18 literal — pure constant evaluation,
///     decidable everywhere;
///   * a SYMBOLIC char yields — like the `Z3_mk_array_ext` witness — a cached
///     fresh BV18 constant `v` pinned by the background axioms
///     `bv2int(v) = code` and `bvule v 196607` (the BV-side image bound, so
///     range violations refute inside the pure BV lane). Since `bv2int` is a
///     bijection from BV18 onto `[0, 2^18)` and the code point lies in that
///     range, `v` is UNIQUELY the bit-vector Z3 returns — an exact encoding,
///     not an approximation (the model's extra internal `!ay.char2bv!`
///     constant is an introspection-shape difference only). Repeated calls on
///     the same char term return the identical witness, and ground pairwise
///     injectivity lemmas (`bv2int(v_i) = bv2int(v_j) ⇒ v_i = v_j`) keep the
///     bridge congruent. HONEST INCOMPLETENESS: queries that force a BV-side
///     constraint on `v` back through the bridge onto a SYMBOLIC code point
///     (e.g. `to_bv(c) = lit` for free `c`) sit in the engine's mixed BV+LIA
///     combination, which currently reports `unknown` — never a wrong
///     verdict (libz3 decides these; documented residual gap).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_char_to_bv(c: Z3_context, ch: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if ch == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_char_to_bv: null AST argument".to_string());
                return 0;
            }
            // The underlying Char term IS the Int code point (in `[0, 196607]`
            // by the standing Char range invariant).
            let code = require_term_ast_or_return!(ctx, ch, "Z3_mk_char_to_bv", "character", 0);
            // Literal char → exact BV literal (int2bv of a constant, folded).
            if ctx.solver.is_numeral(code) {
                if let Some(value) = ctx
                    .solver
                    .numeral_string(code)
                    .and_then(|s| s.parse::<i64>().ok())
                    .filter(|v| (0..=AY_MAX_CHAR).contains(v))
                {
                    let t = ctx.solver.bv_const(value, AY_CHAR_BV_WIDTH);
                    let a = term_to_ast(ctx, t);
                    record_ast_sort(ctx, a, Sort::bitvec(AY_CHAR_BV_WIDTH));
                    return a;
                }
            }
            if let Some(&cached) = ctx.char_to_bv_cache.get(&code) {
                return cached; // identical term per char term (Z3 hash-consing parity)
            }
            let old_witness_asts: Vec<Z3_ast> = ctx.char_to_bv_cache.values().copied().collect();
            let old_witnesses = require_term_asts_or_return!(
                ctx,
                &old_witness_asts,
                "Z3_mk_char_to_bv cached witnesses",
                0
            );
            let name = format!("!ay.char2bv!{}", ctx.char_to_bv_cache.len());
            let v = ctx
                .solver
                .declare_const(&name, Sort::bitvec(AY_CHAR_BV_WIDTH));
            let b2i = ctx.solver.bv2int(v);
            let link = ctx.solver.eq(b2i, code);
            ctx.background_axioms.push(link);
            // BV-side image bound: every char code point is <= 196607, so the
            // witness obeys `bvule v 196607` — refutable inside the BV lane
            // without bridge reasoning (e.g. `to_bv(c) = 196608` is UNSAT).
            let max_bv = ctx.solver.bv_const(AY_MAX_CHAR, AY_CHAR_BV_WIDTH);
            let ule = ctx.solver.bvule(v, max_bv);
            ctx.background_axioms.push(ule);
            // Ground injectivity lemmas against the earlier witnesses: true of
            // real `int2bv` semantics (bv2int is injective per width), so they
            // only pin the intended model — never a fabricated constraint.
            for old in old_witnesses {
                let old_b2i = ctx.solver.bv2int(old);
                let eq_codes = ctx.solver.eq(b2i, old_b2i);
                let eq_bvs = ctx.solver.eq(v, old);
                let imp = ctx.solver.implies(eq_codes, eq_bvs);
                ctx.background_axioms.push(imp);
            }
            ctx.clear_decision_check_artifacts();
            let a = term_to_ast(ctx, v);
            record_ast_sort(ctx, a, Sort::bitvec(AY_CHAR_BV_WIDTH));
            ctx.char_to_bv_cache.insert(code, a);
            a
        })
    }
}

/// Char ← BV (Z3's `Z3_mk_char_from_bv`).
///
/// REAL: requires a `(_ BitVec 18)` argument (libz3 rejects every other width
/// with "expected bit-vector sort argument with 18"; so does AY, as
/// `Z3_SORT_ERROR`). The result is the `Char` whose code point is `bv2int(bv)`;
/// recording it at sort `Char` emits the standing `0 <= code <= 196607` range
/// invariant, which makes an out-of-range bit-vector (`196608..2^18-1`)
/// INFEASIBLE.
///
/// That matches libz3 4.16.0's own char theory wherever it actually engages
/// (all probed 2026-07-09): `to_int(from_bv(b)) != bv2int(b) ∧ b <= 196607` is
/// UNSAT (in-range identity), `to_int(from_bv(b)) > 196607` is UNSAT,
/// `to_bv(from_bv(b)) != b` is UNSAT, and every equality/order/to_int query
/// that pins `b > 196607` is UNSAT. libz3's residual out-of-range behavior is
/// DEGENERATE, not a semantics: on `b > 196607 ∧ c = from_bv(b)` it answers
/// "sat" with the UNEVALUATED term `(char.from_bv 196608)` as the "value" of
/// `c` (an incompleteness artifact its own engaged queries contradict), and
/// literal-folding paths abort with "UNEXPECTED CODE WAS REACHED"
/// (rewriter_def.h:226). AY replicates the engaged semantics — the only
/// consistent one — and never the artifact.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_char_from_bv(c: Z3_context, bv: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if bv == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_char_from_bv: null AST argument".to_string());
                return 0;
            }
            let b = require_term_ast_or_return!(ctx, bv, "Z3_mk_char_from_bv", "bit-vector", 0);
            match ctx.solver.sort_of(b) {
                Sort::BitVec(bvs) if bvs.width == AY_CHAR_BV_WIDTH => {}
                other => {
                    // libz3's exact rejection message for a wrong-width argument.
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!(
                        "Z3_mk_char_from_bv: expected bit-vector sort argument with \
                         {AY_CHAR_BV_WIDTH} (got {other:?})"
                    ));
                    return 0;
                }
            }
            let t = ctx.solver.bv2int(b);
            let a = term_to_ast(ctx, t);
            // Sort `Char` ⇒ the standing `0 <= code <= 196607` range invariant
            // is emitted (see `record_ast_sort`), making out-of-range BVs
            // infeasible — libz3's engaged char-theory semantics.
            record_ast_sort(ctx, a, Sort::Char);
            a
        })
    }
}

// ============================================================================
// Special relations — real orders over a fresh axiomatized predicate
// ============================================================================
//
// Each ORDER constructor declares a FRESH binary predicate `R : a*a -> Bool` and
// asserts the exact first-order property axioms for that order kind
// (reflexive/antisymmetric/transitive + total/tree/piecewise) as context-global
// background axioms (see `Z3Context::background_axioms`), then hands back the REAL
// `R` func_decl. AY's quantifier engine (E-matching/MBQI/CEGQI) discharges the
// axioms, so an order query gets a genuine SAT/UNSAT verdict.
//
// SOUNDNESS: the axioms are pure universally-quantified constraints over a FRESH
// symbol, so they can only SHRINK the model set — they can NEVER flip a Z3-unsat
// into an AY-sat. The axiom sets are transcribed to match Z3's
// special_relations_decl_plugin EXACTLY (verified against libz3 4.16.0), so AY is
// never STRICTER than Z3 either (no spurious unsat). Repeated calls with the same
// `(kind, sort, id)` return the identical cached decl (axioms injected once).
//
// `Z3_mk_transitive_closure` is REAL via the same fresh-predicate pattern
// PLUS a model-check gate: a least fixed point is not finitely first-order
// axiomatizable, so its background axioms alone only make UNSAT sound; SAT is
// released by `check_solver_handle` only after the model's TC table is
// verified (Warshall) to equal the reflexive-transitive closure of the
// model's R table.

/// Special-relation order kind. The numeric tag is the `background_axioms` /
/// `special_relation_cache` key discriminator and selects which extra axioms
/// (beyond the shared partial-order core) are emitted.
#[derive(Clone, Copy)]
enum SrKind {
    Partial = 0,
    Linear = 1,
    Tree = 2,
    Piecewise = 3,
}

/// Build the exact property axioms for `kind` over the fresh predicate `r`
/// (`a*a -> Bool`) as universally-quantified `Term`s. The bound variables are
/// UNREGISTERED fresh vars (`fresh_var`), so they never leak into a model.
///
/// Axiom sets (verified against libz3 4.16.0's special_relations plugin):
///   * partial  = refl + antisym + trans
///   * linear   = partial + total
///   * tree     = partial + lefttree (down-set of any node is linearly ordered)
///   * piecewise= partial + lefttree + righttree (up-set also linearly ordered)
fn build_order_axioms(
    ctx: &mut Z3Context,
    r: &FuncDecl,
    sort: &Sort,
    kind: SrKind,
) -> Result<Vec<Term>, String> {
    let x = ctx.solver.fresh_var("z3_sr_x", sort.clone());
    let y = ctx.solver.fresh_var("z3_sr_y", sort.clone());
    let z = ctx.solver.fresh_var("z3_sr_z", sort.clone());
    let mut axioms: Vec<Term> = Vec::new();

    // Reflexivity: forall x. R(x,x)
    {
        let rxx = ctx.solver.apply(r, &[x, x]);
        axioms.push(
            ctx.solver
                .try_forall(&[x], rxx)
                .map_err(|e| format!("{e}"))?,
        );
    }
    // Antisymmetry: forall x,y. (R(x,y) & R(y,x)) => x=y
    {
        let rxy = ctx.solver.apply(r, &[x, y]);
        let ryx = ctx.solver.apply(r, &[y, x]);
        let both = ctx.solver.and_many(&[rxy, ryx]);
        let xeqy = ctx.solver.eq(x, y);
        let imp = ctx.solver.implies(both, xeqy);
        axioms.push(
            ctx.solver
                .try_forall(&[x, y], imp)
                .map_err(|e| format!("{e}"))?,
        );
    }
    // Transitivity: forall x,y,z. (R(x,y) & R(y,z)) => R(x,z)
    {
        let rxy = ctx.solver.apply(r, &[x, y]);
        let ryz = ctx.solver.apply(r, &[y, z]);
        let both = ctx.solver.and_many(&[rxy, ryz]);
        let rxz = ctx.solver.apply(r, &[x, z]);
        let imp = ctx.solver.implies(both, rxz);
        axioms.push(
            ctx.solver
                .try_forall(&[x, y, z], imp)
                .map_err(|e| format!("{e}"))?,
        );
    }
    // Totality (linear only): forall x,y. R(x,y) | R(y,x)
    if matches!(kind, SrKind::Linear) {
        let rxy = ctx.solver.apply(r, &[x, y]);
        let ryx = ctx.solver.apply(r, &[y, x]);
        let tot = ctx.solver.or_many(&[rxy, ryx]);
        axioms.push(
            ctx.solver
                .try_forall(&[x, y], tot)
                .map_err(|e| format!("{e}"))?,
        );
    }
    // Lefttree (tree + piecewise): the down-set of any node is linearly ordered.
    // forall x,y,z. (R(y,x) & R(z,x)) => (R(y,z) | R(z,y))
    if matches!(kind, SrKind::Tree | SrKind::Piecewise) {
        let ryx = ctx.solver.apply(r, &[y, x]);
        let rzx = ctx.solver.apply(r, &[z, x]);
        let both = ctx.solver.and_many(&[ryx, rzx]);
        let ryz = ctx.solver.apply(r, &[y, z]);
        let rzy = ctx.solver.apply(r, &[z, y]);
        let cmp = ctx.solver.or_many(&[ryz, rzy]);
        let imp = ctx.solver.implies(both, cmp);
        axioms.push(
            ctx.solver
                .try_forall(&[x, y, z], imp)
                .map_err(|e| format!("{e}"))?,
        );
    }
    // Righttree (piecewise only): the up-set of any node is linearly ordered.
    // forall x,y,z. (R(x,y) & R(x,z)) => (R(y,z) | R(z,y))
    if matches!(kind, SrKind::Piecewise) {
        let rxy = ctx.solver.apply(r, &[x, y]);
        let rxz = ctx.solver.apply(r, &[x, z]);
        let both = ctx.solver.and_many(&[rxy, rxz]);
        let ryz = ctx.solver.apply(r, &[y, z]);
        let rzy = ctx.solver.apply(r, &[z, y]);
        let cmp = ctx.solver.or_many(&[ryz, rzy]);
        let imp = ctx.solver.implies(both, cmp);
        axioms.push(
            ctx.solver
                .try_forall(&[x, y, z], imp)
                .map_err(|e| format!("{e}"))?,
        );
    }
    Ok(axioms)
}

/// Shared implementation for the four order constructors: declare (or reuse) the
/// fresh predicate `R` for `(kind, sort, id)`, inject its property axioms, and
/// return the REAL func_decl.
///
/// # Safety
/// `c` must be a valid context pointer; `a`, when non-null, a valid sort handle.
unsafe fn mk_special_order(
    c: Z3_context,
    a: Z3_sort,
    id: c_uint,
    kind: SrKind,
    fn_name: &'static str,
) -> Z3_func_decl {
    if a.is_null() {
        // SAFETY: `c` valid per contract; guard null-checks + isolates panics.
        unsafe {
            return ffi_guard_ptr(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!("{fn_name}: null domain sort"));
                ptr::null_mut()
            });
        }
    }
    // SAFETY: `a` null-checked; a valid AY sort handle (single-threaded per context).
    let sort = unsafe { (*a).sort.clone() };
    // SAFETY: `c` valid per contract; `ffi_guard_ptr` null-checks + isolates panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let tag = kind as u8;
            let key = (tag, sort.clone(), id);
            if let Some(&cached) = ctx.special_relation_cache.get(&key) {
                return cached; // Z3 parity: same (kind,sort,id) → same decl.
            }
            // Fresh, unique predicate name (one per distinct (kind, sort, id)).
            // The leading `!` keeps it collision-unlikely with user symbols while
            // still being an accepted (non-`__ay_`-reserved) declaration name.
            let rel_name = format!("!ay.order!{}", ctx.special_relation_cache.len());
            let decl = match ctx.solver.try_declare_fun(
                &rel_name,
                &[sort.clone(), sort.clone()],
                Sort::Bool,
            ) {
                Ok(d) => d,
                Err(e) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!("{fn_name}: {e}"));
                    return ptr::null_mut();
                }
            };
            // Build + inject the property axioms (before moving `decl`).
            match build_order_axioms(ctx, &decl, &sort, kind) {
                Ok(axioms) => ctx.background_axioms.extend(axioms),
                Err(e) => {
                    ctx.last_error = Z3_SORT_ERROR;
                    ctx.error_msg = Some(format!("{fn_name}: {e}"));
                    return ptr::null_mut();
                }
            }
            let handle = cache_func_decl(ctx, decl);
            ctx.special_relation_cache.insert(key, handle);
            handle
        })
    }
}

/// Linear (total) order relation over sort `a` (Z3's `Z3_mk_linear_order`).
///
/// REAL: reflexive + antisymmetric + transitive + total, over a fresh predicate.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_linear_order(c: Z3_context, a: Z3_sort, id: c_uint) -> Z3_func_decl {
    // SAFETY: forwards the caller's contract to the shared builder.
    unsafe { mk_special_order(c, a, id, SrKind::Linear, "Z3_mk_linear_order") }
}

/// Partial order relation over sort `a` (Z3's `Z3_mk_partial_order`).
///
/// REAL: reflexive + antisymmetric + transitive, over a fresh predicate.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_partial_order(
    c: Z3_context,
    a: Z3_sort,
    id: c_uint,
) -> Z3_func_decl {
    // SAFETY: forwards the caller's contract to the shared builder.
    unsafe { mk_special_order(c, a, id, SrKind::Partial, "Z3_mk_partial_order") }
}

/// Piecewise-linear order relation over sort `a` (Z3's
/// `Z3_mk_piecewise_linear_order`).
///
/// REAL: partial order + both the down-set and up-set of every node linearly
/// ordered. Axioms verified against libz3 4.16.0.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_piecewise_linear_order(
    c: Z3_context,
    a: Z3_sort,
    id: c_uint,
) -> Z3_func_decl {
    // SAFETY: forwards the caller's contract to the shared builder.
    unsafe { mk_special_order(c, a, id, SrKind::Piecewise, "Z3_mk_piecewise_linear_order") }
}

/// Tree order relation over sort `a` (Z3's `Z3_mk_tree_order`).
///
/// REAL: partial order + the down-set (ancestors) of every node linearly ordered.
/// Axioms verified against libz3 4.16.0.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_tree_order(c: Z3_context, a: Z3_sort, id: c_uint) -> Z3_func_decl {
    // SAFETY: forwards the caller's contract to the shared builder.
    unsafe { mk_special_order(c, a, id, SrKind::Tree, "Z3_mk_tree_order") }
}

/// Transitive closure of `f` (Z3's `Z3_mk_transitive_closure`).
///
/// REAL, model-check-gated. libz3 4.16.0's semantics (probed 2026-07-09) is
/// the REFLEXIVE-transitive closure — `¬TC(a,a)` is UNSAT with no `R` facts,
/// and its own model prints `TC = (or connected(..) (= (:var 0) (:var 1)))` —
/// with least-fixed-point minimality (`∀xy. R(x,y) ⇔ (x=a ∧ y=b)` makes
/// `TC(b,a)` UNSAT). AY implements it as:
///
///   * a FRESH binary predicate `TC` (cached per underlying relation, so a
///     repeated call returns the identical decl — libz3 parity), plus
///   * the SOUND partial background axioms `∀x. TC(x,x)`,
///     `∀xy. R(x,y) ⇒ TC(x,y)`, `∀xyz. TC(x,y) ∧ TC(y,z) ⇒ TC(x,z)`. Every
///     true RTC model satisfies them, so UNSAT verdicts are sound on their
///     own. They also admit over-approximations (`TC ⊋ RTC(R)`) — a least
///     fixed point is not finitely FO-axiomatizable — so
///   * `Z3_solver_check` GATES SAT (see `verify_transitive_closure_model`):
///     a SAT verdict on this context is only released after the model's `TC`
///     table is verified — by Warshall over the model's enumerable universe —
///     to BE the reflexive-transitive closure of the model's `R` table;
///     otherwise the check honestly reports unknown. SAT is never fabricated.
///
/// Argument validation mirrors libz3's classes: a decl whose two domain sorts
/// are missing or unequal is rejected ("argument sort mismatch..."), a
/// non-Bool range is rejected ("tc relation should be Boolean"); both as
/// `Z3_SORT_ERROR` + null.
///
/// # Safety
/// `c` must be a valid context pointer; `f`, when non-null, a valid decl handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_transitive_closure(c: Z3_context, f: Z3_func_decl) -> Z3_func_decl {
    // SAFETY: `f`, when non-null, is a live decl handle owned by the context
    // arena; `as_ref` null-checks (single-threaded per context).
    let decl = unsafe { f.as_ref() }.map(|h| h.decl.clone());
    // SAFETY: `c` valid per contract; `ffi_guard_ptr` null-checks + isolates panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let refuse = |ctx: &mut Z3Context, code: c_uint, msg: &str| {
                ctx.last_error = code;
                ctx.error_msg = Some(format!("Z3_mk_transitive_closure: {msg}"));
                ptr::null_mut()
            };
            let Some(decl) = decl.clone() else {
                return refuse(ctx, Z3_INVALID_ARG, "null func_decl argument");
            };
            // libz3's validation classes: equal binary domain, Bool range.
            let dom = decl.domain();
            if dom.len() != 2 || dom[0] != dom[1] {
                return refuse(
                    ctx,
                    Z3_SORT_ERROR,
                    "argument sort mismatch. The two arguments should have the same sort",
                );
            }
            if *decl.range() != Sort::Bool {
                return refuse(ctx, Z3_SORT_ERROR, "tc relation should be Boolean");
            }
            let domain = dom[0].clone();
            // Same relation ⇒ same TC decl (libz3 returns the identical decl).
            if let Some(reg) = ctx
                .transitive_closure_regs
                .iter()
                .find(|r| r.rel_name == decl.name() && r.domain == domain)
            {
                return reg.handle;
            }
            let tc_name = format!("!ay.tc!{}", ctx.transitive_closure_regs.len());
            let tc_decl = match ctx.solver.try_declare_fun(
                &tc_name,
                &[domain.clone(), domain.clone()],
                Sort::Bool,
            ) {
                Ok(d) => d,
                Err(e) => return refuse(ctx, Z3_SORT_ERROR, &format!("{e}")),
            };
            match build_transitive_closure_axioms(ctx, &decl, &tc_decl, &domain) {
                Ok(axioms) => ctx.background_axioms.extend(axioms),
                Err(e) => return refuse(ctx, Z3_SORT_ERROR, &e),
            }
            let handle = cache_func_decl(ctx, tc_decl);
            ctx.transitive_closure_regs.push(super::TcRegistration {
                tc_name,
                rel_name: decl.name().to_string(),
                domain,
                handle,
            });
            handle
        })
    }
}

/// The three SOUND partial axioms for `tc = reflexive-transitive-closure(r)`:
/// reflexivity, `r ⊆ tc`, transitivity.
///
/// SOUNDNESS: every genuine RTC model satisfies all three, so asserting them
/// never creates a spurious UNSAT (an AY-unsat with the axioms implies the
/// true-semantics goal is unsatisfiable — UNSAT is sound). Conversely they
/// admit over-approximations `tc ⊋ RTC(r)` (a least fixed point is not
/// finitely FO-axiomatizable), so an engine SAT is NOT yet sound; the model
/// verification gate in `check_solver_handle` supplies minimality.
fn build_transitive_closure_axioms(
    ctx: &mut Z3Context,
    r: &FuncDecl,
    tc: &FuncDecl,
    sort: &Sort,
) -> Result<Vec<Term>, String> {
    let x = ctx.solver.fresh_var("z3_tc_x", sort.clone());
    let y = ctx.solver.fresh_var("z3_tc_y", sort.clone());
    let z = ctx.solver.fresh_var("z3_tc_z", sort.clone());
    let mut axioms: Vec<Term> = Vec::new();
    // Reflexivity: forall x. TC(x,x)   (libz3's TC is the REFLEXIVE closure).
    {
        let txx = ctx.solver.apply(tc, &[x, x]);
        axioms.push(
            ctx.solver
                .try_forall(&[x], txx)
                .map_err(|e| format!("{e}"))?,
        );
    }
    // Inclusion: forall x,y. R(x,y) => TC(x,y)
    {
        let rxy = ctx.solver.apply(r, &[x, y]);
        let txy = ctx.solver.apply(tc, &[x, y]);
        let imp = ctx.solver.implies(rxy, txy);
        axioms.push(
            ctx.solver
                .try_forall(&[x, y], imp)
                .map_err(|e| format!("{e}"))?,
        );
    }
    // Transitivity: forall x,y,z. (TC(x,y) & TC(y,z)) => TC(x,z)
    {
        let txy = ctx.solver.apply(tc, &[x, y]);
        let tyz = ctx.solver.apply(tc, &[y, z]);
        let both = ctx.solver.and_many(&[txy, tyz]);
        let txz = ctx.solver.apply(tc, &[x, z]);
        let imp = ctx.solver.implies(both, txz);
        axioms.push(
            ctx.solver
                .try_forall(&[x, y, z], imp)
                .map_err(|e| format!("{e}"))?,
        );
    }
    Ok(axioms)
}

// ============================================================================
// Higher-order sequence operations (REAL term constructors; ground +
// length-bounded goals are DECIDED, the rest stays honest unknown)
// ============================================================================
//
// Each constructor builds the REAL SMT-LIB named application (`seq.map`,
// `seq.mapi`, `seq.foldl`, `seq.foldli`) with the exact result sort Z3 computes
// from the function's array sort (libz3-cross-checked: e.g. `seq.map` of an
// `Array E R` function over a `Seq E` has sort `Seq R`). The terms round-trip
// through `Z3_get_sort` / `Z3_ast_to_string` / `Z3_get_app_decl`.
//
// SOLVING (#ho-seq): the seq theory's `unfold_ho_seq_ops` pass (ay-dpll
// `executor/theories/seq/ho_unfold.rs`) eliminates the combinators by GROUND +
// BOUNDED unfolding — structurally-known or length-pinned sequence arguments
// unfold to element-wise `select` applications of the function-as-array, and
// a `(= (seq.map f s) K)` atom against a structurally-known `K` rewrites to
// the equivalent length-pin + element-image conjunction (the behavior probe's
// `seq.map`-to-empty goal is now `unsat`, matching libz3). Anything the
// unfolder cannot bound is still outside `SUPPORTED_SEQ_OPS`, so the check
// returns `unknown` (`UnknownReason::Incomplete`) — never a wrong SAT/UNSAT
// from treating the combinator as an uninterpreted function.

/// Peel one array layer off `sort`, or record an honest sort error.
fn array_layer(ctx: &mut Z3Context, who: &str, sort: &Sort) -> Option<(Sort, Sort)> {
    match sort {
        Sort::Array(arr) => Some((arr.index_sort.clone(), arr.element_sort.clone())),
        other => {
            ctx.last_error = Z3_SORT_ERROR;
            ctx.error_msg = Some(format!(
                "{who}: expected a function-as-array argument, got {other:?}"
            ));
            None
        }
    }
}

/// Fold-left over a sequence (Z3's `Z3_mk_seq_foldl`): `(seq.foldl f a s)`.
///
/// REAL term constructor; result sort = the accumulator's sort (Z3 parity).
/// Solving over the term is honestly `unknown` (see the section note).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_foldl(c: Z3_context, f: Z3_ast, a: Z3_ast, s: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if f == 0 || a == 0 || s == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_seq_foldl: null AST argument".to_string());
                return 0;
            }
            let ft = require_term_ast_or_return!(ctx, f, "Z3_mk_seq_foldl", "function", 0);
            let at = require_term_ast_or_return!(ctx, a, "Z3_mk_seq_foldl", "accumulator", 0);
            let st = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_foldl", "sequence", 0);
            let f_sort = ctx.solver.sort_of(ft);
            if array_layer(ctx, "Z3_mk_seq_foldl", &f_sort).is_none() {
                return 0;
            }
            let result_sort = ctx.solver.sort_of(at);
            let t = ctx.solver.seq_foldl(ft, at, st, result_sort.clone());
            let ast = term_to_ast(ctx, t);
            record_ast_sort(ctx, ast, result_sort);
            ast
        })
    }
}

/// Indexed fold-left over a sequence (Z3's `Z3_mk_seq_foldli`):
/// `(seq.foldli f i a s)`.
///
/// REAL term constructor; result sort = the accumulator's sort (Z3 parity).
/// Solving over the term is honestly `unknown` (see the section note).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_foldli(
    c: Z3_context,
    f: Z3_ast,
    i: Z3_ast,
    a: Z3_ast,
    s: Z3_ast,
) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if f == 0 || i == 0 || a == 0 || s == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_seq_foldli: null AST argument".to_string());
                return 0;
            }
            let ft = require_term_ast_or_return!(ctx, f, "Z3_mk_seq_foldli", "function", 0);
            let it = require_term_ast_or_return!(ctx, i, "Z3_mk_seq_foldli", "index", 0);
            let at = require_term_ast_or_return!(ctx, a, "Z3_mk_seq_foldli", "accumulator", 0);
            let st = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_foldli", "sequence", 0);
            let f_sort = ctx.solver.sort_of(ft);
            if array_layer(ctx, "Z3_mk_seq_foldli", &f_sort).is_none() {
                return 0;
            }
            let result_sort = ctx.solver.sort_of(at);
            let t = ctx.solver.seq_foldli(ft, it, at, st, result_sort.clone());
            let ast = term_to_ast(ctx, t);
            record_ast_sort(ctx, ast, result_sort);
            ast
        })
    }
}

/// Map a function over a sequence (Z3's `Z3_mk_seq_map`): `(seq.map f s)`.
///
/// REAL term constructor; for `f : Array E R` the result sort is `(Seq R)`
/// (libz3-cross-checked). Solving over the term is honestly `unknown` (see the
/// section note).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_map(c: Z3_context, f: Z3_ast, s: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if f == 0 || s == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_seq_map: null AST argument".to_string());
                return 0;
            }
            let ft = require_term_ast_or_return!(ctx, f, "Z3_mk_seq_map", "function", 0);
            let st = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_map", "sequence", 0);
            let f_sort = ctx.solver.sort_of(ft);
            let Some((_, range)) = array_layer(ctx, "Z3_mk_seq_map", &f_sort) else {
                return 0;
            };
            let result_sort = Sort::seq(range);
            let t = ctx.solver.seq_map(ft, st, result_sort.clone());
            let ast = term_to_ast(ctx, t);
            record_ast_sort(ctx, ast, result_sort);
            ast
        })
    }
}

/// Indexed map over a sequence (Z3's `Z3_mk_seq_mapi`): `(seq.mapi f i s)`.
///
/// REAL term constructor; for `f : Array Int (Array E R)` (the curried
/// two-argument function-as-array) the result sort is `(Seq R)`. Solving over
/// the term is honestly `unknown` (see the section note).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_mapi(c: Z3_context, f: Z3_ast, i: Z3_ast, s: Z3_ast) -> Z3_ast {
    // SAFETY: `c` valid per contract; `ffi_guard_ast` null-checks + isolates panics.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if f == 0 || i == 0 || s == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_seq_mapi: null AST argument".to_string());
                return 0;
            }
            let ft = require_term_ast_or_return!(ctx, f, "Z3_mk_seq_mapi", "function", 0);
            let it = require_term_ast_or_return!(ctx, i, "Z3_mk_seq_mapi", "index", 0);
            let st = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_mapi", "sequence", 0);
            let f_sort = ctx.solver.sort_of(ft);
            let Some((_, inner)) = array_layer(ctx, "Z3_mk_seq_mapi", &f_sort) else {
                return 0;
            };
            // The curried second layer carries the element→result mapping.
            let Some((_, range)) = array_layer(ctx, "Z3_mk_seq_mapi", &inner) else {
                return 0;
            };
            let result_sort = Sort::seq(range);
            let t = ctx.solver.seq_mapi(ft, it, st, result_sort.clone());
            let ast = term_to_ast(ctx, t);
            record_ast_sort(ctx, ast, result_sort);
            ast
        })
    }
}

#[cfg(test)]
#[path = "batch2_tests.rs"]
mod batch2_tests;

#[cfg(test)]
#[path = "feasible_tier_tests.rs"]
mod feasible_tier_tests;

#[cfg(test)]
#[path = "bounded_gap_tests.rs"]
mod bounded_gap_tests;
