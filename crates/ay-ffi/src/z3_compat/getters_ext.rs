// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible accessor long-tail: numeral introspection, sort structure,
//! quantifier/pattern queries, registry enumerators, tuple-sort decls, and the
//! remaining `Z3_is_*` predicates (Track B, C-API long-tail Wave G).
//!
//! Every function is real over existing AY engine/handle state, or an HONEST
//! DOCUMENTED DIVERGENCE where AY structurally lacks the queried capability
//! (decl parameters other than integers, finite-domain / relation
//! sorts, de-Bruijn indices,
//! `:qid`/`:skid` attributes). Divergent functions set a Z3 error code and
//! return a sound sentinel — they NEVER fabricate a value.
//!
//! All bodies run inside `catch_unwind` via the `ffi_guard_*` helpers (#6192).

use std::collections::HashMap;
use std::ffi::{c_char, c_double, c_uint};
use std::ptr;

use ay_dpll::api::{FuncDecl, Sort, Term, TermKind};
use num_bigint::BigInt;

use super::{
    alloc_sort, cache_dt_func_decl, cache_func_decl, cache_string, engine_ast, ffi_guard_ast,
    ffi_guard_const_ptr, ffi_guard_double, ffi_guard_int, ffi_guard_ptr, ffi_guard_uint,
    ffi_guard_void, finite_set_empty_decl_parameter, lookup_ast_sort, mk_ast,
    require_ast_or_return, require_term_ast_or_return, DatatypeOp, Z3_ast, Z3_context,
    Z3_func_decl, Z3_pattern, Z3_sort, Z3_string, Z3_symbol, Z3_INVALID_ARG, Z3_IOB,
};

// ============================================================================
// Numeral introspection (backed by Solver::numeral_string over BigRational)
// ============================================================================

/// Split a numeral's canonical string into `(numerator, denominator)` big ints.
/// `"n/d"` → `(n, d)`; a plain integer `"n"` → `(n, 1)`. `None` for a
/// non-integer/rational rendering.
fn numeral_parts(s: &str) -> Option<(BigInt, BigInt)> {
    if let Some((n, d)) = s.split_once('/') {
        let n = n.trim().parse::<BigInt>().ok()?;
        let d = d.trim().parse::<BigInt>().ok()?;
        Some((n, d))
    } else {
        let n = s.trim().parse::<BigInt>().ok()?;
        Some((n, BigInt::from(1)))
    }
}

/// Like [`numeral_parts`] but requires both components to fit `i64`. `None` if
/// the string is not an integer/rational or either component overflows.
fn numeral_parts_i64(s: &str) -> Option<(i64, i64)> {
    if let Some((n, d)) = s.split_once('/') {
        Some((n.trim().parse::<i64>().ok()?, d.trim().parse::<i64>().ok()?))
    } else {
        Some((s.trim().parse::<i64>().ok()?, 1))
    }
}

/// Numerator of a rational/integer numeral, as a fresh Int numeral (Z3's
/// `Z3_get_numerator`; integers yield the value itself).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numerator(c: Z3_context, a: Z3_ast) -> Z3_ast {
    if a == 0 {
        return 0;
    }
    // SAFETY: `c` guarded by `ffi_guard_ast`; `a` is a term handle value.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let term = require_ast_or_return!(ctx, a, "Z3_get_numerator", "numeral", 0).term;
            match ctx
                .solver
                .numeral_string(term)
                .as_deref()
                .and_then(numeral_parts)
            {
                Some((num, _den)) => {
                    let t = ctx.solver.int_const_bigint(&num);
                    mk_ast(ctx, t, Sort::Int)
                }
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    0
                }
            }
        })
    }
}

/// Denominator of a rational/integer numeral, as a fresh Int numeral (Z3's
/// `Z3_get_denominator`; integers yield `1`).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_denominator(c: Z3_context, a: Z3_ast) -> Z3_ast {
    if a == 0 {
        return 0;
    }
    // SAFETY: `c` guarded by `ffi_guard_ast`.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let term = require_ast_or_return!(ctx, a, "Z3_get_denominator", "numeral", 0).term;
            match ctx
                .solver
                .numeral_string(term)
                .as_deref()
                .and_then(numeral_parts)
            {
                Some((_num, den)) => {
                    let t = ctx.solver.int_const_bigint(&den);
                    mk_ast(ctx, t, Sort::Int)
                }
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    0
                }
            }
        })
    }
}

/// Approximate `double` value of an `Int`/`Real` numeral (Z3's
/// `Z3_get_numeral_double`). `Z3_INVALID_ARG` + `0.0` for a non-numeral or a
/// bit-vector numeral: libz3 4.15.4 defines this getter over the arithmetic
/// sorts only and rejects a bit-vector rather than returning its value.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_double(c: Z3_context, a: Z3_ast) -> c_double {
    if a == 0 {
        return 0.0;
    }
    // SAFETY: `c` guarded by `ffi_guard_double`.
    unsafe {
        ffi_guard_double(c, 0.0, |ctx| {
            let t = require_ast_or_return!(ctx, a, "Z3_get_numeral_double", "numeral", 0.0).term;
            if matches!(ctx.solver.sort_of(t), Sort::BitVec(_)) {
                ctx.last_error = Z3_INVALID_ARG;
                return 0.0;
            }
            match ctx
                .solver
                .numeral_string(t)
                .as_deref()
                .and_then(numeral_parts)
            {
                // BigInt→f64 via string parse keeps this dependency-light and
                // matches Z3's lossy double conversion for large magnitudes.
                Some((num, den)) => {
                    let n: f64 = num.to_string().parse().unwrap_or(0.0);
                    let d: f64 = den.to_string().parse().unwrap_or(1.0);
                    if d == 0.0 {
                        0.0
                    } else {
                        n / d
                    }
                }
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    0.0
                }
            }
        })
    }
}

/// Fill `*num`/`*den` with a rational numeral's components if both fit `int64`
/// (Z3's `Z3_get_numeral_rational_int64`). Returns false (no write) otherwise.
///
/// # Safety
/// `c` valid; `num`/`den` must be valid writable `int64_t` pointers.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_rational_int64(
    c: Z3_context,
    v: Z3_ast,
    num: *mut i64,
    den: *mut i64,
) -> bool {
    if v == 0 || num.is_null() || den.is_null() {
        return false;
    }
    // SAFETY: `c` guarded by `ffi_guard_int`; `num`/`den` null-checked, valid by contract.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term =
                require_ast_or_return!(ctx, v, "Z3_get_numeral_rational_int64", "numeral", 0).term;
            if let Some((n, d)) = ctx
                .solver
                .numeral_string(term)
                .as_deref()
                .and_then(numeral_parts_i64)
            {
                *num = n;
                *den = d;
                return 1;
            }
            0
        }) != 0
    }
}

/// Z3's `Z3_get_numeral_rational` — a symbol libz3 exports but does NOT declare
/// in any public header (undocumented/legacy). For full exported-symbol parity
/// ("drop-in at the ABI level") AY provides it as a sound alias of
/// [`Z3_get_numeral_rational_int64`]: fills `*num`/`*den` from a rational/integer
/// numeral iff both fit `int64`, else returns false. No documented consumer
/// calls it; this never fabricates a value.
///
/// # Safety
/// `c` valid; `num`/`den` must be valid writable `int64_t` pointers.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_rational(
    c: Z3_context,
    a: Z3_ast,
    num: *mut i64,
    den: *mut i64,
) -> bool {
    // SAFETY: delegates to the fully-guarded sibling.
    unsafe { Z3_get_numeral_rational_int64(c, a, num, den) }
}

/// Like [`Z3_get_numeral_rational_int64`] but sets `Z3_INVALID_ARG` on the
/// failure path (Z3's `Z3_get_numeral_small`).
///
/// # Safety
/// `c` valid; `num`/`den` must be valid writable `int64_t` pointers.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_small(
    c: Z3_context,
    a: Z3_ast,
    num: *mut i64,
    den: *mut i64,
) -> bool {
    if a == 0 || num.is_null() || den.is_null() {
        return false;
    }
    // SAFETY: as `Z3_get_numeral_rational_int64`, but signals `Z3_INVALID_ARG` on failure.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = require_ast_or_return!(ctx, a, "Z3_get_numeral_small", "numeral", 0).term;
            match ctx
                .solver
                .numeral_string(term)
                .as_deref()
                .and_then(numeral_parts_i64)
            {
                Some((n, d)) => {
                    *num = n;
                    *den = d;
                    1
                }
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    0
                }
            }
        }) != 0
    }
}

/// Binary-string rendering of a numeral, MSB-first (Z3's
/// `Z3_get_numeral_binary_string`).
///
/// Renders the numeral's VALUE in minimal binary, with NO zero-padding to the
/// bit-vector width, and accepts every numeral whose value is a non-negative
/// integer — bit-vector, `Int`, or an integral `Real`. A negative value, a
/// non-integral value, or a non-numeral is `Z3_INVALID_ARG` + null.
///
/// The BV `numeral_string` is already the unsigned value, so bit-vectors, `Int`
/// and integral `Real` all reduce to the same non-negative-integer rendering.
/// Contract measured against libz3 4.15.4: `bv8 10` → `1010` (not `00001010`),
/// `bv8 -5` → `11111011`, `int 5` → `101`, `real 4.0` → `100`, while `int -5`,
/// `real 1/2`, a Bool and a non-numeral each yield `Z3_INVALID_ARG` + null.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_binary_string(c: Z3_context, a: Z3_ast) -> Z3_string {
    if a == 0 {
        return ptr::null();
    }
    // SAFETY: `c` guarded by `ffi_guard_const_ptr`.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let term = require_ast_or_return!(
                ctx,
                a,
                "Z3_get_numeral_binary_string",
                "numeral",
                ptr::null()
            )
            .term;
            let value = ctx
                .solver
                .numeral_string(term)
                .as_deref()
                .and_then(numeral_parts)
                // Integral values only: z3 rejects `1/2`.
                .filter(|(_, d)| *d == BigInt::from(1))
                .map(|(n, _)| n)
                // Non-negative only: z3 rejects `-5` for a signed sort.
                .and_then(|n| n.to_biguint());
            match value {
                Some(v) => cache_string(ctx, v.to_str_radix(2)),
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ptr::null()
                }
            }
        })
    }
}

// ============================================================================
// AST structural queries
// ============================================================================

/// Structural nesting depth of a term (Z3's `Z3_get_depth`): a leaf has depth
/// 1, an application `1 + max(child depth)`. Computed by an explicit-stack DFS
/// over the hash-consed term DAG (no engine change, no recursion overflow).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_depth(c: Z3_context, a: Z3_ast) -> c_uint {
    if a == 0 {
        return 0;
    }
    // SAFETY: `c` guarded by `ffi_guard_uint`.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            let root = require_ast_or_return!(ctx, a, "Z3_get_depth", "term", 0).term;
            let mut memo: HashMap<Term, u32> = HashMap::new();
            let mut stack: Vec<(Term, bool)> = vec![(root, false)];
            while let Some((t, processed)) = stack.pop() {
                if memo.contains_key(&t) {
                    continue;
                }
                let children = ctx.solver.term_children(t);
                if processed {
                    let d = 1 + children
                        .iter()
                        .map(|ch| memo.get(ch).copied().unwrap_or(1))
                        .max()
                        .unwrap_or(0);
                    memo.insert(t, d);
                } else {
                    stack.push((t, true));
                    for ch in children {
                        if !memo.contains_key(&ch) {
                            stack.push((ch, false));
                        }
                    }
                }
            }
            memo.get(&root).copied().unwrap_or(1)
        })
    }
}

/// Z3's `Z3_get_index_value` — de-Bruijn index of a bound variable.
///
/// EXACT (over its domain): `Z3_mk_bound(i, s)` encodes the de-Bruijn index into
/// the bound variable's NAME as `__db<i>` (see `quantifiers.rs`), surfaced to the
/// FFI via `term_kind → Var{name}`. This recovers `i` by parsing back the value
/// AY itself wrote. A `Var` whose name is not exactly `__db<N>` is not a
/// de-Bruijn node, so the honest `Z3_INVALID_ARG` sentinel stays (never fabricate
/// an index for a user-named variable).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_index_value(c: Z3_context, a: Z3_ast) -> c_uint {
    if a == 0 {
        // SAFETY: `c` guarded by `ffi_guard_uint`.
        return unsafe {
            ffi_guard_uint(c, 0, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                0
            })
        };
    }
    // SAFETY: `c` guarded by `ffi_guard_uint`.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            let term = require_ast_or_return!(ctx, a, "Z3_get_index_value", "term", 0).term;
            if let TermKind::Var { name } = ctx.solver.term_kind(term) {
                if let Some(idx) =
                    ay_dpll::api::de_bruijn_index(&name).and_then(|k| c_uint::try_from(k).ok())
                {
                    return idx;
                }
            }
            ctx.last_error = Z3_INVALID_ARG;
            0
        })
    }
}

/// Stable per-context identity of a func_decl (Z3's `Z3_get_func_decl_id`).
/// Distinct decls get distinct ids within a context (analogue of
/// `Z3_get_sort_id`); AY keeps no global decl numbering.
///
/// # Safety
/// `c` valid; `f`, when non-null, a valid func_decl handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_func_decl_id(c: Z3_context, f: Z3_func_decl) -> c_uint {
    if f.is_null() {
        return 0;
    }
    // SAFETY: `f` null-checked; `.decl_id` read is single-threaded per context.
    let id = unsafe { (*f).decl_id };
    // SAFETY: `c` guarded by `ffi_guard_uint`.
    unsafe { ffi_guard_uint(c, 0, |_ctx| id) }
}

/// Z3's `Z3_is_algebraic_number`: true exactly for a genuine irrational
/// algebraic value (measured libz3 5.1.0: `√2` true; rationals and
/// rational-valued roots like `√4` false, since both engines intern
/// those as ordinary numerals).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_algebraic_number(c: Z3_context, a: Z3_ast) -> bool {
    // SAFETY: `ffi_guard_int` null-checks `c` and catches panics; pure
    // predicate (a non-value is quietly false, no error, as in z3).
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let is_algebraic = super::algebraic::ast_as_scalar(ctx, a)
                .is_some_and(|s| ay_nra::rcf_api::is_rational(&s) == Some(false));
            i32::from(is_algebraic)
        }) != 0
    }
}

/// The function name inside AY's `(as-array f)` node (`App` head
/// `as-array[f]`, mirroring Z3's `OP_AS_ARRAY` parameter), or `None` for
/// any other term.
fn as_array_func_name(ctx: &super::Z3Context, term: Term) -> Option<String> {
    let head = ctx.solver.app_symbol_name(term)?;
    head.strip_prefix("as-array[")?
        .strip_suffix(']')
        .map(str::to_string)
}

/// Z3's `Z3_is_as_array`: true exactly for `(as-array f)` terms (built by
/// `Z3_mk_as_array` or parsed `(as-array f)`).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_as_array(c: Z3_context, a: Z3_ast) -> bool {
    if a == 0 {
        return false;
    }
    // SAFETY: `c` guarded by `ffi_guard_int`.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = require_term_ast_or_return!(ctx, a, "Z3_is_as_array", "term", 0);
            i32::from(as_array_func_name(ctx, term).is_some())
        }) != 0
    }
}

/// Z3's `Z3_get_as_array_func_decl`: the unary function declaration `f` of
/// an `(as-array f)` term. Non-as-array input sets `Z3_INVALID_ARG` and
/// returns null.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_as_array_func_decl(c: Z3_context, a: Z3_ast) -> Z3_func_decl {
    if a == 0 {
        return ptr::null_mut();
    }
    // SAFETY: `c` guarded by `ffi_guard_ptr`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let term = require_term_ast_or_return!(
                ctx,
                a,
                "Z3_get_as_array_func_decl",
                "term",
                ptr::null_mut()
            );
            let Some(name) = as_array_func_name(ctx, term) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg =
                    Some("Z3_get_as_array_func_decl: argument is not an as-array term".to_string());
                return ptr::null_mut();
            };
            // Prefer the context's authenticated declaration of `f`.
            if let Some(authenticated) = ctx
                .ffi_func_decls
                .values()
                .find(|decl| decl.declaration_identity_name() == name && decl.arity() == 1)
                .cloned()
            {
                return cache_func_decl(ctx, authenticated);
            }
            // Otherwise synthesize `f : index -> element` from the term's
            // recorded `(Array index element)` sort.
            let sort = lookup_ast_sort(ctx, a)
                .cloned()
                .unwrap_or_else(|| ctx.solver.term_sort(term));
            let Sort::Array(array_sort) = sort else {
                ctx.last_error = Z3_INVALID_ARG;
                return ptr::null_mut();
            };
            cache_func_decl(
                ctx,
                FuncDecl::new(name, vec![array_sort.index_sort], array_sort.element_sort),
            )
        })
    }
}

/// Z3's `Z3_is_well_sorted`. Every term in AY's store is well-sorted by
/// construction (typed builders reject `SortMismatch`), so any valid non-null
/// handle is well-sorted.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_well_sorted(c: Z3_context, t: Z3_ast) -> bool {
    // SAFETY: `ffi_guard_int` handles a null context and catches panics.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let _term = require_ast_or_return!(ctx, t, "Z3_is_well_sorted", "term", 0).term;
            1
        }) != 0
    }
}

// ============================================================================
// Decl-parameter getters not implemented by AY
// ============================================================================
//
// `FuncDeclHandle.params` stores integer parameters for indexed operators.
// Finite-set `set.empty` additionally exposes one computed SORT parameter
// through `Z3_get_decl_sort_parameter` in `accessors.rs`, and an
// `(as-array f)` declaration exposes one computed FUNC_DECL parameter
// below. No declaration carries an AST, double, rational, or symbol
// parameter, so those getters set `Z3_IOB` and return a null/zero sentinel.

/// Z3's `Z3_get_decl_ast_parameter` — no AST decl parameters in AY.
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_ast_parameter(
    c: Z3_context,
    _d: Z3_func_decl,
    _idx: c_uint,
) -> Z3_ast {
    // SAFETY: `c` guarded by `ffi_guard_ast`.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            ctx.last_error = Z3_IOB;
            0
        })
    }
}

/// Z3's `Z3_get_decl_double_parameter` — no double decl parameters in AY.
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_double_parameter(
    c: Z3_context,
    _d: Z3_func_decl,
    _idx: c_uint,
) -> c_double {
    // SAFETY: `c` guarded by `ffi_guard_double`.
    unsafe {
        ffi_guard_double(c, 0.0, |ctx| {
            ctx.last_error = Z3_IOB;
            0.0
        })
    }
}

/// The inner function name of an `(as-array f)` declaration: AY encodes
/// the parameter in the declaration's (private) name `as-array[f]`
/// rather than a parameter slot, so the decl-parameter getters compute
/// it on query (the same pattern as the finite-set sort parameter).
pub(crate) fn as_array_decl_inner_name(decl: &FuncDecl) -> Option<&str> {
    decl.name().strip_prefix("as-array[")?.strip_suffix(']')
}

/// Resolve the func-decl parameter of an `(as-array f)` declaration the
/// same way [`Z3_get_as_array_func_decl`] resolves it from the term:
/// the context's authenticated declaration of `f` when one exists,
/// else `f : index -> element` synthesized from the decl's Array
/// range.
pub(crate) fn as_array_decl_parameter(
    ctx: &mut super::Z3Context,
    decl: &FuncDecl,
) -> Option<Z3_func_decl> {
    let name = as_array_decl_inner_name(decl)?;
    if let Some(authenticated) = ctx
        .ffi_func_decls
        .values()
        .find(|d| d.declaration_identity_name() == name && d.arity() == 1)
        .cloned()
    {
        return Some(cache_func_decl(ctx, authenticated));
    }
    let Sort::Array(array_sort) = decl.range() else {
        return None;
    };
    Some(cache_func_decl(
        ctx,
        FuncDecl::new(
            name.to_string(),
            vec![array_sort.index_sort.clone()],
            array_sort.element_sort.clone(),
        ),
    ))
}

/// Z3's `Z3_get_decl_func_decl_parameter`: parameter 0 of an
/// `(as-array f)` declaration is `f` itself (measured libz3 5.1.0:
/// one parameter of kind `Z3_PARAMETER_FUNC_DECL`), and a
/// recognizer's (`is`) one parameter is the constructor it tests
/// for; every other declaration/index is `Z3_IOB` + null.
/// # Safety
/// `c` must be a valid context pointer; `d` null or a live declaration handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_func_decl_parameter(
    c: Z3_context,
    d: Z3_func_decl,
    idx: c_uint,
) -> Z3_func_decl {
    // SAFETY: `c` guarded by `ffi_guard_ptr`; `d` per this function's contract.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if !d.is_null() && idx == 0 {
                if let Some(constructor) = super::datatypes::recognizer_constructor_decl(ctx, d) {
                    return constructor;
                }
                // SAFETY: `d` null-checked; `.decl` clone is a
                // single-threaded read of a context-owned handle.
                let decl = (*d).decl.clone();
                if let Some(handle) = as_array_decl_parameter(ctx, &decl) {
                    ctx.last_error = super::Z3_OK;
                    return handle;
                }
            }
            ctx.last_error = Z3_IOB;
            ptr::null_mut()
        })
    }
}

/// Z3's `Z3_get_decl_rational_parameter`: parameter 0 of a numeral's
/// declaration is its value (`Int`/`Real`/bit-vector numerals, as in z3); no
/// other AY decl has a rational parameter.
/// # Safety
/// `c` must be a valid context pointer; `d` null or a live declaration handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_rational_parameter(
    c: Z3_context,
    d: Z3_func_decl,
    idx: c_uint,
) -> Z3_string {
    // SAFETY: `c` guarded by `ffi_guard_const_ptr`; `d` per this function's contract.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            if let Some(handle) = d.as_ref() {
                if idx == 0 {
                    if let Some(value) =
                        super::accessors::numeral_decl_rational_parameter(ctx, handle)
                    {
                        return cache_string(ctx, value);
                    }
                }
                if let Some(super::accessors::BoundedValueParam::Rational(value)) =
                    super::accessors::bounded_value_decl_parameters(ctx, handle)
                        .and_then(|params| params.get(idx as usize).cloned())
                {
                    return cache_string(ctx, value);
                }
            }
            ctx.last_error = Z3_IOB;
            ptr::null()
        })
    }
}

/// Z3's `Z3_get_decl_sort_parameter` — no sort decl parameters in AY.
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_sort_parameter(
    c: Z3_context,
    d: Z3_func_decl,
    idx: c_uint,
) -> Z3_sort {
    // SAFETY: `c` guarded by `ffi_guard_ptr`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if !d.is_null() && idx == 0 {
                if let Some(sort) = finite_set_empty_decl_parameter(ctx, &(*d).decl) {
                    return alloc_sort(ctx, sort);
                }
            }
            if let Some(super::accessors::BoundedValueParam::Sort(sort)) = d
                .as_ref()
                .and_then(|handle| super::accessors::bounded_value_decl_parameters(ctx, handle))
                .and_then(|params| params.get(idx as usize).cloned())
            {
                return alloc_sort(ctx, sort);
            }
            ctx.last_error = Z3_IOB;
            ptr::null_mut()
        })
    }
}

/// Z3's `Z3_get_decl_symbol_parameter` — no symbol decl parameters in AY.
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_symbol_parameter(
    c: Z3_context,
    _d: Z3_func_decl,
    _idx: c_uint,
) -> Z3_symbol {
    // SAFETY: `c` guarded by `ffi_guard_ptr`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            ctx.last_error = Z3_IOB;
            ptr::null_mut()
        })
    }
}

// ============================================================================
// Sort structure
// ============================================================================

/// The curried domain chain of an array sort: AY canonicalizes an n-domain array
/// (`Z3_mk_array_sort_n`) to nested single-index arrays, so the domains are the
/// index sorts of that chain. `None` for a non-array sort.
///
/// Because the canonical form is shared, a hand-nested array-of-array is the SAME
/// sort as the n-domain one and reports the same chain — the documented AY
/// divergence (libz3 reports arity 1 for a hand-nested array).
fn curried_array_domains(sort: &Sort) -> Option<Vec<Sort>> {
    let mut domains = Vec::new();
    let mut cursor = sort;
    while let Sort::Array(array) = cursor {
        domains.push(array.index_sort.clone());
        cursor = &array.element_sort;
    }
    (!domains.is_empty()).then_some(domains)
}

/// Arity of an array sort (Z3's `Z3_get_array_arity`): the number of curried
/// domains, so `Z3_mk_array_sort_n(2)` reports 2 exactly as libz3 does.
/// Non-array → `Z3_INVALID_ARG`, 0.
///
/// # Safety
/// `c` valid; `s`, when non-null, a valid sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_array_arity(c: Z3_context, s: Z3_sort) -> c_uint {
    if s.is_null() {
        return 0;
    }
    // SAFETY: `s` null-checked; `.sort` read single-threaded; `c` guarded.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| match curried_array_domains(&(*s).sort) {
            Some(domains) => domains.len() as c_uint,
            None => {
                ctx.last_error = Z3_INVALID_ARG;
                0
            }
        })
    }
}

/// The `idx`-th domain sort of an array sort (Z3's `Z3_get_array_sort_domain_n`),
/// indexing the curried domain chain: for `Z3_mk_array_sort_n(2, [Int, Bool], _)`
/// `idx==0` → `Int` and `idx==1` → `Bool`, matching libz3. `idx` past the last
/// domain → `Z3_IOB`, null. Non-array → `Z3_INVALID_ARG`, null.
///
/// # Safety
/// `c` valid; `t`, when non-null, a valid sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_array_sort_domain_n(
    c: Z3_context,
    t: Z3_sort,
    idx: c_uint,
) -> Z3_sort {
    if t.is_null() {
        return ptr::null_mut();
    }
    // Classify before the guard: Some(sort) = in-range curried domain;
    // None + is_array = out of range; None + !is_array = wrong sort.
    // SAFETY: `t` null-checked; `.sort` read single-threaded.
    let domains = curried_array_domains(unsafe { &(*t).sort });
    let is_array = domains.is_some();
    let index_sort = domains.and_then(|d| d.get(idx as usize).cloned());
    // SAFETY: `c` guarded by `ffi_guard_ptr`.
    unsafe {
        ffi_guard_ptr(c, |ctx| match &index_sort {
            Some(sort) => alloc_sort(ctx, sort.clone()),
            None => {
                ctx.last_error = if is_array { Z3_IOB } else { Z3_INVALID_ARG };
                ptr::null_mut()
            }
        })
    }
}

/// Element (basis) sort of a sequence sort (Z3's `Z3_get_seq_sort_basis`).
/// Non-seq → `Z3_INVALID_ARG`, null.
///
/// # Safety
/// `c` valid; `s`, when non-null, a valid sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_seq_sort_basis(c: Z3_context, s: Z3_sort) -> Z3_sort {
    if s.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `s` null-checked; `.sort` read single-threaded.
    let basis = match unsafe { &(*s).sort } {
        Sort::Seq(elem) => Some((**elem).clone()),
        // A String is a sequence of characters, so its basis is the Char sort —
        // reported as `Z3_CHAR_SORT`, exactly as libz3 4.15.4 does.
        Sort::String => Some(Sort::Char),
        _ => None,
    };
    // SAFETY: `c` guarded by `ffi_guard_ptr`.
    unsafe {
        ffi_guard_ptr(c, |ctx| match basis {
            Some(sort) => alloc_sort(ctx, sort),
            None => {
                ctx.last_error = Z3_INVALID_ARG;
                ptr::null_mut()
            }
        })
    }
}

/// Basis sort of a regular-expression sort (Z3's `Z3_get_re_sort_basis`).
/// AY regexes are monomorphic over strings, so the basis is the String sort.
/// Non-RegLan → `Z3_INVALID_ARG`, null.
///
/// # Safety
/// `c` valid; `s`, when non-null, a valid sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_re_sort_basis(c: Z3_context, s: Z3_sort) -> Z3_sort {
    if s.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `s` null-checked; `.sort` read single-threaded.
    let is_re = matches!(unsafe { &(*s).sort }, Sort::RegLan);
    // SAFETY: `c` guarded by `ffi_guard_ptr`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if is_re {
                alloc_sort(ctx, Sort::String)
            } else {
                ctx.last_error = Z3_INVALID_ARG;
                ptr::null_mut()
            }
        })
    }
}

/// Z3's `Z3_get_finite_domain_sort_size`. REAL: writes the cardinality of a
/// [`Sort::FiniteDomain`] created by `Z3_mk_finite_domain_sort` and returns
/// true; for any other sort returns false and writes 0. Measured against libz3
/// 4.15.4, which zeroes the out-param on the failure path rather than leaving
/// the caller's value in place.
///
/// # Safety
/// `c` valid; `s`, when non-null, a valid sort handle; `r` may be null (then
/// only the boolean is reported).
#[no_mangle]
pub unsafe extern "C" fn Z3_get_finite_domain_sort_size(
    _c: Z3_context,
    s: Z3_sort,
    r: *mut u64,
) -> bool {
    if s.is_null() {
        return false;
    }
    // SAFETY: `s` null-checked; `.sort` read single-threaded per Z3 contract.
    let size = unsafe { (*s).sort.finite_domain_size() };
    if !r.is_null() {
        // SAFETY: `r` null-checked; caller guarantees it is writable.
        // Zero on the failure path, matching libz3: a caller that ignores the
        // boolean must not read back its own stale value as a cardinality.
        unsafe { ptr::write(r, size.unwrap_or(0)) };
    }
    size.is_some()
}

/// Z3's `Z3_get_relation_arity`. AY has no relation sort. DIVERGENCE:
/// `Z3_INVALID_ARG`, 0.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_relation_arity(c: Z3_context, _s: Z3_sort) -> c_uint {
    // SAFETY: `c` guarded by `ffi_guard_uint`.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            ctx.last_error = Z3_INVALID_ARG;
            0
        })
    }
}

/// Z3's `Z3_get_relation_column`. AY has no relation sort. DIVERGENCE:
/// `Z3_INVALID_ARG`, null.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_relation_column(
    c: Z3_context,
    _s: Z3_sort,
    _col: c_uint,
) -> Z3_sort {
    // SAFETY: `c` guarded by `ffi_guard_ptr`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            ctx.last_error = Z3_INVALID_ARG;
            ptr::null_mut()
        })
    }
}

/// Z3's `Z3_is_char_sort`. True iff `s` is [`Sort::Char`].
/// # Safety
/// `c` valid; `s`, when non-null, a valid sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_char_sort(_c: Z3_context, s: Z3_sort) -> bool {
    if s.is_null() {
        return false;
    }
    // SAFETY: `s` null-checked; `.sort` read single-threaded.
    matches!(unsafe { &(*s).sort }, Sort::Char)
}

/// Z3's `Z3_is_re_sort`.
/// # Safety
/// `c` valid; `s`, when non-null, a valid sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_re_sort(_c: Z3_context, s: Z3_sort) -> bool {
    if s.is_null() {
        return false;
    }
    // SAFETY: `s` null-checked; `.sort` read single-threaded.
    matches!(unsafe { &(*s).sort }, Sort::RegLan)
}

/// Z3's `Z3_is_seq_sort` (a String is a sequence of characters).
/// # Safety
/// `c` valid; `s`, when non-null, a valid sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_seq_sort(_c: Z3_context, s: Z3_sort) -> bool {
    if s.is_null() {
        return false;
    }
    // SAFETY: `s` null-checked; `.sort` read single-threaded.
    matches!(unsafe { &(*s).sort }, Sort::Seq(_) | Sort::String)
}

/// Z3's `Z3_is_string_sort`.
/// # Safety
/// `c` valid; `s`, when non-null, a valid sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_string_sort(_c: Z3_context, s: Z3_sort) -> bool {
    if s.is_null() {
        return false;
    }
    // SAFETY: `s` null-checked; `.sort` read single-threaded.
    matches!(unsafe { &(*s).sort }, Sort::String)
}

/// Z3's `Z3_is_recursive_datatype_sort`: true iff a constructor field refers
/// back to the datatype itself (a recursive/self-referential definition).
///
/// # Safety
/// `c` valid; `s`, when non-null, a valid sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_recursive_datatype_sort(_c: Z3_context, s: Z3_sort) -> bool {
    if s.is_null() {
        return false;
    }
    // SAFETY: `s` null-checked; `.sort` read single-threaded.
    match unsafe { &(*s).sort } {
        Sort::Datatype(dt) => dt.constructors.iter().any(|ctor| {
            ctor.fields.iter().any(|f| match &f.sort {
                Sort::Datatype(inner) => inner.name == dt.name,
                Sort::Uninterpreted(name) => *name == dt.name,
                _ => false,
            })
        }),
        _ => false,
    }
}

// ============================================================================
// Quantifier / pattern queries
// ============================================================================

/// Number of trigger terms in a pattern (Z3's `Z3_get_pattern_num_terms`).
/// # Safety
/// `c` valid; `p`, when non-null, a valid pattern handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_pattern_num_terms(c: Z3_context, p: Z3_pattern) -> c_uint {
    if p.is_null() {
        return 0;
    }
    // SAFETY: `p` null-checked; `.terms` read single-threaded. Explicit `&`
    // avoids the deny-by-default implicit-autoref-of-raw-pointer lint.
    let n = unsafe { (*p).terms.len() } as c_uint;
    // SAFETY: `c` guarded by `ffi_guard_uint`.
    unsafe { ffi_guard_uint(c, 0, |_ctx| n) }
}

/// The `idx`-th trigger term of a pattern (Z3's `Z3_get_pattern`). Out of range
/// → `Z3_IOB`, null AST.
///
/// # Safety
/// `c` valid; `p`, when non-null, a valid pattern handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_pattern(c: Z3_context, p: Z3_pattern, idx: c_uint) -> Z3_ast {
    if p.is_null() {
        return 0;
    }
    // SAFETY: `p` null-checked; `.terms` read single-threaded. Construct the
    // shared reference explicitly from the field address so no implicit raw
    // pointer autoref is involved.
    let terms = unsafe { &*ptr::addr_of!((*p).terms) };
    let term = terms.get(idx as usize).copied();
    // SAFETY: `c` guarded by `ffi_guard_ast`.
    unsafe {
        ffi_guard_ast(c, |ctx| match term {
            Some(t) => engine_ast(ctx, t),
            None => {
                ctx.last_error = Z3_IOB;
                0
            }
        })
    }
}

/// Z3's `Z3_get_quantifier_id` — the `:qid` (quantifier identifier).
///
/// REAL for any quantifier given an explicit `:qid` through
/// `Z3_mk_quantifier_ex`/`_const_ex`: the id round-trips exactly. Parsed
/// quantifier metadata is rejected until parser AST identity can retain it.
/// When no explicit qid was set, Z3 auto-generates a synthetic symbol AY cannot
/// replicate, so AY returns null (`Z3_INVALID_ARG`) rather than fabricating one.
///
/// A constructor that would hash-cons to an existing term with different qid,
/// skolemid, weight, or no-pattern metadata is rejected with
/// `Z3_INVALID_USAGE`; metadata never aliases between public ASTs.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_quantifier_id(c: Z3_context, a: Z3_ast) -> Z3_symbol {
    if a == 0 {
        // SAFETY: `c` guarded by `ffi_guard_ptr`.
        return unsafe {
            ffi_guard_ptr(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ptr::null_mut()
            })
        };
    }
    // SAFETY: `c` guarded by `ffi_guard_ptr`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let term = require_ast_or_return!(
                ctx,
                a,
                "Z3_get_quantifier_id",
                "quantifier",
                ptr::null_mut()
            )
            .term;
            let symbol = ctx
                .quantifier_ffi_metadata
                .get(&term)
                .and_then(|metadata| metadata.quantifier_id.clone());
            match symbol {
                Some(symbol) => super::cache_symbol_key(ctx, symbol),
                // A quantifier without the id has z3's null symbol.
                None if matches!(
                    ctx.solver.term_kind(term),
                    TermKind::Forall | TermKind::Exists
                ) =>
                {
                    ptr::null_mut()
                }
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ptr::null_mut()
                }
            }
        })
    }
}

/// Z3's `Z3_get_quantifier_skolem_id` — the `:skolemid`.
///
/// REAL for any quantifier given an EXPLICIT `:skolemid`; residual honest null
/// only when none was set. Same mechanism/caveats as [`Z3_get_quantifier_id`].
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_quantifier_skolem_id(c: Z3_context, a: Z3_ast) -> Z3_symbol {
    if a == 0 {
        // SAFETY: `c` guarded by `ffi_guard_ptr`.
        return unsafe {
            ffi_guard_ptr(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ptr::null_mut()
            })
        };
    }
    // SAFETY: `c` guarded by `ffi_guard_ptr`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let term = require_ast_or_return!(
                ctx,
                a,
                "Z3_get_quantifier_skolem_id",
                "quantifier",
                ptr::null_mut()
            )
            .term;
            let symbol = ctx
                .quantifier_ffi_metadata
                .get(&term)
                .and_then(|metadata| metadata.skolem_id.clone());
            match symbol {
                Some(symbol) => super::cache_symbol_key(ctx, symbol),
                // A quantifier without the id has z3's null symbol.
                None if matches!(
                    ctx.solver.term_kind(term),
                    TermKind::Forall | TermKind::Exists
                ) =>
                {
                    ptr::null_mut()
                }
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ptr::null_mut()
                }
            }
        })
    }
}

/// Z3's `Z3_is_lambda`: whether `a` is a lambda (AY's `lambda-array`, which
/// `Z3_mk_lambda` / `Z3_mk_lambda_const` build). z3py reads a `Lambda`'s sort
/// through this predicate: answering false made every lambda a `Bool` term
/// there (`Store(Lambda([x], x), 2, 1)` raised).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_lambda(c: Z3_context, a: Z3_ast) -> bool {
    if a == 0 {
        return false;
    }
    // SAFETY: `c` guarded by `ffi_guard_int`, which handles null and catches
    // panics.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let term = require_ast_or_return!(ctx, a, "Z3_is_lambda", "term", 0).term;
            i32::from(matches!(
                ctx.solver.term_kind(term),
                TermKind::App { name, num_args: 2 } if name == "lambda-array"
            ))
        }) != 0
    }
}

// ============================================================================
// Registry enumerators
// ============================================================================

/// Number of registered tactics (Z3's `Z3_get_num_tactics`).
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_num_tactics(c: Z3_context) -> c_uint {
    // SAFETY: `c` guarded by `ffi_guard_uint`.
    unsafe {
        ffi_guard_uint(c, 0, |_ctx| {
            ay_frontend::SUPPORTED_TACTIC_NAMES.len() as c_uint
        })
    }
}

/// Name of the `i`-th registered tactic (Z3's `Z3_get_tactic_name`).
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_tactic_name(c: Z3_context, i: c_uint) -> Z3_string {
    // SAFETY: `c` guarded by `ffi_guard_const_ptr`.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            match ay_frontend::SUPPORTED_TACTIC_NAMES.get(i as usize) {
                Some(name) => cache_string(ctx, (*name).to_string()),
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ptr::null()
                }
            }
        })
    }
}

/// Number of registered simplifiers (Z3's `Z3_get_num_simplifiers`).
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_num_simplifiers(c: Z3_context) -> c_uint {
    // SAFETY: `c` guarded by `ffi_guard_uint`.
    unsafe {
        ffi_guard_uint(c, 0, |_ctx| {
            super::SUPPORTED_SIMPLIFIER_NAMES.len() as c_uint
        })
    }
}

/// Name of the `i`-th registered simplifier (Z3's `Z3_get_simplifier_name`).
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_simplifier_name(c: Z3_context, i: c_uint) -> Z3_string {
    // SAFETY: `c` guarded by `ffi_guard_const_ptr`.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            match super::SUPPORTED_SIMPLIFIER_NAMES.get(i as usize) {
                Some(name) => cache_string(ctx, (*name).to_string()),
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ptr::null()
                }
            }
        })
    }
}

// ============================================================================
// Tuple sorts (a tuple is a single-constructor datatype)
// ============================================================================

/// Field count of a tuple sort (Z3's `Z3_get_tuple_sort_num_fields`): the field
/// count of a single-constructor datatype. Non-tuple → `Z3_INVALID_ARG`, 0.
///
/// # Safety
/// `c` valid; `t`, when non-null, a valid sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_tuple_sort_num_fields(c: Z3_context, t: Z3_sort) -> c_uint {
    if t.is_null() {
        return 0;
    }
    // SAFETY: `t` null-checked; `.sort` read single-threaded.
    let n = match unsafe { &(*t).sort } {
        Sort::Datatype(dt) if dt.constructors.len() == 1 => Some(dt.constructors[0].fields.len()),
        _ => None,
    };
    // SAFETY: `c` guarded by `ffi_guard_uint`.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| match n {
            Some(k) => k as c_uint,
            None => {
                ctx.last_error = Z3_INVALID_ARG;
                0
            }
        })
    }
}

/// Constructor func_decl of a tuple sort (Z3's `Z3_get_tuple_sort_mk_decl`):
/// the sole constructor of a single-constructor datatype. Non-tuple →
/// `Z3_INVALID_ARG`, null.
///
/// # Safety
/// `c` valid; `t`, when non-null, a valid sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_tuple_sort_mk_decl(c: Z3_context, t: Z3_sort) -> Z3_func_decl {
    if t.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `t` null-checked; `.sort` read single-threaded.
    let dt = match unsafe { &(*t).sort } {
        Sort::Datatype(dt) if dt.constructors.len() == 1 => dt.clone(),
        _ => return ptr::null_mut(),
    };
    let ctor = dt.constructors[0].clone();
    // SAFETY: `c` guarded by `ffi_guard_ptr`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let dt_sort = Sort::Datatype(dt.clone());
            cache_dt_func_decl(
                ctx,
                FuncDecl::new(
                    ctor.name.clone(),
                    ctor.fields.iter().map(|f| f.sort.clone()).collect(),
                    dt_sort,
                ),
                DatatypeOp::Constructor {
                    dt: dt.clone(),
                    ctor: ctor.name.clone(),
                },
            )
        })
    }
}

/// The `i`-th field accessor func_decl of a tuple sort (Z3's
/// `Z3_get_tuple_sort_field_decl`). Non-tuple / out-of-range → `Z3_INVALID_ARG`,
/// null.
///
/// # Safety
/// `c` valid; `t`, when non-null, a valid sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_tuple_sort_field_decl(
    c: Z3_context,
    t: Z3_sort,
    i: c_uint,
) -> Z3_func_decl {
    if t.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `t` null-checked; `.sort` read single-threaded.
    let dt = match unsafe { &(*t).sort } {
        Sort::Datatype(dt) if dt.constructors.len() == 1 => dt.clone(),
        _ => return ptr::null_mut(),
    };
    let Some(field) = dt.constructors[0].fields.get(i as usize).cloned() else {
        return ptr::null_mut();
    };
    // SAFETY: `c` guarded by `ffi_guard_ptr`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let dt_sort = Sort::Datatype(dt.clone());
            cache_dt_func_decl(
                ctx,
                FuncDecl::new(field.name.clone(), vec![dt_sort], field.sort.clone()),
                DatatypeOp::Accessor {
                    field: field.name.clone(),
                    result_sort: field.sort.clone(),
                },
            )
        })
    }
}

// ============================================================================
// String-literal accessors (long form)
// ============================================================================

/// Contents of a string literal plus its byte length (Z3's `Z3_get_lstring`):
/// characters `1..256` as one (Latin-1) byte each, character 0, characters
/// `>= 256` and a backslash before `u` escaped as `\u{hex}`
/// (`super::zstring::encode_lstring`). z3py decodes the bytes as Latin-1.
///
/// For a non-literal, libz3 4.15.4 returns a non-null EMPTY string, sets
/// `Z3_INVALID_ARG` and leaves `*length` untouched — the error code, not the
/// pointer, is what reports the failure. AY matches that contract exactly:
/// returning null here instead would segfault any consumer that does the
/// perfectly-valid-against-libz3 `strlen(Z3_get_lstring(...))`.
///
/// # Safety
/// `c` valid; `length`, when non-null, a valid writable `unsigned` pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_lstring(
    c: Z3_context,
    s: Z3_ast,
    length: *mut c_uint,
) -> *const c_char {
    if s == 0 {
        return ptr::null();
    }
    // SAFETY: `c` guarded by `ffi_guard_const_ptr`; `length` written only when non-null.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let t =
                require_ast_or_return!(ctx, s, "Z3_get_lstring", "string term", ptr::null()).term;
            let text = if ctx.solver.is_numeral(t) && matches!(ctx.solver.sort_of(t), Sort::String)
            {
                ctx.solver.numeral_string(t)
            } else {
                None
            };
            match text {
                Some(text) => {
                    let bytes = super::zstring::encode_lstring(&text);
                    if !length.is_null() {
                        *length = bytes.len() as c_uint;
                    }
                    super::cache_bytes(ctx, bytes)
                }
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    cache_string(ctx, String::new())
                }
            }
        })
    }
}

/// Code points of a string literal, written into `contents[0..min(length, len)]`
/// (Z3's `Z3_get_string_contents`). `Z3_INVALID_ARG` for a non-literal; no-op
/// for a null buffer.
///
/// # Safety
/// `c` valid; `contents`, when non-null, must be writable for `length` `unsigned`s.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_string_contents(
    c: Z3_context,
    s: Z3_ast,
    length: c_uint,
    contents: *mut c_uint,
) {
    if s == 0 || contents.is_null() {
        return;
    }
    // SAFETY: `c` guarded; `contents` valid for `length` writes by contract.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let t = require_ast_or_return!(ctx, s, "Z3_get_string_contents", "string term").term;
            if let Some(text) =
                super::sets_regex::string_literal_text(ctx, t, "Z3_get_string_contents")
            {
                // Code points, a surrogate read back from its carrier
                // `char` (`ay_core::smtlib_char`).
                for (i, ch) in text.chars().take(length as usize).enumerate() {
                    *contents.add(i) = ay_core::smtlib_code_point(ch);
                }
            }
        })
    }
}

#[cfg(test)]
#[path = "getters_ext_tests.rs"]
mod getters_ext_tests;

// Twin-verified (libz3 4.15.4) group-A getter tests, re-attached after the
// de-dup merge (e9720830) orphaned the file along with the duplicate
// implementation module it originally accompanied (a38fd968).
#[cfg(test)]
#[path = "numeral_sort_introspect_tests.rs"]
mod numeral_sort_introspect_tests;
