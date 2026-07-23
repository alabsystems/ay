// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible accessor long-tail: numeral introspection, sort structure,
//! quantifier/pattern queries, registry enumerators, tuple-sort decls, and the
//! remaining `Z3_is_*` predicates (Track B, C-API long-tail Wave G).
//!
//! Every function is real over existing AY engine/handle state, or an HONEST
//! DOCUMENTED DIVERGENCE where AY structurally lacks the queried capability
//! (real-closed-field algebraic numbers, `(as-array f)` nodes, decl parameters
//! other than integers, finite-domain / relation sorts, de-Bruijn indices,
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
    alloc_sort, cache_dt_func_decl, cache_string, ffi_guard_ast, ffi_guard_const_ptr,
    ffi_guard_double, ffi_guard_int, ffi_guard_ptr, ffi_guard_uint, ffi_guard_void,
    record_ast_sort, require_term_ast_or_return, term_to_ast, DatatypeOp, Z3_ast, Z3_context,
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
            let term = require_term_ast_or_return!(ctx, a, "Z3_get_numerator", "numeral", 0);
            match ctx
                .solver
                .numeral_string(term)
                .as_deref()
                .and_then(numeral_parts)
            {
                Some((num, _den)) => {
                    let t = ctx.solver.int_const_bigint(&num);
                    let ast = term_to_ast(ctx, t);
                    record_ast_sort(ctx, ast, Sort::Int);
                    ast
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
            let term = require_term_ast_or_return!(ctx, a, "Z3_get_denominator", "numeral", 0);
            match ctx
                .solver
                .numeral_string(term)
                .as_deref()
                .and_then(numeral_parts)
            {
                Some((_num, den)) => {
                    let t = ctx.solver.int_const_bigint(&den);
                    let ast = term_to_ast(ctx, t);
                    record_ast_sort(ctx, ast, Sort::Int);
                    ast
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
            let t = require_term_ast_or_return!(ctx, a, "Z3_get_numeral_double", "numeral", 0.0);
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
                require_term_ast_or_return!(ctx, v, "Z3_get_numeral_rational_int64", "numeral", 0);
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
            let term = require_term_ast_or_return!(ctx, a, "Z3_get_numeral_small", "numeral", 0);
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
            let term = require_term_ast_or_return!(
                ctx,
                a,
                "Z3_get_numeral_binary_string",
                "numeral",
                ptr::null()
            );
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
            let root = require_term_ast_or_return!(ctx, a, "Z3_get_depth", "term", 0);
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
            let term = require_term_ast_or_return!(ctx, a, "Z3_get_index_value", "term", 0);
            if let TermKind::Var { name } = ctx.solver.term_kind(term) {
                if let Some(idx) = name
                    .strip_prefix("__db")
                    .and_then(|s| s.parse::<c_uint>().ok())
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

/// Z3's `Z3_is_algebraic_number`. AY numerals are exact rationals — no RCF
/// algebraic-number AST exists — so always false.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_algebraic_number(_c: Z3_context, _a: Z3_ast) -> bool {
    false
}

/// Z3's `Z3_is_as_array`. AY builds no `(as-array f)` node — always false.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_as_array(_c: Z3_context, _a: Z3_ast) -> bool {
    false
}

/// Z3's `Z3_get_as_array_func_decl`. No `(as-array f)` node exists in AY.
/// DIVERGENCE: set `Z3_INVALID_ARG`, return null.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_as_array_func_decl(c: Z3_context, _a: Z3_ast) -> Z3_func_decl {
    // SAFETY: `c` guarded by `ffi_guard_ptr`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            ctx.last_error = Z3_INVALID_ARG;
            ptr::null_mut()
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
            let _term = require_term_ast_or_return!(ctx, t, "Z3_is_well_sorted", "term", 0);
            1
        }) != 0
    }
}

// ============================================================================
// Decl parameters — DIVERGENCE (AY decls carry only integer params)
// ============================================================================
//
// `FuncDeclHandle.params` is `Vec<c_int>`: AY func_decls only ever carry INTEGER
// parameters (indexed BV ops like extract/rotate). No decl carries an AST /
// double / rational / sort / symbol / func_decl parameter, so every such query
// is out of range. Each sets `Z3_IOB` and returns a null/zero sentinel.

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

/// Z3's `Z3_get_decl_func_decl_parameter` — no func_decl decl parameters in AY.
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_func_decl_parameter(
    c: Z3_context,
    _d: Z3_func_decl,
    _idx: c_uint,
) -> Z3_func_decl {
    // SAFETY: `c` guarded by `ffi_guard_ptr`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            ctx.last_error = Z3_IOB;
            ptr::null_mut()
        })
    }
}

/// Z3's `Z3_get_decl_rational_parameter` — no rational decl parameters in AY.
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_rational_parameter(
    c: Z3_context,
    _d: Z3_func_decl,
    _idx: c_uint,
) -> Z3_string {
    // SAFETY: `c` guarded by `ffi_guard_const_ptr`.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
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
    _d: Z3_func_decl,
    _idx: c_uint,
) -> Z3_sort {
    // SAFETY: `c` guarded by `ffi_guard_ptr`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
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
            Some(t) => term_to_ast(ctx, t),
            None => {
                ctx.last_error = Z3_IOB;
                0
            }
        })
    }
}

/// Z3's `Z3_get_quantifier_id` — the `:qid` (quantifier identifier).
///
/// REAL for any quantifier given an EXPLICIT `:qid` (via `Z3_mk_quantifier_ex`/
/// `_const_ex` or SMT-LIB `:qid`): the id round-trips exactly. RESIDUAL honest
/// divergence only when NO explicit qid was set — Z3 there auto-generates a
/// synthetic symbol AY cannot replicate, so we return null (`Z3_INVALID_ARG`)
/// rather than fabricate one.
///
/// Benign caveat: two structurally-identical quantifiers differing only in `:qid`
/// hash-cons to one term, so the side-map keeps the last-set qid — metadata only,
/// never affects any sat/unsat verdict.
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
            let term = require_term_ast_or_return!(
                ctx,
                a,
                "Z3_get_quantifier_id",
                "quantifier",
                ptr::null_mut()
            );
            match ctx.solver.quantifier_id(term) {
                Some(name) => super::cache_symbol(ctx, name),
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
            let term = require_term_ast_or_return!(
                ctx,
                a,
                "Z3_get_quantifier_skolem_id",
                "quantifier",
                ptr::null_mut()
            );
            match ctx.solver.skolem_id(term) {
                Some(name) => super::cache_symbol(ctx, name),
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ptr::null_mut()
                }
            }
        })
    }
}

/// Z3's `Z3_is_lambda`. AY has no lambda term — always false.
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_lambda(_c: Z3_context, _a: Z3_ast) -> bool {
    false
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

/// Unescaped contents of a string literal plus its byte length (Z3's
/// `Z3_get_lstring`).
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
                require_term_ast_or_return!(ctx, s, "Z3_get_lstring", "string term", ptr::null());
            let text = if ctx.solver.is_numeral(t) && matches!(ctx.solver.sort_of(t), Sort::String)
            {
                ctx.solver.numeral_string(t)
            } else {
                None
            };
            match text {
                Some(text) => {
                    if !length.is_null() {
                        *length = text.len() as c_uint;
                    }
                    cache_string(ctx, text)
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
/// (Z3's `Z3_get_string_contents`). No-op for a non-literal or null buffer.
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
            let t = require_term_ast_or_return!(ctx, s, "Z3_get_string_contents", "string term");
            if ctx.solver.is_numeral(t) && matches!(ctx.solver.sort_of(t), Sort::String) {
                if let Some(text) = ctx.solver.numeral_string(t) {
                    for (i, ch) in text.chars().take(length as usize).enumerate() {
                        *contents.add(i) = ch as c_uint;
                    }
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
