// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible set-theory, regular-expression, and string-literal accessor
//! functions (#capi_breadth).
//!
//! These are thin C-ABI adapters over existing AY term builders and solver
//! operations; they add no independent decision procedure. Correctness still
//! depends on each adapter preserving the intended term encoding, sorts,
//! handles, and ABI behavior. Representative coverage lives in
//! `test_sets_capi`, `test_regex_capi`, and `test_string_accessors_capi`.
//!
//! Sets. Z3 models `(Set T)` as the array sort `(Array T Bool)`: a set is its
//! characteristic function. The set constructors below use these direct
//! encodings:
//!   - `Z3_mk_set_sort(T)`        = `(Array T Bool)`
//!   - `Z3_mk_empty_set(T)`       = `((as const (Array T Bool)) false)`
//!   - `Z3_mk_full_set(T)`        = `((as const (Array T Bool)) true)`
//!   - `Z3_mk_set_add(s, e)`      = `(store s e true)`
//!   - `Z3_mk_set_del(s, e)`      = `(store s e false)`
//!   - `Z3_mk_set_member(e, s)`   = `(select s e)`
//! The pointwise set operations (`union`, `intersect`, `complement`, ...) are
//! intentionally not provided because AY exposes no pointwise/lambda array
//! combinator for encoding them.
//!
//! Regular expressions / sequences. These forward to AY's native `str.*` and
//! `re.*` theory operations (see `api/strings/regex.rs`) and are intended to
//! preserve the expected sorts (`RegLan` for builders, `Bool` for membership).
//!
//! String-literal accessors (`Z3_is_string` / `Z3_get_string` /
//! `Z3_get_string_length`) read back a `Constant::String` term; they report
//! "not a string" rather than guessing for any non-literal.

use std::ffi::{c_char, c_uint};
use std::ptr;

use ay_dpll::api::Sort;

use super::{
    alloc_sort, cache_string, ffi_count_within_limit, ffi_guard_ast, ffi_guard_const_ptr,
    ffi_guard_ptr, ffi_guard_uint, lookup_ast_sort, record_ast_sort, require_term_ast_or_return,
    require_term_asts_or_return, term_to_ast, Z3_ast, Z3_context, Z3_sort, Z3_INVALID_ARG,
    Z3_SORT_ERROR,
};

// ============================================================================
// Sets (modelled as Array<elem, Bool>, matching Z3)
// ============================================================================

/// Create a set sort `(Set elem)`, i.e. the array sort `(Array elem Bool)`.
///
/// Matches `Z3_mk_set_sort`.
///
/// # Safety
/// `c` and `elem` must be valid pointers (or `elem` null, which yields null).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_set_sort(c: Z3_context, elem: Z3_sort) -> Z3_sort {
    if elem.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `elem` was null-checked above and originates from a prior AY FFI
    // allocation whose handle is kept alive by the owning `Z3Context`. Reading
    // `.sort` is a shared-read with no concurrent mutation (single-threaded per
    // context).
    let elem_sort = unsafe { (*elem).sort.clone() };
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ptr` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            alloc_sort(ctx, Sort::array(elem_sort.clone(), Sort::Bool))
        })
    }
}

/// Create the empty set over `domain`: `((as const (Array domain Bool)) false)`.
///
/// Matches `Z3_mk_empty_set`.
///
/// # Safety
/// `c` and `domain` must be valid pointers (or `domain` null, which yields 0).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_empty_set(c: Z3_context, domain: Z3_sort) -> Z3_ast {
    if domain.is_null() {
        return 0;
    }
    // SAFETY: see `Z3_mk_set_sort`.
    let domain_sort = unsafe { (*domain).sort.clone() };
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let f = ctx.solver.bool_const(false);
            let t = ctx.solver.const_array(domain_sort.clone(), f);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::array(domain_sort.clone(), Sort::Bool));
            a
        })
    }
}

/// Create the full (universal) set over `domain`:
/// `((as const (Array domain Bool)) true)`.
///
/// Matches `Z3_mk_full_set`.
///
/// # Safety
/// `c` and `domain` must be valid pointers (or `domain` null, which yields 0).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_full_set(c: Z3_context, domain: Z3_sort) -> Z3_ast {
    if domain.is_null() {
        return 0;
    }
    // SAFETY: see `Z3_mk_set_sort`.
    let domain_sort = unsafe { (*domain).sort.clone() };
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let tt = ctx.solver.bool_const(true);
            let t = ctx.solver.const_array(domain_sort.clone(), tt);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::array(domain_sort.clone(), Sort::Bool));
            a
        })
    }
}

/// Add `elem` to `set`: `(store set elem true)`.
///
/// Matches `Z3_mk_set_add`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_set_add(c: Z3_context, set: Z3_ast, elem: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let tt = ctx.solver.bool_const(true);
            let set_term = require_term_ast_or_return!(ctx, set, "Z3_mk_set_add", "set", 0);
            let elem = require_term_ast_or_return!(ctx, elem, "Z3_mk_set_add", "element", 0);
            let t = ctx.solver.store(set_term, elem, tt);
            let a = term_to_ast(ctx, t);
            // The result is the same array (set) sort as the input set.
            if let Some(sort) = lookup_ast_sort(ctx, set).cloned() {
                record_ast_sort(ctx, a, sort);
            }
            a
        })
    }
}

/// Remove `elem` from `set`: `(store set elem false)`.
///
/// Matches `Z3_mk_set_del`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_set_del(c: Z3_context, set: Z3_ast, elem: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let f = ctx.solver.bool_const(false);
            let set_term = require_term_ast_or_return!(ctx, set, "Z3_mk_set_del", "set", 0);
            let elem = require_term_ast_or_return!(ctx, elem, "Z3_mk_set_del", "element", 0);
            let t = ctx.solver.store(set_term, elem, f);
            let a = term_to_ast(ctx, t);
            if let Some(sort) = lookup_ast_sort(ctx, set).cloned() {
                record_ast_sort(ctx, a, sort);
            }
            a
        })
    }
}

/// Test set membership: `(select set elem)`, returning Bool.
///
/// Matches `Z3_mk_set_member`. Note the Z3 argument order is `(elem, set)`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_set_member(c: Z3_context, elem: Z3_ast, set: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let set = require_term_ast_or_return!(ctx, set, "Z3_mk_set_member", "set", 0);
            let elem = require_term_ast_or_return!(ctx, elem, "Z3_mk_set_member", "element", 0);
            let t = ctx.solver.select(set, elem);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

/// Maximum bitvector element width the cardinality constraint is expanded
/// for: `2^8 = 256` selects is the largest sum that stays cheap to build and
/// solve. Wider BV (and Int/Real/uninterpreted) element domains take the
/// honest-`unknown` route instead.
const SET_HAS_SIZE_MAX_BV_WIDTH: u32 = 8;

/// Predicate `|set| = k` over a Boolean array `set` (a set as its
/// characteristic function). Matches `Z3_mk_set_has_size`.
///
/// Finite element domains AY can enumerate — `Bool` and `BitVec w` with
/// `w <= 8` — build the cardinality constraint
/// `(= (+ (ite (select set e_0) 1 0) ...) k)` for the arithmetic/array
/// engines. Other element domains (Int, Real, uninterpreted, wide BV) build a
/// `(set.has_size set k)` predicate; the executor currently returns `unknown`
/// for that unsupported reasoning path rather than treating the predicate as
/// an unconstrained Boolean (a documented divergence from Z3).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_set_has_size(c: Z3_context, set: Z3_ast, k: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks
    // it and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if set == 0 || k == 0 {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_set_has_size: null AST argument".to_string());
                return 0;
            }
            let set_t = require_term_ast_or_return!(ctx, set, "Z3_mk_set_has_size", "set", 0);
            let k_t = require_term_ast_or_return!(ctx, k, "Z3_mk_set_has_size", "size", 0);
            let set_sort = ctx.solver.sort_of(set_t);
            let Sort::Array(arr) = &set_sort else {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(format!(
                    "Z3_mk_set_has_size: expected a set ((Array E Bool)) argument, got {set_sort:?}"
                ));
                return 0;
            };
            if arr.element_sort != Sort::Bool {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg = Some(format!(
                    "Z3_mk_set_has_size: expected a set ((Array E Bool)) argument, got {set_sort:?}"
                ));
                return 0;
            }
            if ctx.solver.sort_of(k_t) != Sort::Int {
                ctx.last_error = Z3_SORT_ERROR;
                ctx.error_msg =
                    Some("Z3_mk_set_has_size: cardinality argument must be Int-sorted".to_string());
                return 0;
            }
            // Enumerate the element domain when it is finite and small.
            let elems = match &arr.index_sort {
                Sort::Bool => Some(vec![
                    ctx.solver.bool_const(false),
                    ctx.solver.bool_const(true),
                ]),
                Sort::BitVec(bv) if bv.width <= SET_HAS_SIZE_MAX_BV_WIDTH => {
                    let width = bv.width;
                    Some(
                        (0..(1u64 << width))
                            .map(|v| ctx.solver.bv_const_u64(v, width))
                            .collect(),
                    )
                }
                _ => None,
            };
            let t = match elems {
                Some(elems) => {
                    // REAL constraint: |set| as an exact ite-sum over the
                    // whole (finite) domain, equated to k.
                    let one = ctx.solver.int_const(1);
                    let zero = ctx.solver.int_const(0);
                    let mut sum = zero;
                    for e in elems {
                        let member = ctx.solver.select(set_t, e);
                        let contrib = ctx.solver.ite(member, one, zero);
                        sum = ctx.solver.add(sum, contrib);
                    }
                    ctx.solver.eq(sum, k_t)
                }
                // Honest divergence: REAL `(set.has_size set k)` term; the
                // executor's fail-closed gate turns any solve over it into
                // `unknown` (see the function doc).
                None => ctx.solver.set_has_size(set_t, k_t),
            };
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Bool);
            a
        })
    }
}

// ============================================================================
// Regular expressions / sequence-regex bridge
// ============================================================================

/// Convert a string/sequence into the regex matching exactly it (`str.to_re`),
/// returning RegLan. Matches `Z3_mk_seq_to_re`.
///
/// On a sort mismatch (argument not a String) this records `Z3_SORT_ERROR` and
/// returns 0 rather than fabricating a term.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_to_re(c: Z3_context, seq: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let seq = require_term_ast_or_return!(ctx, seq, "Z3_mk_seq_to_re", "sequence", 0);
            match ctx.solver.try_str_to_re(seq) {
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

/// Test sequence membership in a regex (`str.in_re`), returning Bool.
/// Matches `Z3_mk_seq_in_re`.
///
/// On a sort mismatch this records `Z3_SORT_ERROR` and returns 0.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_in_re(c: Z3_context, seq: Z3_ast, re: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let seq = require_term_ast_or_return!(ctx, seq, "Z3_mk_seq_in_re", "sequence", 0);
            let re = require_term_ast_or_return!(ctx, re, "Z3_mk_seq_in_re", "regex", 0);
            match ctx.solver.try_str_in_re(seq, re) {
                Ok(t) => {
                    let a = term_to_ast(ctx, t);
                    record_ast_sort(ctx, a, Sort::Bool);
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

/// Kleene star of a regex (`re.*`), returning RegLan. Matches `Z3_mk_re_star`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_re_star(c: Z3_context, re: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let re = require_term_ast_or_return!(ctx, re, "Z3_mk_re_star", "regex", 0);
            match ctx.solver.try_re_star(re) {
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

/// Kleene plus of a regex (`re.+`), returning RegLan. Matches `Z3_mk_re_plus`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_re_plus(c: Z3_context, re: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let re = require_term_ast_or_return!(ctx, re, "Z3_mk_re_plus", "regex", 0);
            match ctx.solver.try_re_plus(re) {
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

/// Union of `n` regexes (`re.union`), returning RegLan. Matches `Z3_mk_re_union`.
///
/// Z3's `re.union` is n-ary; AY's `re_union` is binary, so this left-folds.
/// `n == 0` is an honest error (`Z3_INVALID_ARG`, returns 0): the empty union
/// (empty language) has no AY constructor, so we do not fabricate one.
///
/// # Safety
/// `c` must be a valid context pointer; `args` must point to `n` valid `Z3_ast`.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_re_union(c: Z3_context, n: c_uint, args: *const Z3_ast) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_re_union", n) } {
        return 0;
    }
    if n == 0 || args.is_null() {
        // SAFETY: see below; ffi_guard_ast null-checks `c`.
        unsafe {
            return ffi_guard_ast(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                0
            });
        }
    }
    let term_asts: Vec<_> = (0..n as usize)
        // SAFETY: caller guarantees `args` points to at least `n` elements; the
        // count was range-checked and `args` null-checked above.
        .map(|i| unsafe { *args.add(i) })
        .collect();
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let terms = require_term_asts_or_return!(ctx, &term_asts, "Z3_mk_re_union", 0);
            let mut acc = terms[0];
            for &t in &terms[1..] {
                match ctx.solver.try_re_union(acc, t) {
                    Ok(r) => acc = r,
                    Err(_) => {
                        ctx.last_error = Z3_SORT_ERROR;
                        return 0;
                    }
                }
            }
            let a = term_to_ast(ctx, acc);
            record_ast_sort(ctx, a, Sort::RegLan);
            a
        })
    }
}

/// Concatenation of `n` regexes (`re.++`), returning RegLan.
/// Matches `Z3_mk_re_concat`.
///
/// Z3's `re.++` is n-ary; AY's `re_concat` is binary, so this left-folds.
/// `n == 0` is an honest error (`Z3_INVALID_ARG`, returns 0).
///
/// # Safety
/// `c` must be a valid context pointer; `args` must point to `n` valid `Z3_ast`.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_re_concat(c: Z3_context, n: c_uint, args: *const Z3_ast) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_re_concat", n) } {
        return 0;
    }
    if n == 0 || args.is_null() {
        // SAFETY: ffi_guard_ast null-checks `c`.
        unsafe {
            return ffi_guard_ast(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                0
            });
        }
    }
    let term_asts: Vec<_> = (0..n as usize)
        // SAFETY: caller guarantees `args` points to at least `n` elements; the
        // count was range-checked and `args` null-checked above.
        .map(|i| unsafe { *args.add(i) })
        .collect();
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let terms = require_term_asts_or_return!(ctx, &term_asts, "Z3_mk_re_concat", 0);
            let mut acc = terms[0];
            for &t in &terms[1..] {
                match ctx.solver.try_re_concat(acc, t) {
                    Ok(r) => acc = r,
                    Err(_) => {
                        ctx.last_error = Z3_SORT_ERROR;
                        return 0;
                    }
                }
            }
            let a = term_to_ast(ctx, acc);
            record_ast_sort(ctx, a, Sort::RegLan);
            a
        })
    }
}

/// Optional regex (`re.opt`), matching the empty string or `re`. Returns
/// RegLan. Matches `Z3_mk_re_option`.
///
/// On a sort mismatch (argument not RegLan) this records `Z3_SORT_ERROR` and
/// returns 0.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_re_option(c: Z3_context, re: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let re = require_term_ast_or_return!(ctx, re, "Z3_mk_re_option", "regex", 0);
            match ctx.solver.try_re_opt(re) {
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

/// Complement of a regex (`re.comp`), matching every string `re` does not.
/// Returns RegLan. Matches `Z3_mk_re_complement`.
///
/// On a sort mismatch this records `Z3_SORT_ERROR` and returns 0.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_re_complement(c: Z3_context, re: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let re = require_term_ast_or_return!(ctx, re, "Z3_mk_re_complement", "regex", 0);
            match ctx.solver.try_re_comp(re) {
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

/// Intersection of `n` regexes (`re.inter`), returning RegLan.
/// Matches `Z3_mk_re_intersect`.
///
/// Z3's `re.inter` is n-ary; AY's `re_inter` is binary, so this left-folds.
/// `n == 0` is an honest error (`Z3_INVALID_ARG`, returns 0).
///
/// # Safety
/// `c` must be a valid context pointer; `args` must point to `n` valid `Z3_ast`.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_re_intersect(
    c: Z3_context,
    n: c_uint,
    args: *const Z3_ast,
) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_re_intersect", n) } {
        return 0;
    }
    if n == 0 || args.is_null() {
        // SAFETY: ffi_guard_ast null-checks `c`.
        unsafe {
            return ffi_guard_ast(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                0
            });
        }
    }
    let term_asts: Vec<_> = (0..n as usize)
        // SAFETY: caller guarantees `args` points to at least `n` elements; the
        // count was range-checked and `args` null-checked above.
        .map(|i| unsafe { *args.add(i) })
        .collect();
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let terms = require_term_asts_or_return!(ctx, &term_asts, "Z3_mk_re_intersect", 0);
            let mut acc = terms[0];
            for &t in &terms[1..] {
                match ctx.solver.try_re_inter(acc, t) {
                    Ok(r) => acc = r,
                    Err(_) => {
                        ctx.last_error = Z3_SORT_ERROR;
                        return 0;
                    }
                }
            }
            let a = term_to_ast(ctx, acc);
            record_ast_sort(ctx, a, Sort::RegLan);
            a
        })
    }
}

/// Range regex (`re.range`) over two single-character strings `lo` and `hi`,
/// matching every character in `[lo, hi]`. Returns RegLan.
/// Matches `Z3_mk_re_range`.
///
/// On a sort mismatch (an argument not String) this records `Z3_SORT_ERROR`
/// and returns 0.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_re_range(c: Z3_context, lo: Z3_ast, hi: Z3_ast) -> Z3_ast {
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let lo = require_term_ast_or_return!(ctx, lo, "Z3_mk_re_range", "lower bound", 0);
            let hi = require_term_ast_or_return!(ctx, hi, "Z3_mk_re_range", "upper bound", 0);
            match ctx.solver.try_re_range(lo, hi) {
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

/// Bounded-repetition regex (`(_ re.loop lo hi) re`), matching between `lo`
/// and `hi` repetitions of `re`. Returns RegLan. Matches `Z3_mk_re_loop`.
///
/// On a sort mismatch (argument not RegLan) this records `Z3_SORT_ERROR` and
/// returns 0.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_re_loop(
    c: Z3_context,
    re: Z3_ast,
    lo: c_uint,
    hi: c_uint,
) -> Z3_ast {
    if lo > hi {
        // SAFETY: `c` is governed by this entry point's context-pointer contract;
        // the guard catches any panic while recording the invalid indexed term.
        return unsafe {
            ffi_guard_ast(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_mk_re_loop: lower bound {lo} exceeds upper bound {hi}"
                ));
                0
            })
        };
    }
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            let re = require_term_ast_or_return!(ctx, re, "Z3_mk_re_loop", "regex", 0);
            match ctx.solver.try_re_loop(re, lo, hi) {
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

/// Universal-language regex (`re.all`) of the given regex sort. Returns RegLan.
/// Matches `Z3_mk_re_full`.
///
/// AY's `RegLan` is monomorphic (string regex), so `re_sort` is validated to be
/// a regex sort but does not parameterize the result. A null or non-regex
/// `re_sort` is an honest error.
///
/// # Safety
/// `c` must be a valid context pointer; `re_sort` a valid sort pointer (or null).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_re_full(c: Z3_context, re_sort: Z3_sort) -> Z3_ast {
    if re_sort.is_null() {
        return 0;
    }
    // SAFETY: `re_sort` was null-checked above and originates from a prior AY FFI
    // allocation kept alive by the owning context.
    let s = unsafe { (*re_sort).sort.clone() };
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if !matches!(s, Sort::RegLan) {
                ctx.last_error = Z3_SORT_ERROR;
                return 0;
            }
            let t = ctx.solver.re_all();
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::RegLan);
            a
        })
    }
}

/// Empty-language regex (`re.none`) of the given regex sort. Returns RegLan.
/// Matches `Z3_mk_re_empty`.
///
/// AY's `RegLan` is monomorphic; see [`Z3_mk_re_full`] for the `re_sort`
/// contract. A null or non-regex `re_sort` is an honest error.
///
/// # Safety
/// `c` must be a valid context pointer; `re_sort` a valid sort pointer (or null).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_re_empty(c: Z3_context, re_sort: Z3_sort) -> Z3_ast {
    if re_sort.is_null() {
        return 0;
    }
    // SAFETY: see `Z3_mk_re_full`.
    let s = unsafe { (*re_sort).sort.clone() };
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if !matches!(s, Sort::RegLan) {
                ctx.last_error = Z3_SORT_ERROR;
                return 0;
            }
            let t = ctx.solver.re_none();
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::RegLan);
            a
        })
    }
}

/// Any-single-character regex (`re.allchar`) of the given regex sort. Returns
/// RegLan. Matches `Z3_mk_re_allchar`.
///
/// AY's `RegLan` is monomorphic; see [`Z3_mk_re_full`] for the `re_sort`
/// contract. A null or non-regex `re_sort` is an honest error.
///
/// # Safety
/// `c` must be a valid context pointer; `re_sort` a valid sort pointer (or null).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_re_allchar(c: Z3_context, re_sort: Z3_sort) -> Z3_ast {
    if re_sort.is_null() {
        return 0;
    }
    // SAFETY: see `Z3_mk_re_full`.
    let s = unsafe { (*re_sort).sort.clone() };
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_ast` null-checks it.
    unsafe {
        ffi_guard_ast(c, |ctx| {
            if !matches!(s, Sort::RegLan) {
                ctx.last_error = Z3_SORT_ERROR;
                return 0;
            }
            let t = ctx.solver.re_allchar();
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::RegLan);
            a
        })
    }
}

// ============================================================================
// String-literal accessors
// ============================================================================

/// Return true iff `a` is a string literal (a `Constant::String` of sort String).
///
/// Matches `Z3_is_string`. Non-literal string-sorted terms (e.g. `(str.++ x y)`)
/// and non-string terms report false.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_is_string(c: Z3_context, a: Z3_ast) -> bool {
    if a == 0 {
        return false;
    }
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_uint` null-checks it
    // and catches panics so none cross the FFI boundary. Encode bool as 0/1.
    let r = unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            let t = require_term_ast_or_return!(ctx, a, "Z3_is_string", "AST", 0);
            let is_str_lit =
                ctx.solver.is_numeral(t) && matches!(ctx.solver.sort_of(t), Sort::String);
            u32::from(is_str_lit)
        })
    };
    r != 0
}

/// Return the unescaped contents of a string literal AST.
///
/// Matches `Z3_get_string`. Returns null for a non-literal (and sets no model
/// state — this is a pure accessor). The returned pointer is owned by the
/// context (Z3 convention).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_string(c: Z3_context, a: Z3_ast) -> *const c_char {
    if a == 0 {
        return ptr::null();
    }
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_const_ptr`
    // null-checks it and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let t = require_term_ast_or_return!(ctx, a, "Z3_get_string", "AST", ptr::null());
            // Only a genuine string literal yields a value; guessing for a
            // non-literal would be unsound.
            if ctx.solver.is_numeral(t) && matches!(ctx.solver.sort_of(t), Sort::String) {
                match ctx.solver.numeral_string(t) {
                    Some(s) => cache_string(ctx, s),
                    None => ptr::null(),
                }
            } else {
                ptr::null()
            }
        })
    }
}

/// Return the character length of a string literal AST.
///
/// Matches `Z3_get_string_length`. Returns 0 for a non-literal.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_string_length(c: Z3_context, a: Z3_ast) -> c_uint {
    if a == 0 {
        return 0;
    }
    // SAFETY: `c` is the caller's context pointer; `ffi_guard_uint` null-checks it
    // and catches panics so none cross the FFI boundary.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            let t = require_term_ast_or_return!(ctx, a, "Z3_get_string_length", "AST", 0);
            if ctx.solver.is_numeral(t) && matches!(ctx.solver.sort_of(t), Sort::String) {
                match ctx.solver.numeral_string(t) {
                    // Z3 counts code points; AY string literals are unescaped
                    // Rust strings, so chars() gives the code-point count.
                    Some(s) => s.chars().count() as c_uint,
                    None => 0,
                }
            } else {
                0
            }
        })
    }
}

// ============================================================================
// Version / global parameters
// ============================================================================

/// Return a human-readable version string, e.g.
/// `"AY <ver> (Z3 5.0.0.0 compatible)"`.
///
/// Matches `Z3_get_full_version`. The pointer is owned by the library and is
/// valid for the program lifetime (Z3 convention).
#[no_mangle]
pub extern "C" fn Z3_get_full_version() -> *const c_char {
    // Reports the same Z3 API compatibility version as `Z3_get_version`
    // (5.0.0.0), plus AY's own crate version for provenance. A 'static
    // NUL-terminated string is valid for the program lifetime, matching Z3's
    // ownership contract.
    concat!(
        "AY ",
        env!("CARGO_PKG_VERSION"),
        " (Z3 5.0.0.0 compatible)\0"
    )
    .as_ptr()
    .cast::<c_char>()
}

// `Z3_global_param_set` / `Z3_global_param_reset_all` moved to
// `global_params.rs` (real readable store + measured z3 4.15.4 registry
// defaults, alongside `Z3_global_param_get`).
