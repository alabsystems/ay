// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible sequence and string operation functions (#phase3-seq).
//!
//! These wire Z3's polymorphic `Z3_mk_seq_*` constructors (plus `Z3_mk_string`
//! and the `str <-> int` conversions) onto AY's native theories. AY models a
//! String as a first-class [`Sort::String`] with a dedicated `str.*` theory
//! (rather than `(Seq Char)`), while general sequences use [`Sort::Seq`]. Z3's
//! sequence API is polymorphic over both, so each `Z3_mk_seq_*` here inspects
//! the operand's sort and dispatches:
//!
//! - [`Sort::String`] operands route to AY's `str_*` Solver methods.
//! - [`Sort::Seq`] operands route to AY's `seq_*` Solver methods.
//!
//! Every operation below is backed by a real `ay_dpll::api::Solver` method whose
//! constructed term matches the Z3 / SMT-LIB 2.6 semantics (cross-checked
//! against z3 4.15). Functions whose semantics AY cannot construct soundly
//! (e.g. `Z3_mk_seq_nth` on a String, which would require a Char element sort AY
//! does not model) return a null AST and record a `Z3_SORT_ERROR` rather than
//! fabricating a term.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via the
//! `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_char, c_uint};

use ay_dpll::api::{Sort, Term};

use super::zstring::decode_escaped;
use super::{
    ffi_count_within_limit, ffi_guard_mk, ffi_read_bounded_bytes, record_ast_sort,
    require_term_ast_or_return, require_term_asts_or_return, term_to_ast, Z3Context, Z3_ast,
    Z3_context, Z3_sort, Z3_INVALID_ARG, Z3_SORT_ERROR,
};

/// Whether a term is AY's first-class String sort.
fn is_string(ctx: &Z3Context, t: Term) -> bool {
    matches!(ctx.solver.sort_of(t), Sort::String)
}

/// Record a `Z3_SORT_ERROR` on the context and return the null AST sentinel.
fn sort_error(ctx: &mut Z3Context, msg: &str) -> Z3_ast {
    ctx.last_error = Z3_SORT_ERROR;
    ctx.error_msg = Some(msg.to_string());
    0
}

/// Construct Z3's sequence power over a String or a general sequence.
///
/// # Safety
/// All handles must be live and owned by `c`, on the calling thread.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_power(c: Z3_context, s: Z3_ast, n: Z3_ast) -> Z3_ast {
    // SAFETY: handles are forwarded under the caller's ownership contract.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_seq_power", |ctx| {
            let base = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_power", "sequence", 0);
            let count = require_term_ast_or_return!(ctx, n, "Z3_mk_seq_power", "exponent", 0);
            let sort = ctx.solver.sort_of(base);
            match ctx.solver.try_seq_power(base, count) {
                Ok(term) => {
                    let ast = term_to_ast(ctx, term);
                    record_ast_sort(ctx, ast, sort)
                }
                Err(error) => sort_error(ctx, &error.to_string()),
            }
        })
    }
}

// =========================================================================
// String literal
// =========================================================================

/// Create a string literal from a (Z3-escaped) C string.
///
/// The bytes are read as z3 reads them (`super::zstring::decode_escaped`):
/// `\u{h..}` and `\uhhhh` escapes are decoded and every other byte is the
/// character with that value. A null string sets `Z3_INVALID_ARG`, as in z3.
/// Backed by `Solver::string_const`.
///
/// # Safety
/// `c` must be a valid context pointer; `s` must be null or a valid,
/// null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_string(c: Z3_context, s: *const c_char) -> Z3_ast {
    // SAFETY: `s` is null or a valid NUL-terminated string per the caller
    // contract; the helper null-checks it and bounds the scan and copy.
    let bytes = unsafe { ffi_read_bounded_bytes(s) };
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_string", |ctx| {
            let bytes = match &bytes {
                Ok(bytes) => bytes,
                Err(error) => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!("Z3_mk_string: {error}"));
                    return 0;
                }
            };
            let value = decode_escaped(bytes);
            let t = ctx.solver.string_const(&value);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::String)
        })
    }
}

// =========================================================================
// Sequence construction
// =========================================================================

/// Create the empty sequence of the given sequence sort.
///
/// `seq` must be a `(Seq T)` or the String sort. For `(Seq T)` this is backed by
/// `Solver::seq_empty(T)`; for the String sort it is the empty string literal.
///
/// # Safety
/// `c` and `seq` must be valid pointers (`seq` null yields the null AST).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_empty(c: Z3_context, seq: Z3_sort) -> Z3_ast {
    if seq.is_null() {
        return 0;
    }
    // SAFETY: `seq` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context`. Reading `.sort` is a shared-read with no
    // concurrent mutation because the Z3 C API is single-threaded per context.
    let sort = unsafe { (*seq).sort.clone() };
    // SAFETY: see module-level note; `ffi_guard_ast` handles null `c` and panic isolation.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_seq_empty", |ctx| match sort {
            Sort::String => {
                let t = ctx.solver.string_const("");
                let a = term_to_ast(ctx, t);
                record_ast_sort(ctx, a, Sort::String)
            }
            Sort::Seq(elem) => {
                let t = ctx.solver.seq_empty((*elem).clone());
                let a = term_to_ast(ctx, t);
                record_ast_sort(ctx, a, Sort::seq((*elem).clone()))
            }
            other => sort_error(
                ctx,
                &format!("Z3_mk_seq_empty: expected a sequence sort, got {other:?}"),
            ),
        })
    }
}

/// Create a unit sequence `(seq.unit a)` containing the single element `a`.
///
/// Backed by `Solver::seq_unit`; the unit of a `Char` is the one-character
/// `String` (z3's `String` is `(Seq Char)`).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_unit(c: Z3_context, a: Z3_ast) -> Z3_ast {
    // SAFETY: see module-level note; `ffi_guard_ast` handles null `c` and panic isolation.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_seq_unit", |ctx| {
            let elem = require_term_ast_or_return!(ctx, a, "Z3_mk_seq_unit", "element", 0);
            // A Char (stored as its bounded Int code point) makes a String, as
            // in z3: the one-character string `str.from_code(c)`, which the Char
            // bound 0..=0x2FFFF keeps from ever being the empty string.
            if super::lookup_ast_sort(ctx, a) == Some(&Sort::Char) {
                // A literal character makes the one-character literal, which
                // z3's simplifier also gives.
                let literal = ctx
                    .solver
                    .numeral_string(elem)
                    .and_then(|code| code.parse::<u32>().ok())
                    .and_then(ay_core::smtlib_char);
                let t = match literal {
                    Some(ch) => ctx.solver.string_const(&ch.to_string()),
                    None => ctx.solver.string_from_code(elem),
                };
                let r = term_to_ast(ctx, t);
                let r = record_ast_sort(ctx, r, Sort::String);
                return r;
            }
            let elem_sort = ctx.solver.sort_of(elem);
            let t = ctx.solver.seq_unit(elem);
            let r = term_to_ast(ctx, t);
            record_ast_sort(ctx, r, Sort::seq(elem_sort))
        })
    }
}

/// Concatenate `n` sequences (or strings) given in `args`.
///
/// Backed by `Solver::seq_concat` / `Solver::str_concat`, folded left-to-right.
/// All arguments must share the same sequence/string sort.
///
/// # Safety
/// `c` must be valid; `args` must point to `n` valid `Z3_ast` values.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_concat(c: Z3_context, n: c_uint, args: *const Z3_ast) -> Z3_ast {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_seq_concat", n) } {
        return 0;
    }
    if n == 0 || args.is_null() {
        return 0;
    }
    // SAFETY: The caller's `# Safety` contract guarantees `args` points to `n` valid elements.
    let terms: Vec<Z3_ast> = (0..n as usize).map(|i| unsafe { *args.add(i) }).collect();
    // SAFETY: see module-level note; `ffi_guard_ast` handles null `c` and panic isolation.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_seq_concat", |ctx| {
            let decoded = require_term_asts_or_return!(ctx, &terms, "Z3_mk_seq_concat", 0);
            let first = decoded[0];
            let is_str = is_string(ctx, first);
            let result_sort = ctx.solver.sort_of(first);
            let mut acc = first;
            for &next in &decoded[1..] {
                acc = if is_str {
                    ctx.solver.str_concat(acc, next)
                } else {
                    ctx.solver.seq_concat(acc, next)
                };
            }
            let a = term_to_ast(ctx, acc);
            record_ast_sort(ctx, a, result_sort)
        })
    }
}

// =========================================================================
// Length
// =========================================================================

/// Length of a sequence or string, returning Int.
///
/// Backed by `Solver::seq_len` / `Solver::str_len`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_length(c: Z3_context, s: Z3_ast) -> Z3_ast {
    // SAFETY: see module-level note; `ffi_guard_ast` handles null `c` and panic isolation.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_seq_length", |ctx| {
            let seq = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_length", "sequence", 0);
            let t = if is_string(ctx, seq) {
                ctx.solver.str_len(seq)
            } else {
                ctx.solver.seq_len(seq)
            };
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Int)
        })
    }
}

// =========================================================================
// Element / position access
// =========================================================================

/// Length-1 subsequence of `s` at `index` (`Z3_mk_seq_at`).
///
/// Z3 defines `seq.at` as the unit subsequence at `index`, i.e.
/// `seq.extract(s, index, 1)`; for strings it is `str.at`. Backed by
/// `Solver::seq_extract` (for `(Seq T)`) or `Solver::str_at` (for String).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_at(c: Z3_context, s: Z3_ast, index: Z3_ast) -> Z3_ast {
    // SAFETY: see module-level note; `ffi_guard_ast` handles null `c` and panic isolation.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_seq_at", |ctx| {
            let seq = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_at", "sequence", 0);
            let idx = require_term_ast_or_return!(ctx, index, "Z3_mk_seq_at", "index", 0);
            if is_string(ctx, seq) {
                let t = ctx.solver.str_at(seq, idx);
                let a = term_to_ast(ctx, t);
                record_ast_sort(ctx, a, Sort::String)
            } else {
                let result_sort = ctx.solver.sort_of(seq);
                // seq.at(s, i) == seq.extract(s, i, 1) — exactly Z3's semantics.
                let one = ctx.solver.int_const(1);
                let t = ctx.solver.seq_extract(seq, idx, one);
                let a = term_to_ast(ctx, t);
                record_ast_sort(ctx, a, result_sort)
            }
        })
    }
}

/// Element of sequence `s` at `index` (`Z3_mk_seq_nth`), returning the element
/// sort.
///
/// Backed by `Solver::seq_nth`. Only valid for `(Seq T)`: AY does not model a
/// Char element sort, so this returns a `Z3_SORT_ERROR` for String operands
/// rather than fabricating a value.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_nth(c: Z3_context, s: Z3_ast, index: Z3_ast) -> Z3_ast {
    // SAFETY: see module-level note; `ffi_guard_ast` handles null `c` and panic isolation.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_seq_nth", |ctx| {
            let seq = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_nth", "sequence", 0);
            match ctx.solver.sort_of(seq) {
                Sort::Seq(elem) => {
                    let idx = require_term_ast_or_return!(ctx, index, "Z3_mk_seq_nth", "index", 0);
                    let t = ctx.solver.seq_nth(seq, idx);
                    let a = term_to_ast(ctx, t);
                    record_ast_sort(ctx, a, (*elem).clone())
                }
                other => sort_error(
                    ctx,
                    &format!(
                        "Z3_mk_seq_nth: AY models String without a Char element sort; \
                         use Z3_mk_seq_at for a length-1 substring. Got {other:?}"
                    ),
                ),
            }
        })
    }
}

/// Subsequence of `s` starting at `offset` of length `length` (`Z3_mk_seq_extract`).
///
/// Backed by `Solver::seq_extract` / `Solver::str_substr`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_extract(
    c: Z3_context,
    s: Z3_ast,
    offset: Z3_ast,
    length: Z3_ast,
) -> Z3_ast {
    // SAFETY: see module-level note; `ffi_guard_ast` handles null `c` and panic isolation.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_seq_extract", |ctx| {
            let seq = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_extract", "sequence", 0);
            let off = require_term_ast_or_return!(ctx, offset, "Z3_mk_seq_extract", "offset", 0);
            let len = require_term_ast_or_return!(ctx, length, "Z3_mk_seq_extract", "length", 0);
            let result_sort = ctx.solver.sort_of(seq);
            let t = if is_string(ctx, seq) {
                ctx.solver.str_substr(seq, off, len)
            } else {
                ctx.solver.seq_extract(seq, off, len)
            };
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, result_sort)
        })
    }
}

// =========================================================================
// Predicates
// =========================================================================

/// Test whether `container` contains `containee` (`Z3_mk_seq_contains`),
/// returning Bool.
///
/// Backed by `Solver::seq_contains` / `Solver::str_contains`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_contains(
    c: Z3_context,
    container: Z3_ast,
    containee: Z3_ast,
) -> Z3_ast {
    // SAFETY: see module-level note; `ffi_guard_ast` handles null `c` and panic isolation.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_seq_contains", |ctx| {
            let s =
                require_term_ast_or_return!(ctx, container, "Z3_mk_seq_contains", "container", 0);
            let t =
                require_term_ast_or_return!(ctx, containee, "Z3_mk_seq_contains", "containee", 0);
            let r = if is_string(ctx, s) {
                ctx.solver.str_contains(s, t)
            } else {
                ctx.solver.seq_contains(s, t)
            };
            let a = term_to_ast(ctx, r);
            record_ast_sort(ctx, a, Sort::Bool)
        })
    }
}

/// Test whether `prefix` is a prefix of `s` (`Z3_mk_seq_prefix`), returning
/// Bool.
///
/// Backed by `Solver::seq_prefixof` / `Solver::str_prefixof`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_prefix(c: Z3_context, prefix: Z3_ast, s: Z3_ast) -> Z3_ast {
    // SAFETY: see module-level note; `ffi_guard_ast` handles null `c` and panic isolation.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_seq_prefix", |ctx| {
            let p = require_term_ast_or_return!(ctx, prefix, "Z3_mk_seq_prefix", "prefix", 0);
            let seq = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_prefix", "sequence", 0);
            let r = if is_string(ctx, seq) {
                ctx.solver.str_prefixof(p, seq)
            } else {
                ctx.solver.seq_prefixof(p, seq)
            };
            let a = term_to_ast(ctx, r);
            record_ast_sort(ctx, a, Sort::Bool)
        })
    }
}

/// Test whether `suffix` is a suffix of `s` (`Z3_mk_seq_suffix`), returning
/// Bool.
///
/// Backed by `Solver::seq_suffixof` / `Solver::str_suffixof`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_suffix(c: Z3_context, suffix: Z3_ast, s: Z3_ast) -> Z3_ast {
    // SAFETY: see module-level note; `ffi_guard_ast` handles null `c` and panic isolation.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_seq_suffix", |ctx| {
            let suf = require_term_ast_or_return!(ctx, suffix, "Z3_mk_seq_suffix", "suffix", 0);
            let seq = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_suffix", "sequence", 0);
            let r = if is_string(ctx, seq) {
                ctx.solver.str_suffixof(suf, seq)
            } else {
                ctx.solver.seq_suffixof(suf, seq)
            };
            let a = term_to_ast(ctx, r);
            record_ast_sort(ctx, a, Sort::Bool)
        })
    }
}

// =========================================================================
// Search / replace
// =========================================================================

/// Index of the first occurrence of `substr` in `s` at or after `offset`
/// (`Z3_mk_seq_index`), returning Int (-1 if not found).
///
/// Backed by `Solver::seq_indexof` / `Solver::str_indexof`.
///
/// NOTE: for `(Seq T)` operands AY's sequence decision procedure is currently
/// incomplete and may answer `unknown` for queries z3 decides; the constructed
/// term, however, is the correct SMT-LIB `seq.indexof` term. String operands are
/// decided fully.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_index(
    c: Z3_context,
    s: Z3_ast,
    substr: Z3_ast,
    offset: Z3_ast,
) -> Z3_ast {
    // SAFETY: see module-level note; `ffi_guard_ast` handles null `c` and panic isolation.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_seq_index", |ctx| {
            let seq = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_index", "sequence", 0);
            let needle =
                require_term_ast_or_return!(ctx, substr, "Z3_mk_seq_index", "substring", 0);
            let off = require_term_ast_or_return!(ctx, offset, "Z3_mk_seq_index", "offset", 0);
            let t = if is_string(ctx, seq) {
                ctx.solver.str_indexof(seq, needle, off)
            } else {
                ctx.solver.seq_indexof(seq, needle, off)
            };
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Int)
        })
    }
}

/// Replace the first occurrence of `src` in `s` with `dst` (`Z3_mk_seq_replace`).
///
/// Backed by `Solver::seq_replace` / `Solver::str_replace`.
///
/// NOTE: for `(Seq T)` operands AY's sequence decision procedure is currently
/// incomplete and may answer `unknown` for queries z3 decides; the constructed
/// term is the correct SMT-LIB `seq.replace` term. String operands are decided
/// fully.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_replace(
    c: Z3_context,
    s: Z3_ast,
    src: Z3_ast,
    dst: Z3_ast,
) -> Z3_ast {
    // SAFETY: see module-level note; `ffi_guard_ast` handles null `c` and panic isolation.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_seq_replace", |ctx| {
            let seq = require_term_ast_or_return!(ctx, s, "Z3_mk_seq_replace", "sequence", 0);
            let from = require_term_ast_or_return!(ctx, src, "Z3_mk_seq_replace", "source", 0);
            let to = require_term_ast_or_return!(ctx, dst, "Z3_mk_seq_replace", "replacement", 0);
            let result_sort = ctx.solver.sort_of(seq);
            let t = if is_string(ctx, seq) {
                ctx.solver.str_replace(seq, from, to)
            } else {
                ctx.solver.seq_replace(seq, from, to)
            };
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, result_sort)
        })
    }
}

// =========================================================================
// String <-> Int conversions
// =========================================================================

/// Convert a string to an integer (`Z3_mk_str_to_int`), returning Int (-1 if
/// the string is not a canonical non-negative numeral).
///
/// Backed by `Solver::str_to_int`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_str_to_int(c: Z3_context, s: Z3_ast) -> Z3_ast {
    // SAFETY: see module-level note; `ffi_guard_ast` handles null `c` and panic isolation.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_str_to_int", |ctx| {
            let s = require_term_ast_or_return!(ctx, s, "Z3_mk_str_to_int", "string", 0);
            let t = ctx.solver.str_to_int(s);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::Int)
        })
    }
}

/// Convert an integer to a string (`Z3_mk_int_to_str`), returning String (the
/// empty string for negative integers).
///
/// Backed by `Solver::str_from_int`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_int_to_str(c: Z3_context, s: Z3_ast) -> Z3_ast {
    // SAFETY: see module-level note; `ffi_guard_ast` handles null `c` and panic isolation.
    unsafe {
        ffi_guard_mk(c, "Z3_mk_int_to_str", |ctx| {
            let s = require_term_ast_or_return!(ctx, s, "Z3_mk_int_to_str", "integer", 0);
            let t = ctx.solver.str_from_int(s);
            let a = term_to_ast(ctx, t);
            record_ast_sort(ctx, a, Sort::String)
        })
    }
}

#[cfg(test)]
#[path = "sequence_power_tests.rs"]
mod sequence_power_tests;
