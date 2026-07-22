// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible AST inspection (extended), decl_kind mapping, error handling,
//! and AST vector functions.
//!
//! Functions that overlap with `accessors.rs` (Z3_get_ast_kind, Z3_is_app,
//! Z3_get_app_num_args, Z3_get_app_arg, Z3_get_app_decl, Z3_get_decl_name,
//! Z3_get_arity, Z3_get_domain, Z3_get_range, Z3_get_numeral_int) live in
//! `accessors.rs`. This module holds the remaining inspection/utility functions.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_char, c_uint};
use std::ptr;

use num_bigint::BigInt;
use num_traits::{Signed, Zero};

use super::{
    ast_to_term, cache_ast_vector, cache_string, ffi_guard_ast, ffi_guard_const_ptr,
    ffi_guard_const_ptr_keep_error, ffi_guard_ptr, ffi_guard_uint, ffi_guard_uint_keep_error,
    ffi_guard_void, Z3_ast, Z3_ast_vector, Z3_context, Z3_func_decl, MAX_FFI_CONTAINER_ELEMENTS,
    MAX_FFI_DECIMAL_PRECISION, Z3_INVALID_ARG, Z3_OP_ABS, Z3_OP_ADD, Z3_OP_AND, Z3_OP_BADD,
    Z3_OP_BAND, Z3_OP_BASHR, Z3_OP_BLSHR, Z3_OP_BMUL, Z3_OP_BNEG, Z3_OP_BNOT, Z3_OP_BOR,
    Z3_OP_BSDIV, Z3_OP_BSHL, Z3_OP_BSMOD, Z3_OP_BSREM, Z3_OP_BSUB, Z3_OP_BUDIV, Z3_OP_BUREM,
    Z3_OP_BXOR, Z3_OP_CONCAT, Z3_OP_CONST_ARRAY, Z3_OP_DISTINCT, Z3_OP_DIV, Z3_OP_EQ,
    Z3_OP_EXTRACT, Z3_OP_FALSE, Z3_OP_GE, Z3_OP_GT, Z3_OP_IDIV, Z3_OP_IFF, Z3_OP_IMPLIES,
    Z3_OP_IS_INT, Z3_OP_ITE, Z3_OP_LE, Z3_OP_LT, Z3_OP_MOD, Z3_OP_MUL, Z3_OP_NOT, Z3_OP_OR,
    Z3_OP_POWER, Z3_OP_REPEAT, Z3_OP_ROTATE_LEFT, Z3_OP_ROTATE_RIGHT, Z3_OP_SELECT, Z3_OP_SGEQ,
    Z3_OP_SGT, Z3_OP_SIGN_EXT, Z3_OP_SLEQ, Z3_OP_SLT, Z3_OP_STORE, Z3_OP_SUB, Z3_OP_TO_INT,
    Z3_OP_TO_REAL, Z3_OP_TRUE, Z3_OP_UGEQ, Z3_OP_UGT, Z3_OP_ULEQ, Z3_OP_ULT, Z3_OP_UMINUS,
    Z3_OP_UNINTERPRETED, Z3_OP_XOR, Z3_OP_ZERO_EXT,
};

// ---- AST string conversion ----
// Note: Z3_is_eq_ast, Z3_get_ast_id, Z3_get_ast_hash live in ast_identity.rs.

/// Get the string representation of a numeral AST.
///
/// Returns NULL for a non-numeral AST — matching Z3's invalid-argument
/// behavior and `Z3_get_numeral_decimal_string`. (A previous version returned
/// the AST HANDLE NUMBER formatted as text here, which consumers reading model
/// values through `as_long()`-style accessors would interpret as a fabricated
/// numeric value — a wrong-model-answer fake, removed.)
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_string(c: Z3_context, a: Z3_ast) -> *const c_char {
    if a == 0 {
        return ptr::null();
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_const_ptr` handles the null case internally and catches any unwinding panic
    // so it cannot cross the FFI boundary.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| match ctx.solver.numeral_string(ast_to_term(a)) {
            Some(s) => cache_string(ctx, s),
            None => ptr::null(),
        })
    }
}

/// Get the decimal string representation of a numeral AST.
///
/// For rationals, produces a decimal expansion to `precision` places
/// (e.g., `"0.333333"` for 1/3 with precision 6).
/// For integers and bitvectors, behaves identically to `Z3_get_numeral_string`.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_numeral_decimal_string(
    c: Z3_context,
    a: Z3_ast,
    precision: c_uint,
) -> *const c_char {
    if a == 0 {
        return ptr::null();
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_const_ptr` handles the null case internally and catches any unwinding panic
    // so it cannot cross the FFI boundary.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            match ctx.solver.numeral_string(ast_to_term(a)) {
                Some(s) => {
                    // If it's a rational (contains '/'), convert to decimal via scaled BigInt division
                    if let Some((num_s, den_s)) = s.split_once('/') {
                        if precision > MAX_FFI_DECIMAL_PRECISION {
                            ctx.last_error = Z3_INVALID_ARG;
                            ctx.error_msg = Some(format!(
                                "decimal precision {precision} exceeds the supported maximum {MAX_FFI_DECIMAL_PRECISION}"
                            ));
                            return ptr::null();
                        }
                        if let (Ok(num), Ok(den)) = (
                            num_s.trim().parse::<BigInt>(),
                            den_s.trim().parse::<BigInt>(),
                        ) {
                            if !den.is_zero() {
                                let prec = precision as usize;
                                let scale = BigInt::from(10).pow(prec as u32);
                                let scaled = &num * &scale / &den;
                                let (sign, abs) = if scaled.is_negative() {
                                    ("-", -scaled)
                                } else {
                                    ("", scaled)
                                };
                                let abs_str = abs.to_string();
                                let decimal = if prec == 0 {
                                    format!("{sign}{abs_str}")
                                } else if abs_str.len() <= prec {
                                    let zeros = "0".repeat(prec - abs_str.len());
                                    format!("{sign}0.{zeros}{abs_str}")
                                } else {
                                    let split = abs_str.len() - prec;
                                    format!("{sign}{}.{}", &abs_str[..split], &abs_str[split..])
                                };
                                return cache_string(ctx, decimal);
                            }
                        }
                    }
                    cache_string(ctx, s)
                }
                None => ptr::null(),
            }
        })
    }
}

/// Convert an AST to a string.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_to_string(c: Z3_context, a: Z3_ast) -> *const c_char {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_const_ptr` handles the null case internally and catches any unwinding panic
    // so it cannot cross the FFI boundary.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            // A null AST handle has no rendering.
            if a == 0 {
                return ptr::null();
            }
            // Proof-AST handles (from Z3_solver_get_proof) carry the high-bit
            // tag and index into the context's stored Alethe proof texts. For
            // these, Z3_ast_to_string returns the solver's real proof artifact
            // (#phase3-proof), never the generic `(ast ...)` placeholder.
            if let Some(text) = super::proof_text_for_ast(ctx, a) {
                return cache_string(ctx, text.to_string());
            }
            // Algebraic-number handles (from Z3_algebraic_root / Z3_algebraic_*
            // arithmetic) carry the bit-62 tag and index the context's exact
            // RealScalar store; they are not arena terms, so the formatter
            // below cannot render them. Print z3's exact `root-obj` form (e.g.
            // `(root-obj (+ (^ x 2) (- 2)) 2)` for √2) computed from the
            // stored value's defining polynomial — never `(null)` and never a
            // lossy decimal guess.
            if super::algebraic::is_algebraic_ast(a) {
                if let Some(text) = super::algebraic::ast_as_scalar(ctx, a)
                    .as_ref()
                    .and_then(ay_nra::rcf_api::root_obj_string)
                {
                    return cache_string(ctx, text);
                }
                // Dangling/foreign algebraic index: no rendering (null), the
                // pre-existing honest failure shape.
                return ptr::null();
            }
            // Sort-AST handles (from Z3_sort_to_ast): render the SMT-LIB sort
            // text via `Sort: Display` — z3 parity measured on 4.15.4:
            // `Int`, `(Array Int Int)`, `(_ BitVec 8)`.
            if a & super::HANDLE_TAG_MASK == super::SORT_AST_TAG {
                let handle = super::sort_ast_to_handle(ctx, a);
                if handle.is_null() {
                    return ptr::null(); // dangling/foreign: honest null
                }
                // SAFETY: non-null handles in `sort_ast_handles` are live
                // arena allocations owned by this context (enclosing unsafe).
                let text = format!("{}", &(*handle).sort);
                return cache_string(ctx, text);
            }
            // Func-decl-AST handles (from Z3_func_decl_to_ast): z3 renders the
            // full declaration, e.g. `(declare-fun f (Int (Array Int Int))
            // (_ BitVec 8))`, nullary `(declare-fun c () Int)` (measured).
            if a & super::HANDLE_TAG_MASK == super::FUNC_DECL_AST_TAG {
                let handle = super::func_decl_ast_to_handle(ctx, a);
                if handle.is_null() {
                    return ptr::null(); // dangling/foreign: honest null
                }
                // SAFETY: non-null handles in `decl_ast_handles` are live
                // arena allocations owned by this context (enclosing unsafe).
                let decl = &(*handle).decl;
                let display_name = (*handle)
                    .symbol
                    .as_ref()
                    .map(super::SymbolKey::display_name)
                    .unwrap_or_else(|| decl.name().to_string());
                let mut text = format!("(declare-fun {display_name} (");
                for (i, s) in decl.domain().iter().enumerate() {
                    if i > 0 {
                        text.push(' ');
                    }
                    text.push_str(&format!("{s}"));
                }
                text.push_str(&format!(") {})", decl.range()));
                return cache_string(ctx, text);
            }
            // Ordinary term: render the real s-expression via the solver's
            // formatter (e.g. `(+ x (* 2 y))`), matching z3's `sexpr()` output.
            // A foreign/stale handle yields `None` -> null (the Python layer
            // falls back); it never panics across the FFI boundary.
            match ctx.solver.format_term_checked(ast_to_term(a)) {
                Some(s) => cache_string(ctx, s),
                None => ptr::null(),
            }
        })
    }
}

// ---- AST depth ----

// ---- as-array model terms ----

// ---- Decl kind ----

/// Map an operator name (from AY TermKind) to the Z3 decl_kind constant.
fn operator_name_to_decl_kind(name: &str) -> c_uint {
    match name {
        // Boolean
        "true" => Z3_OP_TRUE,
        "false" => Z3_OP_FALSE,
        "=" => Z3_OP_EQ,
        "distinct" => Z3_OP_DISTINCT,
        // z3py reports the if-then-else operator's canonical decl name as "if"
        // (see `Z3_get_app_decl`'s name canonicalization); AY's core / SMT-LIB
        // symbol is "ite". Both spellings map to the same Z3_OP_ITE kind.
        "ite" | "if" => Z3_OP_ITE,
        "and" => Z3_OP_AND,
        "or" => Z3_OP_OR,
        "iff" | "<=>" => Z3_OP_IFF,
        "xor" => Z3_OP_XOR,
        "not" => Z3_OP_NOT,
        "=>" | "implies" => Z3_OP_IMPLIES,
        // Arithmetic
        "<=" => Z3_OP_LE,
        ">=" => Z3_OP_GE,
        "<" => Z3_OP_LT,
        ">" => Z3_OP_GT,
        "+" => Z3_OP_ADD,
        "-" => Z3_OP_SUB,
        "neg" | "unary_minus" => Z3_OP_UMINUS,
        "*" => Z3_OP_MUL,
        // `Z3_mk_div` is sort-polymorphic (matching z3's `Z3_mk_div`): Int
        // operands build the SMT-LIB integer-division term (core symbol "div",
        // z3py Z3_OP_IDIV), Real operands build real division (core symbol "/",
        // z3py Z3_OP_DIV). Route each symbol to the kind z3py reports.
        "/" => Z3_OP_DIV,
        "div" | "intdiv" | "ediv" => Z3_OP_IDIV,
        "mod" => Z3_OP_MOD,
        "to_real" => Z3_OP_TO_REAL,
        "to_int" => Z3_OP_TO_INT,
        "is_int" => Z3_OP_IS_INT,
        "^" | "power" => Z3_OP_POWER,
        "abs" => Z3_OP_ABS,
        // Arrays
        "store" => Z3_OP_STORE,
        "select" => Z3_OP_SELECT,
        "const" | "const_array" => Z3_OP_CONST_ARRAY,
        // Bitvectors
        "bvneg" => Z3_OP_BNEG,
        "bvadd" => Z3_OP_BADD,
        "bvsub" => Z3_OP_BSUB,
        "bvmul" => Z3_OP_BMUL,
        "bvsdiv" => Z3_OP_BSDIV,
        "bvudiv" => Z3_OP_BUDIV,
        "bvsrem" => Z3_OP_BSREM,
        "bvurem" => Z3_OP_BUREM,
        "bvsmod" => Z3_OP_BSMOD,
        "bvand" => Z3_OP_BAND,
        "bvor" => Z3_OP_BOR,
        "bvnot" => Z3_OP_BNOT,
        "bvxor" => Z3_OP_BXOR,
        "concat" => Z3_OP_CONCAT,
        "sign_extend" => Z3_OP_SIGN_EXT,
        "zero_extend" => Z3_OP_ZERO_EXT,
        "extract" => Z3_OP_EXTRACT,
        "bvshl" => Z3_OP_BSHL,
        "bvlshr" => Z3_OP_BLSHR,
        "bvashr" => Z3_OP_BASHR,
        "repeat" => Z3_OP_REPEAT,
        "rotate_left" => Z3_OP_ROTATE_LEFT,
        "rotate_right" => Z3_OP_ROTATE_RIGHT,
        "bvsle" => Z3_OP_SLEQ,
        "bvslt" => Z3_OP_SLT,
        "bvule" => Z3_OP_ULEQ,
        "bvult" => Z3_OP_ULT,
        // AY's core normalizes the `>=`/`>` comparisons into `<=`/`<` with
        // swapped arguments (`bvuge(a,b)` → `bvule(b,a)`, etc.), so a decl
        // literally named `bvuge`/`bvugt`/`bvsge`/`bvsgt` does not arise from
        // the constructors today. The names are mapped anyway for correctness
        // by name (matching z3py's `Z3_OP_UGEQ`/`UGT`/`SGEQ`/`SGT`) in case one
        // reaches this path via another route (e.g. a preserved SMT-LIB decl).
        "bvuge" => Z3_OP_UGEQ,
        "bvugt" => Z3_OP_UGT,
        "bvsge" => Z3_OP_SGEQ,
        "bvsgt" => Z3_OP_SGT,
        // Default: uninterpreted function
        _ => Z3_OP_UNINTERPRETED,
    }
}

/// Return the declaration kind corresponding to a function declaration.
///
/// Maps the operator name stored in the func_decl to the Z3 `Z3_decl_kind`
/// enum value. Unrecognized operators return `Z3_OP_UNINTERPRETED`.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_decl_kind(_c: Z3_context, d: Z3_func_decl) -> c_uint {
    if d.is_null() {
        return Z3_OP_UNINTERPRETED;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_uint(_c, Z3_OP_UNINTERPRETED, |_ctx| {
            let decl = &(*d).decl;
            operator_name_to_decl_kind(decl.name())
        })
    }
}

// ---- Error handling ----

/// Get the error code from the last operation.
///
/// Uses the `_keep_error` guard: every other API entry point clears the error
/// state on entry (as libz3 does), but reading the code must not clear it.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_error_code(c: Z3_context) -> c_uint {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint_keep_error` handles the null case internally and catches any unwinding
    // panic so it cannot cross the FFI boundary.
    unsafe { ffi_guard_uint_keep_error(c, Z3_INVALID_ARG, |ctx| ctx.last_error) }
}

/// Get the error message for a given error code.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_error_msg(c: Z3_context, err: c_uint) -> *const c_char {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_const_ptr_keep_error` handles the null case internally and catches any
    // unwinding panic so it cannot cross the FFI boundary. It must not clear the error state
    // it is reporting on.
    unsafe {
        ffi_guard_const_ptr_keep_error(c, |ctx| {
            // A pending detailed message OVERRIDES the code argument entirely
            // (measured on z3 4.15.4: after a sort mismatch, get_error_msg
            // with code 4 and even code 0 both return the detailed message).
            // This is what surfaces e.g. the Z3_add_rec_def rejection reasons
            // through every binding. Residual divergence (documented, not
            // chased): AY's guards clear `error_msg` on the next API entry,
            // z3's buffer is sticky across a later successful call; no
            // binding reads the message after a successful call.
            if let Some(msg) = &ctx.error_msg {
                if !msg.is_empty() {
                    let msg = msg.clone();
                    return cache_string(ctx, msg);
                }
            }
            // Canonical strings, byte-identical to z3 4.15.4 (measured table;
            // any code > 12 → "unknown").
            let msg = match err {
                0 => "ok",
                1 => "type error",
                2 => "index out of bounds",
                3 => "invalid argument",
                4 => "parser error",
                5 => "parser (data) is not available",
                6 => "invalid pattern",
                7 => "out of memory",
                8 => "file access error",
                9 => "internal error",
                10 => "invalid usage",
                11 => "invalid dec_ref command",
                12 => "Z3 exception",
                _ => "unknown",
            };
            cache_string(ctx, msg.to_string())
        })
    }
}

/// Set an error handler (currently a no-op).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_set_error_handler(
    _c: Z3_context,
    _h: Option<unsafe extern "C" fn(Z3_context, c_uint)>,
) {
}

// ---- AST vectors ----

/// Create an empty AST vector.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_ast_vector(c: Z3_context) -> Z3_ast_vector {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| cache_ast_vector(ctx, Vec::new())) }
}

/// Increment AST vector reference count (no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_vector_inc_ref(_c: Z3_context, _v: Z3_ast_vector) {}

/// Decrement AST vector reference count (no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_vector_dec_ref(_c: Z3_context, _v: Z3_ast_vector) {}

/// Get AST vector size.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_vector_size(_c: Z3_context, v: Z3_ast_vector) -> c_uint {
    if v.is_null() {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_uint(_c, 0, |_ctx| (*v).asts.len() as c_uint) }
}

/// Get an element from an AST vector.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_vector_get(_c: Z3_context, v: Z3_ast_vector, i: c_uint) -> Z3_ast {
    if v.is_null() {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ast` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ast(_c, |_ctx| {
            let vec = &(*v).asts;
            match vec.get(i as usize) {
                Some(&ast) => ast,
                None => 0,
            }
        })
    }
}

/// Push an element to an AST vector.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_vector_push(_c: Z3_context, v: Z3_ast_vector, a: Z3_ast) {
    if v.is_null() {
        return;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_void(_c, |_ctx| {
            (*v).asts.push(a);
        });
    }
}

/// Set an element in an AST vector.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_vector_set(_c: Z3_context, v: Z3_ast_vector, i: c_uint, a: Z3_ast) {
    if v.is_null() {
        return;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_void(_c, |_ctx| {
            let vec = &mut (*v).asts;
            if (i as usize) < vec.len() {
                vec[i as usize] = a;
            }
        });
    }
}

/// Resize an AST vector.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_ast_vector_resize(_c: Z3_context, v: Z3_ast_vector, n: c_uint) {
    if v.is_null() {
        return;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_void` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_void(_c, |ctx| {
            if n > MAX_FFI_CONTAINER_ELEMENTS {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_ast_vector_resize: requested size {n} exceeds the supported maximum {MAX_FFI_CONTAINER_ELEMENTS}"
                ));
                return;
            }
            (*v).asts.resize(n as usize, 0);
        });
    }
}
