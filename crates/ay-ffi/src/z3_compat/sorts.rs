// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible sort construction and inspection functions.
//!
//! All functions that call into the solver are wrapped in `catch_unwind` via
//! the `ffi_guard_*` helpers (#6192) to prevent undefined behavior from panics
//! unwinding across the `extern "C"` boundary.

use std::ffi::{c_char, c_uint};
use std::ptr;

use ay_dpll::api::Sort;

use super::{
    alloc_sort, cache_string, ffi_guard_const_ptr, ffi_guard_ptr, ffi_guard_uint, SymbolKey,
    Z3_context, Z3_sort, Z3_symbol, MAX_FFI_BITVECTOR_WIDTH, Z3_ARRAY_SORT, Z3_BOOL_SORT,
    Z3_BV_SORT, Z3_CHAR_SORT, Z3_DATATYPE_SORT, Z3_FINITE_DOMAIN_SORT, Z3_INT_SORT, Z3_INVALID_ARG,
    Z3_REAL_SORT, Z3_RE_SORT, Z3_SEQ_SORT, Z3_TYPE_VAR, Z3_UNINTERPRETED_SORT, Z3_UNKNOWN_AST,
};

const BUILTIN_FP_SIMPLE_SORT_NAMES: &[&str] =
    &["RoundingMode", "Float16", "Float32", "Float64", "Float128"];

/// Create Bool sort.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bool_sort(c: Z3_context) -> Z3_sort {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, Sort::Bool)) }
}

/// Create Int sort.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_int_sort(c: Z3_context) -> Z3_sort {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, Sort::Int)) }
}

/// Create Real sort.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_real_sort(c: Z3_context) -> Z3_sort {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, Sort::Real)) }
}

/// Create bitvector sort of given width.
///
/// Returns null with `Z3_INVALID_ARG` for zero or for widths beyond AY's
/// dense-bitblasting envelope.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_bv_sort(c: Z3_context, sz: c_uint) -> Z3_sort {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if sz == 0 || sz > MAX_FFI_BITVECTOR_WIDTH {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_mk_bv_sort: width {sz} is outside the supported range 1..={MAX_FFI_BITVECTOR_WIDTH}"
                ));
                return ptr::null_mut();
            }
            alloc_sort(ctx, Sort::bitvec(sz))
        })
    }
}

/// Create array sort with given domain and range sorts.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_array_sort(
    c: Z3_context,
    domain: Z3_sort,
    range: Z3_sort,
) -> Z3_sort {
    if domain.is_null() || range.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `domain` was null-checked above and originates from a prior AY FFI allocation
    // whose handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`).
    // Reading `.sort` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let d = unsafe { (*domain).sort.clone() };
    // SAFETY: `range` was null-checked above and originates from a prior AY FFI allocation
    // whose handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`).
    // Reading `.sort` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let r = unsafe { (*range).sort.clone() };
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, Sort::array(d.clone(), r.clone()))) }
}

/// Create uninterpreted sort.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_uninterpreted_sort(c: Z3_context, s: Z3_symbol) -> Z3_sort {
    if s.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `s` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.key` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let symbol = unsafe { (*s).key.clone() };
    let display_name = symbol.display_name();
    let semantic_name = symbol.semantic_name();
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if matches!(symbol, SymbolKey::String(_))
                && BUILTIN_FP_SIMPLE_SORT_NAMES.contains(&display_name.as_str())
            {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(format!(
                    "Z3_mk_uninterpreted_sort: '{display_name}' is a builtin FloatingPoint-theory sort"
                ));
                return ptr::null_mut();
            }
            let sort = Sort::Uninterpreted(semantic_name.clone());
            ctx.ffi_sort_symbols.insert(sort.clone(), symbol.clone());
            alloc_sort(ctx, sort)
        })
    }
}

/// Create a sequence sort `(Seq elem)` for the given element sort.
///
/// Backed by AY's `Sort::Seq`. The Z3 sequence theory is exercised through the
/// `Z3_mk_seq_*` constructors.
///
/// # Safety
/// `c` and `elem` must be valid pointers (or `elem` null, which yields null).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_seq_sort(c: Z3_context, elem: Z3_sort) -> Z3_sort {
    if elem.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `elem` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.sort` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let elem_sort = unsafe { (*elem).sort.clone() };
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, Sort::seq(elem_sort.clone()))) }
}

/// Create a regular-expression sort `(RegEx basis)` for the given basis
/// sequence/string sort.
///
/// Matches `Z3_mk_re_sort`. AY's regex sort (`RegLan`) is monomorphic — every
/// AY regex is over strings — so the basis sort is accepted (it identifies the
/// sequence domain in Z3) but does not parameterize the result. A null `basis`
/// yields null.
///
/// # Safety
/// `c` and `basis` must be valid pointers (or `basis` null, which yields null).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_re_sort(c: Z3_context, basis: Z3_sort) -> Z3_sort {
    if basis.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; `ffi_guard_ptr`
    // handles the null case internally and catches any unwinding panic so it cannot
    // cross the FFI boundary. `basis` was null-checked above; its content is not
    // read because AY's `RegLan` is monomorphic.
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, Sort::RegLan)) }
}

/// Create the string sort.
///
/// AY models strings as a first-class `Sort::String` with a dedicated `str.*`
/// theory (rather than `(Seq Char)`), so this returns `Sort::String`. From the
/// Z3 C API perspective a string is still a sequence: `Z3_get_sort_kind` of this
/// sort reports `Z3_SEQ_SORT` and the polymorphic `Z3_mk_seq_*` constructors
/// accept it (dispatching to AY's `str.*` operations).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_string_sort(c: Z3_context) -> Z3_sort {
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, Sort::String)) }
}

/// Get the sort kind.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_sort_kind(_c: Z3_context, t: Z3_sort) -> c_uint {
    if t.is_null() {
        return Z3_UNKNOWN_AST;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_uint(_c, Z3_UNKNOWN_AST, |_ctx| match &(*t).sort {
            Sort::Bool => Z3_BOOL_SORT,
            Sort::Int => Z3_INT_SORT,
            Sort::Real => Z3_REAL_SORT,
            Sort::BitVec(_) => Z3_BV_SORT,
            Sort::Array(_) => Z3_ARRAY_SORT,
            Sort::Uninterpreted(_) => Z3_UNINTERPRETED_SORT,
            // An algebraic datatype (declared via Z3_mk_datatype /
            // declare-datatypes) reports Z3_DATATYPE_SORT, matching z3py's
            // Z3_get_sort_kind on a DatatypeSortRef (#phase3-dt).
            Sort::Datatype(_) => Z3_DATATYPE_SORT,
            // A String is a sequence (of characters) in Z3's model, so both
            // report Z3_SEQ_SORT (#phase3-seq).
            Sort::Seq(_) | Sort::String => Z3_SEQ_SORT,
            // The regular-expression sort (RegLan) reports Z3_RE_SORT, matching
            // z3py's Z3_get_sort_kind on a ReSortRef.
            Sort::RegLan => Z3_RE_SORT,
            // The character sort reports Z3_CHAR_SORT, matching z3py's
            // Z3_get_sort_kind on a CharSortRef (AY models a Char as a bounded
            // Int code point).
            Sort::Char => Z3_CHAR_SORT,
            // A finite-domain sort (bounded-Int lowering, like Char) reports
            // Z3_FINITE_DOMAIN_SORT; a type variable reports Z3_TYPE_VAR —
            // both verified against libz3 4.16.
            Sort::FiniteDomain(_, _) => Z3_FINITE_DOMAIN_SORT,
            Sort::TypeVar(_) => Z3_TYPE_VAR,
            _ => Z3_UNKNOWN_AST,
        })
    }
}

/// Get the size of a bitvector sort.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_bv_sort_size(_c: Z3_context, t: Z3_sort) -> c_uint {
    if t.is_null() {
        return 0;
    }
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_uint` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe {
        ffi_guard_uint(_c, 0, |_ctx| match &(*t).sort {
            Sort::BitVec(bvs) => bvs.width,
            _ => 0,
        })
    }
}

/// Get the domain sort of an array sort.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_array_sort_domain(c: Z3_context, t: Z3_sort) -> Z3_sort {
    if t.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `t` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.sort` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let sort = match unsafe { &(*t).sort } {
        Sort::Array(a) => a.index_sort.clone(),
        _ => return ptr::null_mut(),
    };
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, sort.clone())) }
}

/// Get the range sort of an array sort.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_array_sort_range(c: Z3_context, t: Z3_sort) -> Z3_sort {
    if t.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `t` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.sort` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let sort = match unsafe { &(*t).sort } {
        Sort::Array(a) => a.element_sort.clone(),
        _ => return ptr::null_mut(),
    };
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_ptr` handles the null case internally and catches any unwinding panic so it
    // cannot cross the FFI boundary.
    unsafe { ffi_guard_ptr(c, |ctx| alloc_sort(ctx, sort.clone())) }
}

/// Convert a sort to a string representation.
///
/// # Safety
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_sort_to_string(c: Z3_context, s: Z3_sort) -> *const c_char {
    if s.is_null() {
        return ptr::null();
    }
    // SAFETY: `s` was null-checked above and originates from a prior AY FFI allocation whose
    // handle is kept alive by the owning `Z3Context` (see handle caches in `mod.rs`). Reading
    // `.sort` is a shared-read with no concurrent mutation because the Z3 C API is
    // single-threaded per context.
    let sort_str = format!("{:?}", unsafe { &(*s).sort });
    // SAFETY: `c` is the Z3_context pointer supplied by the caller; the `# Safety` on this
    // extern "C" function requires it to be a valid, non-aliased pointer (or null).
    // `ffi_guard_const_ptr` handles the null case internally and catches any unwinding panic
    // so it cannot cross the FFI boundary.
    unsafe { ffi_guard_const_ptr(c, |ctx| cache_string(ctx, sort_str.clone())) }
}
