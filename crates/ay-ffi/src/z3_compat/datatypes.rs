// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible algebraic-datatype declaration and constructor API (#phase3-dt).
//!
//! Implements the multi-step Z3 datatype workflow:
//!
//! 1. [`Z3_mk_constructor`] builds a constructor *descriptor* (name, recognizer,
//!    fields, field sorts, and sort-reference indices). It does NOT create a sort
//!    yet — the parent datatype does not exist at this point.
//! 2. [`Z3_mk_datatype`] (or [`Z3_mk_constructor_list`] + [`Z3_mk_datatypes`])
//!    creates the datatype sort, declares it on the AY solver, and back-fills
//!    each descriptor with the concrete constructor / recognizer / accessor
//!    [`Z3_func_decl`]s. These func_decls carry a [`DatatypeOp`] marker so that
//!    `Z3_mk_app` dispatches through AY's verified datatype term builders.
//! 3. [`Z3_query_constructor`] reads the func_decls back out of a descriptor.
//! 4. [`Z3_del_constructor`] / [`Z3_del_constructor_list`] free the descriptors.
//!
//! # Soundness
//!
//! A constructor/recognizer/accessor func_decl produced here, when applied via
//! `Z3_mk_app`, yields exactly the term AY's SMT-LIB elaborator produces for the
//! equivalent `declare-datatypes`: constructors route through
//! `Solver::datatype_constructor` (so nullary constructors resolve to the
//! registered constant), recognizers through `datatype_tester` (`is-Ctor`), and
//! accessors through `datatype_selector`. The AY datatype theory then provides
//! the semantics. Verified against `z3 -in` (see `c_consumer.c` / Rust tests).
//!
//! # Recursion
//!
//! Self-referential (recursive) datatypes — a field whose sort is the datatype
//! under construction, expressed via a NULL `sorts[i]` and `sort_refs[i] == 0` —
//! ARE supported (e.g. a `List`), because AY models the datatype sort as an
//! uninterpreted sort and resolves the self-reference to it. Mutually recursive
//! datatypes (`Z3_mk_datatypes` with cross-datatype `sort_refs`) are NOT yet
//! supported and are rejected rather than mis-encoded.
//!
//! All functions calling into the solver are wrapped via the `ffi_guard_*`
//! helpers (#6192) to keep panics from unwinding across the FFI boundary.

use std::ffi::c_uint;
use std::ptr;

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, FuncDecl, Sort};

use super::{
    alloc_sort, cache_dt_func_decl, cache_dt_func_decl_with_symbol, ffi_count_within_limit,
    ffi_counts_within_limit, ffi_guard_ptr, ffi_guard_uint, ffi_guard_void, ConstructorHandle,
    ConstructorListHandle, DatatypeOp, SymbolKey, Z3Context, Z3_constructor, Z3_constructor_list,
    Z3_context, Z3_func_decl, Z3_sort, Z3_symbol, MAX_FFI_CONTAINER_ELEMENTS, Z3_INVALID_ARG,
};

fn extend_datatype_descriptor_budget(
    total_descriptors: &mut usize,
    field_counts: impl IntoIterator<Item = usize>,
    limit: usize,
) -> Result<(), ()> {
    for fields in field_counts {
        *total_descriptors = (*total_descriptors)
            .checked_add(1)
            .and_then(|total| total.checked_add(fields))
            .filter(|total| *total <= limit)
            .ok_or(())?;
    }
    Ok(())
}

/// Read the name from a `Z3_symbol`, or `None` if null.
///
/// # Safety
/// `s` must be null or a valid symbol handle from a prior AY FFI allocation.
unsafe fn symbol_key(s: Z3_symbol) -> Option<SymbolKey> {
    if s.is_null() {
        return None;
    }
    // SAFETY: `s` was null-checked above and originates from a prior AY FFI
    // allocation kept alive by the owning context; single-threaded per context.
    Some(unsafe { (*s).key.clone() })
}

/// Create a datatype constructor descriptor.
///
/// Mirrors Z3's `Z3_mk_constructor`. The returned handle is owned by the CALLER
/// and must be released with [`Z3_del_constructor`] — it is intentionally NOT
/// registered in a context arena, so there is no double-free with
/// `Z3_del_context`.
///
/// `sorts[i]` may be null to denote a sort reference (recursive field), in which
/// case `sort_refs[i]` selects the referenced datatype (`0` == the datatype
/// under construction, i.e. a self-reference). When `sorts[i]` is non-null,
/// `sort_refs[i]` is ignored.
///
/// # Safety
/// - `c` must be a valid context pointer.
/// - `field_names`, `sorts`, `sort_refs` must each point to `num_fields`
///   elements (or be null only when `num_fields == 0`).
/// - Pointers must originate from prior AY FFI allocations.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_constructor(
    c: Z3_context,
    name: Z3_symbol,
    recognizer: Z3_symbol,
    num_fields: c_uint,
    field_names: *const Z3_symbol,
    sorts: *const Z3_sort,
    sort_refs: *const c_uint,
) -> Z3_constructor {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe {
        ffi_counts_within_limit(
            c,
            "Z3_mk_constructor field-name, sort, and sort-reference arrays",
            &[num_fields, num_fields, num_fields],
        )
    } {
        return ptr::null_mut();
    }
    if name.is_null() {
        return ptr::null_mut();
    }
    if num_fields > 0 && (field_names.is_null() || sorts.is_null() || sort_refs.is_null()) {
        return ptr::null_mut();
    }

    // SAFETY: `name` null-checked above; valid AY symbol handle.
    let Some(ctor_symbol) = (unsafe { symbol_key(name) }) else {
        return ptr::null_mut();
    };
    let ctor_name = ctor_symbol.semantic_name();
    // SAFETY: a non-null recognizer is a live caller-owned symbol; the helper
    // accepts null so Z3's synthesized recognizer convention remains supported.
    let recognizer_symbol = unsafe { symbol_key(recognizer) }
        .unwrap_or_else(|| SymbolKey::String(format!("is-{}", ctor_symbol.display_name())));

    let mut field_name_vec = Vec::with_capacity(num_fields as usize);
    let mut field_symbol_vec = Vec::with_capacity(num_fields as usize);
    let mut field_sort_vec: Vec<Option<Sort>> = Vec::with_capacity(num_fields as usize);
    let mut sort_ref_vec = Vec::with_capacity(num_fields as usize);

    for i in 0..num_fields as usize {
        // SAFETY: `field_names` points to `num_fields` elems (checked above).
        let fname_sym = unsafe { *field_names.add(i) };
        // SAFETY: `fname_sym` is a valid AY symbol handle (or null -> reject).
        let Some(field_symbol) = (unsafe { symbol_key(fname_sym) }) else {
            return ptr::null_mut();
        };
        field_name_vec.push(field_symbol.semantic_name());
        field_symbol_vec.push(field_symbol);

        // SAFETY: `sorts` points to `num_fields` elems (checked above).
        let sort_ptr = unsafe { *sorts.add(i) };
        // SAFETY: `sort_refs` points to `num_fields` elems (checked above).
        let sref = unsafe { *sort_refs.add(i) };
        if sort_ptr.is_null() {
            // Sort reference (recursive field): resolved at Z3_mk_datatype time.
            field_sort_vec.push(None);
        } else {
            // SAFETY: `sort_ptr` is a valid AY sort handle from a prior alloc.
            field_sort_vec.push(Some(unsafe { (*sort_ptr).sort.clone() }));
        }
        sort_ref_vec.push(sref);
    }

    let handle = Box::into_raw(Box::new(ConstructorHandle {
        name: ctor_name,
        name_symbol: ctor_symbol,
        recognizer_symbol,
        field_names: field_name_vec,
        field_symbols: field_symbol_vec,
        field_sorts: field_sort_vec,
        sort_refs: sort_ref_vec,
        constructor_decl: ptr::null_mut(),
        tester_decl: ptr::null_mut(),
        accessor_decls: Vec::new(),
    }));
    // Touch the context only to validate it; the handle is caller-owned.
    if c.is_null() {
        // SAFETY: `handle` was just produced by Box::into_raw and not shared.
        unsafe {
            let _ = Box::from_raw(handle);
        }
        return ptr::null_mut();
    }
    handle
}

/// Create a constructor-list descriptor from an array of constructors.
///
/// The list borrows the constructor handles (it does not take ownership); the
/// caller must still free each constructor with [`Z3_del_constructor`] and free
/// the list itself with [`Z3_del_constructor_list`].
///
/// # Safety
/// - `c` must be a valid context pointer.
/// - `constructors` must point to `num_constructors` valid constructor handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_constructor_list(
    c: Z3_context,
    num_constructors: c_uint,
    constructors: *const Z3_constructor,
) -> Z3_constructor_list {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_constructor_list", num_constructors) } {
        return ptr::null_mut();
    }
    if c.is_null() {
        return ptr::null_mut();
    }
    if num_constructors > 0 && constructors.is_null() {
        return ptr::null_mut();
    }
    let mut ctors = Vec::with_capacity(num_constructors as usize);
    for i in 0..num_constructors as usize {
        // SAFETY: `constructors` points to `num_constructors` elems (checked).
        let cp = unsafe { *constructors.add(i) };
        if cp.is_null() {
            return ptr::null_mut();
        }
        ctors.push(cp);
    }
    Box::into_raw(Box::new(ConstructorListHandle {
        constructors: ctors,
    }))
}

/// Build a `DatatypeSort` from constructor descriptors and resolve sort refs.
///
/// `dt_name` is the datatype being created. A NULL field sort (sort reference)
/// with `sort_refs[i] == 0` is resolved to a self-reference (the datatype under
/// construction). Any other (cross-datatype) sort reference returns `None` to
/// signal "unsupported".
///
/// # Safety
/// Each pointer in `ctor_handles` must be a valid constructor handle.
unsafe fn build_datatype_sort(
    dt_name: &str,
    ctor_handles: &[Z3_constructor],
) -> Option<DatatypeSort> {
    let self_sort = Sort::Uninterpreted(dt_name.to_string());
    let mut constructors = Vec::with_capacity(ctor_handles.len());
    for &cp in ctor_handles {
        if cp.is_null() {
            return None;
        }
        // SAFETY: caller guarantees `cp` is a valid constructor handle.
        let ch = unsafe { &*cp };
        let mut fields = Vec::with_capacity(ch.field_names.len());
        for (idx, fname) in ch.field_names.iter().enumerate() {
            let field_sort = match &ch.field_sorts[idx] {
                Some(s) => s.clone(),
                None => {
                    // Sort reference. Only the self-reference (ref index 0) is
                    // supported in the single-datatype path.
                    if ch.sort_refs[idx] == 0 {
                        self_sort.clone()
                    } else {
                        return None;
                    }
                }
            };
            fields.push(DatatypeField {
                name: fname.clone(),
                sort: field_sort,
            });
        }
        constructors.push(DatatypeConstructor {
            name: ch.name.clone(),
            fields,
        });
    }
    Some(DatatypeSort {
        name: dt_name.to_string(),
        constructors,
    })
}

/// Declare a datatype on the solver and back-fill each constructor descriptor
/// with its constructor/recognizer/accessor func_decls.
///
/// Returns the datatype sort handle, or null on failure (sets `last_error`).
fn declare_and_fill(
    ctx: &mut Z3Context,
    dt: &DatatypeSort,
    dt_symbol: &SymbolKey,
    ctor_handles: &[Z3_constructor],
) -> Z3_sort {
    if let Err(e) = ctx.solver.try_declare_datatype(dt) {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some(format!("{e}"));
        return ptr::null_mut();
    }
    let dt_sort = Sort::Datatype(dt.clone());

    for (&cp, ctor) in ctor_handles.iter().zip(dt.constructors.iter()) {
        // SAFETY: constructor handles were validated by
        // `build_datatype_sort` and remain caller-owned for this call.
        let ch = unsafe { &*cp };
        // Constructor func_decl: (field sorts...) -> DT.
        let ctor_decl = cache_dt_func_decl_with_symbol(
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
            ch.name_symbol.clone(),
        );
        // The recognizer operation is tied to `ctor`. Its core declaration
        // keeps the canonical tester identity used by datatype metadata, while
        // the handle separately retains the caller's exact symbol.
        let tester_decl = cache_dt_func_decl_with_symbol(
            ctx,
            FuncDecl::new(
                format!("is-{}", ctor.name),
                vec![dt_sort.clone()],
                Sort::Bool,
            ),
            DatatypeOp::Recognizer {
                ctor: ctor.name.clone(),
            },
            ch.recognizer_symbol.clone(),
        );
        // Accessor func_decls: DT -> field_sort, one per field.
        let mut accessors = Vec::with_capacity(ctor.fields.len());
        for (field, field_symbol) in ctor.fields.iter().zip(ch.field_symbols.iter()) {
            let acc = cache_dt_func_decl_with_symbol(
                ctx,
                FuncDecl::new(
                    field.name.clone(),
                    vec![dt_sort.clone()],
                    field.sort.clone(),
                ),
                DatatypeOp::Accessor {
                    field: field.name.clone(),
                    result_sort: field.sort.clone(),
                },
                field_symbol.clone(),
            );
            accessors.push(acc);
        }

        // SAFETY: `cp` is a valid, caller-owned constructor handle (validated by
        // `build_datatype_sort`). We hold no other reference to it here.
        unsafe {
            (*cp).constructor_decl = ctor_decl;
            (*cp).tester_decl = tester_decl;
            (*cp).accessor_decls = accessors;
        }
    }

    ctx.ffi_sort_symbols
        .insert(dt_sort.clone(), dt_symbol.clone());
    alloc_sort(ctx, dt_sort)
}

/// Create a datatype sort from constructor descriptors (single, possibly
/// self-recursive, datatype).
///
/// Mirrors Z3's `Z3_mk_datatype`: declares the datatype, fills in each
/// constructor descriptor's func_decls (query via [`Z3_query_constructor`]), and
/// returns the new sort.
///
/// # Safety
/// - `c` must be a valid context pointer.
/// - `name` must be a valid symbol handle.
/// - `constructors` must point to `num_constructors` valid constructor handles
///   (this array is filled in-place and remains caller-owned).
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_datatype(
    c: Z3_context,
    name: Z3_symbol,
    num_constructors: c_uint,
    constructors: *mut Z3_constructor,
) -> Z3_sort {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe { ffi_count_within_limit(c, "Z3_mk_datatype constructors", num_constructors) } {
        return ptr::null_mut();
    }
    if name.is_null() || constructors.is_null() || num_constructors == 0 {
        return ptr::null_mut();
    }
    // SAFETY: `name` null-checked; valid AY symbol handle.
    let Some(dt_symbol) = (unsafe { symbol_key(name) }) else {
        return ptr::null_mut();
    };
    let dt_name = dt_symbol.semantic_name();
    let mut ctor_handles = Vec::with_capacity(num_constructors as usize);
    let mut total_descriptors = 0usize;
    for i in 0..num_constructors as usize {
        // SAFETY: `constructors` points to `num_constructors` elems (checked).
        let cp = unsafe { *constructors.add(i) };
        if cp.is_null() {
            return ptr::null_mut();
        }
        // SAFETY: `cp` was null-checked and is valid per the caller contract.
        let fields = unsafe { (*cp).field_names.len() };
        if extend_datatype_descriptor_budget(
            &mut total_descriptors,
            std::iter::once(fields),
            MAX_FFI_CONTAINER_ELEMENTS as usize,
        )
        .is_err()
        {
            // SAFETY: this public entry point requires `c` to be null or a live,
            // exclusively borrowed context; the bound checker only updates its error state.
            unsafe {
                ffi_count_within_limit(
                    c,
                    "Z3_mk_datatype aggregate constructor and field descriptors",
                    MAX_FFI_CONTAINER_ELEMENTS + 1,
                );
            }
            return ptr::null_mut();
        }
        ctor_handles.push(cp);
    }

    // SAFETY: every handle in `ctor_handles` was null-checked above.
    let Some(dt) = (unsafe { build_datatype_sort(&dt_name, &ctor_handles) }) else {
        // Unsupported (cross-datatype) sort reference: report and bail.
        // SAFETY: `c` valid per contract; `ffi_guard_ptr` handles null.
        return unsafe {
            ffi_guard_ptr(c, |ctx| {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some(
                    "Z3_mk_datatype: cross-datatype sort references are not supported \
                     (use Z3_mk_datatypes is also unsupported for mutual recursion)"
                        .to_string(),
                );
                ptr::null_mut()
            })
        };
    };

    // SAFETY: `c` valid per contract; `ffi_guard_ptr` handles null + panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            declare_and_fill(ctx, &dt, &dt_symbol, &ctor_handles)
        })
    }
}

/// Read the constructor, recognizer (tester), and accessor func_decls out of a
/// constructor descriptor previously processed by [`Z3_mk_datatype`].
///
/// Writes into the provided out-pointers when non-null. `accessors` must have
/// room for `num_fields` entries.
///
/// # Safety
/// - `constr` must be a valid constructor handle that has been through
///   `Z3_mk_datatype`.
/// - `constructor`, `tester` (if non-null) must be writable.
/// - `accessors` (if non-null) must point to at least `num_fields` slots.
#[no_mangle]
pub unsafe extern "C" fn Z3_query_constructor(
    _c: Z3_context,
    constr: Z3_constructor,
    num_fields: c_uint,
    constructor: *mut Z3_func_decl,
    tester: *mut Z3_func_decl,
    accessors: *mut Z3_func_decl,
) {
    if constr.is_null() {
        return;
    }
    // SAFETY: `constr` valid per contract; single-threaded per context.
    let ch = unsafe { &*constr };
    if !constructor.is_null() {
        // SAFETY: `constructor` writable per contract.
        unsafe { *constructor = ch.constructor_decl };
    }
    if !tester.is_null() {
        // SAFETY: `tester` writable per contract.
        unsafe { *tester = ch.tester_decl };
    }
    if !accessors.is_null() {
        let n = (num_fields as usize).min(ch.accessor_decls.len());
        for (i, &acc) in ch.accessor_decls.iter().take(n).enumerate() {
            // SAFETY: `accessors` has room for `num_fields` >= n entries.
            unsafe { *accessors.add(i) = acc };
        }
    }
}

/// Free a constructor descriptor created by [`Z3_mk_constructor`].
///
/// Consumes the caller-owned box exactly once. The func_decls it referenced are
/// owned by the context arena and are NOT freed here.
///
/// # Safety
/// `constr` must be a constructor handle from `Z3_mk_constructor` that has not
/// already been freed.
#[no_mangle]
pub unsafe extern "C" fn Z3_del_constructor(_c: Z3_context, constr: Z3_constructor) {
    if constr.is_null() {
        return;
    }
    // SAFETY: `constr` came from `Box::into_raw` in `Z3_mk_constructor` and is
    // freed exactly once (the caller must not double-free, matching Z3).
    unsafe {
        let _ = Box::from_raw(constr);
    }
}

/// Free a constructor-list descriptor created by [`Z3_mk_constructor_list`].
///
/// Does NOT free the constructors it listed (they remain caller-owned and must
/// be freed via [`Z3_del_constructor`]), matching Z3.
///
/// # Safety
/// `clist` must be a list handle from `Z3_mk_constructor_list` that has not
/// already been freed.
#[no_mangle]
pub unsafe extern "C" fn Z3_del_constructor_list(_c: Z3_context, clist: Z3_constructor_list) {
    if clist.is_null() {
        return;
    }
    // SAFETY: `clist` came from `Box::into_raw` in `Z3_mk_constructor_list` and
    // is freed exactly once.
    unsafe {
        let _ = Box::from_raw(clist);
    }
}

/// Create multiple datatype sorts at once (Z3's `Z3_mk_datatypes`).
///
/// AY does not yet support mutually recursive datatypes (cross-datatype sort
/// references). Each datatype is declared independently here; any cross-datatype
/// sort reference is rejected (the corresponding `sorts[]` entry is left null and
/// `last_error` is set). Self-recursive datatypes within a single list entry are
/// supported.
///
/// # Safety
/// - `c` must be a valid context pointer.
/// - `sort_names` and `constructor_lists` must point to `num_sorts` elements.
/// - `sorts` must point to `num_sorts` writable slots.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_datatypes(
    c: Z3_context,
    num_sorts: c_uint,
    sort_names: *const Z3_symbol,
    sorts: *mut Z3_sort,
    constructor_lists: *const Z3_constructor_list,
) {
    // SAFETY: this public entry point requires `c` to be null or a live,
    // exclusively borrowed context; the bound checker only updates its error state.
    if !unsafe {
        ffi_counts_within_limit(
            c,
            "Z3_mk_datatypes sort-name, output, and constructor-list arrays",
            &[num_sorts, num_sorts, num_sorts],
        )
    } {
        return;
    }
    if num_sorts == 0 || sort_names.is_null() || sorts.is_null() || constructor_lists.is_null() {
        return;
    }

    // Preflight the WHOLE call before writing an output slot or declaring a
    // sort. A caller may reuse one large constructor list for many sort names;
    // per-sort limits alone permit product-scale work and partially mutate the
    // context before the aggregate budget is eventually exceeded.
    let mut total_descriptors = (num_sorts as usize).saturating_mul(3);
    for i in 0..num_sorts as usize {
        // SAFETY: `constructor_lists` points to `num_sorts` elements.
        let list_ptr = unsafe { *constructor_lists.add(i) };
        if list_ptr.is_null() {
            continue;
        }
        // SAFETY: `list_ptr` is a live constructor-list handle per the API
        // contract. Borrow it here; do not clone its potentially large vector.
        let constructors = unsafe { &(*list_ptr).constructors };
        for &constructor in constructors {
            if constructor.is_null() {
                // SAFETY: `c` is valid per this entry point's contract.
                unsafe {
                    ffi_guard_void(c, |ctx| {
                        ctx.last_error = Z3_INVALID_ARG;
                        ctx.error_msg = Some(
                            "Z3_mk_datatypes: null constructor in constructor list".to_string(),
                        );
                    });
                }
                return;
            }
            // SAFETY: constructor-list entries are live handles per contract.
            let fields = unsafe { (*constructor).field_names.len() };
            if extend_datatype_descriptor_budget(
                &mut total_descriptors,
                std::iter::once(fields),
                MAX_FFI_CONTAINER_ELEMENTS as usize,
            )
            .is_err()
            {
                // SAFETY: `c` is valid per this entry point's contract.
                unsafe {
                    ffi_count_within_limit(
                        c,
                        "Z3_mk_datatypes aggregate arrays and datatype descriptors",
                        MAX_FFI_CONTAINER_ELEMENTS + 1,
                    );
                }
                return;
            }
        }
    }

    for i in 0..num_sorts as usize {
        // SAFETY: arrays point to `num_sorts` elems (checked above).
        let name_sym = unsafe { *sort_names.add(i) };
        let list_ptr = unsafe { *constructor_lists.add(i) };
        let out_slot = unsafe { sorts.add(i) };
        // Default each out slot to null so partial failure is observable.
        // SAFETY: `out_slot` is within the writable `sorts` array.
        unsafe { *out_slot = ptr::null_mut() };

        // SAFETY: `name_sym` is a valid symbol handle or null.
        let Some(dt_symbol) = (unsafe { symbol_key(name_sym) }) else {
            continue;
        };
        let dt_name = dt_symbol.semantic_name();
        if list_ptr.is_null() {
            continue;
        }
        // SAFETY: `list_ptr` is a valid constructor-list handle.
        let ctor_handles = unsafe { (*list_ptr).constructors.clone() };

        // SAFETY: handles validated when the list was built.
        let Some(dt) = (unsafe { build_datatype_sort(&dt_name, &ctor_handles) }) else {
            // Cross-datatype (mutually recursive) reference: unsupported.
            // SAFETY: `c` valid per contract.
            unsafe {
                ffi_guard_void(c, |ctx| {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!(
                        "Z3_mk_datatypes: datatype '{dt_name}' uses an unsupported \
                         (mutually recursive / cross-datatype) sort reference"
                    ));
                });
            }
            continue;
        };

        // SAFETY: `c` valid per contract; guard handles null + panics.
        let sort_handle = unsafe {
            ffi_guard_ptr(c, |ctx| {
                declare_and_fill(ctx, &dt, &dt_symbol, &ctor_handles)
            })
        };
        // SAFETY: `out_slot` within writable `sorts`.
        unsafe { *out_slot = sort_handle };
    }
}

// ============================================================================
// Datatype sort introspection (Z3_get_datatype_sort_*)
// ============================================================================
//
// These read a datatype sort (as returned by `Z3_mk_datatype`, whose handle
// carries the full `Sort::Datatype(DatatypeSort)`) back out: constructor count,
// and the constructor / recognizer / accessor func_decls. Each returned
// func_decl is built through the SAME path `Z3_mk_datatype` uses
// (`cache_dt_func_decl` with the matching `DatatypeOp`), so it is REAL — usable
// with `Z3_mk_app` — and its name/arity/domain/range agree with libz3 for the
// same datatype. Caller-supplied constructor/recognizer/accessor symbols retain
// their exact integer-vs-string kind through these round trips.

/// Number of constructors of a datatype sort (Z3's
/// `Z3_get_datatype_sort_num_constructors`). Returns 0 for a non-datatype or
/// null sort.
///
/// # Safety
/// `c` must be a valid context pointer; `t`, when non-null, a valid sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_datatype_sort_num_constructors(
    c: Z3_context,
    t: Z3_sort,
) -> c_uint {
    if t.is_null() {
        return 0;
    }
    // SAFETY: `c` guarded by `ffi_guard_uint`; `t` is a valid, non-aliasing sort
    // handle owned by the context.
    unsafe {
        ffi_guard_uint(c, 0, |_ctx| match &(*t).sort {
            Sort::Datatype(dt) => dt.constructors.len() as c_uint,
            _ => 0,
        })
    }
}

/// The `idx`-th constructor func_decl of a datatype sort (Z3's
/// `Z3_get_datatype_sort_constructor`).
///
/// The returned decl is `(field sorts...) -> DT`, tagged so `Z3_mk_app` builds a
/// real constructor term. Returns null for a non-datatype/null sort or
/// out-of-range `idx`.
///
/// # Safety
/// `c` must be a valid context pointer; `t`, when non-null, a valid sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_datatype_sort_constructor(
    c: Z3_context,
    t: Z3_sort,
    idx: c_uint,
) -> Z3_func_decl {
    if t.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `t` is a valid sort handle; `.sort` read is single-threaded.
    let dt = match unsafe { &(*t).sort } {
        Sort::Datatype(dt) => dt.clone(),
        _ => return ptr::null_mut(),
    };
    let Some(ctor) = dt.constructors.get(idx as usize).cloned() else {
        return ptr::null_mut();
    };
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

/// The `idx`-th recognizer func_decl (`DT -> Bool`) of a datatype
/// sort (Z3's `Z3_get_datatype_sort_recognizer`).
///
/// Returns null for a non-datatype/null sort or out-of-range `idx`.
///
/// # Safety
/// `c` must be a valid context pointer; `t`, when non-null, a valid sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_datatype_sort_recognizer(
    c: Z3_context,
    t: Z3_sort,
    idx: c_uint,
) -> Z3_func_decl {
    if t.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `t` is a valid sort handle; `.sort` read is single-threaded.
    let dt = match unsafe { &(*t).sort } {
        Sort::Datatype(dt) => dt.clone(),
        _ => return ptr::null_mut(),
    };
    let Some(ctor) = dt.constructors.get(idx as usize).cloned() else {
        return ptr::null_mut();
    };
    // SAFETY: `c` guarded by `ffi_guard_ptr`.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let dt_sort = Sort::Datatype(dt.clone());
            let recognizer_symbol = ctx
                .ffi_dt_recognizers
                .get(&(dt_sort.clone(), ctor.name.clone()))
                .cloned()
                .unwrap_or_else(|| {
                    let display = ctx
                        .ffi_decl_symbols
                        .get(&ctor.name)
                        .map(SymbolKey::display_name)
                        .unwrap_or_else(|| ctor.name.clone());
                    SymbolKey::String(format!("is-{display}"))
                });
            cache_dt_func_decl_with_symbol(
                ctx,
                FuncDecl::new(format!("is-{}", ctor.name), vec![dt_sort], Sort::Bool),
                DatatypeOp::Recognizer {
                    ctor: ctor.name.clone(),
                },
                recognizer_symbol,
            )
        })
    }
}

/// The `idx_a`-th accessor (selector) func_decl of the `idx_c`-th constructor of
/// a datatype sort (Z3's `Z3_get_datatype_sort_constructor_accessor`).
///
/// The returned decl is `DT -> field_sort`, tagged so `Z3_mk_app` builds a real
/// selector term. Returns null for a non-datatype/null sort or an out-of-range
/// constructor/field index.
///
/// # Safety
/// `c` must be a valid context pointer; `t`, when non-null, a valid sort handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_datatype_sort_constructor_accessor(
    c: Z3_context,
    t: Z3_sort,
    idx_c: c_uint,
    idx_a: c_uint,
) -> Z3_func_decl {
    if t.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: `t` is a valid sort handle; `.sort` read is single-threaded.
    let dt = match unsafe { &(*t).sort } {
        Sort::Datatype(dt) => dt.clone(),
        _ => return ptr::null_mut(),
    };
    let Some(ctor) = dt.constructors.get(idx_c as usize) else {
        return ptr::null_mut();
    };
    let Some(field) = ctor.fields.get(idx_a as usize).cloned() else {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn datatype_descriptor_budget_is_cumulative_across_reused_lists() {
        let mut descriptors = 0;
        extend_datatype_descriptor_budget(&mut descriptors, [2, 1], 5).expect("first list fits");
        assert_eq!(descriptors, 5, "two constructors plus three fields");
        assert_eq!(
            extend_datatype_descriptor_budget(&mut descriptors, [0], 5),
            Err(())
        );

        let mut reused = 0;
        extend_datatype_descriptor_budget(&mut reused, [0, 0], 5)
            .expect("first constructor list fits");
        extend_datatype_descriptor_budget(&mut reused, [1], 5)
            .expect("reused list remains within aggregate limit");
        assert_eq!(reused, 4);
        assert_eq!(
            extend_datatype_descriptor_budget(&mut reused, [1], 5),
            Err(())
        );
    }
}
