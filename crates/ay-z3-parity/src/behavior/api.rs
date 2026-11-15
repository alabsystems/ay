// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The C entry points the behavior probes drive, resolved from each library
//! at the signatures declared here.

use std::ffi::{c_char, c_int, c_uint, c_void};

use crate::loader::Library;

/// Handle/AST word: every probed signature passes handles and ASTs in one
/// pointer-sized register on both implementations (libz3: pointers; AY:
/// pointer-or-u64-id), so `usize` is ABI-exact for both.
pub(super) type W = usize;

/// The on_clause callback shape (`Z3_on_clause_eh`).
type OnClauseEh = unsafe extern "C" fn(*mut c_void, W, c_uint, *const c_uint, W);

type ReduceAppEh = unsafe extern "C" fn(*mut c_void, W, c_uint, *const W, *mut W);
type ReduceAssignEh = unsafe extern "C" fn(*mut c_void, W, c_uint, *const W, c_uint, *const W);
type NewLemmaEh = unsafe extern "C" fn(*mut c_void, W, c_uint);
type PredecessorEh = unsafe extern "C" fn(*mut c_void);
type UnfoldEh = unsafe extern "C" fn(*mut c_void);

/// The raw C entry points the probes drive, resolved per library.
#[allow(non_snake_case)]
pub(super) struct Api {
    pub(super) Z3_mk_config: unsafe extern "C" fn() -> W,
    pub(super) Z3_mk_context: unsafe extern "C" fn(W) -> W,
    pub(super) Z3_del_config: unsafe extern "C" fn(W),
    pub(super) Z3_del_context: unsafe extern "C" fn(W),
    pub(super) Z3_set_error_handler: unsafe extern "C" fn(W, W),
    pub(super) Z3_get_error_code: unsafe extern "C" fn(W) -> c_uint,
    pub(super) Z3_get_error_msg: unsafe extern "C" fn(W, c_uint) -> *const c_char,
    pub(super) Z3_eval_smtlib2_string: unsafe extern "C" fn(W, *const c_char) -> *const c_char,
    pub(super) Z3_mk_string_symbol: unsafe extern "C" fn(W, *const c_char) -> W,
    pub(super) Z3_mk_int_sort: unsafe extern "C" fn(W) -> W,
    pub(super) Z3_mk_bool_sort: unsafe extern "C" fn(W) -> W,
    pub(super) Z3_mk_bv_sort: unsafe extern "C" fn(W, c_uint) -> W,
    pub(super) Z3_mk_func_decl: unsafe extern "C" fn(W, W, c_uint, *const W, W) -> W,
    pub(super) Z3_mk_app: unsafe extern "C" fn(W, W, c_uint, *const W) -> W,
    pub(super) Z3_mk_int: unsafe extern "C" fn(W, c_int, W) -> W,
    pub(super) Z3_mk_unsigned_int64: unsafe extern "C" fn(W, u64, W) -> W,
    pub(super) Z3_mk_true: unsafe extern "C" fn(W) -> W,
    pub(super) Z3_get_sort: unsafe extern "C" fn(W, W) -> W,
    pub(super) Z3_get_sort_kind: unsafe extern "C" fn(W, W) -> c_uint,
    pub(super) Z3_get_bv_sort_size: unsafe extern "C" fn(W, W) -> c_uint,
    pub(super) Z3_mk_char: unsafe extern "C" fn(W, c_uint) -> W,
    pub(super) Z3_mk_char_to_bv: unsafe extern "C" fn(W, W) -> W,
    pub(super) Z3_mk_char_from_bv: unsafe extern "C" fn(W, W) -> W,
    pub(super) Z3_mk_transitive_closure: unsafe extern "C" fn(W, W) -> W,
    pub(super) Z3_mk_type_variable: unsafe extern "C" fn(W, W) -> W,
    pub(super) Z3_mk_solver: unsafe extern "C" fn(W) -> W,
    pub(super) Z3_solver_register_on_clause: unsafe extern "C" fn(W, W, *mut c_void, OnClauseEh),
    pub(super) Z3_mk_fixedpoint: unsafe extern "C" fn(W) -> W,
    pub(super) Z3_fixedpoint_inc_ref: unsafe extern "C" fn(W, W),
    pub(super) Z3_fixedpoint_register_relation: unsafe extern "C" fn(W, W, W),
    pub(super) Z3_fixedpoint_init: unsafe extern "C" fn(W, W, *mut c_void),
    pub(super) Z3_fixedpoint_get_reachable: unsafe extern "C" fn(W, W, W) -> W,
    pub(super) Z3_fixedpoint_get_cover_delta: unsafe extern "C" fn(W, W, c_int, W) -> W,
    pub(super) Z3_fixedpoint_add_cover: unsafe extern "C" fn(W, W, c_int, W, W),
    pub(super) Z3_fixedpoint_add_constraint: unsafe extern "C" fn(W, W, W, c_uint),
    pub(super) Z3_fixedpoint_set_predicate_representation:
        unsafe extern "C" fn(W, W, W, c_uint, *const W),
    pub(super) Z3_fixedpoint_set_reduce_app_callback: unsafe extern "C" fn(W, W, ReduceAppEh),
    pub(super) Z3_fixedpoint_set_reduce_assign_callback: unsafe extern "C" fn(W, W, ReduceAssignEh),
    pub(super) Z3_fixedpoint_add_callback:
        unsafe extern "C" fn(W, W, *mut c_void, NewLemmaEh, PredecessorEh, UnfoldEh),
    pub(super) Z3_mk_params: unsafe extern "C" fn(W) -> W,
    pub(super) Z3_params_inc_ref: unsafe extern "C" fn(W, W),
    pub(super) Z3_params_set_symbol: unsafe extern "C" fn(W, W, W, W),
    pub(super) Z3_fixedpoint_set_params: unsafe extern "C" fn(W, W, W),
}

macro_rules! resolve {
    ($lib:expr, $($name:ident),+ $(,)?) => {{
        Ok::<Api, String>(Api {
            $($name: {
                let mut sym = stringify!($name).as_bytes().to_vec();
                sym.push(0);
                // SAFETY: looked up by its documented Z3 C name and used only
                // at the matching signature declared in `Api`.
                let f = unsafe { $lib.get::<*const c_void>(&sym) }
                    .map_err(|e| format!("missing symbol {}: {e}", stringify!($name)))?;
                // SAFETY: transmute of a dlsym address to its C signature.
                // The target type is the `Api` field's declared signature, one
                // hop away; spelling out all 40+ signatures again here would
                // only invite drift between the annotation and the field.
                #[allow(clippy::missing_transmute_annotations)]
                let f = unsafe { std::mem::transmute::<*const c_void, _>(*f) };
                f
            }),+
        })
    }};
}

pub(super) fn load(lib: &Library) -> Result<Api, String> {
    resolve!(
        lib,
        Z3_mk_config,
        Z3_mk_context,
        Z3_del_config,
        Z3_del_context,
        Z3_set_error_handler,
        Z3_get_error_code,
        Z3_get_error_msg,
        Z3_eval_smtlib2_string,
        Z3_mk_string_symbol,
        Z3_mk_int_sort,
        Z3_mk_bool_sort,
        Z3_mk_bv_sort,
        Z3_mk_func_decl,
        Z3_mk_app,
        Z3_mk_int,
        Z3_mk_unsigned_int64,
        Z3_mk_true,
        Z3_get_sort,
        Z3_get_sort_kind,
        Z3_get_bv_sort_size,
        Z3_mk_char,
        Z3_mk_char_to_bv,
        Z3_mk_char_from_bv,
        Z3_mk_transitive_closure,
        Z3_mk_type_variable,
        Z3_mk_solver,
        Z3_solver_register_on_clause,
        Z3_mk_fixedpoint,
        Z3_fixedpoint_inc_ref,
        Z3_fixedpoint_register_relation,
        Z3_fixedpoint_init,
        Z3_fixedpoint_get_reachable,
        Z3_fixedpoint_get_cover_delta,
        Z3_fixedpoint_add_cover,
        Z3_fixedpoint_add_constraint,
        Z3_fixedpoint_set_predicate_representation,
        Z3_fixedpoint_set_reduce_app_callback,
        Z3_fixedpoint_set_reduce_assign_callback,
        Z3_fixedpoint_add_callback,
        Z3_mk_params,
        Z3_params_inc_ref,
        Z3_params_set_symbol,
        Z3_fixedpoint_set_params,
    )
}
