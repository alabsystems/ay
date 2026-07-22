// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Process-global parameter store (`Z3_global_param_set` / `_get` /
//! `_reset_all`).
//!
//! Semantics measured against real z3 4.15.4 with an internal probe harness
//! and matched exactly where AY can represent them:
//!
//! * Keys are normalized: ASCII-lowercased AND `-` → `_`, across the whole key
//!   including any module prefix (`pp.MAX-WIDTH` ≡ `pp.max_width`).
//! * The top-level registry is CLOSED (the 24 params below, captured verbatim
//!   from z3's own legal-parameter listing). z3 REFUSES to store an unknown
//!   top-level key, an unknown module (`nomod.foo`), an unknown param inside a
//!   known module (`pp.not_a_param`), and a value that fails the registered
//!   type parse (`verbose=notanum` keeps the prior value). AY does the same;
//!   the only divergence is that z3 prints a stderr WARNING on refusal and AY
//!   is silent (AY has no warning stream).
//! * A never-set known param `get`s its registry DEFAULT (`timeout` →
//!   `4294967295`); an unknown key `get`s `false` and NULLS the out-buffer
//!   (measured: z3 overwrites a preloaded sentinel pointer with NULL).
//! * `reset_all` restores defaults (`pp.max_depth` → `5` after reset).
//! * The store is process-global and thread-shared (measured: a set in one
//!   thread is visible from another), and the returned string lives in a
//!   single static buffer valid until the next `Z3_global_param_get` — z3 has
//!   the same single-buffer contract.
//!
//! DIVERGENCE (documented, verdict-irrelevant): of z3's module registries
//! (hundreds of `smt.*`/`sat.*`/... entries) AY carries only the `pp` module
//! (18 params, measured via `z3 -pm:pp`). A set/get on a real z3 module AY
//! does not know (e.g. `smt.arith.solver`) is refused/`false` where z3 would
//! store/answer. Replicating those registries wholesale would be a drift
//! liability for zero soundness gain.
//!
//! HONESTY: this is a readable STORE — exactly what the get/set API
//! contracts. AY's solving honors none of these process-global keys (all AY
//! configuration is per-context); no behavior is faked, and the store is never
//! consulted by any solve path, so it cannot affect a verdict by construction.

use std::collections::HashMap;
use std::ffi::CString;
use std::ptr;
use std::sync::Mutex;

use super::{ffi_read_bounded_text, Z3_string};

/// Registered value type of a global parameter (drives set-time validation).
#[derive(Clone, Copy)]
enum ParamKind {
    Bool,
    UInt,
    Str,
}

/// The 24 top-level globals with z3 4.15.4's exact defaults (measured).
const GLOBAL_DEFAULTS: &[(&str, &str, ParamKind)] = &[
    ("auto_config", "true", ParamKind::Bool),
    ("ctrl_c", "true", ParamKind::Bool),
    ("debug_ref_count", "false", ParamKind::Bool),
    ("dot_proof_file", "proof.dot", ParamKind::Str),
    ("dump_models", "false", ParamKind::Bool),
    ("encoding", "unicode", ParamKind::Str),
    ("memory_high_watermark", "0", ParamKind::UInt),
    ("memory_high_watermark_mb", "0", ParamKind::UInt),
    ("memory_max_alloc_count", "0", ParamKind::UInt),
    ("memory_max_size", "0", ParamKind::UInt),
    ("model", "true", ParamKind::Bool),
    ("model_validate", "false", ParamKind::Bool),
    ("proof", "false", ParamKind::Bool),
    ("rlimit", "0", ParamKind::UInt),
    ("smtlib2_compliant", "false", ParamKind::Bool),
    ("stats", "false", ParamKind::Bool),
    ("timeout", "4294967295", ParamKind::UInt),
    ("trace", "false", ParamKind::Bool),
    ("trace_file_name", "z3.log", ParamKind::Str),
    ("type_check", "true", ParamKind::Bool),
    ("unsat_core", "false", ParamKind::Bool),
    ("verbose", "0", ParamKind::UInt),
    ("warning", "true", ParamKind::Bool),
    ("well_sorted_check", "false", ParamKind::Bool),
];

/// The `pp` module's 18 params with z3 4.15.4's exact defaults (measured via
/// `z3 -pm:pp`).
const PP_DEFAULTS: &[(&str, &str, ParamKind)] = &[
    ("bounded", "false", ParamKind::Bool),
    ("bv_literals", "true", ParamKind::Bool),
    ("bv_neg", "false", ParamKind::Bool),
    ("decimal", "false", ParamKind::Bool),
    ("decimal_precision", "10", ParamKind::UInt),
    ("fixed_indent", "false", ParamKind::Bool),
    ("flat_assoc", "true", ParamKind::Bool),
    ("fp_real_literals", "false", ParamKind::Bool),
    ("max_depth", "5", ParamKind::UInt),
    ("max_indent", "4294967295", ParamKind::UInt),
    ("max_num_lines", "4294967295", ParamKind::UInt),
    ("max_ribbon", "80", ParamKind::UInt),
    ("max_width", "80", ParamKind::UInt),
    ("min_alias_size", "10", ParamKind::UInt),
    ("no_lets", "false", ParamKind::Bool),
    ("pretty_proof", "false", ParamKind::Bool),
    ("simplify_implies", "true", ParamKind::Bool),
    ("single_line", "false", ParamKind::Bool),
];

/// The process-global store (normalized key → value). Mutex-protected because
/// the global-param API has no context argument and z3's is thread-shared.
static STORE: Mutex<Option<HashMap<String, String>>> = Mutex::new(None);

/// Single static out-buffer for `Z3_global_param_get`. z3's contract: the
/// returned pointer is valid until the NEXT `Z3_global_param_get` (z3 itself
/// has the same single shared buffer across threads — measured).
static GET_BUF: Mutex<Option<CString>> = Mutex::new(None);

/// z3's key normalization (measured): ASCII-lowercase and `-` → `_`, applied
/// to the whole key including any module prefix.
fn normalize(key: &str) -> String {
    key.chars()
        .map(|ch| {
            if ch == '-' {
                '_'
            } else {
                ch.to_ascii_lowercase()
            }
        })
        .collect()
}

/// Look up the registry entry for a normalized key: top-level keys in
/// [`GLOBAL_DEFAULTS`], `pp.*` keys in [`PP_DEFAULTS`]. `None` for anything
/// else (unknown top-level, unknown module, unknown param in `pp`).
fn registry_entry(norm_key: &str) -> Option<(&'static str, ParamKind)> {
    match norm_key.split_once('.') {
        None => GLOBAL_DEFAULTS
            .iter()
            .find(|(k, _, _)| *k == norm_key)
            .map(|(_, d, t)| (*d, *t)),
        Some(("pp", param)) => PP_DEFAULTS
            .iter()
            .find(|(k, _, _)| *k == param)
            .map(|(_, d, t)| (*d, *t)),
        Some(_) => None,
    }
}

/// Set-time value validation against the registered type (z3 refuses an
/// invalid value and keeps the prior one — measured).
fn value_ok(kind: ParamKind, value: &str) -> bool {
    match kind {
        ParamKind::Bool => matches!(value, "true" | "false"),
        ParamKind::UInt => value.parse::<u64>().is_ok(),
        ParamKind::Str => true,
    }
}

/// Set a process-global configuration parameter (Z3's `Z3_global_param_set`).
///
/// Stores the value for later `Z3_global_param_get` readback iff the key is in
/// the registry and the value parses at the registered type; otherwise it is
/// refused silently (z3 refuses too, with a stderr warning AY does not print —
/// see the module doc for the full measured contract). Store-only: AY's
/// solving never consults this store, so it can never affect a verdict.
///
/// # Safety
/// `param_id` and `param_value` may be null (refused) or must point to valid
/// NUL-terminated strings.
#[no_mangle]
pub unsafe extern "C" fn Z3_global_param_set(param_id: Z3_string, param_value: Z3_string) {
    if param_id.is_null() || param_value.is_null() {
        return;
    }
    // SAFETY: both pointers were null-checked and are NUL-terminated per the
    // caller contract; the helper bounds each scan and clone.
    let (Ok(key), Ok(value)) = (unsafe { ffi_read_bounded_text(param_id) }, unsafe {
        ffi_read_bounded_text(param_value)
    }) else {
        return; // non-UTF-8: refuse, never store garbage
    };
    let norm = normalize(&key);
    let Some((_, kind)) = registry_entry(&norm) else {
        return; // unknown key/module/param: refuse (z3 parity)
    };
    if !value_ok(kind, &value) {
        return; // invalid value for the registered type: refuse (z3 parity)
    }
    let mut store = match STORE.lock() {
        Ok(g) => g,
        Err(poisoned) => poisoned.into_inner(),
    };
    store.get_or_insert_with(HashMap::new).insert(norm, value);
}

/// Query a process-global configuration parameter (Z3's `Z3_global_param_get`).
///
/// Returns `true` with the stored value (or, if never set, the measured z3
/// registry default) for a known key; `false` with `*param_value` set to NULL
/// for an unknown key (measured: z3 nulls the out-buffer on failure). The
/// returned string lives in a static buffer valid until the next call (z3's
/// own contract).
///
/// # Safety
/// `param_id` may be null (returns `false`); `param_value`, when non-null,
/// must be a valid out-pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_global_param_get(
    param_id: Z3_string,
    param_value: *mut Z3_string,
) -> bool {
    // Helper writing the out-param, tolerating a null out-pointer.
    let write_out = |v: *const std::ffi::c_char| {
        if !param_value.is_null() {
            // SAFETY: null-checked; caller contract guarantees validity.
            unsafe { *param_value = v };
        }
    };
    if param_id.is_null() {
        write_out(ptr::null());
        return false;
    }
    // SAFETY: null-checked above and NUL-terminated per the caller contract;
    // the helper bounds the scan and clone.
    let Ok(key) = (unsafe { ffi_read_bounded_text(param_id) }) else {
        write_out(ptr::null());
        return false;
    };
    let norm = normalize(&key);
    let stored = {
        let mut guard = match STORE.lock() {
            Ok(g) => g,
            Err(poisoned) => poisoned.into_inner(),
        };
        guard.get_or_insert_with(HashMap::new).get(&norm).cloned()
    };
    let value = match stored {
        Some(v) => v,
        None => match registry_entry(&norm) {
            Some((default, _)) => default.to_string(),
            None => {
                // Unknown key: honest false + NULL out-buffer (measured z3
                // behavior) — never a fabricated value.
                write_out(ptr::null());
                return false;
            }
        },
    };
    let Ok(cstring) = CString::new(value) else {
        write_out(ptr::null());
        return false;
    };
    let mut buf = match GET_BUF.lock() {
        Ok(g) => g,
        Err(poisoned) => poisoned.into_inner(),
    };
    let ptr = cstring.as_ptr();
    *buf = Some(cstring);
    write_out(ptr);
    true
}

/// Reset all process-global parameters to their defaults (Z3's
/// `Z3_global_param_reset_all`): clears the store, so subsequent gets fall
/// back to the registry defaults (measured z3 behavior).
#[no_mangle]
pub extern "C" fn Z3_global_param_reset_all() {
    let mut store = match STORE.lock() {
        Ok(g) => g,
        Err(poisoned) => poisoned.into_inner(),
    };
    if let Some(map) = store.as_mut() {
        map.clear();
    }
}
