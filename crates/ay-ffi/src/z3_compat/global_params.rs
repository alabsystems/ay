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
//! (hundreds of `smt.*`/`sat.*`/... entries) AY carries the `pp` module
//! and the implemented 5.3.3 `rewriter.max_power_expansion` option. A set/get on a real z3 module AY
//! does not know (e.g. `smt.arith.solver`) is refused/`false` where z3 would
//! store/answer. Replicating those registries wholesale would be a drift
//! liability for zero soundness gain.
//!
//! Most entries remain readable configuration DATA. The encoding check and
//! simplify tactic's sequence-power rewriting consume their actual settings;
//! none of these settings supplies a resource grant or changes word semantics.

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
        Some(("rewriter", "max_power_expansion")) => Some(("2", ParamKind::UInt)),
        Some(("rewriter", "som" | "expand_power" | "mul_to_power" | "sort_sums")) => {
            Some(("false", ParamKind::Bool))
        }
        Some(("rewriter", "flat" | "push_to_real")) => Some(("true", ParamKind::Bool)),
        Some(("rewriter", "som_blowup")) => Some(("10", ParamKind::UInt)),
        Some(("rewriter", "max_degree")) => Some(("64", ParamKind::UInt)),
        Some(_) => None,
    }
}

pub(crate) fn polynomial_parameters(
    owner: &dyn ay_core::term::TermConstructionAdmission,
) -> Result<ay_dpll::api::PolynomialParameters, &'static str> {
    let mut result = ay_dpll::api::PolynomialParameters::default();
    for key in [
        "rewriter.som",
        "rewriter.som_blowup",
        "rewriter.flat",
        "rewriter.expand_power",
        "rewriter.mul_to_power",
        "rewriter.max_degree",
        "rewriter.sort_sums",
        "rewriter.push_to_real",
    ] {
        owner
            .admit(key.len(), 0)
            .map_err(|_| "polynomial parameter owner stopped")?;
        let bytes = {
            let values = STORE
                .lock()
                .map_err(|_| "global parameter store unavailable")?;
            values
                .as_ref()
                .and_then(|v| v.get(key))
                .map_or(0, String::len)
        };
        owner
            .admit(
                bytes
                    .checked_add(key.len())
                    .ok_or("parameter work overflow")?,
                0,
            )
            .map_err(|_| "polynomial parameter owner stopped")?;
        let value = {
            let values = STORE
                .lock()
                .map_err(|_| "global parameter store unavailable")?;
            match values.as_ref().and_then(|v| v.get(key)) {
                Some(value) if value.len() <= bytes => {
                    let (_, kind) = registry_entry(key).ok_or("parameter registry missing")?;
                    Some(match kind {
                        ParamKind::Bool => ay_dpll::api::TacticParameterValue::Bool(
                            value.parse().map_err(|_| "invalid Boolean parameter")?,
                        ),
                        ParamKind::UInt => ay_dpll::api::TacticParameterValue::UInt(
                            value.parse().map_err(|_| "invalid unsigned parameter")?,
                        ),
                        ParamKind::Str => return Err("invalid polynomial registry type"),
                    })
                }
                Some(_) => return Err("global parameter changed during admission"),
                None => None,
            }
        };
        owner
            .check()
            .map_err(|_| "polynomial parameter owner stopped")?;
        if let Some(value) = value {
            result
                .set(key.trim_start_matches("rewriter."), value)
                .map_err(|_| "invalid polynomial parameter")?;
        }
    }
    Ok(result)
}

/// A configuration choice, not an admission grant. The actual sequence
/// rewriter retains its original operation's work/storage/deadline owner.
pub(crate) fn sequence_power_expansion(
    owner: &dyn ay_core::term::TermConstructionAdmission,
) -> Result<u32, &'static str> {
    sequence_power_from(&STORE, owner)
}

fn sequence_power_from(
    store: &Mutex<Option<HashMap<String, String>>>,
    owner: &dyn ay_core::term::TermConstructionAdmission,
) -> Result<u32, &'static str> {
    const KEY: &str = "rewriter.max_power_expansion";
    const STOPPED: &str = "original global parameter read refused";
    owner.admit(KEY.len(), 0).map_err(|_| STOPPED)?;
    let bytes = {
        let values = store
            .lock()
            .map_err(|_| "global parameter store unavailable")?;
        values
            .as_ref()
            .and_then(|v| v.get(KEY))
            .map_or(0, String::len)
    };
    // A valid UInt can retain arbitrarily many leading zeros. Debit the real
    // borrowed bytes, not a scalar-width guess. No mutex spans this callback.
    owner
        .admit(bytes.checked_add(KEY.len()).ok_or(STOPPED)?, 0)
        .map_err(|_| STOPPED)?;
    let result = {
        let values = store
            .lock()
            .map_err(|_| "global parameter store unavailable")?;
        match values.as_ref().and_then(|v| v.get(KEY)) {
            Some(value) if value.len() <= bytes => value
                .parse()
                .map_err(|_| "invalid sequence expansion parameter"),
            Some(_) => Err("global parameter changed during admission"),
            None => Ok(2),
        }
    };
    owner.check().map_err(|_| STOPPED)?;
    result
}

#[cfg(test)]
mod sequence_power_read_tests {
    use super::*;
    use ay_core::original_query::{CountedAdmission, CountedAdmissionError, FiniteAdmissionGrant};
    use ay_core::term::TermConstructionAdmission;
    use std::{cell::Cell, sync::Arc};

    fn data(value: String) -> Mutex<Option<HashMap<String, String>>> {
        Mutex::new(Some(HashMap::from([(
            "rewriter.max_power_expansion".into(),
            value,
        )])))
    }

    #[test]
    fn sequence_power_global_read_prices_actual_bytes_cumulatively() {
        let store = data(format!("{}4", "0".repeat(4096)));
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(6000, 4096),
            None,
            Arc::new(|| false),
        )
        .unwrap();
        assert_eq!(sequence_power_from(&store, &owner), Ok(4));
        assert!(sequence_power_from(&store, &owner).is_err());
        assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
        assert!(sequence_power_from(&store, &owner).is_err());
    }

    #[test]
    fn sequence_power_global_read_allows_callback_reentry_but_not_unpaid_growth() {
        struct Reenter<'a> {
            store: &'a Mutex<Option<HashMap<String, String>>>,
            calls: Cell<usize>,
        }
        impl TermConstructionAdmission for Reenter<'_> {
            fn admit(&self, _: usize, _: usize) -> Result<(), CountedAdmissionError> {
                let n = self.calls.get() + 1;
                self.calls.set(n);
                if n == 2 {
                    self.store
                        .lock()
                        .unwrap()
                        .as_mut()
                        .unwrap()
                        .insert("rewriter.max_power_expansion".into(), "00004".into());
                }
                Ok(())
            }
            fn refuse(&self, e: CountedAdmissionError) -> CountedAdmissionError {
                e
            }
        }
        let store = data("4".into());
        let owner = Reenter {
            store: &store,
            calls: Cell::new(0),
        };
        assert_eq!(
            sequence_power_from(&store, &owner),
            Err("global parameter changed during admission")
        );
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

/// Whether z3's `encoding` global is its default `unicode`.
///
/// `encoding` is the one stored parameter that changes z3's SEMANTICS: under
/// `bmp` or `ascii` z3's character alphabet ends at 0xFFFF or 255, which
/// changes `Z3_mk_string`'s escape decoding, `str.from_code`, `str.to_code`
/// and every character bound. AY implements the unicode alphabet only, so
/// under any other value the string builders refuse instead of answering
/// with unicode semantics (see `ffi_guard_mk`).
pub(crate) fn string_encoding_is_unicode() -> bool {
    let store = match STORE.lock() {
        Ok(g) => g,
        Err(poisoned) => poisoned.into_inner(),
    };
    encoding_is_unicode(
        store
            .as_ref()
            .and_then(|map| map.get("encoding"))
            .map(String::as_str),
    )
}

/// Whether a stored `encoding` value (`None`: never set) is `unicode`.
pub(crate) fn encoding_is_unicode(value: Option<&str>) -> bool {
    value.is_none_or(|value| value == "unicode")
}

/// Set a process-global configuration parameter (Z3's `Z3_global_param_set`).
///
/// Stores the value for later `Z3_global_param_get` readback iff the key is in
/// the registry and the value parses at the registered type; otherwise it is
/// refused silently (z3 refuses too, with a stderr warning AY does not print —
/// see the module doc for the full measured contract). Store-only: AY's
/// solving never consults this store, so it can never affect a verdict; the
/// one semantic parameter, `encoding`, makes the string builders refuse when
/// it is not `unicode` ([`string_encoding_is_unicode`]).
///
/// # Safety
/// `param_id` and `param_value` may be null (refused) or must point to valid
/// NUL-terminated strings.
#[no_mangle]
pub unsafe extern "C" fn Z3_global_param_set(param_id: Z3_string, param_value: Z3_string) {
    if param_id.is_null() || param_value.is_null() {
        return;
    }
    let key = {
        // SAFETY: `param_id` was null-checked above and the caller guarantees it
        // remains a valid NUL-terminated string while the bounded helper clones it.
        unsafe { ffi_read_bounded_text(param_id) }
    };
    let value = {
        // SAFETY: `param_value` was null-checked above and the caller guarantees it
        // remains a valid NUL-terminated string while the bounded helper clones it.
        unsafe { ffi_read_bounded_text(param_value) }
    };
    let (Ok(key), Ok(value)) = (key, value) else {
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
