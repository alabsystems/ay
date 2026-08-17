// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible solver statistics (`Z3_solver_get_statistics` + `Z3_stats_*`).
//!
//! AY's executor tracks a rich set of REAL solve counters (conflicts, decisions,
//! propagations, restarts, memory, per-theory activity, ...). This module
//! exposes that snapshot through the Z3 C API so z3py's `Solver.statistics()`
//! works over ayz3.
//!
//! # Honesty contract
//!
//! Every value reported here is a REAL AY counter read from the executor's
//! `statistics()` — captured into the solver handle right after the check that
//! produced it (see `check_solver_handle`). Nothing is fabricated:
//!
//! - Keys are named in a z3-ish style (`conflicts`, `decisions`, `max memory`,
//!   ...) but each maps to an actual AY counter. AY's counter SET differs from
//!   z3's (AY has no `mk bool var`, z3 has no `nelson-oppen rounds`); this is a
//!   documented, honest divergence — we never invent a z3-specific key with a
//!   made-up value.
//! - Non-numeric (string) statistics labels are omitted: z3's statistics model
//!   is purely `uint`/`double`, and z3py reads every entry as one of those, so
//!   surfacing a string label would force a bogus numeric read. Skipping them is
//!   the correct mapping, not a loss of a real number.
//! - Before any check has run on a solver handle, its snapshot is empty and the
//!   handle reports an all-zero statistics set (honest: no solve activity yet).

use std::ffi::c_uint;

use ay_dpll::{StatValue, Statistics};

use super::{
    cache_string, ffi_guard_const_ptr, ffi_guard_double, ffi_guard_int, ffi_guard_ptr,
    ffi_guard_uint, Z3Context, Z3_context, Z3_solver, Z3_stats, Z3_string, Z3_INVALID_ARG, Z3_OK,
};

/// One statistic value, classified for the Z3 `uint`/`double` split.
///
/// Integer counters that fit in a 32-bit `unsigned` are `Uint` (exactly what
/// `Z3_stats_get_uint_value` returns); anything larger — or an inherently
/// real-valued stat like memory/time — is `Double`. This keeps the invariant
/// that a `Uint` never truncates when read as `unsigned`.
#[derive(Debug, Clone, Copy)]
pub(crate) enum StatEntry {
    Uint(u64),
    Double(f64),
}

impl StatEntry {
    /// Classify an integer counter: `Uint` when it fits `u32`, else `Double`
    /// (a `f64` exactly represents integers up to 2^53, so no fabrication).
    pub(crate) fn from_uint(v: u64) -> Self {
        if u32::try_from(v).is_ok() {
            StatEntry::Uint(v)
        } else {
            StatEntry::Double(v as f64)
        }
    }
}

/// Internal state for a `Z3_stats` handle: an ordered list of `(key, value)`
/// entries flattened from a [`Statistics`] snapshot at
/// `Z3_solver_get_statistics` time. Arena-owned by the context
/// (`stats_handle_cache`) and freed at `Z3_del_context`; `Z3_stats_inc_ref` /
/// `Z3_stats_dec_ref` are bookkeeping-only no-ops (the handle is never freed
/// early), matching `Z3_solver_inc_ref`/`Z3_solver_dec_ref`.
pub struct StatsHandle {
    pub(crate) entries: Vec<(String, StatEntry)>,
}

/// Flatten a [`Statistics`] snapshot into an ordered `(key, value)` list using
/// z3-ish key names over AY's REAL counters.
///
/// The core SAT counters and the resource stats (memory/time/rlimit) are always
/// present (even at zero) so `stats['conflicts']` always resolves after a check;
/// the richer per-theory counters are included only when non-zero to avoid
/// noise, and every `extra` numeric counter AY recorded is appended verbatim
/// (its own honest name). String-valued extras are skipped (see module docs).
pub(crate) fn flatten_statistics(stats: &Statistics) -> Vec<(String, StatEntry)> {
    // Core SAT-level counters — always present.
    let mut out: Vec<(String, StatEntry)> = vec![
        (
            "conflicts".to_string(),
            StatEntry::from_uint(stats.conflicts),
        ),
        (
            "decisions".to_string(),
            StatEntry::from_uint(stats.decisions),
        ),
        (
            "propagations".to_string(),
            StatEntry::from_uint(stats.propagations),
        ),
        ("restarts".to_string(), StatEntry::from_uint(stats.restarts)),
    ];

    // Richer counters — only when non-zero (z3 also omits zero-valued stats).
    for (key, v) in [
        ("learned clauses", stats.learned_clauses),
        ("deleted clauses", stats.deleted_clauses),
        ("theory conflicts", stats.theory_conflicts),
        ("theory propagations", stats.theory_propagations),
        ("nelson-oppen rounds", stats.nelson_oppen_rounds),
        (
            "equalities propagated to euf",
            stats.equalities_propagated_to_euf,
        ),
        (
            "equalities propagated to arith",
            stats.equalities_propagated_to_arith,
        ),
        ("ematching rounds", stats.ematching_rounds_completed),
        ("ematching instances", stats.ematching_instances_created),
        ("refinement count", stats.refinement_count),
        ("model validation failures", stats.model_validation_failures),
        ("model validation skips", stats.model_validation_skips),
        ("proof clauses", stats.proof_clause_count),
    ] {
        if v > 0 {
            out.push((key.to_string(), StatEntry::from_uint(v)));
        }
    }

    // Problem-size and resource stats — always present.
    out.push((
        "num assertions".to_string(),
        StatEntry::from_uint(stats.num_assertions),
    ));
    out.push((
        "rlimit count".to_string(),
        StatEntry::from_uint(stats.rlimit_count),
    ));
    out.push((
        "max memory".to_string(),
        StatEntry::Double(stats.max_memory_mb),
    ));
    out.push(("memory".to_string(), StatEntry::Double(stats.memory_mb)));
    out.push(("time".to_string(), StatEntry::Double(stats.time_seconds)));

    // Every extra numeric counter AY recorded (its own honest name). String
    // labels are not numeric statistics and are skipped (see module docs).
    for (name, value) in &stats.extra {
        match value {
            StatValue::Int(i) => out.push((name.clone(), StatEntry::from_uint(*i))),
            StatValue::Float(f) => out.push((name.clone(), StatEntry::Double(*f))),
            // String labels are not numeric statistics (see module docs), and
            // `StatValue` is `#[non_exhaustive]`, so any string/future variant
            // is skipped rather than surfaced as a bogus numeric read.
            _ => {}
        }
    }

    out
}

/// Render an entry list in z3's `(:key val\n :key val)` statistics shape.
pub(crate) fn stats_to_string(entries: &[(String, StatEntry)]) -> String {
    let mut s = String::from("(");
    for (i, (key, value)) in entries.iter().enumerate() {
        if i > 0 {
            s.push_str("\n ");
        }
        match value {
            StatEntry::Uint(u) => s.push_str(&format!(":{key} {u}")),
            StatEntry::Double(d) => s.push_str(&format!(":{key} {d:.2}")),
        }
    }
    s.push(')');
    s
}

/// Record the honest error for a null `Z3_stats` handle.
fn note_null_stats_handle(ctx: &mut Z3Context, operation: &str) {
    ctx.last_error = Z3_INVALID_ARG;
    ctx.error_msg = Some(format!("{operation}: null Z3_stats handle"));
}

/// Get the statistics of THIS solver handle's last check.
///
/// Returns a `Z3_stats` handle over a SNAPSHOT of the executor's real counters
/// for exactly that check (materialized at check time). If no check has run on
/// the handle, the snapshot is empty and the returned statistics are all zero.
///
/// The handle is context-owned (freed at `Z3_del_context`).
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid solver handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_solver_get_statistics(c: Z3_context, s: Z3_solver) -> Z3_stats {
    // SAFETY: `c` is null-checked and panic-contained by `ffi_guard_ptr`; `s` is
    // null-checked via `as_ref` and, when non-null, is a handle owned by this
    // context's arena (single-threaded per context, so no race).
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let stats = match s.as_ref() {
                Some(handle) => handle.last_statistics.clone().unwrap_or_default(),
                // This surface deliberately treats a null solver as an empty
                // pre-check snapshot. It is a sentinel query used by existing
                // C consumers; returning a real arena-owned stats handle keeps
                // every subsequent stats accessor safe and deterministic.
                None => Statistics::default(),
            };
            let entries = flatten_statistics(&stats);
            let handle = Box::into_raw(Box::new(StatsHandle { entries }));
            ctx.stats_handle_cache.push(handle);
            ctx.last_error = Z3_OK;
            handle
        })
    }
}

/// Increment statistics reference count (bookkeeping-only no-op; the handle is
/// arena-owned and freed at `Z3_del_context`).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_stats_inc_ref(_c: Z3_context, _s: Z3_stats) {}

/// Decrement statistics reference count (bookkeeping-only no-op).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_stats_dec_ref(_c: Z3_context, _s: Z3_stats) {}

/// Number of statistics entries in the handle.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid stats handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_stats_size(c: Z3_context, s: Z3_stats) -> c_uint {
    // SAFETY: `c` is null-checked and panic-contained by `ffi_guard_uint`; `s`
    // is null-checked via `as_ref`.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            let Some(handle) = s.as_ref() else {
                note_null_stats_handle(ctx, "Z3_stats_size");
                return 0;
            };
            handle.entries.len() as c_uint
        })
    }
}

/// Key (name) of the statistics entry at `idx`.
///
/// Returns a context-owned string (valid until `Z3_del_context`), or NULL if
/// `idx` is out of range.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid stats handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_stats_get_key(c: Z3_context, s: Z3_stats, idx: c_uint) -> Z3_string {
    // SAFETY: `c` is null-checked and panic-contained by `ffi_guard_const_ptr`;
    // `s` is null-checked via `as_ref`.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let Some(handle) = s.as_ref() else {
                note_null_stats_handle(ctx, "Z3_stats_get_key");
                return std::ptr::null();
            };
            match handle.entries.get(idx as usize) {
                Some((key, _)) => cache_string(ctx, key.clone()),
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!("Z3_stats_get_key: index {idx} out of range"));
                    std::ptr::null()
                }
            }
        })
    }
}

/// True iff the entry at `idx` is a `uint` value.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid stats handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_stats_is_uint(c: Z3_context, s: Z3_stats, idx: c_uint) -> bool {
    // SAFETY: `c` is null-checked and panic-contained by `ffi_guard_int`; the
    // c_int sentinel is re-routed through bool. `s` is null-checked via `as_ref`.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let Some(handle) = s.as_ref() else {
                note_null_stats_handle(ctx, "Z3_stats_is_uint");
                return 0;
            };
            i32::from(matches!(
                handle.entries.get(idx as usize),
                Some((_, StatEntry::Uint(_)))
            ))
        }) != 0
    }
}

/// True iff the entry at `idx` is a `double` value.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid stats handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_stats_is_double(c: Z3_context, s: Z3_stats, idx: c_uint) -> bool {
    // SAFETY: `c` and `s` satisfy the caller contract; `ffi_guard_int`
    // null-checks `c`, and the closure checks `s` before reading its entries.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let Some(handle) = s.as_ref() else {
                note_null_stats_handle(ctx, "Z3_stats_is_double");
                return 0;
            };
            i32::from(matches!(
                handle.entries.get(idx as usize),
                Some((_, StatEntry::Double(_)))
            ))
        }) != 0
    }
}

/// `uint` value of the entry at `idx`.
///
/// Returns the exact counter for a `uint` entry (which fits `u32` by
/// construction). Returns 0 for a `double` entry or an out-of-range index —
/// callers should gate on `Z3_stats_is_uint` (z3py does).
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid stats handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_stats_get_uint_value(
    c: Z3_context,
    s: Z3_stats,
    idx: c_uint,
) -> c_uint {
    // SAFETY: `c` is null-checked and panic-contained by `ffi_guard_uint`; `s`
    // is null-checked via `as_ref`.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            let Some(handle) = s.as_ref() else {
                note_null_stats_handle(ctx, "Z3_stats_get_uint_value");
                return 0;
            };
            match handle.entries.get(idx as usize) {
                // `from_uint` guarantees a `Uint` fits `u32`, so this is exact.
                Some((_, StatEntry::Uint(v))) => *v as c_uint,
                _ => 0,
            }
        })
    }
}

/// `double` value of the entry at `idx`.
///
/// Works for either representation: a `uint` entry is returned as its exact
/// `f64` (integers up to 2^53 are exact), a `double` entry as itself. Returns
/// 0.0 for an out-of-range index.
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid stats handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_stats_get_double_value(c: Z3_context, s: Z3_stats, idx: c_uint) -> f64 {
    // SAFETY: `c` is null-checked and panic-contained by `ffi_guard_double`; `s`
    // is null-checked via `as_ref`.
    unsafe {
        ffi_guard_double(c, 0.0, |ctx| {
            let Some(handle) = s.as_ref() else {
                note_null_stats_handle(ctx, "Z3_stats_get_double_value");
                return 0.0;
            };
            match handle.entries.get(idx as usize) {
                Some((_, StatEntry::Uint(v))) => *v as f64,
                Some((_, StatEntry::Double(d))) => *d,
                None => 0.0,
            }
        })
    }
}

/// Render the statistics as a string in z3's `(:key val ...)` shape.
///
/// The returned string is context-owned (valid until `Z3_del_context`).
///
/// # Safety
/// `c` must be a valid context pointer; `s`, when non-null, a valid stats handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_stats_to_string(c: Z3_context, s: Z3_stats) -> Z3_string {
    // SAFETY: `c` is null-checked and panic-contained by `ffi_guard_const_ptr`;
    // `s` is null-checked via `as_ref`.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let Some(handle) = s.as_ref() else {
                note_null_stats_handle(ctx, "Z3_stats_to_string");
                return std::ptr::null();
            };
            let text = stats_to_string(&handle.entries);
            cache_string(ctx, text)
        })
    }
}

#[cfg(test)]
#[path = "statistics_tests.rs"]
mod statistics_tests;
