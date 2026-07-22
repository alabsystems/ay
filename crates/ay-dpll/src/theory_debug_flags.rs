// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory-layer disable flags and debug flags for DPLL(T) (#8319, #8331).
//!
//! All `AY_NO_*` and `AY_DEBUG_*` queries are delegated to the centralized
//! `ay_core::debug_channel_active()` and `ay_core::theory_disable_flags()`
//! singletons.

// ---------------------------------------------------------------------------
// Theory-layer disable flags (AY_NO_* / AY_DISABLE_*)
// ---------------------------------------------------------------------------

pub(crate) fn no_bound_axioms() -> bool {
    ay_core::theory_disable_flags().no_bound_axioms
}

#[allow(dead_code)]
pub(crate) fn no_theory_propagation() -> bool {
    ay_core::theory_disable_flags().no_theory_propagation
}

pub(crate) fn no_bcp_theory_check() -> bool {
    ay_core::theory_disable_flags().no_bcp_theory_check
}

pub(crate) fn no_ite_deferral() -> bool {
    ay_core::theory_disable_flags().no_ite_deferral
}

pub(crate) fn disable_theory_check() -> bool {
    ay_core::theory_disable_flags().disable_theory_check
}

pub(crate) fn max_fixpoint_rounds() -> Option<usize> {
    ay_core::theory_disable_flags().max_fixpoint_rounds
}

pub(crate) fn no_inline_lemmas() -> bool {
    ay_core::theory_disable_flags().no_inline_lemmas
}

// ---------------------------------------------------------------------------
// Debug flags (AY_DEBUG_*)
// ---------------------------------------------------------------------------

pub(crate) fn debug_dpll() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::Dpll)
}

pub(crate) fn debug_sync() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::Sync)
}

pub(crate) fn debug_verify() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::Verify)
}

pub(crate) fn debug_nelson_oppen() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::NelsonOppen)
}

pub(crate) fn debug_model() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::Model)
}

pub(crate) fn debug_var_subst() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::VarSubst)
}

pub(crate) fn debug_concat_eq() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::ConcatEq)
}

pub(crate) fn debug_ite_eq() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::IteEq)
}

pub(crate) fn debug_ufseqlia() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::Auflia)
}

pub(crate) fn debug_ufseq() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::Auflia)
}

#[cfg(debug_assertions)]
pub(crate) fn debug_lia_only() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::Lia)
}

pub(crate) fn debug_auflia() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::Auflia)
}

pub(crate) fn debug_ite_conditions() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::IteConditions)
}

pub(crate) fn debug_linking() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::Linking)
}

pub(crate) fn debug_preprocessed() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::Preprocessed)
}

// ---------------------------------------------------------------------------
// Trace file env vars (string payloads, not boolean flags)
// ---------------------------------------------------------------------------

pub(crate) fn dpll_diagnostic_path() -> Option<String> {
    // Reads from the centralized `MiscCliFlags` singleton (#8835) — the CLI
    // populates `dpll_diagnostic_file` / `dpll_diagnostic_enabled` from
    // `--dpll-diagnostic-file` / `--dpll-diagnostic`. Env-var fallback is
    // retained for library consumers via `misc_cli_flags()` initialization.
    let flags = ay_core::misc_cli_flags();
    if let Some(path) = flags.dpll_diagnostic_file.as_ref() {
        return Some(path.clone());
    }
    if flags.dpll_diagnostic_enabled {
        let pid = std::process::id();
        let path = std::env::temp_dir().join(format!("ay_dpll_diagnostic_{pid}.jsonl"));
        return Some(path.to_string_lossy().into_owned());
    }
    None
}

pub(crate) fn dpll_trace_file_path() -> Option<String> {
    // Reads from the centralized `MiscCliFlags` singleton (#8835); the CLI
    // populates `dpll_trace_file` from `--dpll-trace-file`.
    ay_core::misc_cli_flags().dpll_trace_file.clone()
}
