// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Experimental (`AY_XP_*`) probe / vivify / backbone measurement knobs.
//!
//! DEFAULT-OFF measured-infra. These env knobs exist ONLY to reproduce the
//! root-cause experiment that tested the hypothesis "AY under-invests in
//! probe/vivify unit derivation, so deeper probe+vivify would flip UNKNOWN
//! instances by deriving more units." That hypothesis was **refuted by direct
//! measurement** (wf_c4cfe21f, base c3cec0ad):
//!
//! * Deeper PROBE (`AY_XP_PROBE_PERMILLE`/`AY_XP_PROBE_MIN`) is
//!   candidate-exhausted — `generate_probes` only enqueues BIG-roots, so 3x the
//!   tick budget re-probes the same roots and derives ZERO extra units
//!   (5dbe7b31: probe units 330 -> 329).
//! * Deeper VIVIFY (`AY_XP_VIV_PERMILLE`) moves its own counters 3-6x
//!   (5dbe7b31 strengthened 595 -> 3,467) and nudges BVE +13% on cdd89d1b, but
//!   `fixed_vars` (units) stays FLAT (~39.9K / ~4.8K) and NOTHING FLIPS.
//! * Skipping backbone (`AY_XP_NO_BACKBONE`) frees the 5.8-7.8s
//!   binary-backbone ring pass whose 2-11 units turn out redundant
//!   (`fixed_vars` is unchanged-or-higher without it), buys only +7.8%
//!   conflicts on 5dbe7b31 (the rest absorbed by sweep), and FLIPS NOTHING.
//!
//! Units are already at 89-94% of kissat with substitution at parity; the
//! residual gaps are BVE depth and SAT search-trajectory, neither addressable
//! by unit derivation. This is a textbook sufficient-mechanism / insufficient-
//! result case (campaign lesson: a lever that moves its own counter but flips
//! nothing is a measured-negative -> default OFF, honest).
//!
//! **Because every accessor returns `None`/`false` when its variable is unset,
//! the shipping code path is byte-for-byte unchanged and the regression floor
//! holds by construction.** These knobs are diagnostic reproduction handles,
//! NOT a shipping lever, and are namespaced `AY_XP_*` (experiment) rather than
//! `AY_AB_*` (shipping A/B kill-switch) to make that distinction explicit.
//!
//! Each knob is parsed once per process and cached (`OnceLock`), matching the
//! house `variant.rs` idiom.

use std::sync::OnceLock;

/// `AY_XP_PROBE_PERMILLE` — override the per-round failed-literal probe tick
/// budget permille (permille of the search-tick delta; shipping defaults are
/// `PROBE_EFFORT_PERMILLE=8` / `PROBE_LARGE_FORMULA_EFFORT_PERMILLE=25`).
/// `None` (unset / non-positive / unparsable) => use the shipping constant.
pub(super) fn probe_permille() -> Option<u64> {
    static V: OnceLock<Option<u64>> = OnceLock::new();
    *V.get_or_init(|| parse_pos_u64("AY_XP_PROBE_PERMILLE"))
}

/// `AY_XP_PROBE_MIN` — override the probe tick-budget floor
/// (shipping default `PROBE_MIN_EFFORT=10_000`). `None` => use the constant.
pub(super) fn probe_min_effort() -> Option<u64> {
    static V: OnceLock<Option<u64>> = OnceLock::new();
    *V.get_or_init(|| parse_pos_u64("AY_XP_PROBE_MIN"))
}

/// `AY_XP_VIV_PERMILLE` — override `VIVIFY_EFFORT_PERMILLE` (shipping default
/// `100`) for both the learned-clause and irredundant vivify budgets.
/// `None` => use the constant.
pub(super) fn vivify_permille() -> Option<u64> {
    static V: OnceLock<Option<u64>> = OnceLock::new();
    *V.get_or_init(|| parse_pos_u64("AY_XP_VIV_PERMILLE"))
}

/// `AY_XP_NO_BACKBONE=1` — skip both backbone passes (binary-clause ring scan
/// and bounded-CDCL) for the whole run, by forcing `should_backbone()` false.
/// Any other value (incl. unset) => backbone runs normally.
pub(super) fn no_backbone() -> bool {
    // B21: the AY_XP_NO_BACKBONE ablation switch is retired (never set, no
    // CLI need recorded); backbone runs on its own gates.
    false
}

/// Parse a strictly-positive `u64` from an env var; `None` on unset / parse
/// failure / non-positive so the caller falls through to its shipping default.
fn parse_pos_u64(name: &str) -> Option<u64> {
    std::env::var(name)
        .ok()
        .and_then(|value| value.parse::<u64>().ok())
        .filter(|value| *value > 0)
}
