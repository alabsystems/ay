// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Process-wide EUF debug and soundness-policy defaults.

use std::sync::OnceLock;

/// #6359: Cached debug flags for EUF solver.
pub(super) struct EufDebugFlags {
    pub(super) debug_euf: bool,
    pub(super) debug_nelson_oppen: bool,
    /// Kill switch for Bool-argument congruence completeness. Default OFF
    /// (disabled) as of 2026-06-17: the completion is UNSOUND/incomplete — it
    /// decides Bool-valued-UF-arg atoms but produces a FALSE-SAT on witnesses
    /// like `(= (fb true) (fb p0))` ∧ `(not (= (fb (or p1 p0)) (fb p0)))`
    /// (AY sat, truth unsat; found by the declared-division soundness audit).
    /// With it OFF, EUF leaves these clauseless Bool-arg atoms UNDECIDED and
    /// returns a sound `unknown` (the pre-f6915645 behavior), which is correct.
    /// OFF process-wide (the former `AY_EUF_BOOL_ARG_MERGE` env override is
    /// removed — no environment variable may enable an unsound path); the
    /// standalone EUF unit tests enable it per-instance via
    /// `set_bool_arg_congruence`. When enabled, Bool-sorted terms that appear
    /// as UF arguments participate in the true/false equivalence-class merge
    /// so congruence fires on their parent applications.
    pub(super) bool_arg_congruence: bool,
    /// Read-only SOUND Bool-arg congruence MODEL VALIDATION. Default ON.
    /// At a candidate `Sat` verdict, refuses to certify a model that is provably
    /// non-congruent over Bool UF-args (two apps with identical non-Bool args
    /// and identical Bool-arg truth values in different classes) by downgrading
    /// `Sat` -> `Unknown`. Only ever downgrades — never asserts UNSAT — so it has
    /// no false-UNSAT risk (unlike the merge). This is the SOUND fallback that
    /// keeps the flagship from false-SAT on Bool-arg congruence gaps the lemma
    /// cannot close (e.g. `uf_fs2`). Always ON (the former
    /// `AY_EUF_BOOL_ARG_VALIDATE=0` env kill-switch is removed — no
    /// environment variable may turn off a soundness guard); `solve_euf`
    /// tunes it per-instance via `set_bool_arg_validate`.
    pub(super) bool_arg_validate: bool,
    /// Transitive (congruence-closing) variant of the validation. Default ON.
    pub(super) bool_arg_validate_transitive: bool,
}

static EUF_DEBUG_FLAGS: OnceLock<EufDebugFlags> = OnceLock::new();

pub(super) fn euf_debug_flags() -> &'static EufDebugFlags {
    EUF_DEBUG_FLAGS.get_or_init(|| EufDebugFlags {
        debug_euf: ay_core::debug_channel_active(ay_core::DebugChannel::Euf),
        debug_nelson_oppen: ay_core::debug_channel_active(ay_core::DebugChannel::EufNelsonOppen),
        // EUF-side Bool-arg truth-value class merge. DEFAULT OFF.
        //
        // This merges UF-application arguments that share a *model* truth value
        // into the true/false class so congruence fires on their parent apps,
        // INCLUDING builtin/connective and (with the constant fold added here)
        // constant Bool args. It is the only mechanism that can relate
        // syntactically-different-but-model-equal complex Bool args (the
        // `uf_fs2` witness). However it remains UNSOUND in the false-UNSAT
        // direction: run during BCP over the extended builtin Bool-arg set, it
        // can emit congruence conflicts whose reason literals are not faithfully
        // explainable, yielding a wrong learned clause and a false UNSAT
        // (reproducer: deeply nested `fb(xor(..))`/`fb(and(..))` over a
        // partial assignment). The conflict verifier cannot catch this (it
        // re-runs the same deterministic merge). It is therefore kept OFF,
        // permanently and process-wide (the former `AY_EUF_BOOL_ARG_MERGE=1`
        // env force-enable is removed — no environment variable may enable an
        // unsound path); the SOUND production driver is the formula-level
        // congruence-lemma injection in `solve_euf`. The standalone EUF unit
        // tests enable it per-instance via `set_bool_arg_congruence`.
        bool_arg_congruence: false,
        // Read-only SOUND model-validation guard (always ON). Only ever
        // downgrades Sat -> Unknown (no false-UNSAT risk). It is the soundness
        // net for Bool-arg congruence false-SATs in BOTH incremental and
        // non-incremental mode (the eager congruence lemma closes them
        // non-incrementally but is unsound across push/pop). The baseline-class
        // gate in `bool_arg_model_is_congruent` confines it to genuine Bool-arg
        // congruence violations so it does not over-fire on dense incremental
        // models. (Former `AY_EUF_BOOL_ARG_VALIDATE=0` /
        // `AY_EUF_BOOL_ARG_VALIDATE_TRANSITIVE=0` env kill-switches removed —
        // no environment variable may turn off a soundness guard.)
        bool_arg_validate: true,
        bool_arg_validate_transitive: true,
    })
}
