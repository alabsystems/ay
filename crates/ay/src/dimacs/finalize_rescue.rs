// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ---------------------------------------------------------------------------
// FINALIZE_SAT_FAIL rescue lane
// ---------------------------------------------------------------------------

/// Kill-switch for the finalize-fail rescue lane. Default ON: the lane only
/// runs after a would-be `s UNKNOWN`, so its worst case equals the status quo.
fn finalize_rescue_applicable(
    solver: &SatSolver,
    result: &SatResult,
    proof_config: Option<&ProofConfig>,
) -> bool {
    // Alethe/Lean4 write their exports in dedicated runners before the
    // finish path; a rescue UNSAT could not re-emit them here. DRAT/LRAT are
    // re-emitted from scratch by the retry solver.
    let proof_compatible = match proof_config {
        None => true,
        Some(proof) => matches!(proof.format, ProofFormat::Drat | ProofFormat::Lrat),
    };
    matches!(result, SatResult::Unknown)
        && proof_compatible
        && solver.last_unknown_reason() == Some(ay_sat::SatUnknownReason::InvalidSatModel)
        && !is_timed_out()
        && ay_core::sat_ab_switches().finalize_rescue.unwrap_or(true)
}

/// Maximal-reconstruction-robustness retry profile: every technique that
/// mutates the model (needs reconstruction witnesses) or deletes/substitutes
/// original constraints is OFF. Techniques that only add logically implied
/// clauses or remove redundant ones (model-preserving) stay ON, as do
/// phase-initialization heuristics (walk/warmup) whose candidate models still
/// pass the finalize gate.
fn finalize_rescue_profile() -> ay_sat::InprocessingFeatureProfile {
    let mut profile = ay_sat::InprocessingFeatureProfile::default();
    // Initial preprocess pipeline (ELS/pure literals/elimination): the
    // largest reconstruction surface — OFF.
    profile.preprocess = false;
    // Model-mutating / witness-reconstructing eliminations — OFF.
    profile.bve = false;
    profile.bce = false;
    profile.cce = false;
    profile.condition = false;
    profile.decompose = false;
    profile.sweep = false;
    profile.symmetry = false;
    // Variable-adding / gate-rewriting structure passes — OFF.
    profile.factor = false;
    profile.sbva = false;
    profile.gate = false;
    profile.congruence = false;
    // Clause-deleting resolution passes with historical constraint-loss
    // defects (HTR: b1402a16 e318e2ac/90bec6dc/e4ac15cf) — OFF.
    profile.htr = false;
    // Kept ON (model-preserving): vivify, subsume, probe, transred, hbr,
    // shrink, backbone, reorder, walk, warmup.
    profile
}

/// Retry the solve once on the ORIGINAL formula with the degraded profile.
/// Returns the retry result and the retry solver, or None when the original
/// DIMACS text is unavailable or unparseable. The retry result is trustworthy
/// through the same channels as any first-attempt result: SAT models are
/// validated against the retry solver's original ledger (== the original
/// formula) by the finalize gate inside declare_sat_from_model; a retry UNSAT
/// in DRAT/LRAT mode re-emits its proof stream from scratch to the (already
/// cleaned-up) proof path and flows through the same post-solve verification.
fn run_finalize_rescue(
    source: DimacsInputSource<'_>,
    proof_config: Option<&ProofConfig>,
) -> Option<(SatResult, SatSolver)> {
    run_finalize_rescue_body(source, proof_config)
}

// ---------------------------------------------------------------------------
// Streaming DIMACS parser for large formulas
// ---------------------------------------------------------------------------

/// Clause count threshold for streaming parser activation.
const STREAMING_CLAUSE_THRESHOLD: usize = 500_000;
