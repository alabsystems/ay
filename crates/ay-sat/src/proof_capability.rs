// Copyright 2026 Andrew Yates, Inc.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof-mode capability policy for SAT inprocessing transforms.

use crate::InprocessingFeatureProfile;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProofMode {
    Drat,
    Lrat,
}

impl ProofMode {
    pub(crate) const fn from_lrat_enabled(lrat_enabled: bool) -> Self {
        if lrat_enabled {
            Self::Lrat
        } else {
            Self::Drat
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProofTransform {
    Inprobe,
    Vivify,
    VivifyIrred,
    Subsume,
    Probe,
    Backbone,
    Bve,
    Bce,
    Condition,
    Decompose,
    Factor,
    Sbva,
    Transred,
    Htr,
    Gate,
    Congruence,
    Sweep,
    Cce,
    Reorder,
    Symmetry,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ProofCapability {
    transform: ProofTransform,
    drat: bool,
    lrat: bool,
}

impl ProofCapability {
    const fn new(transform: ProofTransform, drat: bool, lrat: bool) -> Self {
        Self {
            transform,
            drat,
            lrat,
        }
    }

    const fn allows(self, mode: ProofMode) -> bool {
        match mode {
            ProofMode::Drat => self.drat,
            ProofMode::Lrat => self.lrat,
        }
    }
}

const PROOF_CAPABILITY_REGISTRY: &[ProofCapability] = &[
    ProofCapability::new(ProofTransform::Inprobe, true, true),
    ProofCapability::new(ProofTransform::Vivify, true, true),
    ProofCapability::new(ProofTransform::VivifyIrred, true, true),
    ProofCapability::new(ProofTransform::Subsume, true, true),
    ProofCapability::new(ProofTransform::Probe, true, true),
    ProofCapability::new(ProofTransform::Backbone, true, true),
    // DRAT proof policy allows BVE if a profile enables it. LRAT stays
    // fail-closed until the transform has checked LRAT hint support.
    ProofCapability::new(ProofTransform::Bve, true, false),
    ProofCapability::new(ProofTransform::Bce, true, true),
    ProofCapability::new(ProofTransform::Condition, true, true),
    // Decompose (SCC equivalent-literal substitution): DRAT is OPEN as of
    // 2026-07-09. The historical clamp ("model reconstruction inconsistent on
    // Braun UNSAT circuits") is STALE evidence: ef818369 root-caused that
    // braun FINALIZE_SAT_FAIL to preprocess-subsume constraint loss (a learned
    // subsumer was not promoted before irredundant deletion — fixed in
    // config_preprocess_cleanup.rs), and the SAT-side reconstruction audit
    // (group_misc finalize_sat_fail*, incl. braun_family_no_finalize_sat_fail)
    // passes clean with decompose enabled. Proof side, measured 2026-07-09:
    // decompose-active DRAT emissions verified end-to-end by the external
    // chain dpr-trim (DRAT/DPR -> LPR) + cake_lpr on every UNSAT probe run
    // (14/14 incl. braun7/8/10/12, 5246b7b9, 296fd43e with 4-1353 substituted
    // vars). LRAT stays fail-closed until SCC LRAT IDs are checked (#8197).
    // Kill-switch: --sat-no-drat-subst restores the pre-unlock DRAT clamp (see
    // `transform_allowed`).
    ProofCapability::new(ProofTransform::Decompose, true, false),
    ProofCapability::new(ProofTransform::Factor, true, false),
    ProofCapability::new(ProofTransform::Sbva, true, false),
    ProofCapability::new(ProofTransform::Transred, true, true),
    ProofCapability::new(ProofTransform::Htr, true, true),
    ProofCapability::new(ProofTransform::Gate, true, true),
    // Congruence: DRAT is OPEN as of 2026-07-10 (wf_ff5991a1). The 2026-07-09
    // clamp reasons are both root-caused and FIXED on the emission/rewriting
    // side (no checker or gate touched):
    // (a) duplicate watch-literal debug ICE — merge_or_contradict records the
    //     contradicting merge pair (x, ¬x) as an equivalence edge (needed so
    //     the UNSAT witness unit's RUP probe sees the closed cycle); its
    //     "binaries" degenerate to duplicate-literal units. Fixed by skipping
    //     complementary edges at every emission site (solver/inprocessing/
    //     congruence/mod.rs, proof_ladder.rs) and in forward subsumption's UF
    //     build; the contradiction is discharged by the witness-unit path.
    //     Regression: group_fuzz cnf_fuzz_inprocessing_mixed_{small,dense}.
    // (b) cmu-bmc-barrel6 FINALIZE_SAT_FAIL — NOT a reconstruction bug:
    //     vivify's prefix-subsumption flush accepted a mark_garbage_keep_data
    //     husk (left by congruence forward subsumption; still is_active())
    //     as a subsumer and deleted the live decompose-substituted twin —
    //     constraint loss caught fail-closed by the finalize gate. Fixed by
    //     excluding garbage-kept clauses from vivify candidates
    //     (vivify/tier.rs). barrel6 now solves Unsat (kissat-confirmed).
    // Proof side re-verified with the fixes (2026-07-10): congruence-active
    // DRAT (cong_equivs 54-300) end-to-end dpr-trim -> cake_lpr VERIFIED on
    // 4/4 UNSAT runs (braun8/10, 5246b7b9, 296fd43e), on top of the prior
    // 6/6 escape-hatch verifications (2026-07-09, wf_17e73a0f). SAT side:
    // finalize_sat_fail audits green under (retired B36) +
    // --sat-no-drat-subst=1 with debug asserts armed, and congruence-fired SAT
    // models validated externally against the original CNF (zero violations).
    // LRAT stays fail-closed until congruence LRAT hints are checked.
    // Kill-switch: --sat-no-drat-subst restores the DRAT clamp (see
    // `transform_allowed`). The feature itself remains OPT-IN on the Default
    // DIMACS route (0 measured flips — see variant.rs).
    ProofCapability::new(ProofTransform::Congruence, true, false),
    ProofCapability::new(ProofTransform::Sweep, false, false),
    ProofCapability::new(ProofTransform::Cce, true, true),
    ProofCapability::new(ProofTransform::Reorder, true, true),
    ProofCapability::new(ProofTransform::Symmetry, false, false),
];

/// Whether a proof surface can carry one of the explicitly supported symmetry
/// proof routes.
///
/// The generic DPR and full-tower SR experiments were retired because their
/// per-generator witnesses did not compose against earlier symmetry breakers.
/// The remaining exceptions are family-specific aux-free and orbitope SR steps,
/// plus HHW's plain-DRAT image-and-chain construction. All are wired through a
/// clause-stream writer (the DRAT writer, or the VeriPB writer which serializes
/// the same steps as `red`/`rup`); LRAT and clause-trace reconstruction remain
/// clamped because neither can represent a witnessed addition.
pub(crate) fn symmetry_extended_drat_allowed(mode: ProofMode) -> bool {
    matches!(mode, ProofMode::Drat)
}

/// Whether the DECLARED external checker (CLI `--proof-checker`, default
/// dsr-trim) will verify an SR-witnessed step written on the live proof
/// surface.
///
/// [`symmetry_extended_drat_allowed`] answers "is this proof SURFACE one the
/// symmetry proof routes support"; this answers the orthogonal capability
/// question "will the checker the run is declared against actually verify an
/// SR-witnessed step". It has two halves, and BOTH must hold:
///
///  1. the checker accepts substitution witnesses at all. Measured 2026-08-24
///     on php_11_8's orbitope staircase proof: dsr-trim `s VERIFIED UNSAT`;
///     drat-trim AND dpr-trim `s NOT VERIFIED`. VeriPB accepts them via `red`
///     (measured same day on php_sudoku_p15_h14, 91 witnessed steps,
///     `s VERIFIED UNSATISFIABLE` under the pinned checker of `ci/veripb.pin`).
///  2. the checker reads the format actually being emitted. `dsr-trim` reads
///     the DRAT-family stream and VeriPB reads `.pbp`; neither can read the
///     other. `veripb_surface` is the live [`crate::proof::ProofOutput`] kind,
///     so `--proof-format drat --proof-checker veripb` and
///     `--proof-format veripb --proof-checker dsr-trim` both clamp.
///
/// A SAT-COMP submission declares its checker up front and a rejected UNSAT
/// proof is disqualifying, so under any mismatched declaration the
/// SR-witnessed routes (aux-free WLOG chains, orbitope staircase) skip cleanly
/// to plain CDCL — the same shape as the LRAT/clause-trace clamps. HHW and the
/// other witness-free routes emit plain RUP/RAT and are NOT gated by this.
pub(crate) fn declared_checker_accepts_sr_witnesses(veripb_surface: bool) -> bool {
    let checker = ay_core::declared_proof_checker();
    checker.accepts_sr_witnesses() && checker.reads_veripb() == veripb_surface
}

pub(crate) fn transform_allowed(mode: ProofMode, transform: ProofTransform) -> bool {
    // Substitution-family DRAT knob (campaign #15). The registry now ships
    // BOTH Decompose { drat: true } (2026-07-09) and Congruence { drat: true }
    // (2026-07-10, wf_ff5991a1 — see the registry entries), so this knob is
    // purely the kill-switch for those unlocks. DRAT-only in both directions —
    // LRAT is never touched, so the official LRAT submission route is
    // unaffected.
    //
    //   unset (default)     -> registry truth: Decompose AND Congruence open
    //                          on DRAT.
    //   --sat-no-drat-subst  -> kill-switch: force-clamp BOTH Decompose and
    //                          Congruence on DRAT (pre-2026-07-09 behavior).
    //   --sat-no-drat-subst=1  -> now redundant with the registry (kept for
    //                          probe-script compatibility; it was the
    //                          congruence escape hatch before 2026-07-10).
    if matches!(mode, ProofMode::Drat)
        && matches!(
            transform,
            ProofTransform::Decompose | ProofTransform::Congruence
        )
        && ay_core::sat_ab_switches().no_drat_subst
    {
        return false;
    }
    PROOF_CAPABILITY_REGISTRY
        .iter()
        .find(|capability| capability.transform == transform)
        .map(|capability| capability.allows(mode))
        .unwrap_or_else(|| panic!("missing proof capability for {transform:?}"))
}

pub(crate) fn apply_profile_permissions(profile: &mut InprocessingFeatureProfile, mode: ProofMode) {
    if !transform_allowed(mode, ProofTransform::Vivify) {
        profile.vivify = false;
    }
    if !transform_allowed(mode, ProofTransform::Subsume) {
        profile.subsume = false;
    }
    if !transform_allowed(mode, ProofTransform::Probe) {
        profile.probe = false;
    }
    if !transform_allowed(mode, ProofTransform::Bve) {
        profile.bve = false;
    }
    if !transform_allowed(mode, ProofTransform::Bce) {
        profile.bce = false;
    }
    if !transform_allowed(mode, ProofTransform::Condition) {
        profile.condition = false;
    }
    if !transform_allowed(mode, ProofTransform::Decompose) {
        profile.decompose = false;
    }
    if !transform_allowed(mode, ProofTransform::Factor) {
        profile.factor = false;
    }
    if !transform_allowed(mode, ProofTransform::Sbva) {
        profile.sbva = false;
    }
    if !transform_allowed(mode, ProofTransform::Transred) {
        profile.transred = false;
    }
    if !transform_allowed(mode, ProofTransform::Htr) {
        profile.htr = false;
    }
    if !transform_allowed(mode, ProofTransform::Gate) {
        profile.gate = false;
    }
    if !transform_allowed(mode, ProofTransform::Congruence) {
        profile.congruence = false;
    }
    if !transform_allowed(mode, ProofTransform::Sweep) {
        profile.sweep = false;
    }
    if !transform_allowed(mode, ProofTransform::Backbone) {
        profile.backbone = false;
    }
    if !transform_allowed(mode, ProofTransform::Reorder) {
        profile.reorder = false;
    }
    if !transform_allowed(mode, ProofTransform::Cce) {
        profile.cce = false;
    }
    if !transform_allowed(mode, ProofTransform::Symmetry) {
        profile.symmetry = false;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_registry_lrat_current_transform_permissions() {
        assert!(!transform_allowed(ProofMode::Lrat, ProofTransform::Bve));
        assert!(!transform_allowed(
            ProofMode::Lrat,
            ProofTransform::Decompose
        ));
        assert!(!transform_allowed(ProofMode::Lrat, ProofTransform::Factor));
        assert!(!transform_allowed(ProofMode::Lrat, ProofTransform::Sbva));
        assert!(!transform_allowed(
            ProofMode::Lrat,
            ProofTransform::Congruence
        ));
        assert!(!transform_allowed(ProofMode::Lrat, ProofTransform::Sweep));
        assert!(!transform_allowed(
            ProofMode::Lrat,
            ProofTransform::Symmetry
        ));
        assert!(transform_allowed(ProofMode::Lrat, ProofTransform::Vivify));
    }

    #[test]
    fn test_registry_drat_current_transform_permissions() {
        // Decompose DRAT unclamped 2026-07-09 (external dpr-trim + cake_lpr
        // verification; braun reconstruction root cause fixed by ef818369).
        assert!(transform_allowed(
            ProofMode::Drat,
            ProofTransform::Decompose
        ));
        // Congruence DRAT unclamped 2026-07-10 (wf_ff5991a1: complementary-
        // edge and vivify-husk fixes; external dpr-trim + cake_lpr
        // verification 4/4 with the fixes + prior 6/6; finalize audits green).
        assert!(transform_allowed(
            ProofMode::Drat,
            ProofTransform::Congruence
        ));
        assert!(transform_allowed(ProofMode::Drat, ProofTransform::Factor));
        assert!(transform_allowed(ProofMode::Drat, ProofTransform::Sbva));
        assert!(!transform_allowed(ProofMode::Drat, ProofTransform::Sweep));
        assert!(!transform_allowed(
            ProofMode::Drat,
            ProofTransform::Symmetry
        ));
    }
}
