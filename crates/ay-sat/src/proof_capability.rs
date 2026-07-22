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
    // Kill-switch: AY_AB_DRAT_SUBST=0 restores the pre-unlock DRAT clamp (see
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
    // finalize_sat_fail audits green under AY_AB_CONGRUENCE=1 +
    // AY_AB_DRAT_SUBST=1 with debug asserts armed, and congruence-fired SAT
    // models validated externally against the original CNF (zero violations).
    // LRAT stays fail-closed until congruence LRAT hints are checked.
    // Kill-switch: AY_AB_DRAT_SUBST=0 restores the DRAT clamp (see
    // `transform_allowed`). The feature itself remains OPT-IN on the Default
    // DIMACS route (0 measured flips — see variant.rs).
    ProofCapability::new(ProofTransform::Congruence, true, false),
    ProofCapability::new(ProofTransform::Sweep, false, false),
    ProofCapability::new(ProofTransform::Cce, true, true),
    ProofCapability::new(ProofTransform::Reorder, true, true),
    ProofCapability::new(ProofTransform::Symmetry, false, false),
];

/// The single soundness chokepoint for unclamping symmetry breaking under a
/// proof: symmetry SBP lex clauses are PR (propagation-redundant), NOT RAT, so
/// the registry keeps [`ProofTransform::Symmetry`] clamped for plain DRAT/LRAT
/// (RUP/RAT) proofs. This predicate is the ONLY place that may re-enable it, and
/// only when BOTH hold:
///   1. a DPR (PR) proof is actually being emitted for the SBP lex clauses (the
///      σ-image witness `a`-lines, see `symmetry::detector` and `proof::drat::add_pr`),
///      and
///   2. that DPR proof is verified by the external trust anchor (cake_lpr).
///
/// This is now ENABLED for the DRAT route only (#8011 step 5): the symmetry
/// preprocessor emits the aux-free `j=0` per-generator lex-leader binaries as DPR
/// `a`-lines carrying the σ-image witness (see
/// `solver::proof_emit::proof_emit_add_pr` and `symmetry::detector`). Those DPR
/// proofs are NOT verified by AY's internal RUP/RAT checker — they are elaborated
/// by the vendored `dpr-trim` (DPR→LPR) and verified by the external trust anchor
/// `cake_lpr`. A wrong PR accept is a false UNSAT (disqualification), so the
/// soundness guarantee rests on that external check, never on AY's emission.
///
/// The aux tower (`j>0` clauses + equal-prefix Tseitin definitions) is NOT
/// single-σ-PR, so the emitter DROPS it: only the binary `j=0` clauses are added
/// and proved. The LRAT/LPR direct route is not wired, so this stays `false` for
/// LRAT — that submission path is unaffected and remains fully RUP/RAT-checkable.
pub(crate) fn symmetry_pr_proof_allowed(mode: ProofMode) -> bool {
    // PR/DPR is a DRAT-family extension; the LRAT (LPR) route is not wired yet.
    matches!(mode, ProofMode::Drat)
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
    //   AY_AB_DRAT_SUBST=0  -> kill-switch: force-clamp BOTH Decompose and
    //                          Congruence on DRAT (pre-2026-07-09 behavior).
    //   AY_AB_DRAT_SUBST=1  -> now redundant with the registry (kept for
    //                          probe-script compatibility; it was the
    //                          congruence escape hatch before 2026-07-10).
    if matches!(mode, ProofMode::Drat)
        && matches!(
            transform,
            ProofTransform::Decompose | ProofTransform::Congruence
        )
    {
        match std::env::var("AY_AB_DRAT_SUBST").ok().as_deref() {
            Some("0") => return false,
            Some(_) => return true,
            None => {}
        }
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
