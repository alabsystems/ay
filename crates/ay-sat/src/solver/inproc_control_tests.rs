// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_default_controls_match_current_behavior() {
    let ctrl = InprocessingControls::new();

    // Enabled by default
    assert!(ctrl.vivify.enabled);
    assert!(ctrl.vivify_irred.enabled);
    assert!(ctrl.subsume.enabled);
    assert!(ctrl.probe.enabled);
    assert!(ctrl.backbone.enabled);
    // Disabled by default (CaDiCaL block=0, condition=0; #8080)
    assert!(!ctrl.bce.enabled);
    assert!(!ctrl.condition.enabled);
    assert!(ctrl.transred.enabled);
    assert!(ctrl.htr.enabled);
    assert!(ctrl.gate.enabled);
    assert!(
        !ctrl.congruence.enabled,
        "congruence is opt-in until equivalence reconstruction is safe by default"
    );

    // Disabled by default (BVE unsafe for DPLL(T))
    assert!(!ctrl.bve.enabled);
    // Disabled by default (CaDiCaL cover=0; #8190)
    assert!(!ctrl.cce.enabled);
    // Enabled by default (#7037: re-enabled with clause rewriting)
    assert!(ctrl.sweep.enabled);
    // Decompose is opt-in until final model reconstruction is safe by default.
    assert!(!ctrl.decompose.enabled);
    assert!(ctrl.factor.enabled);
    assert!(ctrl.sbva.enabled);
}

#[test]
fn test_drat_overrides_clamp_proof_incomplete_transforms() {
    let ctrl = InprocessingControls::new().with_proof_overrides(false);

    assert!(ctrl.vivify.enabled);
    assert!(ctrl.vivify_irred.enabled);
    assert!(ctrl.subsume.enabled);
    assert!(ctrl.probe.enabled);
    assert!(!ctrl.bve.enabled); // disabled by default, not by DRAT
    assert!(!ctrl.cce.enabled); // disabled by default (CaDiCaL cover=0; #8190)
    assert!(!ctrl.bce.enabled); // disabled by default (#8080), not by DRAT
    assert!(!ctrl.condition.enabled); // disabled by default (#8080), not by DRAT
    assert!(ctrl.transred.enabled);
    assert!(ctrl.htr.enabled);
    assert!(
        !ctrl.congruence.enabled,
        "congruence is disabled by default feature policy (opt-in), no longer \
         by the DRAT clamp — registry Congruence drat=true since 2026-07-10 \
         (wf_ff5991a1)"
    );
    assert!(
        !ctrl.decompose.enabled,
        "decompose is disabled by default feature policy (opt-in), no longer \
         by the DRAT clamp — registry Decompose drat=true since 2026-07-09"
    );
    assert!(ctrl.factor.enabled); // DRAT divider+blocked+quotient (#4242)
    assert!(ctrl.sbva.enabled);
    assert!(!ctrl.sweep.enabled); // #8011: sweep equivalences are not RUP/RAT-derivable in DRAT mode
    assert!(ctrl.gate.enabled);
}

#[test]
fn test_lrat_overrides_disable_destructive_transforms() {
    let ctrl = InprocessingControls::new().with_proof_overrides(true);

    assert!(ctrl.vivify.enabled);
    assert!(ctrl.vivify_irred.enabled);
    assert!(ctrl.subsume.enabled);
    // BCE and condition are disabled by default (#8080), not by LRAT override.
    assert!(!ctrl.bce.enabled);
    assert!(!ctrl.condition.enabled);
    assert!(ctrl.transred.enabled);
    assert!(ctrl.htr.enabled);
    assert!(ctrl.gate.enabled);
    assert!(
        !ctrl.congruence.enabled,
        "congruence must stay disabled in LRAT until its LRAT hints are \
         checked (registry lrat=false)"
    );
    assert!(
        ctrl.probe.enabled,
        "probe: LRAT-safe with backward reconstruction (#8105)"
    );
    assert!(
        !ctrl.decompose.enabled,
        "decompose must stay disabled in LRAT until SCC LRAT IDs are checked (#8197)"
    );
    assert!(
        !ctrl.bve.enabled,
        "BVE must be disabled in official LRAT mode"
    );
    assert!(
        !ctrl.factor.enabled,
        "factor must be disabled in official LRAT mode"
    );
    assert!(
        !ctrl.sbva.enabled,
        "SBVA must be disabled in official LRAT mode"
    );
    assert!(
        !ctrl.sweep.enabled,
        "sweep: proof-capability registry disables in all proof modes (#8011)"
    );
}

#[test]
fn test_dense_factor_bve_lrat_route_does_not_reopen_controls_globally() {
    let mut ctrl = InprocessingControls::new();
    ctrl.bve.enabled = true;
    ctrl.factor.enabled = true;
    ctrl.sbva.enabled = true;
    ctrl.sweep.enabled = true;

    let ctrl = ctrl.with_proof_overrides_for_route(true, true);

    assert!(
        !ctrl.bve.enabled,
        "internal dense LRAT route must not globally reopen BVE"
    );
    assert!(
        !ctrl.factor.enabled,
        "internal dense LRAT route must not globally reopen factor"
    );
    assert!(!ctrl.sbva.enabled, "SBVA remains closed in LRAT");
    assert!(
        !ctrl.sweep.enabled,
        "proof_override techniques remain closed in LRAT"
    );
}

#[test]
fn test_default_intervals_match_constants() {
    let ctrl = InprocessingControls::new();

    assert_eq!(ctrl.vivify.next_conflict, VIVIFY_INTERVAL);
    assert_eq!(ctrl.vivify_irred.next_conflict, VIVIFY_IRRED_INTERVAL);
    assert_eq!(ctrl.subsume.next_conflict, SUBSUME_INTERVAL);
    assert_eq!(ctrl.probe.next_conflict, PROBE_INTERVAL);
    assert_eq!(ctrl.backbone.next_conflict, BACKBONE_INTERVAL);
    assert_eq!(ctrl.bve.next_conflict, 0);
    assert_eq!(ctrl.bce.next_conflict, BCE_INTERVAL);
    assert_eq!(ctrl.condition.next_conflict, CONDITION_INTERVAL);
    assert_eq!(ctrl.decompose.next_conflict, 0);
    assert_eq!(ctrl.factor.next_conflict, FACTOR_INTERVAL);
    assert_eq!(ctrl.transred.next_conflict, TRANSRED_INTERVAL);
    assert_eq!(ctrl.htr.next_conflict, HTR_INTERVAL);
    assert_eq!(ctrl.gate.next_conflict, 0);
    assert_eq!(ctrl.congruence.next_conflict, 0);
    assert_eq!(ctrl.sweep.next_conflict, SWEEP_INTERVAL);
    assert_eq!(ctrl.cce.next_conflict, CCE_INTERVAL);
}

#[test]
fn test_pass_descriptors_cover_controls() {
    let descriptors = InprocessingControls::PASS_DESCRIPTORS;

    assert_eq!(descriptors.len(), 19);
    assert!(descriptors.iter().any(|pass| {
        pass.name == "vivify"
            && pass.default_enabled
            && pass.default_interval == VIVIFY_INTERVAL
            && pass.mutability == InprocessingMutability::ClauseDatabase
            && pass.proof_support == InprocessingProofSupport::All
    }));
    assert!(descriptors.iter().any(|pass| {
        pass.name == "factor"
            && pass.proof_support == InprocessingProofSupport::DratOnly
            && pass.mutability == InprocessingMutability::ExtensionVariables
            && !pass.incremental_safe
    }));
    assert!(descriptors.iter().any(|pass| {
        pass.name == "sweep"
            && pass.proof_support == InprocessingProofSupport::None
            && pass.state_effect == "sat-sweep-equivalences"
    }));
    assert!(descriptors.iter().any(|pass| {
        pass.name == "decompose"
            && pass.proof_support == InprocessingProofSupport::DratOnly
            && pass.state_effect == "substitute-components"
    }));
    assert!(descriptors.iter().any(|pass| {
        pass.name == "congruence"
            && pass.proof_support == InprocessingProofSupport::DratOnly
            && pass.state_effect == "rewrite-equivalences"
    }));
}

#[test]
fn test_compatibility_policy_matches_default_controls() {
    let ctrl = InprocessingControls::new();
    let ledger = ctrl.compatibility_policy_ledger(InprocessingPolicyMode::Search);

    assert_eq!(ledger.len(), InprocessingControls::PASS_DESCRIPTORS.len());
    for entry in ledger {
        let expected_enabled = !matches!(
            entry.pass.name,
            "bve" | "bce" | "condition" | "cce" | "congruence" | "decompose"
        );
        let expected_decision = if expected_enabled {
            InprocessingPolicyDecision::Run
        } else {
            InprocessingPolicyDecision::Disable
        };
        assert_eq!(entry.decision, expected_decision, "{}", entry.pass.name);
    }
}

#[test]
fn test_compatibility_policy_enforces_proof_support_without_mutating_controls() {
    let ctrl = InprocessingControls::new();

    let drat_ledger = ctrl.compatibility_policy_ledger(InprocessingPolicyMode::DratProof);
    assert_eq!(
        decision_for(&drat_ledger, "factor"),
        InprocessingPolicyDecision::Run
    );
    assert_eq!(
        decision_for(&drat_ledger, "decompose"),
        InprocessingPolicyDecision::Disable
    );
    assert_eq!(
        reason_for(&drat_ledger, "decompose"),
        InprocessingPolicyReason::DisabledByFeature
    );
    assert_eq!(
        decision_for(&drat_ledger, "congruence"),
        InprocessingPolicyDecision::Disable
    );
    assert_eq!(
        reason_for(&drat_ledger, "congruence"),
        InprocessingPolicyReason::DisabledByFeature
    );
    assert_eq!(
        decision_for(&drat_ledger, "sweep"),
        InprocessingPolicyDecision::Disable
    );
    assert_eq!(
        reason_for(&drat_ledger, "sweep"),
        InprocessingPolicyReason::DisabledByProofMode
    );

    let lrat_ledger = ctrl.compatibility_policy_ledger(InprocessingPolicyMode::LratProof);
    assert_eq!(
        decision_for(&lrat_ledger, "factor"),
        InprocessingPolicyDecision::Disable
    );
    assert_eq!(
        reason_for(&lrat_ledger, "factor"),
        InprocessingPolicyReason::DisabledByProofMode
    );
    assert_eq!(
        decision_for(&lrat_ledger, "sbva"),
        InprocessingPolicyDecision::Disable
    );
}

fn decision_for(ledger: &[InprocessingLedgerEntry], name: &str) -> InprocessingPolicyDecision {
    ledger
        .iter()
        .find(|entry| entry.pass.name == name)
        .unwrap_or_else(|| panic!("missing ledger entry for {name}"))
        .decision
}

fn reason_for(ledger: &[InprocessingLedgerEntry], name: &str) -> InprocessingPolicyReason {
    ledger
        .iter()
        .find(|entry| entry.pass.name == name)
        .unwrap_or_else(|| panic!("missing ledger entry for {name}"))
        .reason
}

#[test]
fn test_should_fire_logic() {
    let tc = TechniqueControl::new(true, 100);
    assert!(!tc.should_fire(99));
    assert!(tc.should_fire(100));
    assert!(tc.should_fire(200));

    let disabled = TechniqueControl::new(false, 0);
    assert!(!disabled.should_fire(0));
    assert!(!disabled.should_fire(1000));
}

#[test]
fn test_reschedule() {
    let mut tc = TechniqueControl::new(true, 0);
    assert!(tc.should_fire(0));

    tc.reschedule(500, 100);
    assert_eq!(tc.next_conflict, 600);
    assert!(!tc.should_fire(599));
    assert!(tc.should_fire(600));
}

#[test]
fn test_reschedule_growing() {
    let mut tc = TechniqueControl::new(true, 5000);
    // First fire at conflict 5000
    assert!(tc.should_fire(5000));

    // 1.5x growth: 5000 → 7500 → 11250 → 16875
    let interval = tc.reschedule_growing(5000, 5000, 3, 2, 80_000);
    assert_eq!(interval, 7500);
    assert_eq!(tc.next_conflict, 12_500);

    let interval = tc.reschedule_growing(12_500, 5000, 3, 2, 80_000);
    assert_eq!(interval, 11_250);
    assert_eq!(tc.next_conflict, 23_750);

    let interval = tc.reschedule_growing(23_750, 5000, 3, 2, 80_000);
    assert_eq!(interval, 16_875);

    // Verify capping at max_interval
    let mut tc2 = TechniqueControl::new(true, 50_000);
    tc2.interval_used = 60_000;
    let interval = tc2.reschedule_growing(100_000, 5000, 3, 2, 80_000);
    assert_eq!(interval, 80_000); // capped at max
}

#[test]
fn test_reset_interval() {
    let mut tc = TechniqueControl::new(true, 5000);
    tc.interval_used = 40_000;
    tc.next_conflict = 100_000;

    tc.reset_interval(5000);
    assert_eq!(tc.next_conflict, 5000);
    assert_eq!(tc.interval_used, 5000);
}
