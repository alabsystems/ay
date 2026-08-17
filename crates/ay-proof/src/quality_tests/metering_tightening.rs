// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The two structural charge classes are TIGHTENINGS, not exemptions.
//!
//! `SemanticChargeClass::BoundedAssignmentEval` and
//! `SemanticChargeClass::UnorderedClauseMatch` replace the `General`
//! `unfolded_work^2` product for two validators that provably do not perform a
//! quadratic recursive walk. The property that makes them safe to ship is that
//! neither ever charges MORE than `General` did for the same payload:
//!
//!  * no proof that fits the caller's envelope today can stop fitting it, and
//!  * every refusal is still an a-priori RESERVATION taken before the validator
//!    runs, so a step too large to complete is still declined without doing its
//!    work — the fast-fail the previous attempt at this fix gave away by
//!    charging such steps `(0, 0)` and letting them run to the envelope.
//!
//! These tests pin both halves: monotone-vs-`General` over a wide payload
//! sweep, and the exact saturating shape above/below the environment width.

use super::*;

fn bool_tautology_step() -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "Bool".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::BoolTautology,
        lia: None,
    }
}

fn or_step(clause_len: usize) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::Or,
        clause: vec![TermId(0); clause_len],
        premises: vec![ProofId(0)],
        args: Vec::new(),
    }
}

fn payload(work: usize, unfolded: usize) -> PayloadStats {
    PayloadStats {
        work,
        bytes: 64,
        unfolded_work: unfolded,
        order_assignments: 0,
    }
}

/// The charge main took for these steps BEFORE the tightening classes existed:
/// the `General` recursive-tree product, scaled by the private per-kind factor
/// (`1 << 8` for the bounded-evaluation family, none for `AletheRule::Or`).
///
/// Spelled out here rather than routed through `SemanticChargeClass::General`,
/// because the production `General` path no longer sees these two step shapes
/// at all — the comparison has to be against the historical formula, which is
/// the thing a regression would be measured from.
fn legacy_charge(stats: PayloadStats, scale: usize) -> usize {
    let named = stats.work * stats.unfolded_work;
    let paired = stats.unfolded_work * stats.unfolded_work;
    named.max(paired) * scale
}

#[test]
fn bounded_assignment_eval_never_charges_more_than_the_general_product() {
    let step = bool_tautology_step();
    let mut strictly_cheaper = 0_usize;
    // 1_169 = sqrt(350M / 256) is THIS class's real legacy cliff (the
    // 1 << 8 scale); 18_708 = sqrt(350M) is the unscaled classes'. Sweep both.
    for unfolded in [
        1, 2, 4, 8, 9, 10, 16, 64, 733, 819, 1_169, 4_096, 18_708, 100_000,
    ] {
        for work in [1, unfolded / 2 + 1, unfolded] {
            let stats = payload(work, unfolded);
            let tight =
                semantic_validator_charge(&step, stats, SemanticChargeClass::BoundedAssignmentEval)
                    .expect("the sweep stays far below usize overflow")
                    .0;
            let legacy = legacy_charge(stats, BOUNDED_EVAL_ASSIGNMENTS);
            assert!(
                tight <= legacy,
                "tightening must never charge more: unfolded={unfolded} work={work} \
                 tight={tight} legacy={legacy}"
            );
            if tight < legacy {
                strictly_cheaper += 1;
            }
        }
    }
    assert!(
        strictly_cheaper > 0,
        "the class must actually be cheaper somewhere, else it is a no-op"
    );
}

/// Below the environment width the charge is the SAME quadratic the `General`
/// product computes; above it the second factor saturates and the charge grows
/// LINEARLY. That is the whole behavioural change: a wide packed unit stops
/// being unverifiable by construction, while a narrow one is billed exactly as
/// before.
#[test]
fn bounded_assignment_eval_saturates_at_the_environment_width() {
    let step = bool_tautology_step();
    let charge = |unfolded: usize| {
        semantic_validator_charge(
            &step,
            payload(1, unfolded),
            SemanticChargeClass::BoundedAssignmentEval,
        )
        .expect("small payloads fit usize")
        .0
    };
    // Narrow: identical to the product it replaces.
    for unfolded in 1..=BOUNDED_EVAL_ENV_WIDTH {
        // The modelled value is the same quadratic PLUS the linear structural
        // term; the tightening cap holds it at exactly the legacy product.
        let expected = BOUNDED_EVAL_ASSIGNMENTS * unfolded * unfolded;
        assert_eq!(charge(unfolded), expected, "narrow unfolded={unfolded}");
    }
    // Wide: linear in the payload, at the saturated factor.
    for unfolded in [BOUNDED_EVAL_ENV_WIDTH + 1, 1_000, 100_000] {
        let expected = BOUNDED_EVAL_ASSIGNMENTS * unfolded * BOUNDED_EVAL_ENV_WIDTH + 1 + unfolded;
        assert_eq!(charge(unfolded), expected, "wide unfolded={unfolded}");
    }
    // Doubling the payload doubles the charge once saturated (it QUADRUPLED
    // under the product, which is what made large units unreachable).
    assert_eq!(charge(200_000) - 200_001, 2 * (charge(100_000) - 100_001));
}

/// The reproducer's binding step.
///
/// the development design notes
/// is declined by a SINGLE charge of at least 137,479,682 against a 350,000,000
/// envelope — 39% of the whole budget for one lemma — measured with
/// `AY_PROBE_STRICT_CHECK=1`. That charge is `1 << 8` times a ~733-node
/// unfolded payload squared. At the same payload the tightened class bills
/// under two million, which is why the obligation now certifies.
///
/// Two numbers appear in the record and they are NOT interchangeable:
/// 137,479,682 is what THIS modelled `payload(733, 733)` reproduces (the
/// assertion below is a lower bound on it — the model actually computes
/// 137,545,984), while a review control run of the real reproducer file on the
/// merged tree measured 142,871,042 for its own, larger payload. Substituting
/// the latter here fails the assertion, because the model cannot reach it.
#[test]
fn the_reproducers_binding_lemma_no_longer_eats_the_envelope() {
    const MEASURED_DECLINE: usize = 137_479_682;
    let step = bool_tautology_step();
    let stats = payload(733, 733);
    let legacy = legacy_charge(stats, BOUNDED_EVAL_ASSIGNMENTS);
    let tight = semantic_validator_charge(&step, stats, SemanticChargeClass::BoundedAssignmentEval)
        .expect("small payloads fit usize")
        .0;
    assert!(
        legacy >= MEASURED_DECLINE,
        "the modelled payload must reproduce the measured decline: {legacy}"
    );
    assert!(
        tight < MEASURED_DECLINE / 50,
        "the binding lemma must drop by more than 50x: legacy={legacy} tight={tight}"
    );
}

#[test]
fn unordered_clause_match_charges_the_clause_not_the_term_dag() {
    for clause_len in [1_usize, 2, 8, 64] {
        let step = or_step(clause_len);
        for unfolded in [clause_len, clause_len * 16, clause_len * 4_096] {
            let stats = payload(clause_len, unfolded);
            let tight =
                semantic_validator_charge(&step, stats, SemanticChargeClass::UnorderedClauseMatch)
                    .expect("small payloads fit usize")
                    .0;
            let legacy = legacy_charge(stats, 1);
            assert!(
                tight <= legacy,
                "tightening must never charge more: clause_len={clause_len} \
                 unfolded={unfolded} tight={tight} legacy={legacy}"
            );
            // The charge tracks the CLAUSE, so a deeper term DAG under the same
            // clause does not change it (until the legacy cap binds, which it
            // only can when the DAG is no larger than the clause).
            let modelled = clause_len * clause_len + clause_len;
            assert_eq!(tight, modelled.min(legacy));
        }
    }
}

/// A step whose payload is genuinely enormous is still REFUSED up front. The
/// charge grows without bound in the payload, so admission stays an a-priori
/// reservation rather than "run it and see".
#[test]
fn a_huge_bounded_eval_payload_still_exceeds_a_production_sized_envelope() {
    const PRODUCTION_ENVELOPE: usize = 350_000_000;
    let step = bool_tautology_step();
    let huge = payload(200_000_000, 200_000_000);
    let tight = semantic_validator_charge(&step, huge, SemanticChargeClass::BoundedAssignmentEval)
        .expect("the product still fits usize on a 64-bit target")
        .0;
    assert!(
        tight > PRODUCTION_ENVELOPE,
        "an unreachable payload must still be declined before the validator runs: {tight}"
    );
}
