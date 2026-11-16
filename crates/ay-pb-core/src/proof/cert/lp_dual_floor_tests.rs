// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::arithmetic::MAX_DUAL_SCALE;
use super::dual_floor_verdict;
use crate::optimize::lp_bound::DUAL_DENOMINATOR_LADDER;
use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm};

/// End-to-end over the EQUALITY-SPAN lane: a mixed-sign objective pinned
/// to a constant by one `=` row (the `mult_diagcomm` shape in miniature)
/// must certify `BOUNDS 0 <= obj <= 0` with the objective expressed as an
/// exact combination of the equality's two split halves — no simplex tier
/// in the loop.
#[test]
fn equality_span_instance_certifies_end_to_end() {
    let term = |coeff: i128, var: u32| PbTerm {
        coeff,
        lits: vec![PbLit {
            var,
            negated: false,
        }],
    };
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![PbConstraint {
            terms: vec![term(1, 1), term(-1, 2)],
            rel: PbRel::Eq,
            rhs: 0,
        }],
        objective: Some(PbObjective {
            terms: vec![term(1, 1), term(-1, 2)],
        }),
    };
    let proof = super::certify_opt_lin_lp_dual_floor(&instance, &[false, false], 0)
        .expect("the equality-span certificate must emit");
    assert!(
        proof.contains("conclusion BOUNDS 0 :"),
        "equal bounds at the optimum, got:\n{proof}"
    );
}

/// The reduction ladder lives in the LP module and the cap that refuses its
/// output lives here. A rung past the cap would build a plan this emitter is
/// guaranteed to refuse — wasted work that looks like an unreachable model.
#[test]
fn every_denominator_rung_is_within_the_emitters_cap() {
    assert!(
        DUAL_DENOMINATOR_LADDER
            .iter()
            .all(|&rung| rung <= MAX_DUAL_SCALE),
        "a ladder rung exceeds MAX_DUAL_SCALE={MAX_DUAL_SCALE}: {DUAL_DENOMINATOR_LADDER:?}"
    );
}

/// The shortfall verdict must be decided by CONVERGENCE, not by the shortfall
/// alone. Before this split, both rows below printed the same definitive
/// `UNREACHABLE ... (integrality gap)`, so a dual solve that merely ran out of
/// wall clock was recorded as a mathematical obstruction.
#[test]
fn shortfall_is_only_an_integrality_gap_when_the_solve_converged() {
    assert_eq!(
        dual_floor_verdict(5785, true, 5867, false),
        "UNREACHABLE:lp-floor-below-optimum(integrality gap)"
    );
    assert!(dual_floor_verdict(5785, false, 5867, false).starts_with("INCONCLUSIVE:"));
}

/// A floor ABOVE the claimed optimum impeaches the incumbent at any dual
/// point, converged or not: weak duality bounds every dual-feasible floor by
/// the true optimum.
#[test]
fn floor_above_optimum_is_conclusive_either_way() {
    for converged in [true, false] {
        assert_eq!(
            dual_floor_verdict(9, converged, 8, false),
            "UNREACHABLE:lp-floor-above-optimum(bad incumbent?)"
        );
    }
}

/// Tight floors keep their existing two verdicts, and reaching the optimum
/// with an unconverged dual is still REACHABLE — the emitter's self-check,
/// not convergence, is what licenses the certificate.
#[test]
fn tight_floor_verdicts_are_unchanged() {
    assert_eq!(
        dual_floor_verdict(-2, true, -2, false),
        "REACHABLE:lp-tight"
    );
    assert_eq!(
        dual_floor_verdict(-2, false, -2, false),
        "REACHABLE:lp-tight"
    );
    assert_eq!(
        dual_floor_verdict(-2, true, -2, true),
        "LOST:denominator-exceeds-MAX_DUAL_SCALE"
    );
}
