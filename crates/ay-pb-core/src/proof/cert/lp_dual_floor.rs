// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact LP-dual OPT-LIN certificates.
//!
//! The LP solver complements variables with negative objective coefficients and
//! returns duals for normalized constraint rows followed by one box row per
//! variable. This module maps that dual back to the original variables, combines
//! the original VeriPB `f` rows and literal axioms with non-negative multipliers,
//! and adds the incumbent's `soli` row to the derived objective floor.
//!
//! Rational duals are cleared with one bounded common denominator `k`. The proof
//! is built at scale `k` and closed by VeriPB's Chvatal-Gomory division, deriving
//! `objective >= ceil(LP*)`; this is what lets a half-integral dual certify an
//! integer optimum above the fractional LP value.
//!
//! Every shape, sign, conversion, and arithmetic check declines through `None`.
//! The returned bytes are proof text only and remain untrusted until the external
//! VeriPB verify-before-claim gate accepts them.

mod arithmetic;

use num_bigint::BigInt;

use self::arithmetic::{
    common_dual_scale, denominator_profile, linear_rows, objective_coefficients, prepare_plan,
    DualPlan, MAX_DUAL_SCALE,
};
use super::{evaluate_linear_objective, format_assignment};
use crate::optimize::lp_bound::LpDualRaw;
use crate::proof::steps::{ConstraintId, ProofStep};
use crate::proof::veripb::{veripb_input_constraint_count, VeriPbWriter};
use crate::types::PbInstance;

enum AxiomKind {
    /// Box dual: `x >= 0` when complemented, `~x >= 0` otherwise.
    Box,
    /// Opposite axiom used to lift the aggregate to the objective coefficient.
    Lift,
}

fn emit_row_aggregate(
    writer: &mut VeriPbWriter<Vec<u8>>,
    multipliers: &[i128],
) -> Option<ConstraintId> {
    // `linear_rows` preserves VeriPB input order, so normalized row index `r`
    // is exactly input constraint id `r + 1` here.
    let mut terms = multipliers
        .iter()
        .enumerate()
        .filter(|(_, multiplier)| **multiplier != 0);
    let (first_row, &first_multiplier) = terms.next()?;
    let first_id = u64::try_from(first_row.checked_add(1)?).ok()?;
    let mut expression = if first_multiplier == 1 {
        first_id.to_string()
    } else {
        format!("{first_id} {first_multiplier} *")
    };
    for (row, &multiplier) in terms {
        let id = u64::try_from(row.checked_add(1)?).ok()?;
        if multiplier == 1 {
            expression.push_str(&format!(" {id} +"));
        } else {
            expression.push_str(&format!(" {id} {multiplier} * +"));
        }
    }
    expression.push_str(" ;");
    writer.log_step(ProofStep::Polynomial(expression)).ok()
}

fn emit_axioms(
    writer: &mut VeriPbWriter<Vec<u8>>,
    mut current: ConstraintId,
    multipliers: &[i128],
    complement: &[bool],
    kind: AxiomKind,
) -> Option<ConstraintId> {
    for (index, (&multiplier, &is_complemented)) in multipliers.iter().zip(complement).enumerate() {
        if multiplier == 0 {
            continue;
        }
        let variable = index.checked_add(1)?;
        let literal = match (&kind, is_complemented) {
            (AxiomKind::Box, true) | (AxiomKind::Lift, false) => "x",
            (AxiomKind::Box, false) | (AxiomKind::Lift, true) => "~x",
        };
        let expression = if multiplier == 1 {
            format!("{current} {literal}{variable} + ;")
        } else {
            format!("{current} {literal}{variable} {multiplier} * + ;")
        };
        current = writer.log_step(ProofStep::Polynomial(expression)).ok()?;
    }
    Some(current)
}

fn emit_proof(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    plan: &DualPlan,
) -> Option<String> {
    // `soli` both proves the upper bound and installs its objective-improving row.
    // The reconstructed floor below contradicts that row, giving equal bounds.
    let input_count = veripb_input_constraint_count(instance).ok()?;
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), input_count).ok()?;
    let solution_id = writer
        .log_step(ProofStep::SolutionImproving(format_assignment(incumbent)))
        .ok()?;
    let aggregate = emit_row_aggregate(&mut writer, &plan.row_multipliers)?;
    let with_boxes = emit_axioms(
        &mut writer,
        aggregate,
        &plan.box_multipliers,
        &plan.complement,
        AxiomKind::Box,
    )?;
    let mut floor = emit_axioms(
        &mut writer,
        with_boxes,
        &plan.lifts,
        &plan.complement,
        AxiomKind::Lift,
    )?;
    if plan.scale >= 2 {
        // Integral duals need no division. Rational duals close with the one native
        // CG division licensed by their common denominator.
        floor = writer.log_step(ProofStep::Divide(floor, plan.scale)).ok()?;
    }
    let contradiction = writer
        .log_step(ProofStep::Addition(floor, solution_id))
        .ok()?;
    writer.set_opt_bounds(optimum, optimum).ok()?;
    writer
        .conclude_opt_hinted(Some(contradiction), Some(&format_assignment(incumbent)))
        .ok()?;
    String::from_utf8(writer.into_inner()).ok()
}

/// Implements the public contract in [`super::certify_opt_lin_lp_dual_floor`].
///
/// There is intentionally no objective-sign gate: maximization and mixed-sign
/// objectives are valid when the exact LP floor is tight. The fixed one-minute
/// simplex slice bounds certificate work; timeout declines without affecting the
/// underlying optimum verdict.
pub(super) fn certify_opt_lin_lp_dual_floor(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
) -> Option<String> {
    let objective = instance.objective.as_ref()?;
    let objective_coefficients = objective_coefficients(objective).ok()?;
    let num_vars = instance.num_vars as usize;
    if incumbent.len() != num_vars
        || evaluate_linear_objective(objective, incumbent)? != optimum
        || !crate::eval::verify_all_constraints(&instance.constraints, incumbent)
    {
        return None;
    }
    let rows = linear_rows(&instance.constraints).ok()?;
    let deadline = std::time::Instant::now() + std::time::Duration::from_mins(1);
    // The claimed optimum is threaded as the dual solve's TARGET and the
    // emitter's denominator cap as its scale budget. Both are quality inputs
    // only: a wrong target or an unusable scale can make the solve stop early or
    // hand back a different dual-feasible point, and the reconstruction below
    // still re-derives every coefficient and refuses anything that does not land
    // exactly on `optimum`.
    let raw = crate::optimize::lp_bound::lp_dual_raw_diagnosed(
        objective,
        &instance.constraints,
        instance.num_vars,
        Some(optimum),
        Some(MAX_DUAL_SCALE),
        &|| std::time::Instant::now() >= deadline,
    )
    .ok()?;
    if raw.bound != optimum {
        return None;
    }
    let scale = common_dual_scale(&raw.duals)?;
    if scale.capped {
        return None;
    }
    let plan = prepare_plan(
        &objective_coefficients,
        &rows,
        num_vars,
        &raw,
        &scale.value,
        optimum,
    )
    .ok()?;
    emit_proof(instance, incumbent, optimum, &plan)
}

/// Reports why [`certify_opt_lin_lp_dual_floor`] did or did not fire.
///
/// This measurement-only path re-runs the exact dual solve and distinguishes
/// an LP integrality gap from a tight relaxation lost to reconstruction or the
/// denominator cap. It is never called by the production certificate chain.
pub(super) fn lp_dual_floor_diagnosis(instance: &PbInstance, optimum: i128) -> String {
    let Some(objective) = instance.objective.as_ref() else {
        return "no-objective".to_string();
    };
    for term in &objective.terms {
        match term.lits.as_slice() {
            [literal] if !literal.negated && literal.var != 0 => {}
            _ => return "shape:objective-not-plain-positive-literals".to_string(),
        }
    }
    if instance
        .constraints
        .iter()
        .any(|constraint| constraint.terms.iter().any(|term| term.lits.len() != 1))
    {
        return "shape:nonlinear-row".to_string();
    }
    let deadline = std::time::Instant::now() + std::time::Duration::from_mins(1);
    // No target and no scale budget: the census wants the truth about the
    // RELAXATION (`ceil(LP*)` when the solve converges), not the shortest route
    // to the claimed optimum.
    let raw = match crate::optimize::lp_bound::lp_dual_raw_diagnosed(
        objective,
        &instance.constraints,
        instance.num_vars,
        None,
        None,
        &|| std::time::Instant::now() >= deadline,
    ) {
        Ok(raw) => raw,
        Err(decline) => return format!("lp:dual-solve-declined({})", decline.label()),
    };
    let Some(scale) = common_dual_scale(&raw.duals) else {
        return "lp:invalid-dual-scale".to_string();
    };
    let verdict = dual_floor_verdict(raw.bound, raw.converged, optimum, scale.capped);
    let why = if verdict == "REACHABLE:lp-tight" {
        certify_opt_lin_lp_dual_floor_declined_reason(instance, &raw, &scale.value, optimum)
            .map(|reason| format!(" declined={reason}"))
            .unwrap_or_default()
    } else {
        String::new()
    };
    let displayed_scale = if scale.capped {
        format!(">cap({})", denominator_profile(&raw.duals))
    } else {
        scale.value.to_string()
    };
    // Name the number for what it actually is. Only a converged solve produces
    // `ceil(LP*)`; otherwise this is just some valid floor at or below it, and
    // calling it `ceil_lp` is what made the shortfall look like a property of the
    // relaxation.
    let floor_label = if raw.converged { "ceil_lp" } else { "floor" };
    format!(
        "{verdict} {floor_label}={} opt={optimum} scale={displayed_scale} tier={}{why}",
        raw.bound, raw.tier
    )
}

/// Classifies a dual floor against a claimed optimum.
///
/// Split out from [`lp_dual_floor_diagnosis`] so the one judgement that can be
/// WRONG WITHOUT BEING VISIBLY WRONG — calling a shortfall an integrality gap —
/// is testable without needing to drive a real simplex into a timeout.
fn dual_floor_verdict(
    floor: i128,
    converged: bool,
    optimum: i128,
    scale_capped: bool,
) -> &'static str {
    match (floor.cmp(&optimum), converged) {
        // A converged solve puts `floor` exactly at `ceil(LP*)`, so a shortfall
        // is a relaxation gap no non-negative multiplier can close. This is the
        // only branch entitled to say `UNREACHABLE` about a shortfall.
        (std::cmp::Ordering::Less, true) => "UNREACHABLE:lp-floor-below-optimum(integrality gap)",
        // An unconverged solve stopped at an arbitrary dual-feasible point below
        // `ceil(LP*)` (deadline, pivot cap, degenerate stall). The shortfall is a
        // fact about the SOLVE, not about the relaxation, and must not be
        // reported as an obstruction.
        (std::cmp::Ordering::Less, false) => {
            "INCONCLUSIVE:dual-solve-did-not-converge(floor is a valid lower bound on ceil(LP*), not ceil(LP*))"
        }
        // Any dual-feasible point yields a floor <= the true optimum, so a floor
        // ABOVE it impeaches the claimed optimum whether or not we converged.
        (std::cmp::Ordering::Greater, _) => "UNREACHABLE:lp-floor-above-optimum(bad incumbent?)",
        (std::cmp::Ordering::Equal, _) if scale_capped => "LOST:denominator-exceeds-MAX_DUAL_SCALE",
        (std::cmp::Ordering::Equal, _) => "REACHABLE:lp-tight",
    }
}

#[cfg(test)]
mod tests {
    use super::arithmetic::MAX_DUAL_SCALE;
    use super::dual_floor_verdict;
    use crate::optimize::lp_bound::DUAL_DENOMINATOR_LADDER;

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
}

/// Names the first arithmetic guard that would decline the LP-dual emitter.
fn certify_opt_lin_lp_dual_floor_declined_reason(
    instance: &PbInstance,
    raw: &LpDualRaw,
    scale: &BigInt,
    optimum: i128,
) -> Option<String> {
    let objective = objective_coefficients(instance.objective.as_ref()?).ok()?;
    let rows = linear_rows(&instance.constraints).ok()?;
    prepare_plan(
        &objective,
        &rows,
        instance.num_vars as usize,
        raw,
        scale,
        optimum,
    )
    .err()?
    .diagnosis(optimum)
}
