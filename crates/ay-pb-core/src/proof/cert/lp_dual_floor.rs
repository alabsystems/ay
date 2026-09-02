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
    // is exactly input constraint id `r + 1` here. This `r + 1` is NOT the
    // historical row-id-shift bug and has been audited as correct (2026-08-29):
    // `linear_rows` (see `lp_dual_floor/arithmetic.rs`) already splits a
    // `PbRel::Eq` row into two consecutive rows in VeriPB's own import order,
    // so the index is post-split. Do not re-file.
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

/// Deterministic work cap for the exact dual solve, counted in `should_stop`
/// POLLS — a COUNT, never a duration, exactly as the other floor rungs' caps
/// (`odd_cycle_cover::packing::Limits`: "a clock-based cap would make the
/// emitted bytes depend on machine load"). The LP tiers poll at deterministic
/// sites only — every `TABLEAU_INIT_POLL_ROWS` rows of tableau init, once per
/// pivot, and every `PIVOT_POLL_ENTRIES` tableau entries at row granularity
/// inside a pivot (see `optimize::lp_bound`) — so a poll is a fixed-size chunk
/// of tableau work and the count at which this cap fires is identical on every
/// machine.
///
/// WHY THIS EXISTS. This rung is a FLOOR rung: it runs outside the
/// `CertRouteBudget` scheduler so that a caller whose deadline is already
/// spent (the normal case for the CLI) still gets every floor route. Its
/// previous private budget was a fresh one-minute WALL deadline taken at rung
/// entry, which is how a 5 s `--timeout` proof run spent 60+ s here: measured
/// on the 2026-08-29 definitive census, `aim-200-2_0-yes1-2`,
/// `knapPI_11_1000_1000_5` and `mult_diagcomm_..._nbits_16` each took 60-65 s
/// in proof mode at `--timeout 5000` and then FAILED to certify — the minute
/// bought nothing on exactly the instances that consumed it.
///
/// SIZING, from measurement (probe build bfe9acce, PB25 OPT-LIN REACHABLE
/// sweep, 2026-08-30): the largest poll count of ANY instance this rung
/// certifies is 2,061 (`lo_14x14_007`; next is 1,479, then <=136), while the
/// smallest count of the pathological non-certifying instances is 7,047
/// (`aim-200` at its old 60 s deadline). 4096 is the power of two inside that
/// measured gap: ~2x headroom over the heaviest certifying member, and it
/// converts the pathologies' minute into a bounded, machine-independent slice.
/// Raising it cannot make a proof wrong, only slower; lowering it turns
/// certificates into declines. The A/B gate for any resizing is proof-sha
/// equality on the certifying corpus.
const MAX_DUAL_SOLVE_POLLS: u64 = 4096;

/// Implements the public contract in [`super::certify_opt_lin_lp_dual_floor`].
///
/// There is intentionally no objective-sign gate: maximization and mixed-sign
/// objectives are valid when the exact LP floor is tight. The dual solve is
/// bounded by [`MAX_DUAL_SOLVE_POLLS`] — a deterministic work count, never a
/// wall clock — and an out-of-budget solve declines without affecting the
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
    // The claimed optimum is threaded as the dual solve's TARGET and the
    // emitter's denominator cap as its scale budget. Both are quality inputs
    // only: a wrong target or an unusable scale can make the solve stop early or
    // hand back a different dual-feasible point, and the reconstruction below
    // still re-derives every coefficient and refuses anything that does not land
    // exactly on `optimum`.
    //
    // The stop predicate is a WORK COUNT, latched once exceeded: every poll is a
    // deterministic chunk of tableau work, so where this solve stops does not
    // depend on the machine or its load. (The advisory f64 tier keeps its own
    // small internal wall budget — pre-existing, fail-closed, and its output is
    // re-verified exactly — so it is the one place a slow box can still turn a
    // would-be certificate into a decline; it could turn none into a wrong one.)
    let polls = std::cell::Cell::new(0u64);
    let raw = crate::optimize::lp_bound::lp_dual_raw_diagnosed(
        objective,
        &instance.constraints,
        instance.num_vars,
        Some(optimum),
        Some(MAX_DUAL_SCALE),
        &|| {
            let spent = polls.get().saturating_add(1);
            polls.set(spent);
            spent > MAX_DUAL_SOLVE_POLLS
        },
    );
    if ay_core::misc_cli_flags().cert_debug {
        eprintln!(
            "c [cert/lp-dual-floor] polls={}/{} -> {}",
            polls.get(),
            MAX_DUAL_SOLVE_POLLS,
            match &raw {
                Ok(r) => format!(
                    "tier={} converged={} bound={} opt={optimum}",
                    r.tier, r.converged, r.bound
                ),
                Err(decline) => format!("decline({})", decline.label()),
            }
        );
    }
    let raw = raw.ok()?;
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
    use super::MAX_DUAL_SOLVE_POLLS;
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

    /// The poll cap was sized from a measured gap, and this pins BOTH edges so
    /// a blind resize cannot silently cross either. Probe sweep 2026-08-30
    /// (PB25 OPT-LIN REACHABLE + the three census pathologies): the heaviest
    /// instance the rung CERTIFIES spends 2,061 polls (`lo_14x14_007`); the
    /// cheapest instance that used to burn the old one-minute wall deadline
    /// WITHOUT certifying spends 7,047 (`aim-200-2_0-yes1-2`). Below the lower
    /// edge the cap costs measured certificates; at or above the upper edge it
    /// readmits the 12x `--timeout` overshoot the count exists to close. A
    /// legitimate move of either edge is a NEW measurement, and the A/B gate
    /// for it is proof-sha equality on the certifying corpus.
    #[test]
    fn dual_solve_poll_cap_sits_inside_the_measured_gap() {
        assert!(
            MAX_DUAL_SOLVE_POLLS > 2_061,
            "cap {MAX_DUAL_SOLVE_POLLS} would decline the heaviest measured certifying member"
        );
        assert!(
            MAX_DUAL_SOLVE_POLLS < 7_047,
            "cap {MAX_DUAL_SOLVE_POLLS} readmits the cheapest measured pathology"
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
