// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resource-bounded bit-width widening for the IC3 candidate lane.

use std::sync::Arc;
use std::time::Duration;

use super::resources::Resources;
use crate::smt::replay_control::ScopedReplayControl;
use crate::smt::resource_observation::ScopedResourceObservation;
use crate::PdrConfig;
use ay_core::resource::ResourceGuard;
use ay_core::time::Instant;

use crate::ic3::solver::{Ic3Result, Ic3Solver};
use crate::pdr::model::InvariantModel;
use crate::{ChcProblem, ChcSort};

#[cfg(test)]
use super::{back_translate, lower_loop};
use super::{
    back_translate_controlled, lift_header_to_full_model_controlled, lower_loop_controlled,
    Control, Lowering,
};

#[cfg(test)]
mod tests;

/// First bit-blast width tried for numeric predicate arguments.
pub(super) const INT_WIDTH: usize = 8;

/// Largest original bit-vector width the IC3 candidate lane models exactly.
pub(super) const MAX_EXACT_BV_BLAST_WIDTH: usize = 128;

/// Hard resource bound applied before latch and Tseitin-CNF construction.
pub(super) const MAX_IC3_STATE_LATCHES: usize = 4_096;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct BlastWidth {
    pub(super) cap: usize,
}

impl BlastWidth {
    pub(super) fn new(cap: usize) -> Self {
        Self {
            cap: cap.clamp(1, MAX_EXACT_BV_BLAST_WIDTH),
        }
    }

    pub(super) fn bitvec(self, width: u32) -> usize {
        (width as usize).clamp(1, self.cap)
    }

    pub(super) fn sort(self, sort: &ChcSort) -> Option<usize> {
        match sort {
            ChcSort::Bool => Some(1),
            ChcSort::Int => Some(self.cap),
            ChcSort::BitVec(width) => Some(self.bitvec(*width)),
            _ => None,
        }
    }
}

/// Data-driven widening rungs for this problem. `Int` has no finite authored
/// width, so its final abstraction is 64 bits. Bit-vectors add their original
/// width, capped at [`MAX_EXACT_BV_BLAST_WIDTH`]. Duplicate effective rungs are
/// removed (for example, a BV12 problem tries 8 then 12).
fn widening_widths_controlled(problem: &ChcProblem, control: &Control<'_>) -> Option<Vec<usize>> {
    control.poll()?;
    let mut target = INT_WIDTH;
    let mut has_int = false;
    for predicate in problem.predicates() {
        control.poll()?;
        for sort in &predicate.arg_sorts {
            control.poll()?;
            match sort {
                ChcSort::Int => has_int = true,
                ChcSort::BitVec(width) => {
                    target = target.max((*width as usize).min(MAX_EXACT_BV_BLAST_WIDTH));
                }
                _ => {}
            }
        }
    }
    if has_int {
        target = target.max(64);
    }

    let mut widths = Vec::new();
    for width in [8usize, 16, 32, 64, target] {
        let effective = width.min(target);
        if widths.last().copied() != Some(effective) {
            widths.push(effective);
        }
        if effective == target {
            break;
        }
    }
    control.poll()?;
    Some(widths)
}

#[cfg(test)]
fn widening_widths(problem: &ChcProblem) -> Vec<usize> {
    let mut live = || true;
    let control = Control::new(
        ay_core::time::Instant::now() + Duration::from_secs(3600),
        &mut live,
    );
    widening_widths_controlled(problem, &control).unwrap_or_default()
}

/// Try the IC3 width ladder and return only a candidate independently accepted
/// by the original word-level validator. The public caller still repeats its
/// mandatory admission validation before any `Safe` result is trusted.
pub fn try_prove_chc_loop(problem: &ChcProblem, timeout: Duration) -> Option<InvariantModel> {
    let deadline = Instant::now().checked_add(timeout)?;
    try_prove_chc_loop_with_resources(
        problem,
        deadline,
        &PdrConfig::production(false),
        &ResourceGuard::new(),
    )
}

/// Additive IC3 candidate entry under the caller's absolute wall and owner.
///
/// Cloning the guard shares its ticks/cancel flag, never a renewed allowance.
/// Caller/ambient walls and per-SMT-context term caps only tighten; Some(0)
/// refuses before lowering or context construction. One sticky cancellation
/// attempt spans all rungs. Local rung expiry does not poison a live parent.
/// Polls debit one guard tick; opaque lowering/SAT/GC/validation operations are
/// cooperative, not exact work accounting or a process-RSS reservation.
/// The returned model remains a candidate, not a Safe/proof credential.
pub fn try_prove_chc_loop_with_resources(
    problem: &ChcProblem,
    original_deadline: Instant,
    config: &PdrConfig,
    owner: &ResourceGuard,
) -> Option<InvariantModel> {
    let mut deadline = owner
        .effective_deadline()
        .map_or(original_deadline, |d| d.min(original_deadline));
    if let Some(timeout) = config.solve_timeout {
        deadline = deadline.min(Instant::now().checked_add(timeout)?);
    }
    let caller = config.effective_cancellation_token();
    let replay = ScopedReplayControl::install_until(deadline, caller.as_ref());
    let resources = Arc::new(Resources::capture(owner, config, &replay));
    let mut live = || resources.poll();
    let control = Control::new(replay.deadline(), &mut live);
    control.poll()?;
    let debug = ay_core::misc_cli_flags().ic3_lane_debug;
    maybe_dump_problem(problem);
    control.poll()?;
    let _memory = resources.install_memory();
    let result = try_widening_ladder(problem, debug, &control, &resources)?;
    control.poll()?;
    Some(result)
}

fn maybe_dump_problem(problem: &ChcProblem) {
    if let Some(path) = ay_core::misc_cli_flags().ic3_lane_dump.as_deref() {
        use std::io::Write as _;
        if let Ok(mut file) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
        {
            let _ = writeln!(
                file,
                "=== IC3_LANE_DUMP preds={} clauses={} ===\n{:#?}\n",
                problem.predicates().len(),
                problem.clauses().len(),
                problem
            );
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RungBudget {
    search: Duration,
    validation: Duration,
}

impl RungBudget {
    fn total(self) -> Duration {
        self.search.saturating_add(self.validation)
    }
}

/// Front-load the established 8-bit lane while retaining fixed base slices for
/// every wider rung. The final weight is deliberately nonzero and is not lent
/// backward; only unused time carries forward.
fn rung_weights(count: usize) -> Option<&'static [u32]> {
    match count {
        1 => Some(&[1]),
        2 => Some(&[24, 2]),
        3 => Some(&[24, 2, 2]),
        4 => Some(&[24, 4, 2, 2]),
        5 => Some(&[24, 8, 4, 2, 2]),
        _ => None,
    }
}

fn allocate_rung_budgets(total: Duration, count: usize) -> Option<Vec<RungBudget>> {
    let weights = rung_weights(count)?;
    let total_weight = weights.iter().copied().sum::<u32>();
    let unit = total / total_weight;
    if unit.is_zero() {
        return None;
    }

    weights
        .iter()
        .copied()
        .map(|weight| {
            let rung_total = unit * weight;
            let search = rung_total / 2;
            let validation = rung_total.saturating_sub(search);
            (!search.is_zero() && !validation.is_zero())
                .then_some(RungBudget { search, validation })
        })
        .collect()
}

fn add_forward_carry(base: RungBudget, carry: Duration, available: Duration) -> Option<RungBudget> {
    let carry_search = carry / 2;
    let mut budget = RungBudget {
        search: base.search.saturating_add(carry_search),
        validation: base
            .validation
            .saturating_add(carry.saturating_sub(carry_search)),
    };
    let excess = budget.total().saturating_sub(available);
    budget.search = budget.search.saturating_sub(excess);
    (!budget.search.is_zero() && !budget.validation.is_zero()).then_some(budget)
}

fn try_widening_ladder(
    problem: &ChcProblem,
    debug: bool,
    control: &Control<'_>,
    resources: &Arc<Resources>,
) -> Option<InvariantModel> {
    control.poll()?;
    let deadline = control.deadline();
    let widths = widening_widths_controlled(problem, control)?;
    let available = deadline.saturating_duration_since(ay_core::time::Instant::now());
    let base_budgets = allocate_rung_budgets(available, widths.len())?;
    let mut carry = Duration::ZERO;
    for (index, width) in widths.iter().copied().enumerate() {
        control.poll()?;
        let rung_start = ay_core::time::Instant::now();
        let available = deadline.saturating_duration_since(rung_start);
        let budget = add_forward_carry(base_budgets[index], carry, available)?;
        let search_deadline = rung_start.checked_add(budget.search)?;
        let rung_deadline = search_deadline.checked_add(budget.validation)?;
        let Some(candidate) =
            ic3_candidate_at_width(problem, width, search_deadline, debug, control, resources)
        else {
            control.poll()?;
            carry = budget.total().saturating_sub(rung_start.elapsed());
            continue;
        };

        // The search deadline cannot consume the validation slice. Any search
        // time saved joins that bounded slice, but validation never borrows a
        // future rung's base reserve.
        let validation_budget =
            rung_deadline.saturating_duration_since(ay_core::time::Instant::now());
        if validation_budget.is_zero() {
            carry = budget.total().saturating_sub(rung_start.elapsed());
            continue;
        }
        let accepted = match candidate_validates_original(
            problem,
            &candidate,
            rung_deadline,
            control,
            resources,
        ) {
            Some(accepted) => accepted,
            None => {
                // Local expiry does not spend another rung's reserved slice.
                // A refused parent, however, remains terminal for the lane.
                control.poll()?;
                carry = budget.total().saturating_sub(rung_start.elapsed());
                continue;
            }
        };
        if debug {
            eprintln!("IC3_LANE: width={width} original_validation={accepted}");
        }
        control.poll()?;
        let in_rung = ay_core::time::Instant::now() < rung_deadline;
        if accepted && in_rung {
            return Some(candidate);
        }
        carry = budget.total().saturating_sub(rung_start.elapsed());
    }
    None
}

fn ic3_candidate_at_width(
    problem: &ChcProblem,
    width: usize,
    deadline: ay_core::time::Instant,
    debug: bool,
    parent: &Control<'_>,
    resources: &Arc<Resources>,
) -> Option<InvariantModel> {
    let mut live = || parent.poll().is_some();
    let control = Control::new(deadline, &mut live);
    let result = ic3_candidate_inner(problem, width, debug, &control, resources)?;
    control.poll()?;
    Some(result)
}

fn ic3_candidate_inner(
    problem: &ChcProblem,
    width: usize,
    debug: bool,
    control: &Control<'_>,
    resources: &Arc<Resources>,
) -> Option<InvariantModel> {
    let low = lower_loop_controlled(problem, BlastWidth::new(width), control);
    if debug {
        eprintln!(
            "IC3_LANE: lower_loop width={width} result={} (preds={})",
            if low.is_some() { "Some" } else { "None" },
            problem.predicates().len()
        );
    }
    let Lowering {
        ts,
        pred,
        params,
        latches,
        orig_header,
    } = low?;
    control.poll()?;
    let owner = resources.clone();
    let mut solver = Ic3Solver::new(ts, false)
        .with_deadline(Some(control.deadline()))
        .with_resource_poll(Arc::new(move || owner.poll()));
    control.poll()?;
    let Ic3Result::Safe { invariant_level } = solver.solve() else {
        if debug {
            eprintln!("IC3_LANE: solve_safe=false width={width}");
        }
        return None;
    };
    control.poll()?;
    let clauses = solver.invariant_clauses(invariant_level);
    control.poll()?;
    let model = back_translate_controlled(pred, &params, &latches, &clauses, control)?;
    match orig_header {
        None => Some(model),
        Some(header) => model.get(&pred).and_then(|interp| {
            lift_header_to_full_model_controlled(
                problem,
                header,
                &interp.vars,
                &interp.formula,
                control,
            )
        }),
    }
}

fn candidate_validates_original(
    problem: &ChcProblem,
    candidate: &InvariantModel,
    deadline: ay_core::time::Instant,
    parent: &Control<'_>,
    resources: &Arc<Resources>,
) -> Option<bool> {
    let mut live = || parent.poll().is_some();
    let control = Control::new(deadline, &mut live);
    control.poll()?;
    let validation_config = resources.validation_config(deadline);
    let smt_deadline = crate::smt::ScopedSmtDeadline::install_until(deadline);
    // No whole-ladder observer: a local rung wall is not the original wall.
    // Existing ambient first-refusal semantics remain intact, including on Err.
    let observation = ScopedResourceObservation::install();
    let result = crate::engines::validate_external_invariant_model_typed(
        problem,
        candidate,
        &validation_config,
    );
    drop(validation_config);
    drop(smt_deadline);
    resources.observe_validation(observation.first(), &result);
    drop(observation);
    control.poll()?;
    Some(matches!(
        result,
        Ok(crate::engines::ExternalInvariantValidation::Valid)
    ))
}
