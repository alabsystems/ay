// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resource-bounded bit-width widening for the IC3 candidate lane.

use std::time::Duration;

use crate::ic3::solver::{Ic3Result, Ic3Solver};
use crate::pdr::model::InvariantModel;
use crate::{ChcProblem, ChcSort};

use super::{back_translate, lift_header_to_full_model, lower_loop, Lowering};

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
fn widening_widths(problem: &ChcProblem) -> Vec<usize> {
    let mut target = INT_WIDTH;
    let mut has_int = false;
    for predicate in problem.predicates() {
        for sort in &predicate.arg_sorts {
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
    widths
}

/// Try the IC3 width ladder and return only a candidate independently accepted
/// by the original word-level validator. The public caller still repeats its
/// mandatory admission validation before any `Safe` result is trusted.
pub fn try_prove_chc_loop(problem: &ChcProblem, timeout: Duration) -> Option<InvariantModel> {
    let debug = ay_core::misc_cli_flags().ic3_lane_debug;
    maybe_dump_problem(problem);
    try_widening_ladder(problem, timeout, debug)
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
    timeout: Duration,
    debug: bool,
) -> Option<InvariantModel> {
    let deadline = ay_core::time::Instant::now() + timeout;
    let widths = widening_widths(problem);
    let base_budgets = allocate_rung_budgets(timeout, widths.len())?;
    let mut carry = Duration::ZERO;
    for (index, width) in widths.iter().copied().enumerate() {
        let rung_start = ay_core::time::Instant::now();
        let available = deadline.saturating_duration_since(rung_start);
        let budget = add_forward_carry(base_budgets[index], carry, available)?;
        let search_deadline = rung_start + budget.search;
        let rung_deadline = search_deadline + budget.validation;
        let Some(candidate) = ic3_candidate_at_width(problem, width, search_deadline, debug) else {
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
        let accepted = candidate_validates_original(problem, &candidate, validation_budget);
        if debug {
            eprintln!("IC3_LANE: width={width} original_validation={accepted}");
        }
        if accepted {
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
) -> Option<InvariantModel> {
    let low = lower_loop(problem, BlastWidth::new(width));
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

    let mut solver = Ic3Solver::new(ts, false).with_deadline(Some(deadline));
    let Ic3Result::Safe { invariant_level } = solver.solve() else {
        if debug {
            eprintln!("IC3_LANE: solve_safe=false width={width}");
        }
        return None;
    };
    let clauses = solver.invariant_clauses(invariant_level);
    let model = back_translate(pred, &params, &latches, &clauses)?;
    match orig_header {
        None => Some(model),
        Some(header) => model.get(&pred).and_then(|interp| {
            lift_header_to_full_model(
                problem,
                header,
                &interp.vars,
                &interp.formula,
                deadline.saturating_duration_since(ay_core::time::Instant::now()),
            )
        }),
    }
}

fn candidate_validates_original(
    problem: &ChcProblem,
    candidate: &InvariantModel,
    budget: Duration,
) -> bool {
    let mut validation_config = crate::PdrConfig::production(false);
    validation_config.solve_timeout = Some(budget);
    matches!(
        crate::engines::validate_external_invariant_model(problem, candidate, &validation_config),
        Ok(true)
    )
}
