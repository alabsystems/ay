// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Immutable search metadata, LP construction, and deadline budgeting.
//!
//! Deadline planning receives the absolute caller deadline anchored after LP
//! construction and merges it with internal search/finalization limits without
//! restarting that clock. Earlier presolve and probing passes establish their
//! own bounded shares when those optional passes begin.

use std::time::{Duration, Instant};

use num_rational::BigRational;

use crate::model::{Col, Model, Row, Sense};
use crate::opts::SolveOpts;
use crate::outcome::{Outcome, UnknownReason};
use crate::simplex::FloatLp;

use super::{
    apply_bab_lp_opts, branch_hint_ranks, cut_slot_count, finalize_reserve_split_for, integer_cols,
    live_margin_preview_enabled, market_split_rows, ms_branch_rule, FinalizeReplayObligation,
    MsBranch, SearchMode,
};

pub(super) struct BranchMetadata {
    pub(super) ints: Vec<usize>,
    pub(super) hint_ranks: Option<Vec<u32>>,
    pub(super) col_integral: Vec<bool>,
    pub(super) orbitope_branch: bool,
    pub(super) orbitope_interleave: bool,
    pub(super) orbitope_dynamic_branch: bool,
}

pub(super) fn branch_metadata(
    model: &Model,
    branch_hints: &[Col],
    symmetry: &mut Option<crate::symmetry::Symmetry>,
) -> BranchMetadata {
    let ints = integer_cols(model);
    let hint_ranks = branch_hint_ranks(model.num_cols(), branch_hints);
    let col_integral = (0..model.num_cols())
        .map(|column| model.col_kind(Col(column as u32)).is_integral())
        .collect();
    let orbitope_branch = crate::tune::caller_flag(crate::tune::Knob::OrbitopeBranch) == Some(true);
    if let Some(symmetry) = symmetry {
        symmetry.dyn_lane = !symmetry.orbitopes.is_empty()
            && crate::tune::caller_flag(crate::tune::Knob::OrbitopeDyn) == Some(true);
    }
    BranchMetadata {
        ints,
        hint_ranks,
        col_integral,
        orbitope_branch,
        orbitope_interleave: crate::tune::caller_flag(crate::tune::Knob::OrbitopeIlv) == Some(true),
        orbitope_dynamic_branch: crate::tune::caller_flag(crate::tune::Knob::OrbitopeBranchDyn)
            == Some(true),
    }
}

pub(super) struct MarketBranching {
    pub(super) rule: MsBranch,
    pub(super) rows: Vec<(f64, Vec<(usize, f64)>)>,
    pub(super) weights: Vec<f64>,
    pub(super) columns: Vec<Vec<(usize, f64)>>,
}

#[derive(Clone, Copy)]
pub(super) enum MarketClass {
    Split,
    General,
}

pub(super) fn market_branching(model: &Model, class: MarketClass) -> MarketBranching {
    let rule = if matches!(class, MarketClass::Split) {
        ms_branch_rule()
    } else {
        MsBranch::Pc
    };
    let rows = market_rows(model, rule);
    let weight_count = if rows.is_empty() { 0 } else { model.num_cols() };
    let mut weights = vec![0.0; weight_count];
    let mut columns = vec![Vec::new(); weights.len()];
    for (row_index, (_, terms)) in rows.iter().enumerate() {
        for &(column, coefficient) in terms {
            weights[column] += coefficient.abs();
            columns[column].push((row_index, coefficient));
        }
    }
    MarketBranching {
        rule,
        rows,
        weights,
        columns,
    }
}

fn market_rows(model: &Model, rule: MsBranch) -> Vec<(f64, Vec<(usize, f64)>)> {
    if rule == MsBranch::Pc {
        return Vec::new();
    }
    market_split_rows(model)
        .iter()
        .map(|&row| {
            let (coefficients, lower, _) = model.row(Row(row));
            let terms = coefficients
                .iter()
                .filter(|&&(column, _)| model.col_kind(Col(column)).is_integral())
                .map(|&(column, coefficient)| (column as usize, coefficient))
                .collect();
            (lower, terms)
        })
        .collect()
}

pub(super) struct LpBootstrap {
    /// Retained verbatim for later row reloads into this same augmented frame.
    pub(super) objective: Vec<(u32, f64)>,
    pub(super) sense: Sense,
    pub(super) model_offset: BigRational,
    pub(super) slot_count: usize,
    pub(super) augmented_model: Model,
    pub(super) lp: FloatLp,
}

/// Bounded failure to lower the prepared formulation into the float LP lane.
pub(super) struct LpBootstrapError;

impl LpBootstrapError {
    /// Convert the private setup failure at the orchestration boundary.
    pub(super) fn into_outcome(self) -> Outcome {
        Outcome::Unknown {
            reason: UnknownReason::SolverIncomplete {
                detail: "model cannot be lowered to the float lane".to_owned(),
            },
        }
    }
}

#[derive(Clone, Copy)]
pub(super) enum NodeCutPolicy {
    /// Reserve mutable rows for optional, integer-valid node separation.
    Eligible,
    /// Preserve the proof-first layout by omitting optional separation slots.
    ProofFirst,
}

pub(super) fn build_lp(
    model: &Model,
    opts: &SolveOpts,
    mode: SearchMode,
    node_cuts: NodeCutPolicy,
) -> Result<LpBootstrap, LpBootstrapError> {
    let objective = (0..model.num_cols())
        .map(|column| (column as u32, model.obj_coeff(Col(column as u32))))
        .filter(|&(_, coefficient)| coefficient != 0.0)
        .collect::<Vec<_>>();
    let sense = model.sense();
    let slots_requested = crate::tune::count_opt(crate::tune::Knob::NodeCutSlots).is_some()
        || crate::tune::caller_flag(crate::tune::Knob::NodeCuts) == Some(true);
    let slot_count =
        if mode.cheap || matches!(node_cuts, NodeCutPolicy::ProofFirst) || !slots_requested {
            0
        } else {
            cut_slot_count(model)
        };
    let mut augmented_model = model.clone();
    for _ in 0..slot_count {
        augmented_model.add_row(f64::NEG_INFINITY, f64::INFINITY, &[]);
    }
    let Some(mut lp) = FloatLp::from_model(&augmented_model, &objective, sense) else {
        return Err(LpBootstrapError);
    };
    apply_bab_lp_opts(&mut lp, opts);
    lp.plain_cold = true;
    Ok(LpBootstrap {
        objective,
        sense,
        model_offset: model.obj_offset_exact(),
        slot_count,
        augmented_model,
        lp,
    })
}

pub(super) struct DeadlinePlan {
    pub(super) full: Option<Instant>,
    pub(super) finalize_reserve: Option<Duration>,
    pub(super) live_margin_preview: bool,
    pub(super) reserve: Option<FinalizeReservePlan>,
    pub(super) search_floor: Option<Instant>,
    pub(super) search: Option<Instant>,
}

/// Named certificate-replay hold-back derived from one absolute deadline.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct FinalizeReservePlan {
    pub(super) deadline: Instant,
    pub(super) duration: Duration,
    pub(super) search_floor: Duration,
}

pub(super) struct DeadlineRequest<'a> {
    /// Absolute caller deadline anchored before fixed-charge classification.
    pub(super) caller_deadline: Option<Instant>,
    pub(super) mode: SearchMode,
    pub(super) capture: &'a crate::tree_cert::TreeCapture,
    pub(super) market_split: bool,
    pub(super) fixed_charge_dense: bool,
    pub(super) replay: FinalizeReplayObligation,
}

/// Merge absolute deadlines and reserve a bounded tail for certificate replay.
///
/// A reserve yields `search = full - reserve` and a leaf-starved
/// `search_floor = full - floor`, where `floor <= reserve`. Without a reserve,
/// both search deadlines remain the full deadline. Marked-margin capture keeps
/// its replay obligation even before an integral leaf exists.
pub(super) fn plan_deadlines(request: DeadlineRequest<'_>) -> DeadlinePlan {
    let caller = request.caller_deadline;
    let full = match (caller, request.mode.deadline) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    };
    let reserve = reserve_plan(full, &request);
    let finalize_reserve = reserve.map(|plan| plan.duration);
    let live_margin_preview = live_margin_preview_enabled(
        caller.is_some(),
        finalize_reserve,
        matches!(request.replay, FinalizeReplayObligation::MarkedMarginPrefix),
    );
    let (search, search_floor) = match reserve {
        Some(plan) => (
            plan.deadline.checked_sub(plan.duration),
            plan.deadline.checked_sub(plan.search_floor),
        ),
        None => (full, full),
    };
    DeadlinePlan {
        full,
        finalize_reserve,
        live_margin_preview,
        reserve,
        search_floor,
        search,
    }
}

fn reserve_plan(
    full: Option<Instant>,
    request: &DeadlineRequest<'_>,
) -> Option<FinalizeReservePlan> {
    let deadline = full.filter(|_| request.capture.is_armed())?;
    let remaining = deadline.saturating_duration_since(Instant::now());
    let (reserve, floor) = finalize_reserve_split_for(
        remaining,
        request.market_split || request.fixed_charge_dense,
        request.replay,
    );
    (remaining > reserve * 2).then_some(FinalizeReservePlan {
        deadline,
        duration: reserve,
        search_floor: floor,
    })
}

pub(super) fn open_continuous_columns(model: &Model, lp: &FloatLp) -> Vec<usize> {
    (0..lp.n)
        .filter(|&column| !model.col_kind(Col(column as u32)).is_integral())
        .filter(|&column| !lp.lower[column].is_finite() || !lp.upper[column].is_finite())
        .collect()
}

pub(super) fn open_sides(columns: &[usize], lower: &[f64], upper: &[f64]) -> usize {
    columns
        .iter()
        .map(|&column| {
            usize::from(!lower[column].is_finite()) + usize::from(!upper[column].is_finite())
        })
        .sum()
}
