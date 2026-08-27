// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mutable frontier, conflict-store, and heuristic-schedule state.
//!
//! Stored no-good boxes are certified empty, so any node box contained in one
//! may be pruned. Scheduling counters and capacities affect discovery and
//! retention only; they never create a pruning license.

use std::collections::BinaryHeap;
use std::time::Duration;

use ay_lra::rational::Rational;
use num_rational::BigRational;
use num_traits::Zero;

use crate::model::{exact, Model, Sense};
use crate::simplex::FloatLp;

use super::search_controls::MIXED_LEVER_ARM_NODES;
use super::{
    objective_granularity, symmetry_branch_band_setting, to_f64, Node, PcScratch, SearchMode,
};

pub(super) const BALL_USELESS_MIN: u32 = 3;

pub(super) struct FrontierRequest<'a> {
    pub(super) model: &'a Model,
    pub(super) lp: &'a FloatLp,
    pub(super) mode: SearchMode,
    pub(super) sense: Sense,
    pub(super) bottleneck_granularity: Option<&'a BigRational>,
}

pub(super) struct FrontierState {
    pub(super) heap: BinaryHeap<Node>,
    pub(super) dive: Vec<Node>,
    pub(super) minimize_objective: Vec<(u32, Rational)>,
    pub(super) objective_granularity: Option<BigRational>,
    pub(super) granularity_float: Option<f64>,
    pub(super) zero_objective: bool,
    pub(super) unbounded: bool,
    pub(super) nodes: usize,
    pub(super) shared_prefix_entries: usize,
    pub(super) measurement_node_cap: Option<usize>,
    /// External cutoff in the LP's minimize frame; its consumer poisons tree
    /// capture before using it as a prune.
    pub(super) dual_cutoff: Option<BigRational>,
    pub(super) symmetry_branch: bool,
    pub(super) symmetry_branch_band: f64,
}

#[derive(Clone, Copy)]
enum ObjectiveClass {
    Costed,
    Feasibility,
}

pub(super) fn frontier_state(request: FrontierRequest<'_>) -> FrontierState {
    let mut minimize_objective = (0..request.lp.n)
        .filter(|&column| request.lp.cost[column] != 0.0)
        .filter_map(|column| {
            exact(request.lp.cost[column]).map(|cost| (column as u32, Rational::from_big(cost)))
        })
        .collect::<Vec<_>>();
    minimize_objective.sort_unstable_by_key(|&(column, _)| column);
    let objective_granularity =
        objective_granularity(request.model).or_else(|| request.bottleneck_granularity.cloned());
    let granularity_float = objective_granularity
        .as_ref()
        .map(to_f64)
        .filter(|value| *value > 0.0);
    let zero_objective = (0..request.lp.n).all(|column| request.lp.cost[column] == 0.0);
    let objective_class = if zero_objective {
        ObjectiveClass::Feasibility
    } else {
        ObjectiveClass::Costed
    };
    FrontierState {
        heap: BinaryHeap::new(),
        dive: Vec::new(),
        minimize_objective,
        objective_granularity,
        granularity_float,
        zero_objective,
        unbounded: false,
        nodes: 0,
        shared_prefix_entries: 0,
        measurement_node_cap: crate::tune::count_opt(crate::tune::Knob::MaxNodes),
        dual_cutoff: dual_cutoff(&request, objective_class),
        symmetry_branch: crate::tune::caller_flag(crate::tune::Knob::SymBranch).unwrap_or(true),
        symmetry_branch_band: symmetry_branch_band_setting(crate::tune::real_opt(
            crate::tune::Knob::SymBranchBand,
        )),
    }
}

fn dual_cutoff(request: &FrontierRequest<'_>, objective: ObjectiveClass) -> Option<BigRational> {
    if request.mode.depth != 0 || matches!(objective, ObjectiveClass::Feasibility) {
        return None;
    }
    crate::tune::real_opt(crate::tune::Knob::DualCutoff)
        .and_then(exact)
        .map(|value| {
            let offset = exact(request.model.objective_offset()).unwrap_or_else(BigRational::zero);
            match request.sense {
                Sense::Minimize => value - offset,
                Sense::Maximize => offset - value,
            }
        })
}

pub(super) struct NogoodRequest<'a> {
    pub(super) lp: &'a FloatLp,
    pub(super) widen_boxes: bool,
    pub(super) implication_class: bool,
    pub(super) feasibility_class: bool,
}

/// Certified boxes and parallel replacement-policy metadata.
///
/// `boxes`, `generations`, `licenses`, and `activity` have equal lengths and
/// must be mutated together. A Farkas license proves its stored box empty in
/// exact arithmetic, hence also every contained node box. Widening may relax a
/// learned box only after the relaxed box itself retains that certificate.
pub(super) struct NogoodState {
    pub(super) boxes: Vec<Vec<(usize, f64, f64)>>,
    pub(super) pruned: usize,
    pub(super) skipped_long: usize,
    pub(super) check_time: Duration,
    pub(super) generations: Vec<u64>,
    pub(super) next_generation: u64,
    pub(super) subsumed_dropped: usize,
    pub(super) subsumed_removed: usize,
    pub(super) licenses: Vec<u8>,
    pub(super) activity: Vec<u32>,
    pub(super) upward_enabled: bool,
    pub(super) upward_fixed: usize,
    pub(super) upward_pruned: usize,
    pub(super) fire_lengths: [usize; 5],
    pub(super) fix_lengths: [usize; 5],
    pub(super) branch_band: f64,
    pub(super) two_open_counts: Vec<u32>,
    pub(super) two_open_touched: Vec<usize>,
    pub(super) vsids_enabled: bool,
    pub(super) vsids: Vec<f64>,
    pub(super) branch_switched: usize,
    pub(super) ring: usize,
    pub(super) max_len: usize,
    pub(super) capacity: usize,
}

#[derive(Clone, Copy)]
enum NogoodStoreClass {
    ExactBinary,
    Mixed,
    TallMixed,
}

/// Select bounded store geometry; caps are retention policy, not proof rules.
pub(super) fn nogood_state(request: NogoodRequest<'_>) -> NogoodState {
    let upward_enabled = match crate::tune::caller_flag(crate::tune::Knob::NgUp) {
        Some(forced) => forced,
        None => {
            request.widen_boxes
                && (request.lp.tall_lu() || request.implication_class || request.feasibility_class)
        }
    };
    let branch_band = match crate::tune::real_opt(crate::tune::Knob::NgBranchPct) {
        Some(percent) => percent / 100.0,
        None if upward_enabled => 0.25,
        None => 0.0,
    };
    let store_class = if !request.widen_boxes {
        NogoodStoreClass::ExactBinary
    } else if request.lp.tall_lu() {
        NogoodStoreClass::TallMixed
    } else {
        NogoodStoreClass::Mixed
    };
    let (max_len, capacity) = nogood_limits(store_class);
    NogoodState {
        boxes: Vec::new(),
        pruned: 0,
        skipped_long: 0,
        check_time: Duration::ZERO,
        generations: Vec::new(),
        next_generation: 0,
        subsumed_dropped: 0,
        subsumed_removed: 0,
        licenses: Vec::new(),
        activity: Vec::new(),
        upward_enabled,
        upward_fixed: 0,
        upward_pruned: 0,
        fire_lengths: [0; 5],
        fix_lengths: [0; 5],
        branch_band,
        two_open_counts: Vec::new(),
        two_open_touched: Vec::new(),
        vsids_enabled: crate::tune::caller_flag(crate::tune::Knob::Vsids)
            .unwrap_or(request.feasibility_class),
        vsids: Vec::new(),
        branch_switched: 0,
        ring: 0,
        max_len,
        capacity,
    }
}

fn nogood_limits(class: NogoodStoreClass) -> (usize, usize) {
    match class {
        NogoodStoreClass::ExactBinary => (16, 256),
        NogoodStoreClass::Mixed => (32, 1_024),
        NogoodStoreClass::TallMixed => (96, 8_192),
    }
}

pub(super) struct LearnerRequest<'a> {
    pub(super) lp: &'a FloatLp,
    pub(super) widen_boxes: bool,
    pub(super) implications_enabled: bool,
    pub(super) feasibility_class: bool,
}

/// Separate propagation-replay and LP-bound certificate budgets.
///
/// Propagation conflicts may license feasibility or cutoff-bound pruning;
/// lower-bound conflicts require their LP-bound certificate. Both feed the
/// common tagged store without conflating those licenses. Length/capacity 8/128
/// limits are flood control only and never assumptions in a proof.
pub(super) struct LearnerState {
    pub(super) propagation_len_cap: usize,
    pub(super) propagation_capacity: usize,
    pub(super) lower_bound_enabled: bool,
    pub(super) lower_bound_arm: usize,
    pub(super) lower_bound_len_cap: usize,
    pub(super) lower_bound_capacity: usize,
    pub(super) lower_bound_strict: bool,
    pub(super) lower_bound_attempts: usize,
    pub(super) lower_bound_stored: usize,
    pub(super) lower_bound_relaxed: usize,
    pub(super) lower_bound_unrelaxed: usize,
    pub(super) lower_bound_failed: usize,
    pub(super) lower_bound_long: usize,
    pub(super) lower_bound_time: Duration,
    pub(super) propagation_scratch: Option<PcScratch>,
    pub(super) propagation_attempts: usize,
    pub(super) propagation_stored: usize,
    pub(super) propagation_stored_bound: usize,
    pub(super) propagation_minimized: usize,
    pub(super) propagation_failed: usize,
    pub(super) propagation_long: usize,
    pub(super) propagation_time: Duration,
}

pub(super) fn learner_state(request: LearnerRequest<'_>) -> LearnerState {
    let propagation_enabled = match crate::tune::caller_flag(crate::tune::Knob::PropConflict) {
        Some(forced) => forced,
        None => request.implications_enabled || request.feasibility_class,
    };
    let lower_bound_enabled = match crate::tune::count_opt(crate::tune::Knob::LbConflict) {
        Some(1) => request.widen_boxes,
        Some(2) => true,
        _ => false,
    };
    LearnerState {
        propagation_len_cap: 8,
        propagation_capacity: 128,
        lower_bound_enabled,
        lower_bound_arm: crate::tune::count_opt(crate::tune::Knob::LbArm)
            .unwrap_or(MIXED_LEVER_ARM_NODES),
        lower_bound_len_cap: 8,
        lower_bound_capacity: 128,
        lower_bound_strict: crate::tune::caller_flag(crate::tune::Knob::LbStrict).unwrap_or(true),
        lower_bound_attempts: 0,
        lower_bound_stored: 0,
        lower_bound_relaxed: 0,
        lower_bound_unrelaxed: 0,
        lower_bound_failed: 0,
        lower_bound_long: 0,
        lower_bound_time: Duration::ZERO,
        propagation_scratch: propagation_enabled.then(|| PcScratch::new(request.lp.n)),
        propagation_attempts: 0,
        propagation_stored: 0,
        propagation_stored_bound: 0,
        propagation_minimized: 0,
        propagation_failed: 0,
        propagation_long: 0,
        propagation_time: Duration::ZERO,
    }
}
