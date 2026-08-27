// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed construction of node-cut and inference controls.
//!
//! These structures are built once against the immutable cut model and root
//! box. Search nodes tighten that box; they do not reorder rows or columns, so
//! cached slot identities, adjacencies, and implication indices remain stable.

use std::time::Duration;

use crate::model::{Col, Model, Row};
use crate::simplex::FloatLp;

use super::{
    feasibility_conflict_class, mine_implications, mixed_model_gate, set_prop_caps, ImplTable,
    SearchMode, IMPL_MAX_SRC_BINS, NODE_CUT_AGE_STREAK, NODE_CUT_BATCH, NODE_CUT_DEPTH_MAX,
    NODE_CUT_EPS, NODE_CUT_EVERY_MIN, NODE_CUT_MIN_AGE, NODE_CUT_NNZ, PROP_MAX_QUEUE,
    PROP_MAX_SWEEPS,
};

pub(super) const MIXED_LEVER_ARM_NODES: usize = 1_024;
pub(super) const PROP_RETIRE_WINDOW: usize = 96;

/// Mutable bookkeeping for fixed LP cut slots.
///
/// The three per-slot vectors are parallel. A local slot is valid only inside
/// its recorded deriving box; the fixed row/column blocks must not move.
pub(super) struct NodeCutState {
    pub(super) slot_row0: usize,
    pub(super) slot_col0: usize,
    pub(super) odd_cycle: bool,
    pub(super) slot_born: Vec<Option<usize>>,
    pub(super) slot_streak: Vec<u32>,
    pub(super) slot_local: Vec<Option<(Vec<(usize, f64, f64)>, f64, f64)>>,
    pub(super) local_slots_live: usize,
    pub(super) vubs: crate::cuts::Vubs,
    pub(super) batch: usize,
    pub(super) min_age: usize,
    pub(super) depth_max: u32,
    pub(super) epsilon: f64,
    pub(super) age_streak: u32,
    pub(super) local: bool,
    pub(super) gmi_node_rounds: usize,
    pub(super) eager: bool,
    pub(super) gmi: u32,
    pub(super) gmi_only: bool,
    pub(super) gmi_every: usize,
    pub(super) gmi_owner_margin: f64,
    pub(super) nnz: usize,
    pub(super) gmi_budget: usize,
    pub(super) next_gmi_node: usize,
    pub(super) gmi_rounds: usize,
    pub(super) gmi_derived: usize,
    pub(super) gmi_kept: usize,
    pub(super) gmi_time: Duration,
    pub(super) every: usize,
    pub(super) next_node: usize,
    pub(super) writes: usize,
    pub(super) rounds: usize,
    pub(super) dry: usize,
    pub(super) evictions: usize,
    pub(super) rejected: usize,
    pub(super) separation_time: Duration,
    pub(super) derive_time: Duration,
    pub(super) swap_time: Duration,
    pub(super) gain: f64,
}

pub(super) fn node_cut_state(model: &Model, lp: &FloatLp, slot_count: usize) -> NodeCutState {
    let every_min = crate::tune::count_opt(crate::tune::Knob::NodeCutEvery)
        .filter(|&value| value > 0)
        .unwrap_or(NODE_CUT_EVERY_MIN);
    let gmi_every = crate::tune::count_opt(crate::tune::Knob::NodeGmiEvery)
        .filter(|&value| value > 0)
        .unwrap_or(500);
    NodeCutState {
        slot_row0: model.num_rows(),
        slot_col0: lp.n + model.num_rows(),
        odd_cycle: crate::tune::on(crate::tune::Knob::OddCycle)
            && !crate::tune::on(crate::tune::Knob::NoOddCycle),
        slot_born: vec![None; slot_count],
        slot_streak: vec![0; slot_count],
        slot_local: vec![None; slot_count],
        local_slots_live: 0,
        vubs: if slot_count > 0 {
            crate::cuts::node_vubs(model)
        } else {
            crate::cuts::Vubs::new()
        },
        batch: crate::tune::count_opt(crate::tune::Knob::NodeCutBatch)
            .filter(|&value| value > 0)
            .unwrap_or(NODE_CUT_BATCH),
        min_age: crate::tune::count_opt(crate::tune::Knob::NodeCutAge).unwrap_or(NODE_CUT_MIN_AGE),
        depth_max: NODE_CUT_DEPTH_MAX,
        epsilon: NODE_CUT_EPS,
        age_streak: NODE_CUT_AGE_STREAK,
        local: crate::tune::caller_flag(crate::tune::Knob::NodeCutLocal) == Some(true),
        gmi_node_rounds: 1,
        eager: crate::tune::caller_flag(crate::tune::Knob::NodeCutEager) == Some(true),
        gmi: crate::tune::count_opt(crate::tune::Knob::NodeGmi)
            .and_then(|value| u32::try_from(value).ok())
            .unwrap_or(0),
        gmi_only: false,
        gmi_every,
        gmi_owner_margin: crate::tune::real_opt(crate::tune::Knob::NodeGmiMargin).unwrap_or(1.0),
        nnz: NODE_CUT_NNZ,
        gmi_budget: 12,
        next_gmi_node: gmi_every,
        gmi_rounds: 0,
        gmi_derived: 0,
        gmi_kept: 0,
        gmi_time: Duration::ZERO,
        every: every_min,
        next_node: every_min,
        writes: 0,
        rounds: 0,
        dry: 0,
        evictions: 0,
        rejected: 0,
        separation_time: Duration::ZERO,
        derive_time: Duration::ZERO,
        swap_time: Duration::ZERO,
        gain: 0.0,
    }
}

#[derive(Clone, Copy)]
pub(super) enum ImplicationPolicy {
    Enabled,
    Disabled,
}

impl ImplicationPolicy {
    pub(super) const fn enabled(self) -> bool {
        matches!(self, Self::Enabled)
    }
}

pub(super) struct PropagationRequest<'a> {
    pub(super) model: &'a Model,
    pub(super) mode: SearchMode,
    pub(super) symmetry: Option<&'a crate::symmetry::Symmetry>,
    pub(super) root_lower: &'a [f64],
    pub(super) root_upper: &'a [f64],
}

/// Root-frame propagation configuration and immutable row adjacency.
pub(super) struct PropagationState {
    pub(super) default_class: bool,
    pub(super) enabled: bool,
    pub(super) arm_node: usize,
    pub(super) barren_nodes: usize,
    pub(super) feasibility_class: bool,
    pub(super) widen_nogoods: bool,
    pub(super) implication_class: bool,
    pub(super) implication_policy: ImplicationPolicy,
    pub(super) column_rows: Vec<Vec<u32>>,
    pub(super) pruned: usize,
}

#[derive(Clone, Copy)]
enum PropagationRegime {
    OutsideDefault,
    WithoutImplications,
    WithImplications,
}

pub(super) fn propagation_state(request: PropagationRequest<'_>) -> PropagationState {
    let PropagationRequest {
        model,
        mode,
        symmetry,
        root_lower,
        root_upper,
    } = request;
    let default_class = !mode.cheap && !mode.dfs && mixed_model_gate(model);
    let enabled = crate::tune::caller_flag(crate::tune::Knob::NodeProp).unwrap_or(default_class);
    let feasibility_class = feasibility_conflict_class(model, &mode);
    let widen_nogoods = crate::tune::caller_flag(crate::tune::Knob::NgBox)
        .unwrap_or(default_class || feasibility_class);
    let implication_class =
        default_class && symmetry.is_some_and(|value| !value.orbitopes.is_empty());
    let regime = match (default_class, implication_class) {
        (false, _) => PropagationRegime::OutsideDefault,
        (true, false) => PropagationRegime::WithoutImplications,
        (true, true) => PropagationRegime::WithImplications,
    };
    charge_declined_implication_mining(model, root_lower, root_upper, regime);
    let implication_policy = match crate::tune::caller_flag(crate::tune::Knob::ImplLane) {
        Some(true) => ImplicationPolicy::Enabled,
        Some(false) => ImplicationPolicy::Disabled,
        None if implication_class => ImplicationPolicy::Enabled,
        None => ImplicationPolicy::Disabled,
    };
    configure_propagation_caps(model, mode, regime);
    let column_rows = if enabled || implication_policy.enabled() {
        column_rows(model)
    } else {
        Vec::new()
    };
    PropagationState {
        default_class,
        enabled,
        arm_node: MIXED_LEVER_ARM_NODES,
        barren_nodes: 0,
        feasibility_class,
        widen_nogoods,
        implication_class,
        implication_policy,
        column_rows,
        pruned: 0,
    }
}

fn charge_declined_implication_mining(
    model: &Model,
    lower: &[f64],
    upper: &[f64],
    regime: PropagationRegime,
) {
    if !matches!(regime, PropagationRegime::WithoutImplications) {
        return;
    }
    let binaries = (0..model.num_cols())
        .filter(|&column| {
            model.col_kind(Col(column as u32)).is_integral()
                && lower[column] == 0.0
                && upper[column] == 1.0
        })
        .count();
    if binaries > 0 && binaries <= IMPL_MAX_SRC_BINS {
        crate::sepstat::gate_charge(crate::sepstat::GATE_IMPL_ORBITOPE, binaries as u64);
    }
}

fn configure_propagation_caps(model: &Model, mode: SearchMode, regime: PropagationRegime) {
    if mode.depth != 0 {
        return;
    }
    let primary =
        matches!(regime, PropagationRegime::WithoutImplications) && model.num_rows() < 1_200;
    let (sweeps, queue) = if primary {
        (512, model.num_cols().max(PROP_MAX_QUEUE))
    } else {
        (PROP_MAX_SWEEPS, PROP_MAX_QUEUE)
    };
    set_prop_caps(sweeps, queue);
}

/// Build adjacency once; every later node retains these row/column identities.
fn column_rows(model: &Model) -> Vec<Vec<u32>> {
    let mut result = vec![Vec::new(); model.num_cols()];
    for row in 0..model.num_rows() {
        let (coefficients, _, _) = model.row(Row(row as u32));
        for &(column, _) in coefficients {
            result[column as usize].push(row as u32);
        }
    }
    result
}

#[derive(Clone, Copy)]
pub(super) enum FixedChargeClass {
    Dense,
    Ordinary,
}

impl FixedChargeClass {
    const fn is_dense(self) -> bool {
        matches!(self, Self::Dense)
    }
}

pub(super) struct FixedChargeState {
    pub(super) mode: FixedChargeMode,
    pub(super) continuous: Vec<Vec<u32>>,
}

/// Selection-only scoring rule for fixed-charge branch candidates.
#[derive(Clone, Copy)]
pub(super) enum FixedChargeMode {
    Disabled,
    Flow,
    FlowAndObjective,
    ScaledPseudocost,
}

impl FixedChargeMode {
    const fn from_code(code: usize, class: FixedChargeClass) -> Self {
        match code {
            0 => Self::Disabled,
            1 => Self::Flow,
            2 => Self::FlowAndObjective,
            3 => Self::ScaledPseudocost,
            _ if class.is_dense() => Self::ScaledPseudocost,
            _ => Self::Disabled,
        }
    }

    pub(super) const fn enabled(self) -> bool {
        !matches!(self, Self::Disabled)
    }

    const fn code(self) -> u8 {
        match self {
            Self::Disabled => 0,
            Self::Flow => 1,
            Self::FlowAndObjective => 2,
            Self::ScaledPseudocost => 3,
        }
    }

    pub(super) fn score(
        self,
        fractional_distance: f64,
        carried_flow: f64,
        pseudocost: f64,
        objective_magnitude: f64,
    ) -> f64 {
        match self {
            Self::Disabled => 0.0,
            Self::Flow => fractional_distance * carried_flow,
            Self::FlowAndObjective => fractional_distance * (carried_flow + objective_magnitude),
            Self::ScaledPseudocost => pseudocost * (1.0 + carried_flow),
        }
    }
}

pub(super) struct FixedChargeRequest<'a> {
    pub(super) model: &'a Model,
    pub(super) integers: &'a [usize],
    pub(super) root_lower: &'a [f64],
    pub(super) root_upper: &'a [f64],
    pub(super) column_rows: &'a [Vec<u32>],
    pub(super) class: FixedChargeClass,
}

/// Build selection-only branching advice over immutable root-frame adjacency.
///
/// This state can rank or group branches but carries no pruning or verdict
/// authority.
pub(super) fn fixed_charge_state(request: FixedChargeRequest<'_>) -> FixedChargeState {
    let mode = FixedChargeMode::from_code(
        crate::tune::count_opt(crate::tune::Knob::FcMode).unwrap_or(usize::MAX),
        request.class,
    );
    let continuous = if mode.enabled() {
        fixed_charge_adjacency(&request)
    } else {
        Vec::new()
    };
    if mode.enabled() && crate::debug_flags::milp_debug_flags().trace {
        let gated = continuous.iter().filter(|value| !value.is_empty()).count();
        let flows = continuous.iter().map(Vec::len).sum::<usize>();
        let dense = request.class.is_dense();
        let mode = mode.code();
        eprintln!(
            "--trace fixed-charge branching mode={mode} (auto={dense}): {gated} binaries gate {flows} flow-column couplings"
        );
    }
    FixedChargeState { mode, continuous }
}

fn fixed_charge_adjacency(request: &FixedChargeRequest<'_>) -> Vec<Vec<u32>> {
    let owned;
    let column_rows = if request.column_rows.is_empty() {
        owned = column_rows(request.model);
        &owned
    } else {
        request.column_rows
    };
    let mut result = vec![Vec::new(); request.model.num_cols()];
    let mut seen = vec![u32::MAX; request.model.num_cols()];
    for &column in request.integers {
        if request.root_lower[column] != 0.0 || request.root_upper[column] != 1.0 {
            continue;
        }
        for &row in &column_rows[column] {
            let (coefficients, _, _) = request.model.row(Row(row));
            for &(other, _) in coefficients {
                let index = other as usize;
                if !request.model.col_kind(Col(other)).is_integral() && seen[index] != column as u32
                {
                    seen[index] = column as u32;
                    result[column].push(other);
                }
            }
        }
    }
    result
}

pub(super) struct ImplicationRequest<'a> {
    pub(super) model: &'a Model,
    pub(super) lp: &'a FloatLp,
    pub(super) root_lower: &'a [f64],
    pub(super) root_upper: &'a [f64],
    pub(super) column_rows: &'a [Vec<u32>],
    pub(super) policy: ImplicationPolicy,
}

/// Root-box implications and their minimize-frame cutoff cache.
///
/// The table remains valid because every searched node box is a subset of the
/// box in which it was mined; objective terms use the LP's internal minimize
/// frame rather than the caller's objective sense.
pub(super) struct ImplicationState {
    pub(super) table: ImplTable,
    pub(super) fired: usize,
    pub(super) pruned: usize,
    pub(super) changed: Vec<usize>,
    pub(super) seen: Vec<bool>,
    pub(super) cutoff_enabled: bool,
    pub(super) table_enabled: bool,
    pub(super) objective_terms: Vec<(usize, f64)>,
    pub(super) cutoff_cache: Option<(f64, f64)>,
    pub(super) cutoff_pruned: usize,
    pub(super) arm_node: usize,
}

/// Mine the immutable root table and initialize only its mutable counters.
pub(super) fn implication_state(request: ImplicationRequest<'_>) -> ImplicationState {
    let enabled = request.policy.enabled();
    let table = if enabled {
        mine_implications(
            request.model,
            request.column_rows,
            request.root_lower,
            request.root_upper,
        )
    } else {
        ImplTable {
            srcs: Vec::new(),
            ents: Vec::new(),
        }
    };
    trace_implications(
        request.model,
        request.root_lower,
        request.root_upper,
        &table,
        request.policy,
    );
    let cutoff_enabled =
        enabled && crate::tune::caller_flag(crate::tune::Knob::NoImplCut).map_or(true, |no| !no);
    let objective_terms = if cutoff_enabled {
        (0..request.lp.n)
            .filter(|&column| request.lp.cost[column] != 0.0)
            .map(|column| (column, request.lp.cost[column]))
            .collect()
    } else {
        Vec::new()
    };
    ImplicationState {
        table,
        fired: 0,
        pruned: 0,
        changed: Vec::new(),
        seen: vec![false; request.model.num_cols()],
        cutoff_enabled,
        table_enabled: crate::tune::caller_flag(crate::tune::Knob::NoImplTab)
            .map_or(true, |no| !no),
        objective_terms,
        cutoff_cache: None,
        cutoff_pruned: 0,
        arm_node: crate::tune::count_opt(crate::tune::Knob::ImplArm)
            .unwrap_or(MIXED_LEVER_ARM_NODES),
    }
}

fn trace_implications(
    model: &Model,
    lower: &[f64],
    upper: &[f64],
    table: &ImplTable,
    policy: ImplicationPolicy,
) {
    if !policy.enabled() || !crate::debug_flags::milp_debug_flags().trace {
        return;
    }
    let binary_targets = table
        .ents
        .iter()
        .filter(|&&(column, _, _)| {
            model.col_kind(Col(column)).is_integral()
                && lower[column as usize] == 0.0
                && upper[column as usize] <= 1.0
        })
        .count();
    eprintln!(
        "--trace implications: {} sources, {} entries ({} binary-target) mined",
        table.srcs.len(),
        table.ents.len(),
        binary_targets
    );
}
