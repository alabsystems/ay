// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Root-only discovery of exhaustive structural branching disjunctions.
//!
//! Supports are read from the caller/source model before symmetry rows or cuts
//! are added. They guide child construction but never authorize pruning. GUB
//! branching yields to symmetry-owned children, and direct AMO branching yields
//! to dynamic orbitopes because its cloned branch state cannot encode the
//! orbitope lane's multi-fix child.

use crate::model::{Model, Row};

use super::super::{
    amo_multiway_branch_on, conflict_cliques, dynamic_orbitope_blocks_gub, gub_branch_on,
    set_partition_supports, SearchMode,
};
use super::SymmetryMode;

pub(super) struct StructuralBranching {
    pub(super) gub_supports: Option<Vec<Vec<usize>>>,
    pub(super) gub_enabled: bool,
    pub(super) amo_rows: Vec<crate::cardinality_branch::UnitAmoRow>,
    pub(super) amo_requested: bool,
    pub(super) amo_enabled: bool,
}

#[derive(Clone, Copy)]
enum AmoPolicy {
    Disabled,
    DynamicOrbitopeOwned,
    Eligible,
}

enum AmoTraceState {
    Inactive,
    DynamicOrbitopeOwned,
    Armed(usize),
}

/// Discover source-row disjunctions without granting them verdict authority.
pub(super) fn prepare_structural_branching(
    source_model: &Model,
    mode: SearchMode,
    symmetry_mode: SymmetryMode,
    symmetry: Option<&crate::symmetry::Symmetry>,
) -> StructuralBranching {
    let gub_supports = prepare_gub_supports(source_model, mode, symmetry);
    let gub_enabled = gub_branch_on(gub_supports.is_some(), symmetry.is_some());
    if gub_enabled && crate::debug_flags::milp_debug_flags().trace {
        let count = gub_supports.as_ref().map_or(0, |supports| {
            supports.iter().filter(|row| row.len() >= 2).count()
        });
        eprintln!("--trace gub-branch: armed ({count} branchable clique/partition supports)");
    }
    let amo_requested = crate::tune::caller_flag(crate::tune::Knob::AmoMultiway) == Some(true);
    let dynamic_conflict = amo_requested
        && dynamic_orbitope_blocks_gub(
            symmetry_mode.label(),
            crate::tune::caller_flag(crate::tune::Knob::OrbitopeDyn) == Some(true),
            symmetry.is_some_and(|value| !value.orbitopes.is_empty()),
        );
    let amo_policy = match (amo_requested, dynamic_conflict) {
        (false, _) => AmoPolicy::Disabled,
        (true, true) => AmoPolicy::DynamicOrbitopeOwned,
        (true, false) => AmoPolicy::Eligible,
    };
    let amo_rows = prepare_amo_rows(source_model, mode, amo_policy);
    let amo_enabled = amo_multiway_branch_on(!amo_rows.is_empty(), dynamic_conflict);
    let trace_state = if matches!(amo_policy, AmoPolicy::DynamicOrbitopeOwned) {
        AmoTraceState::DynamicOrbitopeOwned
    } else if amo_enabled {
        AmoTraceState::Armed(amo_rows.len())
    } else {
        AmoTraceState::Inactive
    };
    trace_amo_branching(trace_state);
    StructuralBranching {
        gub_supports,
        gub_enabled,
        amo_rows,
        amo_requested,
        amo_enabled,
    }
}

/// Keep only exhaustive source-model supports not owned by symmetry branching.
fn prepare_gub_supports(
    model: &Model,
    mode: SearchMode,
    symmetry: Option<&crate::symmetry::Symmetry>,
) -> Option<Vec<Vec<usize>>> {
    if mode.cheap {
        return None;
    }
    if symmetry.is_some() {
        if let Some(supports) = set_partition_supports(model) {
            crate::sepstat::gate_charge(
                crate::sepstat::GATE_GUB_SYM_DISARM,
                supports.iter().filter(|row| row.len() >= 2).count() as u64,
            );
        }
        return None;
    }
    set_partition_supports(model).map(|mut supports| {
        supports.extend(conflict_cliques(model));
        supports
    })
}

/// Select exact AMO inequalities, excluding equality rows already owned by GUB.
fn prepare_amo_rows(
    model: &Model,
    mode: SearchMode,
    policy: AmoPolicy,
) -> Vec<crate::cardinality_branch::UnitAmoRow> {
    if mode.cheap || !matches!(policy, AmoPolicy::Eligible) {
        return Vec::new();
    }
    crate::cardinality_branch::unit_amo_rows(model)
        .into_iter()
        .filter(|amo| {
            let (_, lower, upper) = model.row(Row(amo.row as u32));
            model
                .row_lb_exact(amo.row, lower)
                .zip(model.row_ub_exact(amo.row, upper))
                .is_none_or(|(true_lower, true_upper)| true_lower != true_upper)
        })
        .collect()
}

fn trace_amo_branching(state: AmoTraceState) {
    if !crate::debug_flags::milp_debug_flags().trace {
        return;
    }
    match state {
        AmoTraceState::Inactive => {}
        AmoTraceState::DynamicOrbitopeOwned => {
            eprintln!("--trace amo-multiway: declined (dynamic orbitope owns branch state)");
        }
        AmoTraceState::Armed(rows) => {
            eprintln!("--trace amo-multiway: armed ({rows} exact AMO inequalities)");
        }
    }
}
