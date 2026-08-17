// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn find(parent: &mut DetHashMap<TermId, TermId>, term: TermId) -> TermId {
    let current = match parent.get(&term).copied() {
        Some(current) => current,
        None => {
            parent.insert(term, term);
            return term;
        }
    };
    if current == term {
        return term;
    }
    let root = find(parent, current);
    parent.insert(term, root);
    root
}

fn admit_forest_edge(
    parent: &mut DetHashMap<TermId, TermId>,
    forest: &mut Vec<EndpointPair>,
    lhs: TermId,
    rhs: TermId,
) {
    let lhs_root = find(parent, lhs);
    let rhs_root = find(parent, rhs);
    if lhs_root == rhs_root {
        return;
    }
    let pair = if lhs_root <= rhs_root {
        (lhs_root, rhs_root)
    } else {
        (rhs_root, lhs_root)
    };
    parent.insert(pair.1, pair.0);
    forest.push(pair);
}

pub(super) fn build_active_forest(
    imported: &EufArrayNotifyReplayState,
    local: &EufArrayNotifyReplayState,
    imported_missing: &[u32],
    local_missing: &[u32],
    parent: &mut DetHashMap<TermId, TermId>,
    forest: &mut Vec<EndpointPair>,
) {
    for &(group_idx, edge_idx) in &imported.order {
        if imported_missing[group_idx as usize] == 0 {
            let (lhs, rhs) = imported.groups[group_idx as usize].edges[edge_idx as usize];
            admit_forest_edge(parent, forest, lhs, rhs);
        }
    }
    for &(group_idx, edge_idx) in &local.order {
        if local_missing[group_idx as usize] == 0 {
            let (lhs, rhs) = local.groups[group_idx as usize].edges[edge_idx as usize];
            admit_forest_edge(parent, forest, lhs, rhs);
        }
    }
}

pub(super) fn extend_active_forest(
    imported: &EufArrayNotifyReplayState,
    imported_start: usize,
    local: &EufArrayNotifyReplayState,
    local_start: usize,
    assignments: &DetHashMap<TermId, bool>,
    imported_missing: &mut Vec<u32>,
    local_missing: &mut Vec<u32>,
    parent: &mut DetHashMap<TermId, TermId>,
    forest: &mut Vec<EndpointPair>,
) {
    extend_missing(imported, assignments, imported_missing);
    extend_missing(local, assignments, local_missing);
    for &(group_idx, edge_idx) in imported.order.iter().skip(imported_start) {
        if imported_missing[group_idx as usize] == 0 {
            let (lhs, rhs) = imported.groups[group_idx as usize].edges[edge_idx as usize];
            admit_forest_edge(parent, forest, lhs, rhs);
        }
    }
    for &(group_idx, edge_idx) in local.order.iter().skip(local_start) {
        if local_missing[group_idx as usize] == 0 {
            let (lhs, rhs) = local.groups[group_idx as usize].edges[edge_idx as usize];
            admit_forest_edge(parent, forest, lhs, rhs);
        }
    }
}

pub(super) fn initialize_missing(
    state: &EufArrayNotifyReplayState,
    assignments: &DetHashMap<TermId, bool>,
) -> Vec<u32> {
    state
        .groups
        .iter()
        .map(|group| {
            group
                .reason
                .iter()
                .filter(|lit| assignments.get(&lit.term) != Some(&lit.value))
                .count() as u32
        })
        .collect()
}

fn extend_missing(
    state: &EufArrayNotifyReplayState,
    assignments: &DetHashMap<TermId, bool>,
    missing: &mut Vec<u32>,
) {
    for group in &state.groups[missing.len()..] {
        missing.push(
            group
                .reason
                .iter()
                .filter(|lit| assignments.get(&lit.term) != Some(&lit.value))
                .count() as u32,
        );
    }
}

pub(super) fn activate_literal_groups(
    state: &EufArrayNotifyReplayState,
    missing: &mut [u32],
    lit: TheoryLit,
    parent: &mut DetHashMap<TermId, TermId>,
    forest: &mut Vec<EndpointPair>,
) {
    let Some(groups) = state.groups_by_literal.get(&lit) else {
        return;
    };
    for &group_idx in groups {
        let group_idx = group_idx as usize;
        if group_idx >= missing.len() || missing[group_idx] == 0 {
            continue;
        }
        missing[group_idx] -= 1;
        if missing[group_idx] == 0 {
            for &(lhs, rhs) in &state.groups[group_idx].edges {
                admit_forest_edge(parent, forest, lhs, rhs);
            }
        }
    }
}
