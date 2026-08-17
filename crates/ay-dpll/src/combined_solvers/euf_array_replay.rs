// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compact, reason-grouped persistence for EUF-to-array notifications.
//!
//! A large AUFLIA component can contribute hundreds of thousands of replay
//! edges while using only hundreds of distinct SAT-visible reason vectors.
//! Storing the reason on every edge both multiplies memory and makes every
//! validity pass re-read millions of literals. This module stores each exact
//! reason once, validates once per stable assignment epoch, and materializes a
//! deterministic minimum-root spanning forest of the active edge graph.

use std::sync::Arc;

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{TermId, TheoryLit};

mod forest;
#[cfg(test)]
mod tests;

#[cfg(test)]
use forest::find;
use forest::{
    activate_literal_groups, build_active_forest, extend_active_forest, initialize_missing,
};

type EndpointPair = (TermId, TermId);
type GroupIndex = u32;
type EdgeIndex = u32;

#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct EufArrayNotifyReplayEdge {
    pub(crate) target: TermId,
    pub(crate) source: TermId,
    pub(crate) reason: Vec<TheoryLit>,
}

#[cfg(test)]
impl EufArrayNotifyReplayEdge {
    pub(crate) fn new(target: TermId, source: TermId, mut reason: Vec<TheoryLit>) -> Self {
        canonicalize_reason(&mut reason);
        Self {
            target,
            source,
            reason,
        }
    }
}

#[derive(Clone, Debug)]
struct ReplayGroup {
    reason: Arc<[TheoryLit]>,
    edges: Vec<EndpointPair>,
    edge_set: DetHashSet<EndpointPair>,
}

impl ReplayGroup {
    fn new(reason: Arc<[TheoryLit]>) -> Self {
        Self {
            reason,
            edges: Vec::new(),
            edge_set: DetHashSet::default(),
        }
    }
}

/// Exact replay relation with one shared allocation per distinct reason.
///
/// `order` records first occurrence, so traversal is deterministic without a
/// repeated global sort. Every insertion is exact-deduplicated within its
/// reason group. Clones share immutable reason allocations through `Arc` and
/// clone only endpoint pairs and compact indices.
#[derive(Clone, Debug, Default)]
pub(crate) struct EufArrayNotifyReplayState {
    groups: Vec<ReplayGroup>,
    group_by_reason: DetHashMap<Arc<[TheoryLit]>, GroupIndex>,
    order: Vec<(GroupIndex, EdgeIndex)>,
    groups_by_literal: DetHashMap<TheoryLit, Vec<GroupIndex>>,
    capacity_exhausted: bool,
}

impl EufArrayNotifyReplayState {
    pub(crate) fn len(&self) -> usize {
        self.order.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.order.is_empty()
    }

    pub(crate) fn clear(&mut self) {
        self.groups.clear();
        self.group_by_reason.clear();
        self.order.clear();
        self.groups_by_literal.clear();
        self.capacity_exhausted = false;
    }

    pub(crate) fn insert(
        &mut self,
        target: TermId,
        source: TermId,
        mut reason: Vec<TheoryLit>,
    ) -> bool {
        canonicalize_reason(&mut reason);
        self.insert_shared(target, source, Arc::from(reason))
    }

    fn insert_shared(&mut self, target: TermId, source: TermId, reason: Arc<[TheoryLit]>) -> bool {
        if target == source || reason.is_empty() {
            return false;
        }
        let Some(group_idx) = self.ensure_group(reason) else {
            return false;
        };
        self.insert_pair(group_idx, (target, source))
    }

    fn ensure_group(&mut self, reason: Arc<[TheoryLit]>) -> Option<GroupIndex> {
        if let Some(&idx) = self.group_by_reason.get(reason.as_ref()) {
            return Some(idx);
        }
        let Some(idx) = compact_index(self.groups.len()) else {
            self.capacity_exhausted = true;
            return None;
        };
        self.group_by_reason.insert(reason.clone(), idx);
        for &lit in reason.iter() {
            self.groups_by_literal.entry(lit).or_default().push(idx);
        }
        self.groups.push(ReplayGroup::new(reason));
        Some(idx)
    }

    fn insert_pair(&mut self, group_idx: GroupIndex, pair: EndpointPair) -> bool {
        let group = &self.groups[group_idx as usize];
        if group.edge_set.contains(&pair) {
            return false;
        }
        let Some(edge_idx) = compact_index(group.edges.len()) else {
            self.capacity_exhausted = true;
            return false;
        };
        let group = &mut self.groups[group_idx as usize];
        group.edge_set.insert(pair);
        group.edges.push(pair);
        self.order.push((group_idx, edge_idx));
        true
    }

    #[cfg(test)]
    pub(crate) fn from_edges(edges: &[EufArrayNotifyReplayEdge]) -> Self {
        let mut state = Self::default();
        for edge in edges {
            state.insert(edge.target, edge.source, edge.reason.clone());
        }
        state
    }

    #[cfg(test)]
    pub(crate) fn to_edges(&self) -> Vec<EufArrayNotifyReplayEdge> {
        self.order
            .iter()
            .map(|&(group_idx, edge_idx)| {
                let group = &self.groups[group_idx as usize];
                let (target, source) = group.edges[edge_idx as usize];
                EufArrayNotifyReplayEdge {
                    target,
                    source,
                    reason: group.reason.to_vec(),
                }
            })
            .collect()
    }

    /// Keep whole exact-reason groups. The predicate is evaluated once per
    /// group, never once per edge.
    pub(crate) fn retain_reason_groups(&mut self, mut keep: impl FnMut(&[TheoryLit]) -> bool) {
        let old_groups = std::mem::take(&mut self.groups);
        let old_order = std::mem::take(&mut self.order);
        self.group_by_reason.clear();
        self.groups_by_literal.clear();

        let mut remap: Vec<Option<GroupIndex>> = vec![None; old_groups.len()];
        for (old_idx, group) in old_groups.into_iter().enumerate() {
            if !keep(group.reason.as_ref()) {
                continue;
            }
            let Some(new_idx) = compact_index(self.groups.len()) else {
                self.capacity_exhausted = true;
                break;
            };
            remap[old_idx] = Some(new_idx);
            self.group_by_reason.insert(group.reason.clone(), new_idx);
            for &lit in group.reason.iter() {
                self.groups_by_literal.entry(lit).or_default().push(new_idx);
            }
            self.groups.push(group);
        }
        self.order = old_order
            .into_iter()
            .filter_map(|(old_group, edge_idx)| {
                remap[old_group as usize].map(|new_group| (new_group, edge_idx))
            })
            .collect();
        self.sort_order_canonical();
    }

    /// Append valid groups from `other`, preserving both states' deterministic
    /// first-occurrence order and exact-deduplicating endpoint pairs.
    pub(crate) fn extend_valid_from(
        &mut self,
        other: &Self,
        mut keep: impl FnMut(&[TheoryLit]) -> bool,
    ) {
        self.capacity_exhausted |= other.capacity_exhausted;
        let mut remap: Vec<Option<GroupIndex>> = vec![None; other.groups.len()];
        for (other_idx, group) in other.groups.iter().enumerate() {
            if keep(group.reason.as_ref()) {
                remap[other_idx] = self.ensure_group(group.reason.clone());
            }
        }
        let mut other_order = other.order.clone();
        other_order.sort_unstable_by_key(|&(group_idx, edge_idx)| {
            let group = &other.groups[group_idx as usize];
            let (target, source) = group.edges[edge_idx as usize];
            (group.reason.len(), target.0, source.0)
        });
        for (other_group, edge_idx) in other_order {
            if let Some(group_idx) = remap[other_group as usize] {
                self.insert_pair(
                    group_idx,
                    other.groups[other_group as usize].edges[edge_idx as usize],
                );
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn group_count(&self) -> usize {
        self.groups.len()
    }

    pub(crate) fn capacity_exhausted(&self) -> bool {
        self.capacity_exhausted
    }

    fn sort_order_canonical(&mut self) {
        let groups = &self.groups;
        self.order.sort_unstable_by_key(|&(group_idx, edge_idx)| {
            let group = &groups[group_idx as usize];
            let (target, source) = group.edges[edge_idx as usize];
            (group.reason.len(), target.0, source.0)
        });
    }
}

/// Assignment-derived replay cache. Invalidations are explicit rather than
/// inferred from wrapping counters, so no generation collision can make stale
/// state observable. The retained `forest` allocation is cleared whenever
/// `initialized` becomes false.
#[derive(Debug, Default)]
pub(crate) struct EufArrayNotifyReplayCache {
    initialized: bool,
    processed_imported: usize,
    processed_local: usize,
    applied_forest: usize,
    forest: Vec<EndpointPair>,
    imported_missing: Vec<u32>,
    local_missing: Vec<u32>,
    contradictory_overwrite: bool,
    #[cfg(test)]
    forest_rebuilds: usize,
}

impl EufArrayNotifyReplayCache {
    /// Add one normalized, SAT-visible literal. DPLL assignments are monotone
    /// inside a scope: reassignment happens only after `pop`, which calls
    /// `invalidate_assignment`. Only exact-reason groups mentioning `lit` are
    /// touched; a group is admitted once its final missing literal arrives.
    pub(crate) fn assignment_added(
        &mut self,
        lit: TheoryLit,
        imported: &EufArrayNotifyReplayState,
        local: &EufArrayNotifyReplayState,
        parent: &mut DetHashMap<TermId, TermId>,
    ) {
        if !self.initialized {
            return;
        }
        activate_literal_groups(
            imported,
            &mut self.imported_missing,
            lit,
            parent,
            &mut self.forest,
        );
        activate_literal_groups(
            local,
            &mut self.local_missing,
            lit,
            parent,
            &mut self.forest,
        );
    }

    pub(crate) fn contradictory_overwrite(&mut self) {
        self.contradictory_overwrite = true;
        self.invalidate_assignment_state();
    }

    pub(crate) fn has_contradictory_overwrite(&self) -> bool {
        self.contradictory_overwrite
    }

    pub(crate) fn invalidate_assignment(&mut self) {
        self.contradictory_overwrite = false;
        self.invalidate_assignment_state();
    }

    fn invalidate_assignment_state(&mut self) {
        self.initialized = false;
        self.processed_imported = 0;
        self.processed_local = 0;
        self.applied_forest = 0;
        self.forest.clear();
        self.imported_missing.clear();
        self.local_missing.clear();
    }

    pub(crate) fn reset(&mut self) {
        *self = Self::default();
    }

    pub(crate) fn is_logically_empty(&self) -> bool {
        self.forest.is_empty()
            && self.applied_forest == 0
            && !self.initialized
            && !self.contradictory_overwrite
    }

    pub(crate) fn ensure_forest(
        &mut self,
        imported: &EufArrayNotifyReplayState,
        local: &EufArrayNotifyReplayState,
        assignments: &DetHashMap<TermId, bool>,
        parent: &mut DetHashMap<TermId, TermId>,
    ) {
        if !self.initialized
            || self.processed_imported > imported.len()
            || self.processed_local > local.len()
        {
            self.forest.clear();
            self.imported_missing = initialize_missing(imported, assignments);
            self.local_missing = initialize_missing(local, assignments);
            build_active_forest(
                imported,
                local,
                &self.imported_missing,
                &self.local_missing,
                parent,
                &mut self.forest,
            );
            self.initialized = true;
            self.processed_imported = imported.len();
            self.processed_local = local.len();
            self.applied_forest = 0;
            #[cfg(test)]
            {
                self.forest_rebuilds += 1;
            }
            return;
        }

        if self.processed_imported < imported.len() || self.processed_local < local.len() {
            extend_active_forest(
                imported,
                self.processed_imported,
                local,
                self.processed_local,
                assignments,
                &mut self.imported_missing,
                &mut self.local_missing,
                parent,
                &mut self.forest,
            );
            self.processed_imported = imported.len();
            self.processed_local = local.len();
        }
    }

    pub(crate) fn needs_application(&self) -> bool {
        self.applied_forest < self.forest.len()
    }

    pub(crate) fn unapplied_forest(&self) -> &[EndpointPair] {
        &self.forest[self.applied_forest..]
    }

    pub(crate) fn mark_applied(&mut self) {
        self.applied_forest = self.forest.len();
    }

    #[cfg(test)]
    pub(crate) fn forest_rebuilds(&self) -> usize {
        self.forest_rebuilds
    }
}

fn canonicalize_reason(reason: &mut Vec<TheoryLit>) {
    reason.sort_by_key(|lit| (lit.term.0, lit.value));
    reason.dedup_by_key(|lit| (lit.term, lit.value));
}

fn compact_index(index: usize) -> Option<u32> {
    u32::try_from(index).ok()
}
