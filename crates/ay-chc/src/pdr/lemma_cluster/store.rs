// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::pattern::{instantiate_pattern_int, PatternExtractionResult};
use super::*;

/// Maximum clusters per predicate before eviction.
///
/// Bounds cluster storage to prevent unbounded growth and O(#clusters) linear
/// scan in `add_blocking_cube()`. Initial value matches Z3 Spacer's MAX_CLUSTERS.
/// Reference: `reference/z3/src/muz/spacer/spacer_cluster.cpp:34-36`
pub(crate) const MAX_CLUSTERS_PER_PREDICATE: usize = 5;

/// Per-predicate storage of lemma clusters.
#[derive(Debug, Default)]
pub(crate) struct ClusterStore {
    /// Clusters indexed by predicate
    clusters: FxHashMap<PredicateId, Vec<LemmaCluster>>,
    /// Operation counters for diagnostics
    counters: ClusterCounters,
}

impl ClusterStore {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Get all clusters for a predicate.
    pub(crate) fn get_clusters(&self, pred: PredicateId) -> Option<&[LemmaCluster]> {
        self.clusters.get(&pred).map(Vec::as_slice)
    }

    /// Get mutable reference to clusters for a predicate.
    pub(crate) fn get_clusters_mut(&mut self, pred: PredicateId) -> Option<&mut Vec<LemmaCluster>> {
        self.clusters.get_mut(&pred)
    }

    /// Try to add a blocking cube to an existing cluster, or create a new one.
    pub(crate) fn add_blocking_cube(
        &mut self,
        predicate: PredicateId,
        blocking_cube: &ChcExpr,
        level: usize,
    ) -> Option<usize> {
        self.counters.calls += 1;
        let blocking_cube = normalize_cube(blocking_cube);
        let clusters = self.clusters.entry(predicate).or_default();

        for (idx, cluster) in clusters.iter_mut().enumerate() {
            let Some(values) =
                match_pattern(&cluster.pattern, &cluster.pattern_vars, &blocking_cube)
            else {
                continue;
            };

            if cluster.members.len() == 1 && !cluster.pattern_vars.is_empty() {
                let singleton = cluster.clone();
                if let Some(refined) =
                    try_refine_singleton_cluster(&singleton, &blocking_cube, level)
                {
                    *cluster = refined;
                    self.counters.singleton_refined += 1;
                    self.counters.hits += 1;
                    self.counters.debug_assert_consistency();
                    return Some(idx);
                }
            }

            cluster.add_member(LemmaInstance::new(level, values));
            self.counters.hits += 1;
            self.counters.debug_assert_consistency();
            return Some(idx);
        }

        self.counters.misses += 1;
        self.counters.debug_assert_consistency();

        if let Some(neighbour_cluster) = try_create_cluster_with_neighbours(
            predicate,
            &blocking_cube,
            level,
            clusters.as_slice(),
        ) {
            self.counters.neighbour_clusters_created += 1;

            if clusters.len() >= MAX_CLUSTERS_PER_PREDICATE {
                let victim_idx = Self::select_eviction_victim(clusters);
                let victim_ineligible = !clusters[victim_idx].is_eligible();
                clusters.remove(victim_idx);
                self.counters.clusters_evicted += 1;
                if victim_ineligible {
                    self.counters.evicted_ineligible += 1;
                }
                self.counters.debug_assert_consistency();
            }

            let idx = clusters.len();
            clusters.push(neighbour_cluster);
            return Some(idx);
        }

        if clusters.len() >= MAX_CLUSTERS_PER_PREDICATE {
            let victim_idx = Self::select_eviction_victim(clusters);
            let victim_ineligible = !clusters[victim_idx].is_eligible();
            clusters.remove(victim_idx);
            self.counters.clusters_evicted += 1;
            if victim_ineligible {
                self.counters.evicted_ineligible += 1;
            }
            self.counters.debug_assert_consistency();
        }

        let PatternExtractionResult {
            pattern,
            pattern_vars,
            subst_values,
        } = extract_pattern(&blocking_cube);
        let mut new_cluster = LemmaCluster::new(predicate, pattern, pattern_vars);
        new_cluster.add_member(LemmaInstance::new(level, subst_values));
        let idx = clusters.len();
        clusters.push(new_cluster);
        Some(idx)
    }

    fn select_eviction_victim(clusters: &[LemmaCluster]) -> usize {
        debug_assert!(!clusters.is_empty());
        clusters
            .iter()
            .enumerate()
            .min_by_key(|(idx, c)| (u8::from(c.is_eligible()), c.size(), c.gas, *idx))
            .map_or(0, |(idx, _)| idx)
    }
}

#[cfg(test)]
impl ClusterStore {
    /// Get cluster statistics (test-only inspection).
    pub(crate) fn stats(&self) -> ClusterStats {
        let mut total_clusters = 0;
        let mut total_members = 0;
        let mut max_cluster_size = 0;

        for clusters in self.clusters.values() {
            total_clusters += clusters.len();
            for cluster in clusters {
                total_members += cluster.size();
                max_cluster_size = max_cluster_size.max(cluster.size());
            }
        }

        ClusterStats {
            total_clusters,
            total_members,
            max_cluster_size,
        }
    }

    /// Get operation counters snapshot (test-only inspection).
    pub(crate) fn counters(&self) -> ClusterCounters {
        self.counters
    }
}

fn try_create_cluster_with_neighbours(
    predicate: PredicateId,
    new_cube: &ChcExpr,
    new_level: usize,
    clusters: &[LemmaCluster],
) -> Option<LemmaCluster> {
    const MAX_NEIGHBOURS: usize = 8;

    let mut neighbours: Vec<(ChcExpr, usize)> = Vec::new();
    for cluster in clusters {
        if !cluster.pattern_vars.iter().all(|v| v.sort == ChcSort::Int) {
            continue;
        }
        for member in &cluster.members {
            let cube = instantiate_pattern_int(
                &cluster.pattern,
                &cluster.pattern_vars,
                &member.subst_values,
            );
            if cube == *new_cube {
                continue;
            }
            if !are_neighbours_int_only(new_cube, &cube) {
                continue;
            }
            neighbours.push((cube, member.level));
            if neighbours.len() >= MAX_NEIGHBOURS {
                break;
            }
        }
        if neighbours.len() >= MAX_NEIGHBOURS {
            break;
        }
    }

    if neighbours.is_empty() {
        return None;
    }

    let mut candidates: Vec<(ChcExpr, Vec<ChcVar>)> = Vec::new();
    for (cube, _) in &neighbours {
        let au = anti_unify(new_cube, cube);
        if au.pattern_vars.is_empty() {
            continue;
        }
        if !au
            .pattern_vars
            .iter()
            .all(|v| v.sort == ChcSort::Int || matches!(v.sort, ChcSort::BitVec(_)))
        {
            continue;
        }
        if !au.is_numeric_int_substitution() {
            continue;
        }
        candidates.push((au.pattern, au.pattern_vars));
    }

    for (pattern, pattern_vars) in candidates {
        let mut member_substs: Vec<(usize, Vec<i128>)> = Vec::with_capacity(neighbours.len());
        let mut ok = true;
        for (cube, lvl) in &neighbours {
            let Some(vals) = match_pattern(&pattern, &pattern_vars, cube) else {
                ok = false;
                break;
            };
            member_substs.push((*lvl, vals));
        }
        if !ok {
            continue;
        }

        let Some(new_vals) = match_pattern(&pattern, &pattern_vars, new_cube) else {
            continue;
        };

        let mut cluster = LemmaCluster::new(predicate, pattern, pattern_vars);
        for (lvl, vals) in member_substs {
            cluster.add_member(LemmaInstance::new(lvl, vals));
        }
        cluster.add_member(LemmaInstance::new(new_level, new_vals));

        if cluster.size() < 2 {
            continue;
        }
        return Some(cluster);
    }

    None
}

fn try_refine_singleton_cluster(
    singleton: &LemmaCluster,
    new_cube: &ChcExpr,
    new_level: usize,
) -> Option<LemmaCluster> {
    debug_assert_eq!(singleton.members.len(), 1);
    debug_assert!(
        !singleton.pattern_vars.is_empty(),
        "caller must ensure singleton has pattern vars"
    );

    let existing_member = singleton.members.front().cloned()?;
    let existing_cube = instantiate_pattern_int(
        &singleton.pattern,
        &singleton.pattern_vars,
        &existing_member.subst_values,
    );

    let au = anti_unify(&existing_cube, new_cube);
    if au.pattern_vars.is_empty() || au.pattern_vars.len() >= singleton.pattern_vars.len() {
        return None;
    }
    if !au
        .pattern_vars
        .iter()
        .all(|v| v.sort == ChcSort::Int || matches!(v.sort, ChcSort::BitVec(_)))
    {
        return None;
    }
    if !au.is_numeric_int_substitution() {
        return None;
    }

    let existing_vals = match_pattern(&au.pattern, &au.pattern_vars, &existing_cube)?;
    let new_vals = match_pattern(&au.pattern, &au.pattern_vars, new_cube)?;

    let mut cluster = LemmaCluster::new(singleton.predicate, au.pattern, au.pattern_vars);
    cluster.add_member(LemmaInstance::new(existing_member.level, existing_vals));
    cluster.add_member(LemmaInstance::new(new_level, new_vals));
    Some(cluster)
}

/// Statistics about cluster store (test-only).
#[cfg(test)]
#[derive(Debug, Default, Clone)]
pub(crate) struct ClusterStats {
    pub(crate) total_clusters: usize,
    pub(crate) total_members: usize,
    pub(crate) max_cluster_size: usize,
}

/// Counters for ClusterStore operations.
#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct ClusterCounters {
    /// Total calls to `add_blocking_cube()`
    pub(crate) calls: u64,
    /// Calls where an existing cluster matched
    pub(crate) hits: u64,
    /// Calls where a new cluster was created
    pub(crate) misses: u64,
    /// New clusters created via neighbour scan + anti-unification.
    pub(crate) neighbour_clusters_created: u64,
    /// Count of singleton clusters refined via anti-unification.
    pub(crate) singleton_refined: u64,
    /// Clusters evicted due to capacity limit
    pub(crate) clusters_evicted: u64,
    /// Evicted clusters that were ineligible (size < 2 or gas == 0)
    pub(crate) evicted_ineligible: u64,
}

impl ClusterCounters {
    #[inline]
    pub(crate) fn debug_assert_consistency(&self) {
        let accounted = self.hits.checked_add(self.misses);
        debug_assert!(
            accounted == Some(self.calls),
            "BUG: ClusterCounters: hits({}) + misses({}) overflow or mismatch calls({})",
            self.hits,
            self.misses,
            self.calls,
        );
        debug_assert!(
            self.evicted_ineligible <= self.clusters_evicted,
            "BUG: ClusterCounters: evicted_ineligible({}) > clusters_evicted({})",
            self.evicted_ineligible,
            self.clusters_evicted,
        );
    }
}
