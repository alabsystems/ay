// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pattern detection: reconstruct high-level constraints from decompositions.
//!
//! FlatZinc decomposes global constraints into primitive constraints. These
//! detection passes reconstruct higher-level constraints (AllDifferent,
//! shifted AllDifferent) from the decomposition, enabling more efficient
//! propagation and SAT encoding.

use std::collections::{BTreeMap as HashMap, BTreeSet as HashSet};

use crate::propagator::Constraint;
use crate::propagators::alldifferent::AllDifferentBounds;
use crate::variable::IntVarId;

use super::CpSatEngine;

impl CpSatEngine {
    /// Detect AllDifferent patterns from PairwiseNeq decompositions.
    ///
    /// FlatZinc decomposes `alldifferent(xs)` into O(n²) `int_ne(x_i, x_j)`
    /// constraints (offset=0). We reconstruct the original AllDifferent by
    /// finding cliques in the neq graph: if n variables are pairwise distinct,
    /// that's an AllDifferent constraint.
    ///
    /// Uses greedy clique detection: sort by degree, greedily extend cliques.
    /// Replaces pairwise neqs with a single AllDifferent constraint that
    /// enables O(n log n) bounds propagation via Hall intervals.
    pub(super) fn detect_alldifferent(&mut self) {
        // Build adjacency for offset-0 PairwiseNeq edges
        let mut neq_edges: HashMap<IntVarId, HashSet<IntVarId>> = HashMap::new();

        for c in &self.constraints {
            if let Constraint::PairwiseNeq { x, y, offset } = c {
                if *offset == 0 {
                    neq_edges.entry(*x).or_default().insert(*y);
                    neq_edges.entry(*y).or_default().insert(*x);
                }
            }
        }

        if neq_edges.is_empty() {
            return;
        }

        // Sort variables by degree (descending) for greedy clique detection
        let mut vars_by_degree: Vec<(IntVarId, usize)> = neq_edges
            .iter()
            .map(|(&v, neighbors)| (v, neighbors.len()))
            .collect();
        vars_by_degree.sort_by(|a, b| b.1.cmp(&a.1));

        let mut used: HashSet<IntVarId> = HashSet::new();
        let mut cliques: Vec<Vec<IntVarId>> = Vec::new();

        for &(seed, _) in &vars_by_degree {
            if used.contains(&seed) {
                continue;
            }
            let seed_neighbors = match neq_edges.get(&seed) {
                Some(n) => n,
                None => continue,
            };

            // Build clique greedily: add variables connected to all current members
            let mut clique = vec![seed];
            let mut candidates: Vec<IntVarId> = seed_neighbors
                .iter()
                .filter(|v| !used.contains(v))
                .copied()
                .collect();
            // Sort candidates by degree (descending) for better cliques
            candidates.sort_by(|a, b| {
                neq_edges
                    .get(b)
                    .map_or(0, HashSet::len)
                    .cmp(&neq_edges.get(a).map_or(0, HashSet::len))
            });

            for cand in candidates {
                let cand_neighbors = match neq_edges.get(&cand) {
                    Some(n) => n,
                    None => continue,
                };
                // Check if cand is connected to all current clique members
                if clique.iter().all(|m| cand_neighbors.contains(m)) {
                    clique.push(cand);
                }
            }

            if clique.len() >= 3 {
                for &v in &clique {
                    used.insert(v);
                }
                cliques.push(clique);
            }
        }

        if cliques.is_empty() {
            return;
        }

        // Remove consumed PairwiseNeq constraints and add AllDifferent
        let mut remove_set: HashSet<usize> = HashSet::new();
        for (i, c) in self.constraints.iter().enumerate() {
            if let Constraint::PairwiseNeq { x, y, offset } = c {
                if *offset == 0 && used.contains(x) && used.contains(y) {
                    for clique in &cliques {
                        if clique.contains(x) && clique.contains(y) {
                            remove_set.insert(i);
                            break;
                        }
                    }
                }
            }
        }

        // Remove in reverse order to preserve indices
        let mut indices: Vec<usize> = remove_set.into_iter().collect();
        indices.sort_unstable();
        for &i in indices.iter().rev() {
            self.constraints.swap_remove(i);
        }

        // Add reconstructed AllDifferent constraints
        for clique in cliques {
            self.constraints.push(Constraint::AllDifferent(clique));
        }
    }

    /// Detect shifted AllDifferent patterns from non-zero-offset PairwiseNeq.
    ///
    /// Queens diagonal constraints decompose as `int_lin_ne([1,-1], [q_i, q_j], i-j)`
    /// producing PairwiseNeq with offset = i-j. If n variables form a complete
    /// clique under a consistent shift assignment, that's `alldiff(q[k] + shift[k])`.
    pub(super) fn detect_shifted_alldifferent(&mut self) {
        let mut edge_set: HashMap<(IntVarId, IntVarId), HashSet<i64>> = HashMap::new();
        let mut var_edges: HashMap<IntVarId, Vec<(IntVarId, i64)>> = HashMap::new();

        for c in &self.constraints {
            if let Constraint::PairwiseNeq { x, y, offset } = c {
                if *offset == 0 {
                    continue;
                }
                var_edges.entry(*x).or_default().push((*y, *offset));
                var_edges.entry(*y).or_default().push((*x, -*offset));
                let (lo, hi, canon) = if *x < *y {
                    (*x, *y, *offset)
                } else {
                    (*y, *x, -*offset)
                };
                edge_set.entry((lo, hi)).or_default().insert(canon);
            }
        }

        if var_edges.is_empty() {
            return;
        }

        let has_edge = |a: IntVarId, b: IntVarId, offset: i64| -> bool {
            let (lo, hi, canon) = if a < b {
                (a, b, offset)
            } else {
                (b, a, -offset)
            };
            edge_set
                .get(&(lo, hi))
                .map_or(false, |s| s.contains(&canon))
        };

        let mut shifted_groups: Vec<(Vec<IntVarId>, Vec<i64>)> = Vec::new();
        let mut consumed: HashSet<(IntVarId, IntVarId, i64)> = HashSet::new();

        let all_vars: Vec<IntVarId> = var_edges.keys().copied().collect();
        for &seed in &all_vars {
            let seed_neighbors = match var_edges.get(&seed) {
                Some(e) => e.clone(),
                None => continue,
            };
            for &(first_nbr, first_offset) in &seed_neighbors {
                if consumed.contains(&(seed, first_nbr, first_offset)) {
                    continue;
                }
                let mut group: HashMap<IntVarId, i64> = HashMap::new();
                group.insert(seed, 0);
                group.insert(first_nbr, -first_offset);

                for &(nbr, offset) in &seed_neighbors {
                    if group.contains_key(&nbr) {
                        continue;
                    }
                    let candidate_shift = -offset;
                    let ok = group
                        .iter()
                        .all(|(&m, &ms)| m == seed || has_edge(m, nbr, ms - candidate_shift));
                    if ok {
                        group.insert(nbr, candidate_shift);
                    }
                }

                if group.len() < 3 {
                    continue;
                }

                let members: Vec<(IntVarId, i64)> = group.iter().map(|(&v, &s)| (v, s)).collect();
                let mut is_clique = true;
                'verify: for i in 0..members.len() {
                    for j in (i + 1)..members.len() {
                        if !has_edge(members[i].0, members[j].0, members[i].1 - members[j].1) {
                            is_clique = false;
                            break 'verify;
                        }
                    }
                }
                if !is_clique {
                    continue;
                }

                for i in 0..members.len() {
                    for j in (i + 1)..members.len() {
                        let (vi, si) = members[i];
                        let (vj, sj) = members[j];
                        consumed.insert((vi, vj, si - sj));
                        consumed.insert((vj, vi, sj - si));
                    }
                }

                let vars: Vec<IntVarId> = members.iter().map(|&(v, _)| v).collect();
                // Negate shifts: the group assigns shift[v] such that the
                // PairwiseNeq offset between vi and vj equals si - sj, i.e.,
                // vi - vj != si - sj. The propagator enforces
                // alldiff(v[k] + s'[k]), meaning vi + s'i != vj + s'j, i.e.,
                // vi - vj != s'j - s'i = -(s'i - s'j). Setting s' = -s gives
                // vi - vj != si - sj, matching the original constraints.
                let shifts: Vec<i64> = members.iter().map(|&(_, s)| -s).collect();
                shifted_groups.push((vars, shifts));
            }
        }

        if shifted_groups.is_empty() {
            return;
        }

        let mut remove_set: HashSet<usize> = HashSet::new();
        for (i, c) in self.constraints.iter().enumerate() {
            if let Constraint::PairwiseNeq { x, y, offset } = c {
                if *offset != 0 && consumed.contains(&(*x, *y, *offset)) {
                    remove_set.insert(i);
                }
            }
        }
        let mut indices: Vec<usize> = remove_set.into_iter().collect();
        indices.sort_unstable();
        for &i in indices.iter().rev() {
            self.constraints.swap_remove(i);
        }

        for (vars, shifts) in shifted_groups {
            // Bounds-consistency propagator on original vars — no auxiliary
            // variables needed, O(n log n) propagation via Lopez-Ortiz
            // union-find in shifted space.
            //
            // AC via aux-var lifting is disabled: LinearLe linking only
            // propagates bounds, not domain holes. AllDifferentAc's
            // build_adjacency sees the full interval [lb, ub] for aux vars,
            // including phantom values not reachable from the original var.
            // This causes incorrect matching/SCC computations → false UNSAT.
            // Re-enabling requires either domain channeling or a native
            // shifted-AllDifferentAc propagator.
            let prop = AllDifferentBounds::new_shifted(vars, shifts);
            self.dirty.push(true);
            self.propagators.push(Box::new(prop));
        }
    }
}
