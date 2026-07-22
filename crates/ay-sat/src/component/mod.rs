// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Formula component decomposition.
//!
//! Detects when a SAT formula splits into independent subproblems (connected
//! components) sharing no variables. Each component can be solved independently:
//! SAT iff all components are SAT, UNSAT iff any component is UNSAT.
//!
//! Algorithm: Union-Find with path compression and union-by-rank over variables.
//! For each active irredundant clause, union all active variables in that clause.
//! The resulting connected components are the independent subproblems.
//!
//! Reference: CryptoMiniSat comphandler.cpp / compfinder.cpp (removed from
//! modern CMS, but the algorithm is standard). Neither CaDiCaL nor Kissat
//! implements this.
//!
//! Complexity: O(clauses * alpha(vars)) where alpha is the inverse Ackermann
//! function (effectively O(clauses) in practice).

#[cfg(test)]
mod tests;

use crate::literal::Literal;

/// Union-Find data structure with path compression and union-by-rank.
///
/// Provides near-O(1) amortized `find` and `union` operations via:
/// - Path halving (iterative, avoids stack overflow on large inputs)
/// - Union-by-rank (keeps tree depth logarithmic)
#[derive(Debug, Clone)]
pub(crate) struct UnionFind {
    parent: Vec<u32>,
    rank: Vec<u8>,
}

impl UnionFind {
    /// Create a new union-find with `n` elements, each in its own set.
    pub(crate) fn new(n: usize) -> Self {
        Self {
            parent: (0..n as u32).collect(),
            rank: vec![0; n],
        }
    }

    /// Find the representative of the set containing `x`.
    ///
    /// Uses iterative path halving for O(alpha(n)) amortized time without
    /// risk of stack overflow on large variable counts.
    pub(crate) fn find(&mut self, mut x: usize) -> usize {
        // Path halving: make every other node point to its grandparent.
        while self.parent[x] as usize != x {
            let grandparent = self.parent[self.parent[x] as usize];
            self.parent[x] = grandparent;
            x = grandparent as usize;
        }
        x
    }

    /// Union the sets containing `x` and `y`.
    ///
    /// Returns `true` if they were in different sets (merge happened),
    /// `false` if already in the same set.
    pub(crate) fn union(&mut self, x: usize, y: usize) -> bool {
        let root_x = self.find(x);
        let root_y = self.find(y);
        if root_x == root_y {
            return false;
        }
        // Union by rank: attach shorter tree under taller tree.
        match self.rank[root_x].cmp(&self.rank[root_y]) {
            std::cmp::Ordering::Less => {
                self.parent[root_x] = root_y as u32;
            }
            std::cmp::Ordering::Greater => {
                self.parent[root_y] = root_x as u32;
            }
            std::cmp::Ordering::Equal => {
                self.parent[root_y] = root_x as u32;
                self.rank[root_x] += 1;
            }
        }
        true
    }
}

/// Result of component analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ComponentResult {
    /// Number of connected components among active variables.
    pub(crate) num_components: usize,
    /// Sizes of each component, sorted descending (largest first).
    pub(crate) component_sizes: Vec<usize>,
    /// Whether decomposition would be beneficial: more than one component
    /// with at least `MIN_COMPONENT_SIZE` variables each.
    pub(crate) beneficial: bool,
}

/// Statistics for formula component decomposition.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct ComponentStats {
    /// Number of times component analysis was run.
    pub runs: u64,
    /// Total number of multi-component formulas detected.
    pub decomposable_found: u64,
    /// Maximum number of components found in any single run.
    pub max_components: u64,
    /// Number of times decompose-and-solve was attempted.
    pub decompose_solves: u64,
    /// Number of decompose-and-solve results that were SAT.
    pub decompose_sat: u64,
    /// Number of decompose-and-solve results that were UNSAT.
    pub decompose_unsat: u64,
}

/// Detailed component decomposition result with variable-to-component mapping.
#[derive(Debug, Clone)]
pub(crate) struct DecompositionMap {
    /// Component ID for each variable index. `u32::MAX` for inactive/unseen variables.
    pub(crate) var_component: Vec<u32>,
    /// Variables belonging to each component.
    /// `components[i]` is the list of original variable indices in component `i`.
    pub(crate) components: Vec<Vec<usize>>,
    /// Number of components (same as `components.len()`).
    pub(crate) num_components: usize,
}

/// Minimum component size to consider decomposition beneficial.
///
/// Components smaller than this are trivially solvable by BCP/preprocessing
/// and do not justify the overhead of sub-solver construction.
const MIN_COMPONENT_SIZE: usize = 10;

/// Find connected components of the variable interaction graph.
///
/// Scans all provided clauses, unioning variables that co-occur in the same
/// clause. Only variables for which `is_active_var(var_index)` returns `true`
/// are considered (allowing the caller to exclude assigned, eliminated, or
/// substituted variables).
///
/// # Arguments
/// * `num_vars` - Total number of variables in the formula
/// * `clauses` - Iterator over clause literal slices (typically active irredundant clauses)
/// * `is_active_var` - Predicate: `true` if the variable should participate in component analysis
pub(crate) fn find_components<'a>(
    num_vars: usize,
    clauses: impl Iterator<Item = &'a [Literal]>,
    is_active_var: impl Fn(usize) -> bool,
) -> ComponentResult {
    if num_vars == 0 {
        return ComponentResult {
            num_components: 0,
            component_sizes: Vec::new(),
            beneficial: false,
        };
    }

    let mut uf = UnionFind::new(num_vars);
    // Track which variables actually appear in clauses.
    let mut seen = vec![false; num_vars];

    for clause in clauses {
        let mut first_active: Option<usize> = None;
        for &lit in clause {
            let vi = lit.variable().index();
            if vi >= num_vars || !is_active_var(vi) {
                continue;
            }
            seen[vi] = true;
            if let Some(first) = first_active {
                uf.union(first, vi);
            } else {
                first_active = Some(vi);
            }
        }
    }

    // Count component sizes (only for variables that appeared in clauses).
    let mut sizes_by_root = vec![0usize; num_vars];
    for (vi, &was_seen) in seen.iter().enumerate().take(num_vars) {
        if !was_seen {
            continue;
        }
        let root = uf.find(vi);
        sizes_by_root[root] += 1;
    }

    let mut component_sizes: Vec<usize> = sizes_by_root.into_iter().filter(|&s| s > 0).collect();
    component_sizes.sort_unstable_by(|a, b| b.cmp(a));

    let num_components = component_sizes.len();
    let beneficial = component_sizes
        .iter()
        .filter(|&&size| size >= MIN_COMPONENT_SIZE)
        .count()
        > 1;

    ComponentResult {
        num_components,
        component_sizes,
        beneficial,
    }
}

/// Find connected components with full variable-to-component mapping.
///
/// Like `find_components`, but also returns a `DecompositionMap` with the
/// variable-to-component assignment needed to construct independent sub-solvers.
pub(crate) fn find_components_detailed<'a>(
    num_vars: usize,
    clauses: impl Iterator<Item = &'a [Literal]>,
    is_active_var: impl Fn(usize) -> bool,
) -> (ComponentResult, DecompositionMap) {
    if num_vars == 0 {
        return (
            ComponentResult {
                num_components: 0,
                component_sizes: Vec::new(),
                beneficial: false,
            },
            DecompositionMap {
                var_component: Vec::new(),
                components: Vec::new(),
                num_components: 0,
            },
        );
    }

    let mut uf = UnionFind::new(num_vars);
    let mut seen = vec![false; num_vars];

    for clause in clauses {
        let mut first_active: Option<usize> = None;
        for &lit in clause {
            let vi = lit.variable().index();
            if vi >= num_vars || !is_active_var(vi) {
                continue;
            }
            seen[vi] = true;
            if let Some(first) = first_active {
                uf.union(first, vi);
            } else {
                first_active = Some(vi);
            }
        }
    }

    // Map UF roots to dense component IDs.
    let mut root_to_component = vec![u32::MAX; num_vars];
    let mut var_component = vec![u32::MAX; num_vars];
    let mut next_id: u32 = 0;

    for (vi, &was_seen) in seen.iter().enumerate().take(num_vars) {
        if !was_seen {
            continue;
        }
        let root = uf.find(vi);
        if root_to_component[root] == u32::MAX {
            root_to_component[root] = next_id;
            next_id += 1;
        }
        var_component[vi] = root_to_component[root];
    }

    let n_comps = next_id as usize;
    let mut components = vec![Vec::new(); n_comps];
    for (vi, &cid) in var_component.iter().enumerate().take(num_vars) {
        if cid != u32::MAX {
            components[cid as usize].push(vi);
        }
    }

    let mut component_sizes: Vec<usize> = components.iter().map(Vec::len).collect();
    component_sizes.sort_unstable_by(|a, b| b.cmp(a));

    let beneficial = component_sizes
        .iter()
        .filter(|&&size| size >= MIN_COMPONENT_SIZE)
        .count()
        > 1;

    (
        ComponentResult {
            num_components: n_comps,
            component_sizes,
            beneficial,
        },
        DecompositionMap {
            var_component,
            components,
            num_components: n_comps,
        },
    )
}
