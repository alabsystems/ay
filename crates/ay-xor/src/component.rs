// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! XOR matrix component splitting via union-find.
//!
//! Partitions XOR constraints into independent connected components, each
//! getting its own `GaussianSolver` instance. Two XOR constraints belong to
//! the same component if they share at least one variable.
//!
//! This dramatically reduces per-row evaluation cost on large XOR systems
//! because Gauss-Jordan elimination is O(n*m*k) where n=rows, m=columns,
//! k=words-per-row. Splitting into small independent matrices reduces both
//! n and m per component.
//!
//! Reference: CryptoMiniSat `matrixfinder.cpp` (MIT license).
//! Source: `reference/cryptominisat/src/matrixfinder.cpp:94-186`

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;

use crate::constraint::XorConstraint;
use crate::VarId;

/// Union-Find (disjoint set) structure for variable partitioning.
///
/// Uses path compression and union-by-rank for near O(1) amortized operations.
struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }

    fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }

    fn union(&mut self, x: usize, y: usize) {
        let rx = self.find(x);
        let ry = self.find(y);
        if rx == ry {
            return;
        }
        match self.rank[rx].cmp(&self.rank[ry]) {
            std::cmp::Ordering::Less => self.parent[rx] = ry,
            std::cmp::Ordering::Greater => self.parent[ry] = rx,
            std::cmp::Ordering::Equal => {
                self.parent[ry] = rx;
                self.rank[rx] += 1;
            }
        }
    }
}

/// Per-component statistics matching CMS `MatrixShape`.
///
/// Reference: `reference/cryptominisat/src/matrixfinder.h:49-68`
#[derive(Debug, Clone)]
pub(crate) struct ComponentStats {
    /// Number of rows (XOR constraints) in this component.
    pub(crate) rows: usize,
    /// Number of columns (unique variables) in this component.
    pub(crate) cols: usize,
    /// Total variable mentions across all XOR constraints. CMS uses this
    /// as the primary sort key (`sum_xor_sizes`).
    pub(crate) sum_xor_sizes: usize,
    /// Matrix density: `sum_xor_sizes / (rows * cols)`.
    /// Used in tests and for diagnostic output (CMS prints this per-matrix).
    #[allow(dead_code)] // Diagnostic: used in tests and debug output
    pub(crate) density: f64,
}

/// A single connected component of XOR constraints.
#[derive(Debug)]
pub(crate) struct XorComponent {
    /// The XOR constraints belonging to this component.
    pub(crate) constraints: Vec<XorConstraint>,
    /// Component statistics for filtering and priority sorting.
    pub(crate) stats: ComponentStats,
}

/// Split XOR constraints into independent connected components.
///
/// Two constraints belong to the same component if they share at least one
/// variable. Uses union-find over variable IDs for O(n * alpha(n)) performance.
///
/// Returns components sorted by `sum_xor_sizes` (largest first), matching CMS's
/// `matrixfinder.cpp:227` sorting by total variable mentions. This prioritizes
/// denser, more interconnected components when applying the `MAX_NUM_MATRICES`
/// cap.
///
/// # Arguments
///
/// * `constraints` - The XOR constraints to partition.
///
/// # Returns
///
/// A vector of `XorComponent`s with per-component statistics. If all
/// constraints share variables, a single component is returned (no
/// splitting benefit).
pub(crate) fn split_components(constraints: &[XorConstraint]) -> Vec<XorComponent> {
    if constraints.is_empty() {
        return Vec::new();
    }

    // Collect all variables and assign dense indices for union-find
    let mut all_vars: Vec<VarId> = constraints
        .iter()
        .flat_map(|c| c.vars.iter().copied())
        .collect();
    all_vars.sort_unstable();
    all_vars.dedup();

    if all_vars.is_empty() {
        // All constraints are empty/tautologies
        return vec![XorComponent {
            constraints: constraints.to_vec(),
            stats: ComponentStats {
                rows: constraints.len(),
                cols: 0,
                sum_xor_sizes: 0,
                density: 0.0,
            },
        }];
    }

    let var_to_idx: HashMap<VarId, usize> =
        all_vars.iter().enumerate().map(|(i, &v)| (v, i)).collect();

    // Union-find: merge variables that appear in the same constraint.
    // CMS `belong_same_matrix` early-exit: skip constraints whose variables
    // are already in the same component, avoiding redundant union operations.
    // Reference: `reference/cryptominisat/src/matrixfinder.cpp:140-141`
    let mut uf = UnionFind::new(all_vars.len());
    for constraint in constraints {
        if constraint.vars.len() < 2 {
            continue;
        }
        // Early exit: if all variables already share the same root, skip.
        let first_idx = var_to_idx[&constraint.vars[0]];
        let first_root = uf.find(first_idx);
        let already_same = constraint.vars[1..]
            .iter()
            .all(|&var| uf.find(var_to_idx[&var]) == first_root);
        if already_same {
            continue;
        }
        for &var in &constraint.vars[1..] {
            let idx = var_to_idx[&var];
            uf.union(first_idx, idx);
        }
    }

    // Group constraints by their component root
    let mut component_map: HashMap<usize, Vec<XorConstraint>> = HashMap::default();
    for constraint in constraints {
        let root = if constraint.vars.is_empty() {
            // Empty constraints (tautologies/conflicts) go to component 0
            // They don't share variables with anything
            usize::MAX
        } else {
            let idx = var_to_idx[&constraint.vars[0]];
            uf.find(idx)
        };
        component_map
            .entry(root)
            .or_default()
            .push(constraint.clone());
    }

    // Build components with statistics, sorted by sum_xor_sizes (largest first).
    // CMS sorts by `sum_xor_sizes` (total variable mentions) because it is a
    // better proxy for matrix density/complexity than constraint count alone.
    // Reference: `reference/cryptominisat/src/matrixfinder.cpp:70-73,227`
    let mut components: Vec<XorComponent> = component_map
        .into_values()
        .map(|comp_constraints| {
            let rows = comp_constraints.len();
            let sum_xor_sizes: usize = comp_constraints.iter().map(|c| c.vars.len()).sum();
            let mut unique_vars: ay_core::kani_compat::DetHashSet<u32> = Default::default();
            for c in &comp_constraints {
                for &v in &c.vars {
                    unique_vars.insert(v);
                }
            }
            let cols = unique_vars.len();
            let tot = rows.saturating_mul(cols);
            let density = if tot > 0 {
                sum_xor_sizes as f64 / tot as f64
            } else {
                0.0
            };
            XorComponent {
                constraints: comp_constraints,
                stats: ComponentStats {
                    rows,
                    cols,
                    sum_xor_sizes,
                    density,
                },
            }
        })
        .collect();

    components.sort_by_key(|b| std::cmp::Reverse(b.stats.sum_xor_sizes));

    components
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_split_single_component() {
        // x0 XOR x1 = 1, x1 XOR x2 = 0 -> all connected via x1
        let constraints = vec![
            XorConstraint::new(vec![0, 1], true),
            XorConstraint::new(vec![1, 2], false),
        ];
        let components = split_components(&constraints);
        assert_eq!(components.len(), 1);
        assert_eq!(components[0].constraints.len(), 2);
    }

    #[test]
    fn test_split_two_components() {
        // x0 XOR x1 = 1 (component A)
        // x2 XOR x3 = 0 (component B, disjoint)
        let constraints = vec![
            XorConstraint::new(vec![0, 1], true),
            XorConstraint::new(vec![2, 3], false),
        ];
        let components = split_components(&constraints);
        assert_eq!(components.len(), 2);
        // Each component has exactly 1 constraint
        assert_eq!(components[0].constraints.len(), 1);
        assert_eq!(components[1].constraints.len(), 1);
    }

    #[test]
    fn test_split_three_components() {
        let constraints = vec![
            XorConstraint::new(vec![0, 1], true),
            XorConstraint::new(vec![2, 3], false),
            XorConstraint::new(vec![4, 5], true),
        ];
        let components = split_components(&constraints);
        assert_eq!(components.len(), 3);
    }

    #[test]
    fn test_split_merges_via_shared_var() {
        // x0 XOR x1 = 1 and x1 XOR x2 = 0 share x1 -> same component
        // x3 XOR x4 = 1 is disjoint -> separate component
        let constraints = vec![
            XorConstraint::new(vec![0, 1], true),
            XorConstraint::new(vec![1, 2], false),
            XorConstraint::new(vec![3, 4], true),
        ];
        let components = split_components(&constraints);
        assert_eq!(components.len(), 2);
        // Largest component first by sum_xor_sizes (4 vs 2)
        assert_eq!(components[0].constraints.len(), 2);
        assert_eq!(components[1].constraints.len(), 1);
    }

    #[test]
    fn test_split_empty_constraints() {
        let components = split_components(&[]);
        assert!(components.is_empty());
    }

    #[test]
    fn test_split_unit_constraints_separate() {
        // x0 = 1 and x1 = 0 are independent
        let constraints = vec![
            XorConstraint::new(vec![0], true),
            XorConstraint::new(vec![1], false),
        ];
        let components = split_components(&constraints);
        assert_eq!(components.len(), 2);
    }

    #[test]
    fn test_split_transitive_merge() {
        // x0-x1, x1-x2, x2-x3 -> all one component by transitivity
        let constraints = vec![
            XorConstraint::new(vec![0, 1], true),
            XorConstraint::new(vec![1, 2], false),
            XorConstraint::new(vec![2, 3], true),
        ];
        let components = split_components(&constraints);
        assert_eq!(components.len(), 1);
        assert_eq!(components[0].constraints.len(), 3);
    }

    #[test]
    fn test_split_large_chain_single_component() {
        // Chain: x0-x1, x1-x2, ..., x98-x99 -> single component
        let constraints: Vec<XorConstraint> = (0..99u32)
            .map(|i| XorConstraint::new(vec![i, i + 1], i % 2 == 0))
            .collect();
        let components = split_components(&constraints);
        assert_eq!(components.len(), 1);
        assert_eq!(components[0].constraints.len(), 99);
    }

    #[test]
    fn test_split_many_independent_pairs() {
        // 50 independent pairs: (0,1), (2,3), ..., (98,99)
        let constraints: Vec<XorConstraint> = (0..50u32)
            .map(|i| XorConstraint::new(vec![i * 2, i * 2 + 1], true))
            .collect();
        let components = split_components(&constraints);
        assert_eq!(components.len(), 50);
    }

    #[test]
    fn test_split_stats_correct() {
        // Component A: x0 XOR x1 = 1, x1 XOR x2 = 0 (3 vars, 2 rows, sum=4)
        // Component B: x3 XOR x4 = 1 (2 vars, 1 row, sum=2)
        let constraints = vec![
            XorConstraint::new(vec![0, 1], true),
            XorConstraint::new(vec![1, 2], false),
            XorConstraint::new(vec![3, 4], true),
        ];
        let components = split_components(&constraints);
        assert_eq!(components.len(), 2);
        // Sorted by sum_xor_sizes descending: component A (sum=4) first
        assert_eq!(components[0].stats.rows, 2);
        assert_eq!(components[0].stats.cols, 3);
        assert_eq!(components[0].stats.sum_xor_sizes, 4);
        assert_eq!(components[1].stats.rows, 1);
        assert_eq!(components[1].stats.cols, 2);
        assert_eq!(components[1].stats.sum_xor_sizes, 2);
    }

    #[test]
    fn test_split_sorts_by_sum_xor_sizes() {
        // Component A: one 5-var XOR (sum=5)
        // Component B: three 2-var XORs sharing no vars with A (sum=6)
        // B should come first despite having fewer total vars, because sum=6 > 5
        let constraints = vec![
            XorConstraint::new(vec![0, 1, 2, 3, 4], true),
            XorConstraint::new(vec![10, 11], false),
            XorConstraint::new(vec![11, 12], true),
            XorConstraint::new(vec![12, 13], false),
        ];
        let components = split_components(&constraints);
        assert_eq!(components.len(), 2);
        // Component B: 3 XORs, sum_xor_sizes = 2+2+2 = 6
        // Component A: 1 XOR, sum_xor_sizes = 5
        assert_eq!(components[0].stats.sum_xor_sizes, 6);
        assert_eq!(components[1].stats.sum_xor_sizes, 5);
    }

    #[test]
    fn test_split_density_computed() {
        // Single 3-var XOR: 1 row, 3 cols, sum=3, density = 3/(1*3) = 1.0
        let constraints = vec![XorConstraint::new(vec![0, 1, 2], true)];
        let components = split_components(&constraints);
        assert_eq!(components.len(), 1);
        let d = components[0].stats.density;
        assert!((d - 1.0).abs() < 1e-10, "expected density 1.0, got {d}");
    }

    #[test]
    fn test_split_early_exit_same_component() {
        // If all vars of a constraint are already in the same component,
        // the union operation is skipped (CMS `belong_same_matrix` optimization).
        // This test verifies correctness: adding a redundant constraint does not
        // create extra components.
        let constraints = vec![
            XorConstraint::new(vec![0, 1], true),
            XorConstraint::new(vec![1, 2], false),
            // Redundant: x0 and x2 are already connected via x1
            XorConstraint::new(vec![0, 2], true),
        ];
        let components = split_components(&constraints);
        assert_eq!(components.len(), 1);
        assert_eq!(components[0].constraints.len(), 3);
    }
}
