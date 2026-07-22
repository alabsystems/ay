// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cube extraction utilities for PDR solver.
//!
//! This module provides functions for extracting cubes (conjunctions of literals)
//! from SMT models and formulas. Cubes are used in PDR to represent states that
//! need to be blocked or tracked.
//!
//! ## Key concepts
//!
//! - **Point cube**: A cube where each variable is assigned a specific constant value
//! - **Model-based extraction**: Building cubes from SMT solver model assignments
//! - **Equality propagation**: Deriving variable values from equality constraints
//!
//! ## Functions
//!
//! - [`value_expr_from_model`]: Evaluate an expression using model values
//! - [`extract_equalities_and_propagate`]: Extract equality constraints and propagate values
//! - [`is_point_cube_for_vars`]: Check if a cube grounds all given variables

mod contradiction;
mod equality;
mod eval;

// Re-export public API used outside cube/
pub(crate) use contradiction::is_trivial_contradiction;
pub(super) use equality::{
    augment_model_from_equalities, extract_equalities_from_formula, is_point_cube_for_vars,
};
pub(super) use eval::value_expr_from_model;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Union-find data structure for checking if a cube is a "point cube".
///
/// A point cube has equality constraints that transitively ground each variable
/// to a constant. This struct tracks equivalence classes and whether each class
/// contains a grounded value.
///
/// Key insight: `x = y` alone does NOT make either grounded. Only `x = 5` grounds x.
/// But `x = y` AND `y = 5` grounds both x and y through transitivity.
pub(super) struct PointCubeUnionFind {
    /// parent[var] = parent variable (or self if root)
    parent: FxHashMap<String, String>,
    /// grounded[root] = true if this equivalence class contains a constant
    grounded: FxHashSet<String>,
}

impl PointCubeUnionFind {
    pub(super) fn new() -> Self {
        Self {
            parent: FxHashMap::default(),
            grounded: FxHashSet::default(),
        }
    }

    /// Find the root representative of a variable's equivalence class.
    ///
    /// #2956 Finding 4: Minimizes String allocations by using entry API
    /// and only cloning when the key is genuinely new or path compression
    /// updates the parent pointer.
    pub(super) fn find(&mut self, var: &str) -> String {
        // Ensure var exists — allocates only on first insertion.
        if !self.parent.contains_key(var) {
            let owned = var.to_string();
            self.parent.insert(owned.clone(), owned.clone());
            return owned;
        }

        // Check if var is its own root (common case — no allocation needed).
        let is_root = self.parent.get(var).is_some_and(|p| p.as_str() == var);
        if is_root {
            // Return the existing key without allocating a new String.
            // Safe: we just confirmed the key exists via contains_key above.
            return self
                .parent
                .get_key_value(var)
                .map_or_else(|| var.to_string(), |(k, _)| k.clone());
        }

        // Non-root: need path compression.
        // Safety: `var` is guaranteed to be in the parent map (checked at line 59).
        let parent = self
            .parent
            .get(var)
            .cloned()
            .expect("invariant: var exists in parent map after contains_key check");
        let root = self.find(&parent);
        // Path compression: point var directly to root.
        // Only allocates if var != root (which we know is true since !is_root).
        self.parent.insert(var.to_string(), root.clone());
        root
    }

    /// Union two equivalence classes
    pub(super) fn union(&mut self, var1: &str, var2: &str) {
        let root1 = self.find(var1);
        let root2 = self.find(var2);
        if root1 != root2 {
            let either_grounded = self.grounded.contains(&root1) || self.grounded.contains(&root2);
            // Merge root2 into root1
            self.parent.insert(root2.clone(), root1.clone());
            // If either class was grounded, the merged class is grounded
            if self.grounded.contains(&root2) {
                self.grounded.insert(root1.clone());
            }
            // Postcondition: if either class was grounded before, merged class must be grounded
            debug_assert!(
                !either_grounded || self.grounded.contains(&root1),
                "BUG: union lost grounded status: var1={var1}, var2={var2}, root={root1}",
            );
        }
    }

    /// Mark a variable's equivalence class as grounded (contains a constant)
    pub(super) fn mark_grounded(&mut self, var: &str) {
        let root = self.find(var);
        self.grounded.insert(root);
        // Postcondition: var must now be grounded
        debug_assert!(
            self.is_grounded(var),
            "BUG: mark_grounded({var}) did not make variable grounded",
        );
    }

    /// Check if a variable is in a grounded equivalence class
    pub(super) fn is_grounded(&mut self, var: &str) -> bool {
        let root = self.find(var);
        self.grounded.contains(&root)
    }
}

#[cfg(test)]
mod tests;
