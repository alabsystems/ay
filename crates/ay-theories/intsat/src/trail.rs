// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bound trail for the IntSat solver.
//!
//! The trail records a sequence of bounds (lower and upper) on integer variables,
//! analogous to the literal trail in SAT CDCL. Each entry records the variable,
//! bound value, reason (decision/propagation/input), and decision level.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use num_bigint::BigInt;
use num_traits::{Signed, Zero};

use crate::types::{BoundEntry, BoundReason, VarId};

/// The bound trail, maintaining current best bounds for each variable.
pub(crate) struct Trail {
    /// Ordered sequence of bound entries.
    entries: Vec<BoundEntry>,
    /// Current lower bound for each variable (x >= value).
    var_lower: HashMap<VarId, BigInt>,
    /// Current upper bound for each variable (x <= value).
    var_upper: HashMap<VarId, BigInt>,
    /// Index into `entries` where each decision level starts.
    /// `decision_level_starts[i]` is the index of the first entry at level i+1.
    decision_level_starts: Vec<usize>,
    /// Current decision level.
    current_level: u32,
}

impl Trail {
    /// Create a new empty trail.
    pub(crate) fn new() -> Self {
        Self {
            entries: Vec::new(),
            var_lower: HashMap::default(),
            var_upper: HashMap::default(),
            decision_level_starts: Vec::new(),
            current_level: 0,
        }
    }

    /// Push a bound onto the trail, updating the variable's bound maps.
    pub(crate) fn push_bound(&mut self, entry: BoundEntry) {
        if entry.is_upper {
            let cur = self.var_upper.get(&entry.var);
            // Only update if tighter (smaller upper bound).
            if cur.is_none() || entry.value < *cur.expect("invariant: checked is_none above") {
                self.var_upper.insert(entry.var, entry.value.clone());
            }
        } else {
            let cur = self.var_lower.get(&entry.var);
            // Only update if tighter (larger lower bound).
            if cur.is_none() || entry.value > *cur.expect("invariant: checked is_none above") {
                self.var_lower.insert(entry.var, entry.value.clone());
            }
        }
        self.entries.push(entry);
    }

    /// Begin a new decision level (called before pushing a decision bound).
    pub(crate) fn new_decision_level(&mut self) {
        self.current_level += 1;
        self.decision_level_starts.push(self.entries.len());
    }

    /// Backtrack to the given decision level, removing all entries above it.
    ///
    /// After this call, `current_level()` returns `level`.
    pub(crate) fn backtrack_to_level(&mut self, level: u32) {
        debug_assert!(
            level <= self.current_level,
            "invariant: cannot backtrack forward from {} to {}",
            self.current_level,
            level,
        );

        if level == self.current_level {
            return;
        }

        // Find the trail position to truncate to.
        let target_idx = if level == 0 {
            // Keep only level-0 entries.
            if self.decision_level_starts.is_empty() {
                self.entries.len()
            } else {
                self.decision_level_starts[0]
            }
        } else {
            self.decision_level_starts[level as usize - 1 + 1 - 1]
        };

        // For level > 0, the start of level (level+1) entries.
        let truncate_to = if (level as usize) < self.decision_level_starts.len() {
            self.decision_level_starts[level as usize]
        } else {
            self.entries.len()
        };

        let _ = target_idx; // Suppress unused warning; we use truncate_to below.
        self.entries.truncate(truncate_to);
        self.decision_level_starts.truncate(level as usize);
        self.current_level = level;

        // Recompute bounds from remaining trail entries.
        self.recompute_bounds();
    }

    /// Recompute var_lower and var_upper from the current trail entries.
    fn recompute_bounds(&mut self) {
        self.var_lower.clear();
        self.var_upper.clear();
        for entry in &self.entries {
            if entry.is_upper {
                let cur = self.var_upper.get(&entry.var);
                if cur.is_none() || entry.value < *cur.expect("invariant: checked") {
                    self.var_upper.insert(entry.var, entry.value.clone());
                }
            } else {
                let cur = self.var_lower.get(&entry.var);
                if cur.is_none() || entry.value > *cur.expect("invariant: checked") {
                    self.var_lower.insert(entry.var, entry.value.clone());
                }
            }
        }
    }

    /// Get the current decision level.
    #[must_use]
    pub(crate) fn current_level(&self) -> u32 {
        self.current_level
    }

    /// Get the current lower bound for a variable, if any.
    #[must_use]
    pub(crate) fn lower_bound(&self, var: VarId) -> Option<&BigInt> {
        self.var_lower.get(&var)
    }

    /// Get the current upper bound for a variable, if any.
    #[must_use]
    pub(crate) fn upper_bound(&self, var: VarId) -> Option<&BigInt> {
        self.var_upper.get(&var)
    }

    /// Check if a variable is fully defined (lower bound == upper bound).
    #[must_use]
    pub(crate) fn is_defined(&self, var: VarId) -> bool {
        match (self.var_lower.get(&var), self.var_upper.get(&var)) {
            (Some(lb), Some(ub)) => lb == ub,
            _ => false,
        }
    }

    /// Get the value of a fully defined variable (panics if not defined).
    #[must_use]
    pub(crate) fn value(&self, var: VarId) -> Option<&BigInt> {
        if self.is_defined(var) {
            self.var_lower.get(&var)
        } else {
            None
        }
    }

    /// Compute the minimum contribution of a variable with the given coefficient.
    ///
    /// For bound propagation: `min(coeff * x)` where x is constrained by current bounds.
    /// - If coeff > 0, min = coeff * lower_bound (or None if unbounded below)
    /// - If coeff < 0, min = coeff * upper_bound (or None if unbounded above)
    /// - If coeff == 0, min = 0
    #[must_use]
    pub(crate) fn min_contribution(&self, var: VarId, coeff: &BigInt) -> Option<BigInt> {
        if coeff.is_zero() {
            return Some(BigInt::zero());
        }
        if coeff.is_positive() {
            self.var_lower.get(&var).map(|lb| coeff * lb)
        } else {
            self.var_upper.get(&var).map(|ub| coeff * ub)
        }
    }

    /// Get the trail entries as a slice.
    #[must_use]
    pub(crate) fn entries(&self) -> &[BoundEntry] {
        &self.entries
    }

    /// Find the decision level at which a bound on `var` with direction `is_upper`
    /// was placed. Searches from the end of the trail (most recent first).
    #[must_use]
    pub(crate) fn level_of_bound(&self, var: VarId, is_upper: bool) -> Option<u32> {
        for entry in self.entries.iter().rev() {
            if entry.var == var && entry.is_upper == is_upper {
                return Some(entry.level);
            }
        }
        None
    }

    /// Find the reason constraint for the most recent bound on `var` with
    /// direction `is_upper`.
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn reason_of_bound(&self, var: VarId, is_upper: bool) -> Option<&BoundReason> {
        for entry in self.entries.iter().rev() {
            if entry.var == var && entry.is_upper == is_upper {
                return Some(&entry.reason);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trail_push_and_query() {
        let mut trail = Trail::new();
        assert_eq!(trail.current_level(), 0);

        // Push a lower bound at level 0.
        trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(0),
            is_upper: false,
            reason: BoundReason::Input,
            level: 0,
        });

        assert_eq!(trail.lower_bound(VarId(0)), Some(&BigInt::from(0)));
        assert_eq!(trail.upper_bound(VarId(0)), None);
        assert!(!trail.is_defined(VarId(0)));
    }

    #[test]
    fn test_trail_defined() {
        let mut trail = Trail::new();
        trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(5),
            is_upper: false,
            reason: BoundReason::Input,
            level: 0,
        });
        trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(5),
            is_upper: true,
            reason: BoundReason::Input,
            level: 0,
        });
        assert!(trail.is_defined(VarId(0)));
        assert_eq!(trail.value(VarId(0)), Some(&BigInt::from(5)));
    }

    #[test]
    fn test_trail_backtrack() {
        let mut trail = Trail::new();

        // Level 0: input bounds.
        trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(0),
            is_upper: false,
            reason: BoundReason::Input,
            level: 0,
        });

        // Level 1: decision.
        trail.new_decision_level();
        trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(3),
            is_upper: true,
            reason: BoundReason::Decision,
            level: 1,
        });
        assert_eq!(trail.current_level(), 1);
        assert_eq!(trail.upper_bound(VarId(0)), Some(&BigInt::from(3)));

        // Backtrack to level 0.
        trail.backtrack_to_level(0);
        assert_eq!(trail.current_level(), 0);
        assert_eq!(trail.upper_bound(VarId(0)), None);
        assert_eq!(trail.lower_bound(VarId(0)), Some(&BigInt::from(0)));
    }

    #[test]
    fn test_min_contribution() {
        let mut trail = Trail::new();
        trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(2),
            is_upper: false,
            reason: BoundReason::Input,
            level: 0,
        });
        trail.push_bound(BoundEntry {
            var: VarId(0),
            value: BigInt::from(10),
            is_upper: true,
            reason: BoundReason::Input,
            level: 0,
        });

        // Positive coeff: min = coeff * lower = 3 * 2 = 6
        assert_eq!(
            trail.min_contribution(VarId(0), &BigInt::from(3)),
            Some(BigInt::from(6))
        );
        // Negative coeff: min = coeff * upper = -2 * 10 = -20
        assert_eq!(
            trail.min_contribution(VarId(0), &BigInt::from(-2)),
            Some(BigInt::from(-20))
        );
    }
}
