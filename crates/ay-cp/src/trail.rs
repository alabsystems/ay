// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integer trail: tracks bound changes with explanations.
//!
//! The integer trail is the CP counterpart to the SAT solver's assignment trail.
//! Every time a propagator narrows a variable's domain (tightens lb or ub), the
//! change is recorded here along with its explanation (the reason clause).
//!
//! On backtrack, entries above the backtrack level are undone, restoring
//! previous bounds. The explanation is used during conflict analysis to
//! produce learned clauses that generalize the conflict.
//!
//! Design follows OR-Tools CP-SAT `IntegerTrail` (ortools/sat/integer.h)
//! and Pumpkin's trail (pumpkin-solver/src/engine/).

use crate::domain::{Domain, DomainEnumerationError, DomainWipeout};
use crate::propagator::Explanation;
use crate::variable::IntVarId;
use ay_sat::Literal;

/// A single entry in the integer trail.
#[derive(Debug, Clone)]
pub struct TrailEntry {
    /// Which variable was modified
    pub var: IntVarId,
    /// The bound change
    pub change: BoundChange,
    /// Decision level at which this change was made
    pub level: u32,
    /// Previous bound value (for undo)
    pub prev_value: i64,
    /// The SAT literal that represents this bound change.
    /// E.g., for `x >= 5`, this is the literal `[x >= 5]` in the encoder.
    pub literal: Literal,
    /// Explanation: why this propagation happened.
    /// `None` for decisions (search choices).
    pub explanation: Option<Explanation>,
}

/// Type of bound change.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundChange {
    /// Lower bound was increased to this value
    LowerBound(i64),
    /// Upper bound was decreased to this value
    UpperBound(i64),
}

/// The integer trail tracks all bound changes during search.
#[derive(Debug)]
pub struct IntegerTrail {
    /// All trail entries in chronological order
    entries: Vec<TrailEntry>,
    /// Current domains for each variable (indexed by IntVarId)
    current_domains: Vec<Domain>,
    /// Trail position at each decision level (for backtracking)
    level_markers: Vec<usize>,
    /// Current decision level
    current_level: u32,
}

impl IntegerTrail {
    /// Create an empty integer trail.
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            current_domains: Vec::new(),
            level_markers: vec![0], // level 0 starts at position 0
            current_level: 0,
        }
    }

    /// Register a new variable with initial bounds.
    pub fn register(&mut self, lb: i64, ub: i64) -> IntVarId {
        self.register_domain(Domain::new(lb, ub))
    }

    /// Register a new variable with an explicit domain.
    pub fn register_domain(&mut self, domain: Domain) -> IntVarId {
        let id = IntVarId(self.current_domains.len() as u32);
        self.current_domains.push(domain);
        id
    }

    /// Get current lower bound of a variable.
    #[inline]
    pub fn lb(&self, var: IntVarId) -> i64 {
        self.current_domains[var.index()].lb()
    }

    /// Get current upper bound of a variable.
    #[inline]
    pub fn ub(&self, var: IntVarId) -> i64 {
        self.current_domains[var.index()].ub()
    }

    /// Is the variable fixed (lb == ub)?
    #[inline]
    pub fn is_fixed(&self, var: IntVarId) -> bool {
        self.current_domains[var.index()].is_fixed()
    }

    /// Get the fixed value, if the variable is fixed.
    #[inline]
    pub fn fixed_value(&self, var: IntVarId) -> Option<i64> {
        self.current_domains[var.index()]
            .is_fixed()
            .then(|| self.current_domains[var.index()].lb())
    }

    /// Is the given value still present in the variable's current domain?
    #[inline]
    pub fn contains(&self, var: IntVarId, value: i64) -> bool {
        self.current_domains[var.index()].contains(value)
    }

    /// Number of currently allowed values in the variable's domain.
    #[inline]
    pub fn domain_size(&self, var: IntVarId) -> u64 {
        self.current_domains[var.index()].size()
    }

    /// Enumerate all currently allowed values in the variable's domain.
    ///
    /// # Panics
    ///
    /// Panics before allocation if the domain exceeds the eager enumeration
    /// limit. Use [`try_values`](Self::try_values) for untrusted domains.
    pub fn values(&self, var: IntVarId) -> Vec<i64> {
        self.try_values(var)
            .expect("domain is too large for eager value enumeration")
    }

    /// Fallible eager enumeration of the variable's current domain.
    pub fn try_values(&self, var: IntVarId) -> Result<Vec<i64>, DomainEnumerationError> {
        self.current_domains[var.index()].try_values()
    }

    /// Values excluded from the variable's bounding interval.
    pub(crate) fn missing_values(&self, var: IntVarId) -> Vec<i64> {
        self.current_domains[var.index()].missing_values()
    }

    /// Current decision level.
    #[inline]
    pub fn current_level(&self) -> u32 {
        self.current_level
    }

    /// Number of registered variables.
    #[inline]
    pub fn num_vars(&self) -> usize {
        self.current_domains.len()
    }

    /// Increase lower bound. Returns the SAT literal that was propagated.
    /// Returns `None` if no change (bound already at least `new_lb`).
    ///
    /// # Errors
    /// Returns `Err(DomainWipeout)` if the new lb exceeds the current ub.
    pub fn set_lb(
        &mut self,
        var: IntVarId,
        new_lb: i64,
        literal: Literal,
        explanation: Option<Explanation>,
    ) -> Result<Option<Literal>, DomainWipeout> {
        let idx = var.index();
        if new_lb <= self.current_domains[idx].lb() {
            return Ok(None);
        }
        let prev = self.current_domains[idx].lb();
        if !self.current_domains[idx].set_lb(new_lb)? {
            return Ok(None);
        }
        let actual_lb = self.current_domains[idx].lb();
        self.entries.push(TrailEntry {
            var,
            change: BoundChange::LowerBound(actual_lb),
            level: self.current_level,
            prev_value: prev,
            literal,
            explanation,
        });
        Ok(Some(literal))
    }

    /// Decrease upper bound. Returns the SAT literal that was propagated.
    /// Returns `None` if no change.
    ///
    /// # Errors
    /// Returns `Err(DomainWipeout)` if the new ub is below the current lb.
    pub fn set_ub(
        &mut self,
        var: IntVarId,
        new_ub: i64,
        literal: Literal,
        explanation: Option<Explanation>,
    ) -> Result<Option<Literal>, DomainWipeout> {
        let idx = var.index();
        if new_ub >= self.current_domains[idx].ub() {
            return Ok(None);
        }
        let prev = self.current_domains[idx].ub();
        if !self.current_domains[idx].set_ub(new_ub)? {
            return Ok(None);
        }
        let actual_ub = self.current_domains[idx].ub();
        self.entries.push(TrailEntry {
            var,
            change: BoundChange::UpperBound(actual_ub),
            level: self.current_level,
            prev_value: prev,
            literal,
            explanation,
        });
        Ok(Some(literal))
    }

    /// Push a new decision level.
    pub fn push_level(&mut self) {
        self.current_level += 1;
        self.level_markers.push(self.entries.len());
    }

    /// Backtrack to a given decision level, undoing all changes above it.
    pub fn backtrack_to(&mut self, level: u32) {
        assert!(level <= self.current_level);
        if level == self.current_level {
            return;
        }

        let marker = self.level_markers[level as usize + 1];

        // Undo entries in reverse order
        for entry in self.entries[marker..].iter().rev() {
            let idx = entry.var.index();
            match entry.change {
                BoundChange::LowerBound(_) => {
                    self.current_domains[idx].restore_lb(entry.prev_value);
                }
                BoundChange::UpperBound(_) => {
                    self.current_domains[idx].restore_ub(entry.prev_value);
                }
            }
        }

        self.entries.truncate(marker);
        self.level_markers.truncate(level as usize + 1);
        self.current_level = level;
    }

    /// Fully reset the trail, undoing ALL entries including level 0.
    ///
    /// This restores all variable bounds to their original registered values.
    /// Required for incremental solving: `backtrack_to(0)` preserves level-0
    /// propagation entries from a previous solve, which can leave stale bounds
    /// that conflict with new bound-tightening constraints (#5910).
    pub fn reset_all(&mut self) {
        // Undo ALL entries in reverse order (including level 0)
        for entry in self.entries.iter().rev() {
            let idx = entry.var.index();
            match entry.change {
                BoundChange::LowerBound(_) => {
                    self.current_domains[idx].restore_lb(entry.prev_value);
                }
                BoundChange::UpperBound(_) => {
                    self.current_domains[idx].restore_ub(entry.prev_value);
                }
            }
        }

        self.entries.clear();
        self.level_markers.truncate(1); // Keep only level-0 marker
        self.current_level = 0;
    }

    /// Get all trail entries (for conflict analysis).
    pub fn entries(&self) -> &[TrailEntry] {
        &self.entries
    }
}

impl Default for IntegerTrail {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
#[path = "trail_tests.rs"]
mod tests;
