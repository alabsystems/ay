// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental solving types: core evolution tracking across check-sat calls.

use ay_core::kani_compat::DetHashMap as HashMap;
use std::sync::Arc;

/// Tracks how unsat cores change across consecutive check-sat calls.
///
/// When a consumer runs multiple check-sat calls in an incremental session
/// (push/assert/check-sat/pop), this type reports which named assertions
/// from the previous core persist, which new ones entered, and whether
/// the current conflict is independent of the previous one.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct IncrementalCoreEvolution {
    /// Named assertions from the previous unsat core.
    pub previous_core: Vec<String>,
    /// Named assertions from the current unsat core.
    pub current_core: Vec<String>,
    persisted: Vec<String>,
    entered: Vec<String>,
    exited: Vec<String>,
}

impl std::fmt::Display for IncrementalCoreEvolution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "CoreEvolution({} persisted, {} entered, {} exited, persistence {:.0}%)",
            self.persisted.len(),
            self.entered.len(),
            self.exited.len(),
            self.persistence_ratio() * 100.0,
        )
    }
}

impl IncrementalCoreEvolution {
    /// Compute core evolution from two consecutive unsat cores.
    #[must_use]
    pub fn new(previous_core: Vec<String>, current_core: Vec<String>) -> Self {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let (persisted, entered, exited) = {
            let prev_set: HashSet<&str> = previous_core.iter().map(String::as_str).collect();
            let curr_set: HashSet<&str> = current_core.iter().map(String::as_str).collect();
            let mut persisted: Vec<String> = prev_set
                .intersection(&curr_set)
                .map(|s| (*s).to_string())
                .collect();
            persisted.sort();
            let mut entered: Vec<String> = curr_set
                .difference(&prev_set)
                .map(|s| (*s).to_string())
                .collect();
            entered.sort();
            let mut exited: Vec<String> = prev_set
                .difference(&curr_set)
                .map(|s| (*s).to_string())
                .collect();
            exited.sort();
            (persisted, entered, exited)
        };
        Self {
            previous_core,
            current_core,
            persisted,
            entered,
            exited,
        }
    }

    /// Named assertions present in both consecutive cores.
    #[must_use]
    pub fn persisted(&self) -> &[String] {
        &self.persisted
    }

    /// Named assertions in the current core but not the previous.
    #[must_use]
    pub fn entered(&self) -> &[String] {
        &self.entered
    }

    /// Named assertions in the previous core but not the current.
    #[must_use]
    pub fn exited(&self) -> &[String] {
        &self.exited
    }

    /// True when cores share no named assertions (independent conflict).
    #[must_use]
    pub fn is_independent(&self) -> bool {
        self.persisted.is_empty()
    }

    /// True when cores are identical (same names, ignoring order).
    #[must_use]
    pub fn is_unchanged(&self) -> bool {
        self.entered.is_empty() && self.exited.is_empty()
    }

    /// Fraction of previous core that persists. 0.0 when empty or independent.
    #[must_use]
    pub fn persistence_ratio(&self) -> f64 {
        if self.previous_core.is_empty() {
            return 0.0;
        }
        self.persisted.len() as f64 / self.previous_core.len() as f64
    }
}

/// Standalone tracker for incremental UNSAT core evolution (#8306).
///
/// Consumers manage this independently of the solver, avoiding the `&mut self`
/// borrow that `Solver::core_evolution()` requires.  After each UNSAT result,
/// call [`update`](CoreEvolutionTracker::update) with the current core names
/// to get the diff against the previous core.
///
/// Uses `Arc<str>` interning internally so that assertion names shared across
/// consecutive cores occupy a single allocation.
///
/// # Example
///
/// ```
/// use ay_dpll::api::types::CoreEvolutionTracker;
///
/// let mut tracker = CoreEvolutionTracker::new();
///
/// // First UNSAT result — no previous core to diff.
/// let core1 = vec!["a".to_string(), "b".to_string()];
/// assert!(tracker.update(&core1).is_none());
///
/// // Second UNSAT result — returns the evolution.
/// let core2 = vec!["b".to_string(), "c".to_string()];
/// let evo = tracker.update(&core2).unwrap();
/// assert_eq!(evo.persisted(), &["b"]);
/// assert_eq!(evo.entered(), &["c"]);
/// assert_eq!(evo.exited(), &["a"]);
/// ```
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct CoreEvolutionTracker {
    /// Previous UNSAT core (interned names).
    previous: Option<Vec<Arc<str>>>,
    /// Intern pool mapping raw names to shared `Arc<str>`.
    intern_pool: HashMap<Box<str>, Arc<str>>,
}

impl CoreEvolutionTracker {
    /// Create a new empty tracker.
    #[must_use]
    pub fn new() -> Self {
        Self {
            previous: None,
            intern_pool: HashMap::default(),
        }
    }

    /// Feed the current UNSAT core and return the evolution since the last call.
    ///
    /// Returns `None` on the first call (no previous core to diff against).
    pub fn update(&mut self, current_core: &[String]) -> Option<IncrementalCoreEvolution> {
        let current_interned: Vec<Arc<str>> =
            current_core.iter().map(|name| self.intern(name)).collect();

        let evolution = self.previous.take().map(|prev_interned| {
            let prev_strings: Vec<String> = prev_interned.iter().map(ToString::to_string).collect();
            IncrementalCoreEvolution::new(prev_strings, current_core.to_vec())
        });

        self.previous = Some(current_interned);
        evolution
    }

    /// Reset the tracker, discarding any stored previous core and intern pool.
    pub fn reset(&mut self) {
        self.previous = None;
        self.intern_pool.clear();
    }

    /// Intern a core assertion name, returning a shared `Arc<str>`.
    fn intern(&mut self, name: &str) -> Arc<str> {
        if let Some(existing) = self.intern_pool.get(name) {
            Arc::clone(existing)
        } else {
            let interned: Arc<str> = Arc::from(name);
            self.intern_pool
                .insert(Box::from(name), Arc::clone(&interned));
            interned
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_core_evolution_tracker_standalone() {
        let mut tracker = CoreEvolutionTracker::new();

        // First call: no previous core, returns None.
        let core1 = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        assert!(tracker.update(&core1).is_none());

        // Second call: returns evolution diff.
        let core2 = vec!["b".to_string(), "c".to_string(), "d".to_string()];
        let evo = tracker.update(&core2).unwrap();
        assert_eq!(evo.persisted(), &["b", "c"]);
        assert_eq!(evo.entered(), &["d"]);
        assert_eq!(evo.exited(), &["a"]);

        // Third call: evolution from core2 to core3.
        let core3 = vec!["d".to_string(), "e".to_string()];
        let evo2 = tracker.update(&core3).unwrap();
        assert_eq!(evo2.persisted(), &["d"]);
        assert_eq!(evo2.entered(), &["e"]);
        assert_eq!(evo2.exited(), &["b", "c"]);

        // Reset clears state — next update returns None.
        tracker.reset();
        let core4 = vec!["x".to_string()];
        assert!(tracker.update(&core4).is_none());
    }

    #[test]
    fn test_core_evolution_tracker_default() {
        let tracker = CoreEvolutionTracker::default();
        assert!(tracker.previous.is_none());
        assert!(tracker.intern_pool.is_empty());
    }

    #[test]
    fn test_core_evolution_tracker_interning_shares_allocations() {
        let mut tracker = CoreEvolutionTracker::new();

        let core1 = vec!["shared_name".to_string()];
        tracker.update(&core1);

        // Same name in second core should reuse the interned Rc.
        let core2 = vec!["shared_name".to_string()];
        tracker.update(&core2);

        // The intern pool should contain exactly one entry.
        assert_eq!(tracker.intern_pool.len(), 1);
    }
}
