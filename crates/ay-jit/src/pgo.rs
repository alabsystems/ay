// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PGO (Profile-Guided Optimization) for JIT BCP (#8266).
//!
//! Tracks per-literal propagation call frequency via software counters.
//! After a configurable conflict threshold, classifies each compiled
//! propagation function as Hot / Warm / Cold:
//!
//! - **Hot** (top 20% by call count): recompiled with PRFM prefetch
//!   scheduling on aarch64 for reduced cache-miss latency.
//! - **Warm** (middle 30%): code preserved via memcpy from snapshot.
//! - **Cold** (bottom 50%): removed; falls back to standard 2WL BCP.
//!
//! The classification uses percentile thresholds on the observed call
//! distribution, consistent with CaDiCaL's focused/stable tier approach.

/// Heat class for a compiled propagation function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeatClass {
    /// Cold: bottom 50% by call count. Removed from compiled formula.
    Cold,
    /// Warm: middle 30% by call count. Preserved via memcpy.
    Warm,
    /// Hot: top 20% by call count. Recompiled with prefetch scheduling.
    Hot,
}

/// Default conflict threshold before PGO analysis triggers.
pub const DEFAULT_PGO_CONFLICT_THRESHOLD: u64 = 10_000;

/// PGO profile collected during SAT solving.
///
/// Tracks per-(variable, polarity) propagation counts to guide
/// recompilation of hot propagation functions with optimized
/// instruction scheduling (PRFM on aarch64).
///
/// Counters are stored as `u32` with saturating arithmetic to avoid
/// overflow while keeping the cache footprint small (4 bytes per
/// literal vs 8 for u64).
#[derive(Debug, Clone)]
pub struct PgoProfile {
    /// Per-literal propagation counts indexed by `var * 2 + polarity`.
    counters: Vec<u32>,
    /// Per-clause propagation frequency counters indexed by clause_id.
    /// Tracks how many times each clause's propagation path was entered.
    clause_counters: Vec<u32>,
    /// Number of variables (counters.len() == num_vars * 2).
    num_vars: usize,
    /// Maximum clause_id seen (for bounds checking clause_counters).
    max_clause_id: u32,
    /// Conflict count at profile creation (for threshold check).
    creation_conflicts: u64,
}

impl PgoProfile {
    /// Create a new zeroed profile.
    ///
    /// `num_vars`: number of SAT variables (allocates 2 * num_vars counters).
    /// `creation_conflicts`: current solver conflict count for threshold math.
    #[must_use]
    pub fn new(num_vars: usize, creation_conflicts: u64) -> Self {
        Self {
            counters: vec![0u32; num_vars * 2],
            clause_counters: Vec::new(),
            num_vars,
            max_clause_id: 0,
            creation_conflicts,
        }
    }

    /// Record a call to the propagation function for `(var, polarity)`.
    ///
    /// Called from `jit_propagate_literal` on every JIT dispatch.
    /// Uses saturating add to avoid overflow.
    #[inline(always)]
    pub fn record_call(&mut self, var: usize, polarity: usize) {
        let idx = var * 2 + polarity;
        if let Some(c) = self.counters.get_mut(idx) {
            *c = c.saturating_add(1);
        }
    }

    /// Record a propagation event for a specific clause.
    ///
    /// Called after JIT dispatch when a clause produces a propagation or
    /// conflict. Tracks which clauses are most active to guide clause
    /// ordering within hot propagation functions.
    #[inline(always)]
    pub fn record_clause_propagation(&mut self, clause_id: u32) {
        let id = clause_id as usize;
        if id >= self.clause_counters.len() {
            // Grow lazily to avoid pre-allocating for all arena offsets.
            self.clause_counters.resize(id + 1, 0);
        }
        if let Some(c) = self.clause_counters.get_mut(id) {
            *c = c.saturating_add(1);
        }
        if clause_id > self.max_clause_id {
            self.max_clause_id = clause_id;
        }
    }

    /// Returns the conflict count at which this profile was created.
    #[inline]
    pub fn creation_conflicts(&self) -> u64 {
        self.creation_conflicts
    }

    /// Returns the propagation count for a specific literal index.
    #[inline]
    pub fn literal_count(&self, idx: usize) -> u32 {
        self.counters.get(idx).copied().unwrap_or(0)
    }

    /// Returns the propagation count for a specific clause.
    #[inline]
    pub fn clause_count(&self, clause_id: u32) -> u32 {
        self.clause_counters
            .get(clause_id as usize)
            .copied()
            .unwrap_or(0)
    }

    /// Identify hot variables that exceed a given propagation count threshold.
    ///
    /// Returns a list of `(var, polarity)` pairs where the propagation
    /// count exceeds `threshold`. Results are sorted by count descending.
    pub fn hot_vars(&self, threshold: u64) -> Vec<(usize, usize)> {
        let threshold_u32 = if threshold > u64::from(u32::MAX) {
            u32::MAX
        } else {
            threshold as u32
        };
        let mut hot: Vec<(usize, usize, u32)> = Vec::new();
        for var in 0..self.num_vars {
            for pol in 0..2usize {
                let idx = var * 2 + pol;
                let count = self.counters.get(idx).copied().unwrap_or(0);
                if count >= threshold_u32 {
                    hot.push((var, pol, count));
                }
            }
        }
        hot.sort_unstable_by_key(|b| std::cmp::Reverse(b.2));
        hot.iter().map(|&(v, p, _)| (v, p)).collect()
    }

    /// Sort clauses by propagation frequency (descending) for a given
    /// literal's clause list. Returns a reordered copy of the input.
    ///
    /// Clauses with higher propagation counts are placed first so that
    /// the most active propagation paths are checked earliest in the
    /// compiled function, improving branch prediction and reducing
    /// average-case instruction count.
    pub fn sort_clauses_by_frequency<'a>(
        &self,
        clauses: &[(u32, &'a [u32])],
    ) -> Vec<(u32, &'a [u32])> {
        let mut sorted: Vec<(u32, &'a [u32])> = clauses.to_vec();
        sorted.sort_by(|a, b| {
            let freq_a = self.clause_count(a.0);
            let freq_b = self.clause_count(b.0);
            freq_b.cmp(&freq_a)
        });
        sorted
    }

    /// Classify each compiled literal pair as Hot / Warm / Cold.
    ///
    /// Only literals that have a compiled function (indicated by
    /// `has_fn_bitmap`) are considered for classification. Literals
    /// without compiled functions are classified as Cold.
    ///
    /// Returns a `Vec<HeatClass>` indexed by `var * 2 + polarity`.
    pub fn classify(&self, has_fn_bitmap: &[u64]) -> Vec<HeatClass> {
        let num_lits = self.num_vars * 2;
        let mut result = vec![HeatClass::Cold; num_lits];

        // Collect (index, count) for all compiled literals.
        let mut compiled: Vec<(usize, u32)> = Vec::new();
        for idx in 0..num_lits {
            let word = idx / 64;
            let bit = idx % 64;
            let has_fn = has_fn_bitmap
                .get(word)
                .is_some_and(|w| w & (1u64 << bit) != 0);
            if has_fn {
                let count = self.counters.get(idx).copied().unwrap_or(0);
                compiled.push((idx, count));
            }
        }

        if compiled.is_empty() {
            return result;
        }

        // Sort by count descending to find percentile boundaries.
        compiled.sort_unstable_by_key(|b| std::cmp::Reverse(b.1));

        let n = compiled.len();
        let hot_cutoff = n * 20 / 100; // top 20%
        let warm_cutoff = hot_cutoff + n * 30 / 100; // next 30%

        for (rank, &(idx, _count)) in compiled.iter().enumerate() {
            result[idx] = if rank < hot_cutoff {
                HeatClass::Hot
            } else if rank < warm_cutoff {
                HeatClass::Warm
            } else {
                HeatClass::Cold
            };
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_profile() {
        let p = PgoProfile::new(100, 5000);
        assert_eq!(p.counters.len(), 200);
        assert_eq!(p.creation_conflicts(), 5000);
        assert!(p.counters.iter().all(|&c| c == 0));
        assert!(p.clause_counters.is_empty());
    }

    #[test]
    fn test_record_call_saturates() {
        let mut p = PgoProfile::new(2, 0);
        p.counters[0] = u32::MAX - 1;
        p.record_call(0, 0);
        assert_eq!(p.counters[0], u32::MAX);
        p.record_call(0, 0); // should saturate, not wrap
        assert_eq!(p.counters[0], u32::MAX);
    }

    #[test]
    fn test_record_call_out_of_bounds() {
        let mut p = PgoProfile::new(2, 0);
        p.record_call(999, 0); // should not panic
    }

    #[test]
    fn test_clause_propagation_counter() {
        let mut p = PgoProfile::new(4, 0);
        // Record propagations for clauses
        p.record_clause_propagation(5);
        p.record_clause_propagation(5);
        p.record_clause_propagation(5);
        p.record_clause_propagation(10);
        p.record_clause_propagation(10);
        p.record_clause_propagation(3);

        assert_eq!(p.clause_count(5), 3);
        assert_eq!(p.clause_count(10), 2);
        assert_eq!(p.clause_count(3), 1);
        assert_eq!(p.clause_count(0), 0); // never recorded
        assert_eq!(p.clause_count(999), 0); // out of range
    }

    #[test]
    fn test_clause_counter_saturates() {
        let mut p = PgoProfile::new(2, 0);
        p.record_clause_propagation(0);
        p.clause_counters[0] = u32::MAX - 1;
        p.record_clause_propagation(0);
        assert_eq!(p.clause_count(0), u32::MAX);
        p.record_clause_propagation(0); // should saturate
        assert_eq!(p.clause_count(0), u32::MAX);
    }

    #[test]
    fn test_clause_counter_lazy_growth() {
        let mut p = PgoProfile::new(2, 0);
        assert!(p.clause_counters.is_empty());
        // Recording a high clause_id should grow the vec lazily
        p.record_clause_propagation(100);
        assert!(p.clause_counters.len() >= 101);
        assert_eq!(p.clause_count(100), 1);
        // Everything below should be 0
        assert_eq!(p.clause_count(50), 0);
    }

    #[test]
    fn test_hot_vars_threshold() {
        let mut p = PgoProfile::new(5, 0);
        // var 0 pos: 100, var 0 neg: 50, var 1 pos: 200, rest: 0
        p.counters[0] = 100; // var 0, polarity 0
        p.counters[1] = 50; // var 0, polarity 1
        p.counters[2] = 200; // var 1, polarity 0
        p.counters[3] = 10; // var 1, polarity 1

        // Threshold 100: should get var 1/pol 0 (200) and var 0/pol 0 (100)
        let hot = p.hot_vars(100);
        assert_eq!(hot.len(), 2);
        assert_eq!(hot[0], (1, 0)); // highest count first
        assert_eq!(hot[1], (0, 0));

        // Threshold 200: only var 1/pol 0
        let hot = p.hot_vars(200);
        assert_eq!(hot.len(), 1);
        assert_eq!(hot[0], (1, 0));

        // Threshold 1000: nothing
        let hot = p.hot_vars(1000);
        assert!(hot.is_empty());
    }

    #[test]
    fn test_hot_vars_empty_profile() {
        let p = PgoProfile::new(5, 0);
        let hot = p.hot_vars(1);
        assert!(hot.is_empty());
    }

    #[test]
    fn test_sort_clauses_by_frequency() {
        let mut p = PgoProfile::new(4, 0);
        // clause 10 = 50 propagations, clause 20 = 100, clause 30 = 25
        p.record_clause_propagation(10);
        p.clause_counters[10] = 50;
        p.record_clause_propagation(20);
        p.clause_counters[20] = 100;
        p.record_clause_propagation(30);
        p.clause_counters[30] = 25;

        let lits_a: Vec<u32> = vec![2, 4];
        let lits_b: Vec<u32> = vec![0, 6];
        let lits_c: Vec<u32> = vec![1, 3];
        let clauses: Vec<(u32, &[u32])> = vec![(10, &lits_a), (20, &lits_b), (30, &lits_c)];

        let sorted = p.sort_clauses_by_frequency(&clauses);
        assert_eq!(sorted[0].0, 20); // highest frequency first
        assert_eq!(sorted[1].0, 10);
        assert_eq!(sorted[2].0, 30);
    }

    #[test]
    fn test_sort_clauses_no_frequency_data() {
        let p = PgoProfile::new(4, 0);
        let lits_a: Vec<u32> = vec![2, 4];
        let lits_b: Vec<u32> = vec![0, 6];
        let clauses: Vec<(u32, &[u32])> = vec![(10, &lits_a), (20, &lits_b)];

        // With no frequency data, order should be preserved (stable sort)
        let sorted = p.sort_clauses_by_frequency(&clauses);
        assert_eq!(sorted[0].0, 10);
        assert_eq!(sorted[1].0, 20);
    }

    #[test]
    fn test_literal_count_accessor() {
        let mut p = PgoProfile::new(3, 0);
        p.record_call(1, 0);
        p.record_call(1, 0);
        p.record_call(1, 0);
        assert_eq!(p.literal_count(2), 3); // var 1, pol 0 => idx 2
        assert_eq!(p.literal_count(0), 0);
        assert_eq!(p.literal_count(999), 0); // out of bounds
    }

    #[test]
    fn test_classify_empty() {
        let p = PgoProfile::new(4, 0);
        let bitmap = vec![0u64; 1]; // no compiled functions
        let classes = p.classify(&bitmap);
        assert!(classes.iter().all(|c| *c == HeatClass::Cold));
    }

    #[test]
    fn test_classify_distribution() {
        // 10 compiled functions with varying call counts
        let mut p = PgoProfile::new(5, 0);
        // Set counts: indices 0-9 with values 100,90,80,...,10
        for i in 0..10 {
            p.counters[i] = (100 - i as u32 * 10).max(1);
        }
        // Bitmap: all 10 literals have functions
        let bitmap = vec![0b1111111111u64]; // bits 0-9 set
        let classes = p.classify(&bitmap);

        // top 20% of 10 = 2 hot
        let hot_count = classes.iter().filter(|&&c| c == HeatClass::Hot).count();
        // next 30% of 10 = 3 warm
        let warm_count = classes.iter().filter(|&&c| c == HeatClass::Warm).count();
        // bottom 50% of 10 = 5 cold (includes the uncompiled ones)
        let cold_count = classes.iter().filter(|&&c| c == HeatClass::Cold).count();

        assert_eq!(hot_count, 2, "top 20% should be hot");
        assert_eq!(warm_count, 3, "middle 30% should be warm");
        assert_eq!(
            cold_count, 5,
            "bottom 50% should be cold (includes uncompiled)"
        );
    }
}
