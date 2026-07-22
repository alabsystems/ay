// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bucket-queue VSIDS for IC3/PDR short queries (#8476).
//!
//! Domain-restricted IC3/PDR queries are overwhelmingly short, so exact
//! activity ordering is overkill for them: variable selection runs on this
//! O(1) amortized bucket queue, which partitions variables into priority
//! classes by discretized activity magnitude, and only unusually hard
//! queries graduate to the standard binary heap (see
//! `Solver::bucket_queue_on_restart` in `solver/restart.rs`).
//!
//! Bucket assignment uses IEEE 754 exponent extraction (O(1) integer bit
//! ops) rather than floating-point log2. Activities are bucketed relative
//! to the maximum activity in the domain, giving fine granularity for the
//! actual activity range instead of wasting buckets on unused f64 exponents.

use crate::literal::Variable;

/// Maximum number of buckets. 32 covers typical IC3 domains well:
/// each bucket spans one IEEE 754 exponent value (a factor of 2),
/// so 32 buckets cover a 2^32 = 4 billion ratio between highest and
/// lowest activity. VSIDS activities in IC3 typically span 10-20 orders
/// of magnitude.
const MAX_BUCKETS: usize = 32;

/// Extract the biased exponent from an f64's IEEE 754 representation.
/// Returns 0 for zero/negative/subnormal values.
///
/// For normal positive f64 values, the biased exponent equals
/// floor(log2(value)) + 1023. This provides an O(1) integer-only
/// approximation of log2.
#[inline]
fn f64_exponent(value: f64) -> u32 {
    if value <= 0.0 {
        return 0;
    }
    let bits = value.to_bits();
    ((bits >> 52) & 0x7FF) as u32
}

/// Priority worklist over decision variables for IC3's short queries.
///
/// Variables live in one of `MAX_BUCKETS` priority classes; class 0 is
/// served first. Membership is a set: a variable is enqueued at most once
/// at any moment, no matter how often callers try to insert it, so each
/// membership yields at most one extraction. A cursor remembers the most
/// urgent class that may still hold entries, so extraction never rescans
/// classes it has already drained.
#[derive(Debug, Clone)]
pub(crate) struct BucketQueue {
    /// Per-class stacks of raw variable indices (class 0 = most urgent).
    /// Extraction order within a class is unspecified.
    buckets: [Vec<u32>; MAX_BUCKETS],
    /// Membership bitmap indexed by variable index; sized by
    /// `ensure_capacity` and grown on demand by `push`.
    in_queue: Vec<bool>,
    /// Most urgent class that may still be non-empty. `MAX_BUCKETS` means
    /// "known drained"; `push` pulls the cursor back whenever it files a
    /// variable below the current value.
    head: usize,
    /// Live entry count, i.e. `len()`.
    count: usize,
    /// Biased-exponent anchor captured by the last `build_from_domain`;
    /// `push_with_activity` buckets reinserted variables relative to it.
    /// Deliberately not reset by `clear`: it is only meaningful between a
    /// build and its matching query, and every build re-derives it.
    max_exponent: u32,
}

impl BucketQueue {
    /// A queue tracking no variables and holding no entries.
    /// `ensure_capacity` / `build_from_domain` size it before real use.
    pub(crate) fn new() -> Self {
        BucketQueue {
            buckets: std::array::from_fn(|_| Vec::new()),
            in_queue: Vec::new(),
            head: MAX_BUCKETS,
            count: 0,
            max_exponent: 0,
        }
    }

    /// Ensure the queue can track variables up to index `num_vars - 1`.
    pub(crate) fn ensure_capacity(&mut self, num_vars: usize) {
        if self.in_queue.len() < num_vars {
            self.in_queue.resize(num_vars, false);
        }
    }

    /// Compute the bucket index for an activity value relative to
    /// `max_exponent`. O(1) via integer bit operations only.
    ///
    /// Higher activity -> lower bucket index (higher priority).
    /// Each bucket spans one IEEE 754 exponent value (factor of 2).
    #[inline]
    fn activity_to_bucket_relative(activity: f64, max_exp: u32) -> usize {
        let exp = f64_exponent(activity);
        if exp == 0 {
            return MAX_BUCKETS - 1;
        }
        let diff = max_exp.saturating_sub(exp) as usize;
        diff.min(MAX_BUCKETS - 1)
    }

    /// Build the bucket queue from a set of domain variables and their
    /// EVSIDS activities. Clears any previous state.
    ///
    /// `domain_vars` contains variable indices (not `Variable` wrappers).
    /// `activities` is the full VSIDS activity array.
    ///
    /// Two-pass O(n) algorithm:
    /// 1. Find max exponent across domain variables
    /// 2. Assign each variable to its relative-exponent bucket
    ///
    /// No sorting required (previous implementation was O(n log n)).
    pub(crate) fn build_from_domain(&mut self, domain_vars: &[usize], activities: &[f64]) {
        self.clear();
        if domain_vars.is_empty() {
            return;
        }

        // Ensure capacity for all variable indices.
        let max_var = domain_vars.iter().copied().max().unwrap_or(0);
        self.ensure_capacity(max_var + 1);

        // Pass 1: find the maximum exponent across domain variables.
        let mut max_exp: u32 = 0;
        for &var_idx in domain_vars {
            let exp = f64_exponent(activities[var_idx]);
            if exp > max_exp {
                max_exp = exp;
            }
        }
        self.max_exponent = max_exp;

        // Pass 2: assign each variable to its relative-exponent bucket.
        let mut min_bucket = MAX_BUCKETS;
        for &var_idx in domain_vars {
            let bucket = Self::activity_to_bucket_relative(activities[var_idx], max_exp);
            self.buckets[bucket].push(var_idx as u32);
            self.in_queue[var_idx] = true;
            self.count += 1;
            if bucket < min_bucket {
                min_bucket = bucket;
            }
        }

        // Set head to the first non-empty bucket.
        self.head = min_bucket.min(MAX_BUCKETS);
    }

    /// File `var` under the given priority class (clamped to the valid
    /// range). Inserting a variable that is already enqueued is a no-op.
    /// O(1).
    #[inline]
    pub(crate) fn push(&mut self, var: Variable, bucket: usize) {
        let idx = var.index();
        self.ensure_capacity(idx + 1);
        if self.in_queue[idx] {
            return;
        }
        self.in_queue[idx] = true;
        let class = bucket.min(MAX_BUCKETS - 1);
        self.buckets[class].push(idx as u32);
        self.count += 1;
        // The new entry may be more urgent than anything the cursor has
        // left to visit; pull the cursor back so `pop` will see it.
        if class < self.head {
            self.head = class;
        }
    }

    /// Push a variable using its current activity, bucketed relative to
    /// the max exponent from the last `build_from_domain` call.
    ///
    /// This is used during backtracking when a domain variable becomes
    /// unassigned and needs to be reinserted into the bucket queue.
    /// Uses O(1) IEEE 754 exponent extraction for bucket computation.
    ///
    /// If the variable's activity has grown beyond `max_exponent` (due to
    /// bumps since the last build), it lands in bucket 0 (highest priority).
    #[inline]
    pub(crate) fn push_with_activity(&mut self, var: Variable, activities: &[f64]) {
        let idx = var.index();
        if idx < self.in_queue.len() && self.in_queue[idx] {
            return;
        }
        let bucket = Self::activity_to_bucket_relative(activities[idx], self.max_exponent);
        self.push(var, bucket);
    }

    /// Remove and return a variable from the most urgent non-empty class,
    /// or `None` when nothing is enqueued.
    ///
    /// Amortized O(1): the cursor only walks forward here, and each
    /// backward move happens in `push` and is paid for by that insertion,
    /// so total scan work over a workload is O(#operations + MAX_BUCKETS).
    #[inline]
    pub(crate) fn pop(&mut self) -> Option<Variable> {
        while let Some(class) = self.buckets.get_mut(self.head) {
            if let Some(raw) = class.pop() {
                self.in_queue[raw as usize] = false;
                self.count -= 1;
                return Some(Variable::new(raw));
            }
            // Class drained: the cursor never needs to revisit it until a
            // push files something there (which pulls the cursor back).
            self.head += 1;
        }
        None
    }

    /// Whether `var` is currently enqueued. O(1); variables beyond the
    /// tracked capacity are never members.
    #[inline]
    pub(crate) fn contains(&self, var: Variable) -> bool {
        self.in_queue.get(var.index()).copied().unwrap_or(false)
    }

    /// Drop every entry, leaving an empty, fully reusable queue.
    ///
    /// Cost is proportional to the number of live entries: the membership
    /// bitmap is un-set entry by entry while draining the classes, rather
    /// than wiped across the whole tracked capacity. That keeps per-query
    /// teardown cheap when the capacity far exceeds the restricted domain.
    pub(crate) fn clear(&mut self) {
        for class in &mut self.buckets {
            for raw in class.drain(..) {
                self.in_queue[raw as usize] = false;
            }
        }
        self.head = MAX_BUCKETS;
        self.count = 0;
    }

    /// True when nothing is enqueued.
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Number of enqueued variables.
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn len(&self) -> usize {
        self.count
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bucket_queue_empty() {
        let mut bq = BucketQueue::new();
        assert!(bq.is_empty());
        assert_eq!(bq.pop(), None);
    }

    #[test]
    fn test_bucket_queue_push_pop_single() {
        let mut bq = BucketQueue::new();
        bq.ensure_capacity(5);
        bq.push(Variable(3), 0);
        assert!(!bq.is_empty());
        assert_eq!(bq.len(), 1);
        assert_eq!(bq.pop(), Some(Variable(3)));
        assert!(bq.is_empty());
        assert_eq!(bq.pop(), None);
    }

    #[test]
    fn test_bucket_queue_priority_order() {
        let mut bq = BucketQueue::new();
        bq.ensure_capacity(5);
        // Lower bucket = higher priority
        bq.push(Variable(0), 3); // low priority
        bq.push(Variable(1), 1); // high priority
        bq.push(Variable(2), 2); // medium priority

        // Should pop in bucket order: 1 (bucket 1), 2 (bucket 2), 0 (bucket 3)
        assert_eq!(bq.pop(), Some(Variable(1)));
        assert_eq!(bq.pop(), Some(Variable(2)));
        assert_eq!(bq.pop(), Some(Variable(0)));
        assert!(bq.is_empty());
    }

    #[test]
    fn test_bucket_queue_same_bucket() {
        let mut bq = BucketQueue::new();
        bq.ensure_capacity(5);
        bq.push(Variable(0), 1);
        bq.push(Variable(1), 1);
        bq.push(Variable(2), 1);

        // All in same bucket -- LIFO order within bucket (Vec::pop)
        let v1 = bq.pop().unwrap();
        let v2 = bq.pop().unwrap();
        let v3 = bq.pop().unwrap();
        // Just check all three are returned
        let mut got = vec![v1.0, v2.0, v3.0];
        got.sort_unstable();
        assert_eq!(got, vec![0, 1, 2]);
        assert!(bq.is_empty());
    }

    #[test]
    fn test_bucket_queue_no_duplicate() {
        let mut bq = BucketQueue::new();
        bq.ensure_capacity(5);
        bq.push(Variable(2), 0);
        bq.push(Variable(2), 0); // duplicate -- should be no-op
        assert_eq!(bq.len(), 1);
        assert_eq!(bq.pop(), Some(Variable(2)));
        assert!(bq.is_empty());
    }

    #[test]
    fn test_bucket_queue_contains() {
        let mut bq = BucketQueue::new();
        bq.ensure_capacity(5);
        assert!(!bq.contains(Variable(1)));
        bq.push(Variable(1), 0);
        assert!(bq.contains(Variable(1)));
        bq.pop();
        assert!(!bq.contains(Variable(1)));
    }

    #[test]
    fn test_bucket_queue_clear() {
        let mut bq = BucketQueue::new();
        bq.ensure_capacity(5);
        bq.push(Variable(0), 0);
        bq.push(Variable(1), 1);
        bq.push(Variable(2), 2);
        assert_eq!(bq.len(), 3);

        bq.clear();
        assert!(bq.is_empty());
        assert_eq!(bq.len(), 0);
        assert!(!bq.contains(Variable(0)));
        assert!(!bq.contains(Variable(1)));
        assert!(!bq.contains(Variable(2)));
    }

    #[test]
    fn test_bucket_queue_build_from_domain() {
        // Activities spanning several orders of magnitude.
        // Relative exponent bucketing: each bucket is one factor-of-2.
        // 10.0 vs 5.0: exponent difference is 1 (2^3 vs 2^2) -> 1 bucket apart
        // 10.0 vs 0.5: exponent difference is ~4 -> 4 buckets apart
        let activities = vec![1.0, 5.0, 3.0, 0.5, 10.0];
        let domain_vars = vec![0, 1, 2, 3, 4];

        let mut bq = BucketQueue::new();
        bq.build_from_domain(&domain_vars, &activities);
        assert_eq!(bq.len(), 5);

        // Var 4 (act=10) has the highest exponent and should be popped first.
        let v1 = bq.pop().unwrap();
        assert_eq!(v1, Variable(4), "highest activity should be popped first");

        // All 5 variables must be returned.
        let mut rest = vec![v1.0];
        while let Some(v) = bq.pop() {
            rest.push(v.0);
        }
        rest.sort_unstable();
        assert_eq!(rest, vec![0, 1, 2, 3, 4]);
    }

    #[test]
    fn test_bucket_queue_build_from_domain_wide_spread() {
        // Activities with large exponent differences.
        // Relative bucketing: bucket = max_exp - this_exp.
        // 1e9 (exp ~30) vs 1.0 (exp 0 relative to max) -> bucket 30
        let activities = vec![1.0, 1e6, 1e3, 0.001, 1e9];
        let domain_vars = vec![0, 1, 2, 3, 4];

        let mut bq = BucketQueue::new();
        bq.build_from_domain(&domain_vars, &activities);
        assert_eq!(bq.len(), 5);

        // Pop order should respect relative exponent ordering:
        // var 4 (act=1e9) bucket 0
        // var 1 (act=1e6) bucket ~10
        // var 2 (act=1e3) bucket ~20
        // var 0 (act=1.0) bucket ~30
        // var 3 (act=0.001) bucket 31 (clamped)
        let v1 = bq.pop().unwrap();
        assert_eq!(v1, Variable(4), "highest activity should be popped first");

        let v2 = bq.pop().unwrap();
        assert_eq!(v2, Variable(1), "second highest activity");

        let v3 = bq.pop().unwrap();
        assert_eq!(v3, Variable(2), "third highest activity");

        // Remaining two
        let mut rest = vec![];
        while let Some(v) = bq.pop() {
            rest.push(v.0);
        }
        rest.sort_unstable();
        assert_eq!(rest, vec![0, 3]);
    }

    #[test]
    fn test_f64_exponent_basic() {
        // 1.0 = 2^0, biased exponent = 1023
        assert_eq!(f64_exponent(1.0), 1023);
        // 2.0 = 2^1, biased exponent = 1024
        assert_eq!(f64_exponent(2.0), 1024);
        // 0.5 = 2^(-1), biased exponent = 1022
        assert_eq!(f64_exponent(0.5), 1022);
        // 0.0 -> 0
        assert_eq!(f64_exponent(0.0), 0);
        // negative -> 0
        assert_eq!(f64_exponent(-5.0), 0);
    }

    #[test]
    fn test_activity_to_bucket_relative_monotonic() {
        // Higher activity must produce lower (or equal) bucket index.
        let max_exp = f64_exponent(1e100);
        let activities = [0.001, 0.01, 0.1, 1.0, 10.0, 100.0, 1e6, 1e12, 1e50, 1e100];
        for i in 1..activities.len() {
            let b_low = BucketQueue::activity_to_bucket_relative(activities[i - 1], max_exp);
            let b_high = BucketQueue::activity_to_bucket_relative(activities[i], max_exp);
            assert!(
                b_high <= b_low,
                "activity_to_bucket_relative must be monotonically non-increasing: \
                 act={} -> bucket {}, act={} -> bucket {}",
                activities[i - 1],
                b_low,
                activities[i],
                b_high
            );
        }
    }

    #[test]
    fn test_activity_to_bucket_relative_zero_and_negative() {
        assert_eq!(
            BucketQueue::activity_to_bucket_relative(0.0, 1023),
            MAX_BUCKETS - 1,
            "zero activity should map to lowest-priority bucket"
        );
        assert_eq!(
            BucketQueue::activity_to_bucket_relative(-1.0, 1023),
            MAX_BUCKETS - 1,
            "negative activity should map to lowest-priority bucket"
        );
    }

    #[test]
    fn test_activity_to_bucket_relative_within_bounds() {
        let max_exp = f64_exponent(f64::MAX);
        let test_values = [
            f64::MIN_POSITIVE,
            1e-300,
            1e-100,
            0.001,
            1.0,
            1e100,
            1e300,
            f64::MAX,
        ];
        for &act in &test_values {
            let b = BucketQueue::activity_to_bucket_relative(act, max_exp);
            assert!(
                b < MAX_BUCKETS,
                "bucket {b} out of range for activity {act}"
            );
        }
    }

    #[test]
    fn test_activity_to_bucket_relative_distinct_for_4x_difference() {
        // 4.0 vs 1.0 differ by 2 exponent values -> should land in
        // distinct buckets (one bucket per factor-of-2).
        let max_exp = f64_exponent(4.0);
        let b_low = BucketQueue::activity_to_bucket_relative(1.0, max_exp);
        let b_high = BucketQueue::activity_to_bucket_relative(4.0, max_exp);
        assert!(
            b_high < b_low,
            "4x difference should produce distinct buckets: \
             1.0 -> {b_low}, 4.0 -> {b_high}"
        );
    }

    #[test]
    fn test_push_with_activity_uses_max_exponent() {
        // Build from domain sets max_exponent. push_with_activity should
        // use it for consistent relative bucketing.
        let activities = vec![1.0, 8.0, 64.0];
        let domain_vars = vec![0, 1, 2];

        let mut bq = BucketQueue::new();
        bq.build_from_domain(&domain_vars, &activities);

        // Pop all, then re-push var 1 using push_with_activity.
        while bq.pop().is_some() {}

        bq.push_with_activity(Variable(1), &activities);
        assert!(bq.contains(Variable(1)));
        let v = bq.pop().unwrap();
        assert_eq!(v, Variable(1));
    }

    #[test]
    fn test_bucket_queue_head_advances_correctly() {
        let mut bq = BucketQueue::new();
        bq.ensure_capacity(3);
        bq.push(Variable(0), 5);
        bq.push(Variable(1), 10);

        // Pop from bucket 5 first (lower index = higher priority)
        let v = bq.pop().unwrap();
        assert_eq!(v, Variable(0));

        // Now head should advance to bucket 10
        let v = bq.pop().unwrap();
        assert_eq!(v, Variable(1));

        assert!(bq.is_empty());
    }
}
