// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Feasible-set data structure for NLSAT-style look-ahead and arithmetic
//! propagation branching.
//!
//! A `FeasibleSet` represents a union of disjoint intervals on the real line
//! where a polynomial constraint is satisfied. Used by the clauseSMT
//! techniques (Wang, ASE 2025) for:
//! - **Clause-level feasible-set look-ahead**: guide literal decisions toward
//!   arithmetic feasibility.
//! - **Arithmetic propagation branching**: classify variables as blocked, fixed,
//!   or narrowed based on feasible-set intersection.
//!
//! Reference: "Improving NLSAT for Nonlinear Real Arithmetic" (Wang, ASE 2025),
//! arXiv:2406.02122.

use num_rational::BigRational;
use num_traits::{One, Zero};
use std::cmp::Ordering;

/// An endpoint of an interval: either a finite value or +/- infinity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Endpoint {
    /// Negative infinity (only valid as a lower bound).
    NegInf,
    /// A finite value.
    Finite(BigRational),
    /// Positive infinity (only valid as an upper bound).
    PosInf,
}

impl Endpoint {
    /// Compare two endpoints. NegInf < Finite(_) < PosInf.
    fn cmp_value(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::NegInf, Self::NegInf) => Ordering::Equal,
            (Self::NegInf, _) => Ordering::Less,
            (_, Self::NegInf) => Ordering::Greater,
            (Self::PosInf, Self::PosInf) => Ordering::Equal,
            (Self::PosInf, _) => Ordering::Greater,
            (_, Self::PosInf) => Ordering::Less,
            (Self::Finite(a), Self::Finite(b)) => a.cmp(b),
        }
    }
}

/// A single interval [lo, hi] with optional strict endpoints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Interval {
    /// Lower bound.
    pub lo: Endpoint,
    /// Whether the lower bound is strict (open).
    pub lo_strict: bool,
    /// Upper bound.
    pub hi: Endpoint,
    /// Whether the upper bound is strict (open).
    pub hi_strict: bool,
}

impl Interval {
    /// Create a new interval.
    fn new(lo: Endpoint, lo_strict: bool, hi: Endpoint, hi_strict: bool) -> Self {
        Self {
            lo,
            lo_strict,
            hi,
            hi_strict,
        }
    }

    /// Check if this interval is a single point [a, a].
    fn as_singleton(&self) -> Option<&BigRational> {
        if self.lo_strict || self.hi_strict {
            return None;
        }
        if let (Endpoint::Finite(a), Endpoint::Finite(b)) = (&self.lo, &self.hi) {
            if a == b {
                return Some(a);
            }
        }
        None
    }

    /// Check if a point is contained in this interval.
    fn contains(&self, v: &BigRational) -> bool {
        let lo_ok = match &self.lo {
            Endpoint::NegInf => true,
            Endpoint::PosInf => false,
            Endpoint::Finite(a) => {
                if self.lo_strict {
                    v > a
                } else {
                    v >= a
                }
            }
        };
        if !lo_ok {
            return false;
        }
        match &self.hi {
            Endpoint::NegInf => false,
            Endpoint::PosInf => true,
            Endpoint::Finite(b) => {
                if self.hi_strict {
                    v < b
                } else {
                    v <= b
                }
            }
        }
    }

    /// Intersect two intervals. Returns None if the intersection is empty.
    fn intersect(&self, other: &Self) -> Option<Self> {
        // Take the larger lower bound
        let (lo, lo_strict) = match self.lo.cmp_value(&other.lo) {
            Ordering::Less => (other.lo.clone(), other.lo_strict),
            Ordering::Greater => (self.lo.clone(), self.lo_strict),
            Ordering::Equal => {
                // Same value: strict if either is strict
                (self.lo.clone(), self.lo_strict || other.lo_strict)
            }
        };
        // Take the smaller upper bound
        let (hi, hi_strict) = match self.hi.cmp_value(&other.hi) {
            Ordering::Less => (self.hi.clone(), self.hi_strict),
            Ordering::Greater => (other.hi.clone(), other.hi_strict),
            Ordering::Equal => (self.hi.clone(), self.hi_strict || other.hi_strict),
        };

        let result = Self::new(lo, lo_strict, hi, hi_strict);
        if result.is_really_empty() {
            None
        } else {
            Some(result)
        }
    }

    /// Stricter emptiness check that handles the [a,a] with strict bounds case.
    fn is_really_empty(&self) -> bool {
        match self.lo.cmp_value(&self.hi) {
            Ordering::Greater => true,
            Ordering::Equal => self.lo_strict || self.hi_strict,
            Ordering::Less => false,
        }
    }

    /// Check if two intervals overlap or are adjacent (for merging in union).
    fn overlaps_or_adjacent(&self, other: &Self) -> bool {
        // self.hi >= other.lo (with strictness check)
        match self.hi.cmp_value(&other.lo) {
            Ordering::Less => false,
            Ordering::Greater => true,
            Ordering::Equal => {
                // [_, a] and [a, _] overlap if at least one is non-strict
                !(self.hi_strict && other.lo_strict)
            }
        }
    }

    /// Merge two overlapping intervals into one.
    fn merge(&self, other: &Self) -> Self {
        let (lo, lo_strict) = match self.lo.cmp_value(&other.lo) {
            Ordering::Less => (self.lo.clone(), self.lo_strict),
            Ordering::Greater => (other.lo.clone(), other.lo_strict),
            Ordering::Equal => {
                // Same value: non-strict if either is non-strict (wider)
                (self.lo.clone(), self.lo_strict && other.lo_strict)
            }
        };
        let (hi, hi_strict) = match self.hi.cmp_value(&other.hi) {
            Ordering::Less => (other.hi.clone(), other.hi_strict),
            Ordering::Greater => (self.hi.clone(), self.hi_strict),
            Ordering::Equal => (self.hi.clone(), self.hi_strict && other.hi_strict),
        };
        Self::new(lo, lo_strict, hi, hi_strict)
    }

    /// Pick a rational value from this interval. Returns None if empty.
    fn pick_value(&self) -> Option<BigRational> {
        if self.is_really_empty() {
            return None;
        }
        match (&self.lo, &self.hi) {
            (Endpoint::NegInf, Endpoint::PosInf) => Some(BigRational::zero()),
            (Endpoint::NegInf, Endpoint::Finite(b)) => {
                if self.hi_strict {
                    Some(b - BigRational::one())
                } else {
                    Some(b.clone())
                }
            }
            (Endpoint::Finite(a), Endpoint::PosInf) => {
                if self.lo_strict {
                    Some(a + BigRational::one())
                } else {
                    Some(a.clone())
                }
            }
            (Endpoint::Finite(a), Endpoint::Finite(b)) => {
                if a == b {
                    // Singleton [a, a]
                    return Some(a.clone());
                }
                // Midpoint (a + b) / 2
                let two = BigRational::from_integer(2.into());
                let mid = (a + b) / two;
                // mid is always strictly between a and b when a < b
                Some(mid)
            }
            _ => None,
        }
    }
}

/// A union of disjoint, sorted intervals on the real line.
///
/// Invariant: intervals are sorted by lower bound and are disjoint
/// (no two intervals overlap or are adjacent).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FeasibleSet {
    /// Sorted, disjoint intervals.
    intervals: Vec<Interval>,
}

impl FeasibleSet {
    /// Create an empty feasible set.
    pub fn empty() -> Self {
        Self {
            intervals: Vec::new(),
        }
    }

    /// Create the full real line (-inf, +inf).
    pub fn full() -> Self {
        Self {
            intervals: vec![Interval::new(
                Endpoint::NegInf,
                true,
                Endpoint::PosInf,
                true,
            )],
        }
    }

    /// Create a singleton set {v} = [v, v].
    pub fn singleton(v: BigRational) -> Self {
        Self {
            intervals: vec![Interval::new(
                Endpoint::Finite(v.clone()),
                false,
                Endpoint::Finite(v),
                false,
            )],
        }
    }

    /// Create a set from a single interval.
    pub fn from_interval(
        lo: Option<BigRational>,
        lo_strict: bool,
        hi: Option<BigRational>,
        hi_strict: bool,
    ) -> Self {
        let lo_ep = match lo {
            Some(v) => Endpoint::Finite(v),
            None => Endpoint::NegInf,
        };
        let hi_ep = match hi {
            Some(v) => Endpoint::Finite(v),
            None => Endpoint::PosInf,
        };
        let iv = Interval::new(lo_ep, lo_strict, hi_ep, hi_strict);
        if iv.is_really_empty() {
            Self::empty()
        } else {
            Self {
                intervals: vec![iv],
            }
        }
    }

    /// Check if the set is empty.
    pub fn is_empty(&self) -> bool {
        self.intervals.is_empty()
    }

    /// If the set is a single point, return it.
    pub fn is_singleton(&self) -> Option<BigRational> {
        if self.intervals.len() != 1 {
            return None;
        }
        self.intervals[0].as_singleton().cloned()
    }

    /// Check if a point is contained in the set.
    pub fn contains_point(&self, v: &BigRational) -> bool {
        self.intervals.iter().any(|iv| iv.contains(v))
    }

    /// Compute the union of two feasible sets.
    pub fn union(&self, other: &Self) -> Self {
        if self.is_empty() {
            return other.clone();
        }
        if other.is_empty() {
            return self.clone();
        }

        // Merge all intervals from both sets, then normalize
        let mut all: Vec<Interval> =
            Vec::with_capacity(self.intervals.len() + other.intervals.len());
        all.extend(self.intervals.iter().cloned());
        all.extend(other.intervals.iter().cloned());

        // Sort by lower bound
        all.sort_by(|a, b| {
            let cmp = a.lo.cmp_value(&b.lo);
            if cmp != Ordering::Equal {
                return cmp;
            }
            // If same lower bound, non-strict comes first (wider)
            a.lo_strict.cmp(&b.lo_strict)
        });

        // Merge overlapping/adjacent intervals
        let mut merged: Vec<Interval> = Vec::with_capacity(all.len());
        for iv in all {
            if let Some(last) = merged.last_mut() {
                if last.overlaps_or_adjacent(&iv) {
                    *last = last.merge(&iv);
                    continue;
                }
            }
            merged.push(iv);
        }

        Self { intervals: merged }
    }

    /// Compute the intersection of two feasible sets.
    pub fn intersection(&self, other: &Self) -> Self {
        if self.is_empty() || other.is_empty() {
            return Self::empty();
        }

        let mut result = Vec::new();
        let mut i = 0;
        let mut j = 0;

        while i < self.intervals.len() && j < other.intervals.len() {
            let a = &self.intervals[i];
            let b = &other.intervals[j];

            if let Some(inter) = a.intersect(b) {
                result.push(inter);
            }

            // Advance the interval that ends first
            match a.hi.cmp_value(&b.hi) {
                Ordering::Less => i += 1,
                Ordering::Greater => j += 1,
                Ordering::Equal => {
                    i += 1;
                    j += 1;
                }
            }
        }

        Self { intervals: result }
    }

    /// Pick a rational value from the feasible set, preferring the midpoint
    /// of the first interval.
    pub fn pick_value(&self) -> Option<BigRational> {
        self.intervals.first().and_then(Interval::pick_value)
    }

    /// Return the number of disjoint intervals in this set.
    pub fn num_intervals(&self) -> usize {
        self.intervals.len()
    }
}

/// Classification of a feasible-set intersection result for arithmetic
/// propagation branching (clauseSMT Technique 2).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FeasibilityClass {
    /// The feasible set is empty: conflicts are unavoidable for this variable.
    /// The variable should be prioritized for branching (highest priority).
    Blocked,
    /// The feasible set is a single point: the variable's value is determined.
    /// Second-highest priority for branching.
    Fixed(BigRational),
    /// The feasible set is non-empty and non-singleton: search space is reduced
    /// but not determined. Use default VSIDS branching.
    Narrowed,
}

impl FeasibleSet {
    /// Classify the feasible set for arithmetic propagation branching.
    pub fn classify(&self) -> FeasibilityClass {
        if self.is_empty() {
            return FeasibilityClass::Blocked;
        }
        if let Some(v) = self.is_singleton() {
            return FeasibilityClass::Fixed(v);
        }
        FeasibilityClass::Narrowed
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(n.into())
    }

    fn rat_frac(n: i64, d: i64) -> BigRational {
        BigRational::new(n.into(), d.into())
    }

    // ====== Interval tests ======

    #[test]
    fn test_interval_singleton_contains() {
        let iv = Interval::new(
            Endpoint::Finite(rat(3)),
            false,
            Endpoint::Finite(rat(3)),
            false,
        );
        assert!(iv.contains(&rat(3)));
        assert!(!iv.contains(&rat(2)));
        assert!(!iv.contains(&rat(4)));
    }

    #[test]
    fn test_interval_open_does_not_contain_endpoint() {
        let iv = Interval::new(
            Endpoint::Finite(rat(1)),
            true,
            Endpoint::Finite(rat(5)),
            true,
        );
        assert!(!iv.contains(&rat(1)));
        assert!(!iv.contains(&rat(5)));
        assert!(iv.contains(&rat(3)));
    }

    #[test]
    fn test_interval_closed_contains_endpoints() {
        let iv = Interval::new(
            Endpoint::Finite(rat(1)),
            false,
            Endpoint::Finite(rat(5)),
            false,
        );
        assert!(iv.contains(&rat(1)));
        assert!(iv.contains(&rat(5)));
        assert!(iv.contains(&rat(3)));
    }

    #[test]
    fn test_interval_infinite() {
        let iv = Interval::new(Endpoint::NegInf, true, Endpoint::PosInf, true);
        assert!(iv.contains(&rat(0)));
        assert!(iv.contains(&rat(-1000)));
        assert!(iv.contains(&rat(1000)));
    }

    #[test]
    fn test_interval_half_open() {
        // [2, +inf)
        let iv = Interval::new(Endpoint::Finite(rat(2)), false, Endpoint::PosInf, true);
        assert!(iv.contains(&rat(2)));
        assert!(iv.contains(&rat(100)));
        assert!(!iv.contains(&rat(1)));
    }

    #[test]
    fn test_interval_empty_inverted() {
        let iv = Interval::new(
            Endpoint::Finite(rat(5)),
            false,
            Endpoint::Finite(rat(1)),
            false,
        );
        assert!(iv.is_really_empty());
    }

    #[test]
    fn test_interval_empty_open_singleton() {
        let iv = Interval::new(
            Endpoint::Finite(rat(3)),
            true,
            Endpoint::Finite(rat(3)),
            false,
        );
        assert!(iv.is_really_empty());
    }

    #[test]
    fn test_interval_pick_value_singleton() {
        let iv = Interval::new(
            Endpoint::Finite(rat(7)),
            false,
            Endpoint::Finite(rat(7)),
            false,
        );
        assert_eq!(iv.pick_value(), Some(rat(7)));
    }

    #[test]
    fn test_interval_pick_value_midpoint() {
        let iv = Interval::new(
            Endpoint::Finite(rat(2)),
            false,
            Endpoint::Finite(rat(4)),
            false,
        );
        assert_eq!(iv.pick_value(), Some(rat(3)));
    }

    #[test]
    fn test_interval_pick_value_open_midpoint() {
        let iv = Interval::new(
            Endpoint::Finite(rat(0)),
            true,
            Endpoint::Finite(rat(10)),
            true,
        );
        assert_eq!(iv.pick_value(), Some(rat(5)));
    }

    #[test]
    fn test_interval_pick_value_neg_inf() {
        let iv = Interval::new(Endpoint::NegInf, true, Endpoint::Finite(rat(5)), false);
        assert_eq!(iv.pick_value(), Some(rat(5)));
    }

    #[test]
    fn test_interval_pick_value_pos_inf() {
        let iv = Interval::new(Endpoint::Finite(rat(3)), false, Endpoint::PosInf, true);
        assert_eq!(iv.pick_value(), Some(rat(3)));
    }

    #[test]
    fn test_interval_pick_value_full() {
        let iv = Interval::new(Endpoint::NegInf, true, Endpoint::PosInf, true);
        assert_eq!(iv.pick_value(), Some(rat(0)));
    }

    // ====== Interval intersection tests ======

    #[test]
    fn test_interval_intersect_overlap() {
        let a = Interval::new(
            Endpoint::Finite(rat(1)),
            false,
            Endpoint::Finite(rat(5)),
            false,
        );
        let b = Interval::new(
            Endpoint::Finite(rat(3)),
            false,
            Endpoint::Finite(rat(7)),
            false,
        );
        let result = a.intersect(&b);
        assert!(result.is_some());
        let r = result.expect("should intersect");
        assert_eq!(r.lo, Endpoint::Finite(rat(3)));
        assert_eq!(r.hi, Endpoint::Finite(rat(5)));
        assert!(!r.lo_strict);
        assert!(!r.hi_strict);
    }

    #[test]
    fn test_interval_intersect_disjoint() {
        let a = Interval::new(
            Endpoint::Finite(rat(1)),
            false,
            Endpoint::Finite(rat(3)),
            false,
        );
        let b = Interval::new(
            Endpoint::Finite(rat(5)),
            false,
            Endpoint::Finite(rat(7)),
            false,
        );
        assert!(a.intersect(&b).is_none());
    }

    #[test]
    fn test_interval_intersect_touching_open() {
        let a = Interval::new(
            Endpoint::Finite(rat(1)),
            false,
            Endpoint::Finite(rat(3)),
            true,
        );
        let b = Interval::new(
            Endpoint::Finite(rat(3)),
            true,
            Endpoint::Finite(rat(5)),
            false,
        );
        assert!(a.intersect(&b).is_none());
    }

    #[test]
    fn test_interval_intersect_touching_closed() {
        let a = Interval::new(
            Endpoint::Finite(rat(1)),
            false,
            Endpoint::Finite(rat(3)),
            false,
        );
        let b = Interval::new(
            Endpoint::Finite(rat(3)),
            false,
            Endpoint::Finite(rat(5)),
            false,
        );
        let result = a.intersect(&b);
        assert!(result.is_some());
        let r = result.expect("should produce singleton");
        assert_eq!(r.as_singleton(), Some(&rat(3)));
    }

    // ====== FeasibleSet tests ======

    #[test]
    fn test_feasible_set_empty() {
        let fs = FeasibleSet::empty();
        assert!(fs.is_empty());
        assert!(!fs.contains_point(&rat(0)));
        assert_eq!(fs.pick_value(), None);
        assert_eq!(fs.classify(), FeasibilityClass::Blocked);
    }

    #[test]
    fn test_feasible_set_full() {
        let fs = FeasibleSet::full();
        assert!(!fs.is_empty());
        assert!(fs.contains_point(&rat(0)));
        assert!(fs.contains_point(&rat(-999)));
        assert_eq!(fs.classify(), FeasibilityClass::Narrowed);
    }

    #[test]
    fn test_feasible_set_singleton() {
        let fs = FeasibleSet::singleton(rat(42));
        assert!(!fs.is_empty());
        assert!(fs.contains_point(&rat(42)));
        assert!(!fs.contains_point(&rat(41)));
        assert_eq!(fs.is_singleton(), Some(rat(42)));
        assert_eq!(fs.classify(), FeasibilityClass::Fixed(rat(42)));
    }

    #[test]
    fn test_feasible_set_from_interval() {
        let fs = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(5)), false);
        assert!(!fs.is_empty());
        assert!(fs.contains_point(&rat(1)));
        assert!(fs.contains_point(&rat(3)));
        assert!(fs.contains_point(&rat(5)));
        assert!(!fs.contains_point(&rat(0)));
        assert!(!fs.contains_point(&rat(6)));
    }

    #[test]
    fn test_feasible_set_from_interval_empty() {
        let fs = FeasibleSet::from_interval(Some(rat(5)), false, Some(rat(1)), false);
        assert!(fs.is_empty());
    }

    #[test]
    fn test_feasible_set_union_disjoint() {
        let a = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(3)), false);
        let b = FeasibleSet::from_interval(Some(rat(5)), false, Some(rat(7)), false);
        let u = a.union(&b);
        assert_eq!(u.num_intervals(), 2);
        assert!(u.contains_point(&rat(2)));
        assert!(u.contains_point(&rat(6)));
        assert!(!u.contains_point(&rat(4)));
    }

    #[test]
    fn test_feasible_set_union_overlapping() {
        let a = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(5)), false);
        let b = FeasibleSet::from_interval(Some(rat(3)), false, Some(rat(7)), false);
        let u = a.union(&b);
        assert_eq!(u.num_intervals(), 1);
        assert!(u.contains_point(&rat(1)));
        assert!(u.contains_point(&rat(7)));
    }

    #[test]
    fn test_feasible_set_union_adjacent() {
        let a = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(3)), false);
        let b = FeasibleSet::from_interval(Some(rat(3)), false, Some(rat(5)), false);
        let u = a.union(&b);
        assert_eq!(u.num_intervals(), 1);
        assert!(u.contains_point(&rat(1)));
        assert!(u.contains_point(&rat(3)));
        assert!(u.contains_point(&rat(5)));
    }

    #[test]
    fn test_feasible_set_union_with_empty() {
        let a = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(3)), false);
        let e = FeasibleSet::empty();
        assert_eq!(a.union(&e), a);
        assert_eq!(e.union(&a), a);
    }

    #[test]
    fn test_feasible_set_intersection_overlap() {
        let a = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(5)), false);
        let b = FeasibleSet::from_interval(Some(rat(3)), false, Some(rat(7)), false);
        let inter = a.intersection(&b);
        assert_eq!(inter.num_intervals(), 1);
        assert!(inter.contains_point(&rat(3)));
        assert!(inter.contains_point(&rat(5)));
        assert!(!inter.contains_point(&rat(2)));
        assert!(!inter.contains_point(&rat(6)));
    }

    #[test]
    fn test_feasible_set_intersection_disjoint() {
        let a = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(3)), false);
        let b = FeasibleSet::from_interval(Some(rat(5)), false, Some(rat(7)), false);
        let inter = a.intersection(&b);
        assert!(inter.is_empty());
    }

    #[test]
    fn test_feasible_set_intersection_with_full() {
        let a = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(5)), false);
        let f = FeasibleSet::full();
        let inter = a.intersection(&f);
        assert_eq!(inter.num_intervals(), 1);
        assert!(inter.contains_point(&rat(3)));
    }

    #[test]
    fn test_feasible_set_intersection_with_empty() {
        let a = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(5)), false);
        let e = FeasibleSet::empty();
        assert!(a.intersection(&e).is_empty());
    }

    #[test]
    fn test_feasible_set_intersection_multi_interval() {
        // a = [1,3] U [5,7]
        let a1 = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(3)), false);
        let a2 = FeasibleSet::from_interval(Some(rat(5)), false, Some(rat(7)), false);
        let a = a1.union(&a2);
        // b = [2,6]
        let b = FeasibleSet::from_interval(Some(rat(2)), false, Some(rat(6)), false);
        let inter = a.intersection(&b);
        // Result should be [2,3] U [5,6]
        assert_eq!(inter.num_intervals(), 2);
        assert!(inter.contains_point(&rat(2)));
        assert!(inter.contains_point(&rat(3)));
        assert!(!inter.contains_point(&rat(4)));
        assert!(inter.contains_point(&rat(5)));
        assert!(inter.contains_point(&rat(6)));
        assert!(!inter.contains_point(&rat(7)));
    }

    #[test]
    fn test_feasible_set_pick_value() {
        let fs = FeasibleSet::from_interval(Some(rat(2)), false, Some(rat(8)), false);
        let v = fs.pick_value().expect("should pick a value");
        assert!(v >= rat(2) && v <= rat(8));
    }

    #[test]
    fn test_feasible_set_classify_blocked() {
        assert_eq!(FeasibleSet::empty().classify(), FeasibilityClass::Blocked);
    }

    #[test]
    fn test_feasible_set_classify_fixed() {
        let fs = FeasibleSet::singleton(rat(5));
        assert_eq!(fs.classify(), FeasibilityClass::Fixed(rat(5)));
    }

    #[test]
    fn test_feasible_set_classify_narrowed() {
        let fs = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(3)), false);
        assert_eq!(fs.classify(), FeasibilityClass::Narrowed);
    }

    #[test]
    fn test_feasible_set_half_open_interval() {
        // (-inf, 5)
        let fs = FeasibleSet::from_interval(None, true, Some(rat(5)), true);
        assert!(fs.contains_point(&rat(0)));
        assert!(fs.contains_point(&rat(-100)));
        assert!(!fs.contains_point(&rat(5)));
        assert!(!fs.contains_point(&rat(6)));
    }

    #[test]
    fn test_feasible_set_fractional() {
        let half = rat_frac(1, 2);
        let three_halves = rat_frac(3, 2);
        let fs = FeasibleSet::from_interval(
            Some(half.clone()),
            false,
            Some(three_halves.clone()),
            false,
        );
        assert!(fs.contains_point(&BigRational::one()));
        assert!(fs.contains_point(&half));
        assert!(fs.contains_point(&three_halves));
        assert!(!fs.contains_point(&rat(0)));
        assert!(!fs.contains_point(&rat(2)));
    }

    // ====== Additional FeasibleSet tests (#8460) ======

    /// Complement-like gap: (-inf,1] U [3,+inf) should exclude (1,3).
    #[test]
    fn test_feasible_set_complement_like_gap_contains() {
        let left = FeasibleSet::from_interval(None, true, Some(rat(1)), false);
        let right = FeasibleSet::from_interval(Some(rat(3)), false, None, true);
        let fs = left.union(&right);

        assert_eq!(fs.num_intervals(), 2);
        assert!(fs.contains_point(&rat(-100)));
        assert!(fs.contains_point(&rat(1)));
        assert!(!fs.contains_point(&rat(2)));
        assert!(!fs.contains_point(&rat_frac(3, 2)));
        assert!(fs.contains_point(&rat(3)));
        assert!(fs.contains_point(&rat(100)));
    }

    /// Union of three disjoint intervals: [1,2] U [4,5] U [7,8].
    #[test]
    fn test_feasible_set_union_three_disjoint_intervals() {
        let a = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(2)), false);
        let b = FeasibleSet::from_interval(Some(rat(4)), false, Some(rat(5)), false);
        let c = FeasibleSet::from_interval(Some(rat(7)), false, Some(rat(8)), false);
        let fs = a.union(&b).union(&c);

        assert_eq!(fs.num_intervals(), 3);
        assert!(fs.contains_point(&rat(1)));
        assert!(fs.contains_point(&rat(5)));
        assert!(fs.contains_point(&rat(8)));
        assert!(!fs.contains_point(&rat(3)));
        assert!(!fs.contains_point(&rat(6)));
    }

    /// Union of three adjacent intervals [1,2] U [2,3] U [3,4] merges into [1,4].
    #[test]
    fn test_feasible_set_union_merges_three_adjacent_intervals() {
        let a = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(2)), false);
        let b = FeasibleSet::from_interval(Some(rat(2)), false, Some(rat(3)), false);
        let c = FeasibleSet::from_interval(Some(rat(3)), false, Some(rat(4)), false);
        let fs = a.union(&b).union(&c);

        assert_eq!(fs.num_intervals(), 1);
        assert!(fs.contains_point(&rat(1)));
        assert!(fs.contains_point(&rat(2)));
        assert!(fs.contains_point(&rat(3)));
        assert!(fs.contains_point(&rat(4)));
        assert!(!fs.contains_point(&rat(0)));
        assert!(!fs.contains_point(&rat(5)));
    }

    /// Intersection where multi-interval set has only one interval fully covered.
    #[test]
    fn test_feasible_set_intersection_multi_interval_one_fully_covered() {
        let a = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(2)), false);
        let b = FeasibleSet::from_interval(Some(rat(4)), false, Some(rat(5)), false);
        let c = FeasibleSet::from_interval(Some(rat(7)), false, Some(rat(8)), false);
        let multi = a.union(&b).union(&c);
        let cover = FeasibleSet::from_interval(Some(rat(3)), false, Some(rat(6)), false);
        let inter = multi.intersection(&cover);

        assert_eq!(inter.num_intervals(), 1);
        assert!(inter.contains_point(&rat(4)));
        assert!(inter.contains_point(&rat_frac(9, 2)));
        assert!(inter.contains_point(&rat(5)));
        assert!(!inter.contains_point(&rat(2)));
        assert!(!inter.contains_point(&rat(7)));
    }

    /// from_interval with both strict bounds at same point => empty.
    #[test]
    fn test_feasible_set_from_interval_strict_same_endpoints_empty() {
        let fs = FeasibleSet::from_interval(Some(rat(5)), true, Some(rat(5)), true);
        assert!(fs.is_empty());
        assert_eq!(fs, FeasibleSet::empty());
    }

    /// from_interval with strict lower at same point as closed upper => empty.
    #[test]
    fn test_feasible_set_from_interval_half_open_strict_lo_same_endpoints_empty() {
        let fs = FeasibleSet::from_interval(Some(rat(3)), true, Some(rat(3)), false);
        assert!(fs.is_empty());
        assert_eq!(fs.pick_value(), None);
    }

    /// pick_value on disjoint multi-interval set returns from the first interval.
    #[test]
    fn test_feasible_set_pick_value_disjoint_multi_interval_uses_first_interval() {
        let a = FeasibleSet::from_interval(Some(rat(2)), false, Some(rat(4)), false);
        let b = FeasibleSet::from_interval(Some(rat(10)), false, Some(rat(12)), false);
        let fs = a.union(&b);

        assert_eq!(fs.pick_value(), Some(rat(3)));
    }

    /// pick_value on singleton returns that value.
    #[test]
    fn test_feasible_set_pick_value_singleton_returns_singleton() {
        let fs = FeasibleSet::singleton(rat(9));
        assert_eq!(fs.pick_value(), Some(rat(9)));
    }

    /// is_singleton on a set with 2 singleton intervals returns None.
    #[test]
    fn test_feasible_set_is_singleton_multi_interval_returns_none() {
        let a = FeasibleSet::singleton(rat(1));
        let b = FeasibleSet::singleton(rat(3));
        let fs = a.union(&b);

        assert_eq!(fs.is_singleton(), None);
    }

    /// is_singleton on a non-degenerate interval returns None.
    #[test]
    fn test_feasible_set_is_singleton_non_degenerate_interval_returns_none() {
        let fs = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(2)), false);
        assert_eq!(fs.is_singleton(), None);
    }

    /// classify on multi-interval set => Narrowed.
    #[test]
    fn test_feasible_set_classify_multi_interval_narrowed() {
        let a = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(2)), false);
        let b = FeasibleSet::from_interval(Some(rat(4)), false, Some(rat(5)), false);
        let fs = a.union(&b);

        assert_eq!(fs.classify(), FeasibilityClass::Narrowed);
    }

    /// Union of two empty sets is empty.
    #[test]
    fn test_feasible_set_union_empty_with_empty() {
        let a = FeasibleSet::empty();
        let b = FeasibleSet::empty();
        let fs = a.union(&b);

        assert!(fs.is_empty());
        assert_eq!(fs, FeasibleSet::empty());
    }

    /// Intersection of full with full is full.
    #[test]
    fn test_feasible_set_intersection_full_with_full() {
        let a = FeasibleSet::full();
        let b = FeasibleSet::full();
        let inter = a.intersection(&b);

        assert_eq!(inter, FeasibleSet::full());
        assert!(inter.contains_point(&rat(-123)));
        assert!(inter.contains_point(&rat(456)));
    }

    /// Intersection of two touching closed intervals produces singleton.
    #[test]
    fn test_feasible_set_intersection_touching_closed_produces_singleton() {
        let a = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(3)), false);
        let b = FeasibleSet::from_interval(Some(rat(3)), false, Some(rat(5)), false);
        let inter = a.intersection(&b);

        assert_eq!(inter.num_intervals(), 1);
        assert_eq!(inter.is_singleton(), Some(rat(3)));
        assert!(inter.contains_point(&rat(3)));
        assert!(!inter.contains_point(&rat(2)));
        assert!(!inter.contains_point(&rat(4)));
    }

    /// Union is commutative.
    #[test]
    fn test_feasible_set_union_is_commutative() {
        let a = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(3)), false);
        let b = FeasibleSet::from_interval(Some(rat(5)), false, Some(rat(7)), false);

        assert_eq!(a.union(&b), b.union(&a));
    }

    /// Intersection is commutative.
    #[test]
    fn test_feasible_set_intersection_is_commutative() {
        let a = FeasibleSet::from_interval(Some(rat(1)), false, Some(rat(5)), false);
        let b = FeasibleSet::from_interval(Some(rat(3)), false, Some(rat(7)), false);

        assert_eq!(a.intersection(&b), b.intersection(&a));
    }

    /// Intersection of identical singletons is that singleton.
    #[test]
    fn test_feasible_set_intersection_same_singletons_is_singleton() {
        let a = FeasibleSet::singleton(rat(4));
        let b = FeasibleSet::singleton(rat(4));
        let inter = a.intersection(&b);

        assert_eq!(inter, FeasibleSet::singleton(rat(4)));
        assert_eq!(inter.is_singleton(), Some(rat(4)));
    }

    /// Intersection of different singletons is empty.
    #[test]
    fn test_feasible_set_intersection_different_singletons_is_empty() {
        let a = FeasibleSet::singleton(rat(4));
        let b = FeasibleSet::singleton(rat(5));
        let inter = a.intersection(&b);

        assert!(inter.is_empty());
        assert_ne!(inter, FeasibleSet::singleton(rat(4)));
    }

    /// Large rational values (10000/7 etc.) should be handled correctly.
    #[test]
    fn test_feasible_set_large_rational_values() {
        let lo = rat_frac(10000, 7);
        let mid = rat_frac(10001, 7);
        let hi = rat_frac(10002, 7);
        let fs = FeasibleSet::from_interval(Some(lo.clone()), false, Some(hi.clone()), false);

        assert!(fs.contains_point(&lo));
        assert!(fs.contains_point(&mid));
        assert!(fs.contains_point(&hi));
        assert!(!fs.contains_point(&rat_frac(9999, 7)));
        assert!(!fs.contains_point(&rat_frac(10003, 7)));
    }

    /// from_interval(None, true, None, true) is the full real line.
    #[test]
    fn test_feasible_set_from_interval_none_none_is_full_real_line() {
        let fs = FeasibleSet::from_interval(None, true, None, true);

        assert_eq!(fs, FeasibleSet::full());
        assert!(fs.contains_point(&rat(-1000)));
        assert!(fs.contains_point(&rat(0)));
        assert!(fs.contains_point(&rat(1000)));
    }
}
