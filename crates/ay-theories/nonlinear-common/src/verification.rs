// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani verification harnesses for the shared nonlinear-common crate.
//!
//! This crate hosts the interval-union `FeasibleSet` used by NIA and NRA.
//! The harnesses below exercise the basic algebraic laws of feasible sets
//! (empty/full identities, intersection with empty, singleton membership)
//! that every downstream NLSAT look-ahead and branching decision relies on.

#[cfg(kani)]
mod kani_proofs {
    use crate::feasible_set::{FeasibilityClass, FeasibleSet};
    use num_rational::BigRational;

    /// Empty feasible set classifies as Blocked. This invariant is required
    /// by clauseSMT Technique 2 (arithmetic propagation branching) to drive
    /// blocked-variable priority: without it, the solver cannot distinguish
    /// unsatisfiable variables from unconstrained ones.
    #[kani::proof]
    fn empty_is_blocked() {
        let fs = FeasibleSet::empty();
        assert!(fs.is_empty());
        assert_eq!(fs.classify(), FeasibilityClass::Blocked);
    }

    /// Singleton feasible set {v} classifies as Fixed(v). This invariant is
    /// required so fixed-value branching picks the forced assignment rather
    /// than an arbitrary VSIDS decision.
    #[kani::proof]
    fn singleton_is_fixed() {
        let v = BigRational::from_integer(0.into());
        let fs = FeasibleSet::singleton(v.clone());
        assert!(!fs.is_empty());
        assert_eq!(fs.is_singleton(), Some(v.clone()));
        assert_eq!(fs.classify(), FeasibilityClass::Fixed(v));
    }

    /// Intersection with the empty set is empty (algebraic-closure invariant).
    /// Both NIA and NRA rely on this when combining multiple polynomial
    /// constraints; a violation would yield false-SAT results.
    #[kani::proof]
    fn intersection_with_empty_is_empty() {
        let a = FeasibleSet::full();
        let e = FeasibleSet::empty();
        assert!(a.intersection(&e).is_empty());
        assert!(e.intersection(&a).is_empty());
    }
}
