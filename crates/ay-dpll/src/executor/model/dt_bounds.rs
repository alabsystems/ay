// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arithmetic bound extraction for DT selector model values (#5506, #1766).
//!
//! In pure QF_DT mode, Int/Real-sorted selector applications have no LIA/LRA
//! model. These helpers scan assertions for comparison constraints and pick
//! satisfying values.

use ay_core::term::{Constant, TermData};
use ay_core::TermId;
use num_bigint::BigInt;
use num_rational::BigRational;

use super::Executor;

impl Executor {
    /// Extract a satisfying integer value for a term from assertion bounds (#5506).
    ///
    /// In pure QF_DT mode, Int-sorted selector applications have no LIA model.
    /// This scans assertions for simple comparison constraints (>, >=, <, <=, =)
    /// involving the given term and integer constants, then picks a value
    /// satisfying all bounds. Returns `None` if no constraints are found.
    pub(super) fn extract_int_from_assertion_bounds(&self, term_id: TermId) -> Option<BigInt> {
        let mut lower: Option<BigInt> = None; // exclusive lower bound
        let mut upper: Option<BigInt> = None; // exclusive upper bound
        let mut exact: Option<BigInt> = None;

        for &assertion in &self.ctx.assertions {
            self.collect_int_bound(
                assertion, term_id, false, &mut lower, &mut upper, &mut exact,
            );
        }

        if let Some(v) = exact {
            return Some(v);
        }

        // Pick a value in (lower, upper). If only one bound, offset by 1.
        match (lower, upper) {
            (Some(lo), Some(hi)) => {
                let candidate = &lo + 1;
                if candidate < hi {
                    Some(candidate)
                } else {
                    None // unsatisfiable bounds
                }
            }
            (Some(lo), None) => Some(&lo + 1),
            (None, Some(hi)) => Some(&hi - 1),
            (None, None) => None,
        }
    }

    /// Collect an integer bound from an assertion term for a target term.
    ///
    /// Handles `(> t c)`, `(>= t c)`, `(< t c)`, `(<= t c)`, `(= t c)` and
    /// their `(not ...)` negations. `t` and `c` can be on either side.
    fn collect_int_bound(
        &self,
        assertion: TermId,
        target: TermId,
        negated: bool,
        lower: &mut Option<BigInt>,
        upper: &mut Option<BigInt>,
        exact: &mut Option<BigInt>,
    ) {
        match self.ctx.terms.get(assertion) {
            TermData::Not(inner) => {
                self.collect_int_bound(*inner, target, !negated, lower, upper, exact);
            }
            TermData::App(sym, args) if args.len() == 2 => {
                let name = sym.name();
                // Determine which side is the target and which is the constant
                let (is_target_left, const_val) = if args[0] == target {
                    if let Some(v) = self.extract_int_const(args[1]) {
                        (true, v)
                    } else {
                        return;
                    }
                } else if args[1] == target {
                    if let Some(v) = self.extract_int_const(args[0]) {
                        (false, v)
                    } else {
                        return;
                    }
                } else {
                    return;
                };

                // Normalize: express as constraint on target
                // (> target c) => target > c  => lower = max(lower, c)
                // (> c target) => target < c  => upper = min(upper, c)
                // (not (> target c)) => target <= c => upper = min(upper, c+1)
                match (name, is_target_left, negated) {
                    // target > c
                    (">", true, false) | ("<", false, false) => {
                        Self::update_int_bound(lower, const_val, true);
                    }
                    // target < c
                    ("<", true, false) | (">", false, false) => {
                        Self::update_int_bound(upper, const_val, false);
                    }
                    // target >= c  =>  target > c-1
                    (">=", true, false) | ("<=", false, false) => {
                        Self::update_int_bound(lower, &const_val - 1, true);
                    }
                    // target <= c  =>  target < c+1
                    ("<=", true, false) | (">=", false, false) => {
                        Self::update_int_bound(upper, &const_val + 1, false);
                    }
                    // target = c
                    ("=", _, false) => {
                        *exact = Some(const_val);
                    }
                    // not (target > c) => target <= c => target < c+1
                    (">", true, true) | ("<", false, true) => {
                        Self::update_int_bound(upper, &const_val + 1, false);
                    }
                    // not (target < c) => target >= c => target > c-1
                    ("<", true, true) | (">", false, true) => {
                        Self::update_int_bound(lower, &const_val - 1, true);
                    }
                    // not (target >= c) => target < c
                    (">=", true, true) | ("<=", false, true) => {
                        Self::update_int_bound(upper, const_val, false);
                    }
                    // not (target <= c) => target > c
                    ("<=", true, true) | (">=", false, true) => {
                        Self::update_int_bound(lower, const_val, true);
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    fn extract_int_const(&self, term_id: TermId) -> Option<BigInt> {
        if let TermData::Const(Constant::Int(v)) = self.ctx.terms.get(term_id) {
            return Some(v.clone());
        }
        // Handle (- n) for negative constants
        if let TermData::App(sym, args) = self.ctx.terms.get(term_id) {
            if sym.name() == "-" && args.len() == 1 {
                if let TermData::Const(Constant::Int(v)) = self.ctx.terms.get(args[0]) {
                    return Some(-v.clone());
                }
            }
        }
        None
    }

    fn update_int_bound(slot: &mut Option<BigInt>, bound: BigInt, take_max: bool) {
        *slot = Some(match slot.take() {
            Some(prev) => {
                if take_max {
                    prev.max(bound)
                } else {
                    prev.min(bound)
                }
            }
            None => bound,
        });
    }

    /// Extract a satisfying rational value for a Real-sorted term from assertion
    /// bounds (#1766). Mirrors `extract_int_from_assertion_bounds` for Real sort.
    pub(super) fn extract_real_from_assertion_bounds(
        &self,
        term_id: TermId,
    ) -> Option<BigRational> {
        let mut lower: Option<BigRational> = None; // exclusive lower bound
        let mut upper: Option<BigRational> = None; // exclusive upper bound
        let mut exact: Option<BigRational> = None;

        for &assertion in &self.ctx.assertions {
            self.collect_real_bound(
                assertion, term_id, false, &mut lower, &mut upper, &mut exact,
            );
        }

        if let Some(v) = exact {
            return Some(v);
        }

        // Pick a value in (lower, upper). Use midpoint or offset by 1.
        let one = BigRational::from(BigInt::from(1));
        match (lower, upper) {
            (Some(lo), Some(hi)) => {
                let two = BigRational::from(BigInt::from(2));
                let mid = (&lo + &hi) / two;
                if mid > lo && mid < hi {
                    Some(mid)
                } else {
                    None
                }
            }
            (Some(lo), None) => Some(&lo + &one),
            (None, Some(hi)) => Some(&hi - &one),
            (None, None) => None,
        }
    }

    fn collect_real_bound(
        &self,
        assertion: TermId,
        target: TermId,
        negated: bool,
        lower: &mut Option<BigRational>,
        upper: &mut Option<BigRational>,
        exact: &mut Option<BigRational>,
    ) {
        match self.ctx.terms.get(assertion) {
            TermData::Not(inner) => {
                self.collect_real_bound(*inner, target, !negated, lower, upper, exact);
            }
            TermData::App(sym, args) if args.len() == 2 => {
                let name = sym.name();
                let (is_target_left, const_val) = if args[0] == target {
                    if let Some(v) = self.extract_real_const(args[1]) {
                        (true, v)
                    } else {
                        return;
                    }
                } else if args[1] == target {
                    if let Some(v) = self.extract_real_const(args[0]) {
                        (false, v)
                    } else {
                        return;
                    }
                } else {
                    return;
                };

                match (name, is_target_left, negated) {
                    // target > c
                    (">", true, false) | ("<", false, false) => {
                        Self::update_rational_bound(lower, const_val, true);
                    }
                    // target < c
                    ("<", true, false) | (">", false, false) => {
                        Self::update_rational_bound(upper, const_val, false);
                    }
                    // target >= c (treat as > c for bound collection; midpoint picks value)
                    (">=", true, false) | ("<=", false, false) => {
                        Self::update_rational_bound(lower, const_val, true);
                    }
                    // target <= c
                    ("<=", true, false) | (">=", false, false) => {
                        Self::update_rational_bound(upper, const_val, false);
                    }
                    // target = c
                    ("=", _, false) => {
                        *exact = Some(const_val);
                    }
                    // not (target > c) => target <= c
                    (">", true, true) | ("<", false, true) => {
                        Self::update_rational_bound(upper, const_val, false);
                    }
                    // not (target < c) => target >= c
                    ("<", true, true) | (">", false, true) => {
                        Self::update_rational_bound(lower, const_val, true);
                    }
                    // not (target >= c) => target < c
                    (">=", true, true) | ("<=", false, true) => {
                        Self::update_rational_bound(upper, const_val, false);
                    }
                    // not (target <= c) => target > c
                    ("<=", true, true) | (">=", false, true) => {
                        Self::update_rational_bound(lower, const_val, true);
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    fn extract_real_const(&self, term_id: TermId) -> Option<BigRational> {
        match self.ctx.terms.get(term_id) {
            TermData::Const(Constant::Rational(v)) => Some(v.0.clone()),
            TermData::Const(Constant::Int(v)) => Some(BigRational::from(v.clone())),
            TermData::App(sym, args) if sym.name() == "-" && args.len() == 1 => {
                self.extract_real_const(args[0]).map(|v| -v)
            }
            TermData::App(sym, args) if sym.name() == "/" && args.len() == 2 => {
                let num = self.extract_real_const(args[0])?;
                let den = self.extract_real_const(args[1])?;
                if den == BigRational::from(BigInt::from(0)) {
                    None
                } else {
                    Some(num / den)
                }
            }
            _ => None,
        }
    }

    fn update_rational_bound(slot: &mut Option<BigRational>, bound: BigRational, take_max: bool) {
        *slot = Some(match slot.take() {
            Some(prev) => {
                if take_max {
                    prev.max(bound)
                } else {
                    prev.min(bound)
                }
            }
            None => bound,
        });
    }
}
