// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arithmetic entailment helpers for string-length reasoning.
//!
//! This module ports the core CVC5 `ArithEntail` surface used by strings:
//! - lower/upper constant bound queries,
//! - non-negativity / ordering checks,
//! - equal-length checks via arithmetic facts,
//! - zero-inference in additive inequalities.
//!
//! The implementation is intentionally conservative: if a bound cannot be
//! established soundly, queries return `false`/`None` instead of guessing.

use crate::state::SolverState;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, TermData, TermId, TermStore};
use std::cell::RefCell;

/// Arithmetic entailment engine for string-length terms.
pub(crate) struct ArithEntail<'a> {
    terms: &'a TermStore,
    state: &'a SolverState,
    constant_bound_cache: RefCell<HashMap<(TermId, bool), Option<i64>>>,
    constant_bound_in_progress: RefCell<HashSet<(TermId, bool)>>,
    length_bound_cache: RefCell<HashMap<(TermId, bool), Option<i64>>>,
    length_bound_in_progress: RefCell<HashSet<(TermId, bool)>>,
}

// LinearExpr and linear-algebra helpers are used by `check`, `check_nonneg`,
// and `infer_zeros_in_sum_geq` — currently only exercised in tests.
// Gated until StringsEntail integration wires them into production.
#[cfg(test)]
mod linear {
    use super::*;

    #[derive(Clone, Debug, Default)]
    pub(super) struct LinearExpr {
        pub(super) constant: i64,
        pub(super) coeffs: HashMap<TermId, i64>,
    }

    impl LinearExpr {
        pub(super) fn int(value: i64) -> Self {
            Self {
                constant: value,
                coeffs: HashMap::default(),
            }
        }

        pub(super) fn atom(term: TermId) -> Self {
            let mut coeffs = HashMap::default();
            coeffs.insert(term, 1);
            Self {
                constant: 0,
                coeffs,
            }
        }

        pub(super) fn add_term_coeff(&mut self, term: TermId, delta: i64) -> Option<()> {
            let next = self
                .coeffs
                .get(&term)
                .copied()
                .unwrap_or(0)
                .checked_add(delta)?;
            if next == 0 {
                self.coeffs.remove(&term);
            } else {
                self.coeffs.insert(term, next);
            }
            Some(())
        }

        pub(super) fn add_assign(&mut self, other: &Self) -> Option<()> {
            self.constant = self.constant.checked_add(other.constant)?;
            for (&term, &coeff) in &other.coeffs {
                self.add_term_coeff(term, coeff)?;
            }
            Some(())
        }

        pub(super) fn sub_assign(&mut self, other: &Self) -> Option<()> {
            self.constant = self.constant.checked_sub(other.constant)?;
            for (&term, &coeff) in &other.coeffs {
                self.add_term_coeff(term, coeff.checked_neg()?)?;
            }
            Some(())
        }

        pub(super) fn negated(&self) -> Option<Self> {
            let mut out = Self::int(self.constant.checked_neg()?);
            for (&term, &coeff) in &self.coeffs {
                out.coeffs.insert(term, coeff.checked_neg()?);
            }
            Some(out)
        }
    }
}

#[cfg(test)]
use linear::LinearExpr;

impl<'a> ArithEntail<'a> {
    /// Create a new entailment helper for a string solver state.
    pub(crate) fn new(terms: &'a TermStore, state: &'a SolverState) -> Self {
        Self {
            terms,
            state,
            constant_bound_cache: RefCell::new(HashMap::default()),
            constant_bound_in_progress: RefCell::new(HashSet::default()),
            length_bound_cache: RefCell::new(HashMap::default()),
            length_bound_in_progress: RefCell::new(HashSet::default()),
        }
    }

    /// Check whether `a == b` is entailed.
    pub(crate) fn check_eq(&self, a: TermId, b: TermId) -> bool {
        if self.state.find(a) == self.state.find(b) {
            return true;
        }
        if let (Some(na), Some(nb)) = (
            self.state.resolve_int_constant(self.terms, a),
            self.state.resolve_int_constant(self.terms, b),
        ) {
            return na == nb;
        }

        if let (Some(la), Some(ua), Some(lb), Some(ub)) = (
            self.get_constant_bound(a, true),
            self.get_constant_bound(a, false),
            self.get_constant_bound(b, true),
            self.get_constant_bound(b, false),
        ) {
            return la == ua && lb == ub && la == lb;
        }

        match (
            self.state.get_str_len_arg(self.terms, a),
            self.state.get_str_len_arg(self.terms, b),
        ) {
            (Some(sa), Some(sb)) => self.state.are_lengths_equal(self.terms, sa, sb),
            _ => false,
        }
    }

    /// Compute a constant lower/upper bound for an integer expression.
    ///
    /// `is_lower = true` computes a lower bound, `false` an upper bound.
    pub(crate) fn get_constant_bound(&self, term: TermId, is_lower: bool) -> Option<i64> {
        if let Some(bound) = self
            .constant_bound_cache
            .borrow()
            .get(&(term, is_lower))
            .copied()
        {
            return bound;
        }

        // Cycle guard (issue4701 SIGBUS): the cache is only written after
        // `compute_constant_bound` completes, so a cycle through EQC
        // representatives (e.g. `B` in the EQC of `R` where `R = (+ ... B ...)`)
        // makes `B -> R -> B -> ...` recurse until the stack dies. Re-entering
        // an in-flight query fails closed with `None` ("no bound derivable"),
        // which is always sound: callers treat `None` as unknown, and a `None`
        // sub-result can only ever suppress a bound, never fabricate one.
        let key = (term, is_lower);
        {
            let mut in_progress = self.constant_bound_in_progress.borrow_mut();
            if !in_progress.insert(key) {
                return None;
            }
        }

        let bound = self.compute_constant_bound(term, is_lower);
        self.constant_bound_in_progress.borrow_mut().remove(&key);
        self.constant_bound_cache.borrow_mut().insert(key, bound);
        bound
    }

    /// Compute a constant lower/upper bound for the length of string term `s`.
    ///
    /// `is_lower = true` computes a lower bound, `false` an upper bound.
    pub(crate) fn get_length_bound(&self, s: TermId, is_lower: bool) -> Option<i64> {
        if let Some(bound) = self
            .length_bound_cache
            .borrow()
            .get(&(s, is_lower))
            .copied()
        {
            return bound;
        }

        let key = (s, is_lower);
        {
            let mut in_progress = self.length_bound_in_progress.borrow_mut();
            if !in_progress.insert(key) {
                return if is_lower { Some(0) } else { None };
            }
        }

        let bound = self.compute_length_bound(s, is_lower);
        self.length_bound_in_progress.borrow_mut().remove(&key);
        self.length_bound_cache.borrow_mut().insert(key, bound);
        bound
    }

    fn compute_constant_bound(&self, term: TermId, is_lower: bool) -> Option<i64> {
        if let Some(n) = self.state.resolve_int_constant(self.terms, term) {
            return Some(n);
        }

        let rep = self.state.find(term);
        if rep != term {
            if let Some(rep_bound) = self.get_constant_bound(rep, is_lower) {
                return Some(rep_bound);
            }
        }

        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => n.try_into().ok(),
            TermData::App(sym, args) if sym.name() == "str.len" && args.len() == 1 => {
                self.get_length_bound(args[0], is_lower)
            }
            TermData::App(sym, args) if sym.name() == "+" => {
                let mut total: i64 = 0;
                for &arg in args {
                    let bound = self.get_constant_bound(arg, is_lower)?;
                    total = total.checked_add(bound)?;
                }
                Some(total)
            }
            TermData::App(sym, args) if sym.name() == "-" => self.subtraction_bound(args, is_lower),
            TermData::App(sym, args) if sym.name() == "*" => {
                self.multiplication_bound(args, is_lower)
            }
            _ => None,
        }
    }

    fn subtraction_bound(&self, args: &[TermId], is_lower: bool) -> Option<i64> {
        match args.len() {
            0 => None,
            1 => self.get_constant_bound(args[0], !is_lower)?.checked_neg(),
            _ => {
                let mut total = self.get_constant_bound(args[0], is_lower)?;
                for &arg in &args[1..] {
                    let bound = self.get_constant_bound(arg, !is_lower)?;
                    total = total.checked_sub(bound)?;
                }
                Some(total)
            }
        }
    }

    fn multiplication_bound(&self, args: &[TermId], is_lower: bool) -> Option<i64> {
        if args.is_empty() {
            return Some(1);
        }

        // Exact product when all factors have exact bounds.
        let mut exact: i64 = 1;
        let mut all_exact = true;
        for &arg in args {
            match (
                self.get_constant_bound(arg, true),
                self.get_constant_bound(arg, false),
            ) {
                (Some(lb), Some(ub)) if lb == ub => {
                    exact = exact.checked_mul(lb)?;
                }
                _ => {
                    all_exact = false;
                    break;
                }
            }
        }
        if all_exact {
            return Some(exact);
        }

        // Conservative lower bound for products of non-negative factors.
        if !is_lower {
            return None;
        }
        let mut product: i64 = 1;
        for &arg in args {
            let lb = self.get_constant_bound(arg, true)?;
            if lb < 0 {
                return None;
            }
            product = product.checked_mul(lb)?;
        }
        Some(product)
    }

    fn compute_length_bound(&self, s: TermId, is_lower: bool) -> Option<i64> {
        let rep = self.state.find(s);

        if let Some(known) = self.state.known_length(self.terms, rep) {
            return i64::try_from(known).ok();
        }
        if let Some(len_term) = self.state.get_length_term(&rep) {
            if let Some(n) = self.state.resolve_int_constant(self.terms, len_term) {
                if n >= 0 {
                    return Some(n);
                }
            }
        }
        if rep != s {
            if let Some(rep_bound) = self.get_length_bound(rep, is_lower) {
                return Some(rep_bound);
            }
        }

        let bound = match self.terms.get(s) {
            TermData::Const(Constant::String(text)) => i64::try_from(text.chars().count()).ok(),
            TermData::App(sym, args)
                if (sym.name() == "str.unit" || sym.name() == "seq.unit") && args.len() == 1 =>
            {
                Some(1)
            }
            TermData::App(sym, args) if sym.name() == "str.++" => {
                let mut sum = 0i64;
                for &child in args {
                    match self.get_length_bound(child, is_lower) {
                        Some(child_bound) => {
                            sum = sum.checked_add(child_bound)?;
                        }
                        None if is_lower => {}
                        None => return None,
                    }
                }
                Some(sum)
            }
            _ => None,
        };

        if is_lower {
            Some(bound.unwrap_or(0))
        } else {
            bound
        }
    }
}

// Methods staged for StringsEntail integration — currently only tested.
#[cfg(test)]
impl ArithEntail<'_> {
    /// Check whether `a >= b` is entailed (`a > b` when `strict` is true).
    pub(crate) fn check(&self, a: TermId, b: TermId, strict: bool) -> bool {
        if self.check_eq(a, b) {
            return !strict;
        }

        if let Some(diff) = self.linear_diff(a, b) {
            if let Some(lower) = self.linear_lower_bound(&diff) {
                return if strict { lower > 0 } else { lower >= 0 };
            }
        }

        if !strict {
            if let TermData::App(sym, args) = self.terms.get(a) {
                if sym.name() == "+" && !args.is_empty() {
                    let mut ys = args.clone();
                    let mut zero_ys = Vec::new();
                    if self.infer_zeros_in_sum_geq(b, &mut ys, &mut zero_ys) {
                        return true;
                    }
                }
            }
        }

        match (
            self.get_constant_bound(a, true),
            self.get_constant_bound(b, false),
        ) {
            (Some(lb), Some(ub)) => {
                if strict {
                    lb > ub
                } else {
                    lb >= ub
                }
            }
            _ => false,
        }
    }

    /// Given `y1 + ... + yn >= x`, remove summands that may be zero while
    /// preserving entailment.
    pub(crate) fn infer_zeros_in_sum_geq(
        &self,
        x: TermId,
        ys: &mut Vec<TermId>,
        zero_ys: &mut Vec<TermId>,
    ) -> bool {
        debug_assert!(zero_ys.is_empty());

        if !self.sum_geq(ys, x) {
            return false;
        }

        let mut i = 0usize;
        while i < ys.len() {
            let yi = ys.remove(i);
            if self.sum_geq(ys, x) {
                zero_ys.push(yi);
            } else {
                ys.insert(i, yi);
                i += 1;
            }
        }
        true
    }

    fn sum_geq(&self, ys: &[TermId], x: TermId) -> bool {
        let mut sum_minus_x = LinearExpr::default();
        for &y in ys {
            let Some(ly) = self.linearize(y) else {
                return false;
            };
            if sum_minus_x.add_assign(&ly).is_none() {
                return false;
            }
        }
        let Some(lx) = self.linearize(x) else {
            return false;
        };
        if sum_minus_x.sub_assign(&lx).is_none() {
            return false;
        }
        self.linear_lower_bound(&sum_minus_x)
            .is_some_and(|lb| lb >= 0)
    }

    fn linear_diff(&self, a: TermId, b: TermId) -> Option<LinearExpr> {
        let mut lhs = self.linearize(a)?;
        let rhs = self.linearize(b)?;
        lhs.sub_assign(&rhs)?;
        Some(lhs)
    }

    fn linear_lower_bound(&self, expr: &LinearExpr) -> Option<i64> {
        let mut lower = expr.constant;
        for (&term, &coeff) in &expr.coeffs {
            let term_bound = if coeff > 0 {
                self.get_constant_bound(term, true)?
            } else {
                self.get_constant_bound(term, false)?
            };
            let product = coeff.checked_mul(term_bound)?;
            lower = lower.checked_add(product)?;
        }
        Some(lower)
    }

    fn linearize(&self, term: TermId) -> Option<LinearExpr> {
        let rep = self.state.find(term);
        if let Some(n) = self.state.resolve_int_constant(self.terms, rep) {
            return Some(LinearExpr::int(n));
        }
        if rep != term {
            return self.linearize(rep);
        }

        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => Some(LinearExpr::int(n.try_into().ok()?)),
            TermData::App(sym, args) if sym.name() == "+" => {
                let mut out = LinearExpr::default();
                for &arg in args {
                    let child = self.linearize(arg)?;
                    out.add_assign(&child)?;
                }
                Some(out)
            }
            TermData::App(sym, args) if sym.name() == "-" => match args.len() {
                0 => None,
                1 => self.linearize(args[0])?.negated(),
                _ => {
                    let mut out = self.linearize(args[0])?;
                    for &arg in &args[1..] {
                        let child = self.linearize(arg)?;
                        out.sub_assign(&child)?;
                    }
                    Some(out)
                }
            },
            TermData::App(sym, args) if sym.name() == "*" => self.linearize_mul(args),
            _ => Some(LinearExpr::atom(rep)),
        }
    }

    fn linearize_mul(&self, args: &[TermId]) -> Option<LinearExpr> {
        if args.is_empty() {
            return Some(LinearExpr::int(1));
        }

        let mut coeff: i64 = 1;
        let mut atom: Option<TermId> = None;

        for &arg in args {
            let factor = self.linearize(arg)?;
            if factor.coeffs.is_empty() {
                coeff = coeff.checked_mul(factor.constant)?;
                continue;
            }
            if factor.coeffs.len() == 1 && factor.constant == 0 {
                let (&factor_term, &factor_coeff) = factor.coeffs.iter().next()?;
                if factor_coeff != 1 || atom.is_some() {
                    return None;
                }
                atom = Some(factor_term);
                continue;
            }
            return None;
        }

        if let Some(t) = atom {
            let mut out = LinearExpr::default();
            out.add_term_coeff(t, coeff)?;
            Some(out)
        } else {
            Some(LinearExpr::int(coeff))
        }
    }
}

#[cfg(test)]
#[path = "arith_entail_tests.rs"]
mod tests;
