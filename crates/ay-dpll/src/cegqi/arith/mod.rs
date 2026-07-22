// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arithmetic instantiation for CEGQI
//!
//! This module handles variable instantiation for LIA (Linear Integer Arithmetic)
//! and LRA (Linear Real Arithmetic) using model-based projection.
//!
//! # Algorithm
//!
//! Based on CVC5's `ceg_arith_instantiator.cpp` and Reynolds et al. FMSD 2017:
//!
//! 1. **Collect bounds**: Parse assertions to extract lower/upper bounds for variables
//! 2. **Select instantiation**: Use model-based projection to choose instantiation term
//! 3. **Handle divisibility**: For LIA, ensure integer divisibility with rho computation
//!
//! # Bound Collection
//!
//! For a variable `x` (or CE variable `e`), we collect bounds from the current
//! assertion context:
//!
//! - `c*x >= t` → lower bound (x >= t/c)
//! - `c*x <= t` → upper bound (x <= t/c)
//! - `c*x = t`  → equality (substitute immediately)
//!
//! # Model-Based Projection (LIA)
//!
//! For integer variable `e` with bounds `c*e >= t` and model values `e^M`, `t^M`:
//!
//! ```text
//! rho = (c*e^M - t^M) mod |c|
//! selection = t + rho
//! ```
//!
//! This ensures the selection term satisfies divisibility constraints.

mod extraction;
mod selection;

use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

/// A bound on a variable: coefficient * var >= term (lower) or <= term (upper)
#[derive(Debug, Clone)]
pub(crate) struct Bound {
    /// Coefficient of the variable (c in c*x <> t)
    pub coeff: BigRational,
    /// The bound term (t in c*x <> t)
    pub term: TermId,
    /// Whether the source arithmetic literal was strict (`<` or `>`).
    ///
    /// Integer strict bounds are tightened during collection, so this is only
    /// semantically relevant for Real-sorted variables.
    pub strict: bool,
    /// Literal that produced this bound, used for diagnostics/proof plumbing.
    #[allow(dead_code)]
    pub source_literal: Option<TermId>,
    /// Model value of the bound term (t^M), computed externally.
    /// Used for: (1) selecting the tightest bound, (2) rho computation.
    pub model_value: Option<BigRational>,
}

/// Arithmetic instantiator for CEGQI
///
/// Handles bound collection and selection term computation for arithmetic
/// quantifier instantiation.
pub(crate) struct ArithInstantiator {
    /// Lower bounds on the variable being instantiated
    pub lower_bounds: Vec<Bound>,
    /// Upper bounds on the variable being instantiated
    pub upper_bounds: Vec<Bound>,
    /// Equality bounds (highest priority - use immediately)
    pub equalities: Vec<(BigRational, TermId)>,
}

impl ArithInstantiator {
    /// Create a new arithmetic instantiator
    pub(crate) fn new() -> Self {
        Self {
            lower_bounds: Vec::new(),
            upper_bounds: Vec::new(),
            equalities: Vec::new(),
        }
    }

    /// Process an assertion to extract bounds for a variable
    ///
    /// # Arguments
    /// * `terms` - Term store
    /// * `lit` - The assertion literal
    /// * `pv` - The "processed variable" (CE variable) to extract bounds for
    ///
    /// # Returns
    /// True if a bound was extracted, false otherwise
    pub(crate) fn process_assertion(
        &mut self,
        terms: &mut TermStore,
        lit: TermId,
        pv: TermId,
    ) -> bool {
        // Clone the term data to release the borrow on terms before calling extract_bound.
        let data = terms.get(lit).clone();

        let is_integer = matches!(terms.sort(pv), Sort::Int);

        match &data {
            // Recurse through conjunctions: (and A B ...) contains multiple bounds.
            // DPLL usually flattens conjunctions, but CEGQI processes the full assertion
            // list which may include unflattened compound assertions.
            // Must match BEFORE the generic 2-arg App pattern to avoid shadowing.
            TermData::App(Symbol::Named(name), args) if name == "and" => {
                let args_vec: Vec<TermId> = args.clone();
                let mut any = false;
                for &arg in &args_vec {
                    if self.process_assertion(terms, arg, pv) {
                        any = true;
                    }
                }
                return any;
            }
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                let (lhs, rhs) = (args[0], args[1]);
                match name.as_str() {
                    "<=" => {
                        if let Some((coeff, bt)) = self.extract_bound(terms, lhs, rhs, pv) {
                            self.add_bound(terms, coeff, bt, true, lit);
                            return true;
                        }
                    }
                    // Strict upper: x < t. For integers, tighten to x <= t-1.
                    // CVC5: for Int, strict < is equivalent to <= (t-1).
                    // Tightening must happen AFTER determining final bound direction
                    // (coefficient sign may flip upper↔lower).
                    "<" => {
                        if let Some((coeff, bt)) = self.extract_bound(terms, lhs, rhs, pv) {
                            self.add_bound_strict(coeff, bt, true, true, is_integer, terms, lit);
                            return true;
                        }
                    }
                    ">=" => {
                        if let Some((coeff, bt)) = self.extract_bound(terms, lhs, rhs, pv) {
                            self.add_bound(terms, coeff, bt, false, lit);
                            return true;
                        }
                    }
                    // Strict lower: x > t. For integers, tighten to x >= t+1.
                    // CVC5: for Int, strict > is equivalent to >= (t+1).
                    // Tightening must happen AFTER determining final bound direction
                    // (coefficient sign may flip upper↔lower).
                    ">" => {
                        if let Some((coeff, bt)) = self.extract_bound(terms, lhs, rhs, pv) {
                            self.add_bound_strict(coeff, bt, false, true, is_integer, terms, lit);
                            return true;
                        }
                    }
                    "=" => {
                        if let Some((coeff, bt)) = self.extract_bound(terms, lhs, rhs, pv) {
                            self.equalities.push((coeff, bt));
                            return true;
                        }
                    }
                    _ => {}
                }
            }
            TermData::Not(inner) => {
                let inner_data = terms.get(*inner).clone();
                match &inner_data {
                    // Not(Not(x)) = x: double negation elimination.
                    // Can arise from De Morgan decomposition of Not(or ...).
                    TermData::Not(inner2) => {
                        return self.process_assertion(terms, *inner2, pv);
                    }
                    // Not(P => Q) ≡ P AND Not(Q). Decompose and recurse.
                    // This arises from CEGQI CE lemmas: forall body `(=> P Q)` is
                    // negated to `Not(=> P Q)` = `P AND Not(Q)`. Without this,
                    // bounds in P (e.g., x > 0) are invisible to the extractor.
                    TermData::App(Symbol::Named(name), args) if name == "=>" && args.len() == 2 => {
                        let (p, q) = (args[0], args[1]);
                        let not_q = terms.mk_not(q);
                        let mut any = false;
                        if self.process_assertion(terms, p, pv) {
                            any = true;
                        }
                        if self.process_assertion(terms, not_q, pv) {
                            any = true;
                        }
                        return any;
                    }
                    // Not(or A B ...) ≡ And(Not(A), Not(B), ...). De Morgan.
                    // Process each negated disjunct for bounds.
                    TermData::App(Symbol::Named(name), args) if name == "or" => {
                        let args_vec: Vec<TermId> = args.clone();
                        let mut any = false;
                        for &arg in &args_vec {
                            let not_arg = terms.mk_not(arg);
                            if self.process_assertion(terms, not_arg, pv) {
                                any = true;
                            }
                        }
                        return any;
                    }
                    TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                        let (lhs, rhs) = (args[0], args[1]);
                        match name.as_str() {
                            // Not(<=) is >: strict lower. For integers, tighten
                            // AFTER determining final bound direction (coeff sign).
                            "<=" => {
                                if let Some((coeff, bt)) = self.extract_bound(terms, lhs, rhs, pv) {
                                    self.add_bound_strict(
                                        coeff, bt, false, true, is_integer, terms, lit,
                                    );
                                    return true;
                                }
                            }
                            // Not(>=) is <: strict upper. For integers, tighten
                            // AFTER determining final bound direction (coeff sign).
                            ">=" => {
                                if let Some((coeff, bt)) = self.extract_bound(terms, lhs, rhs, pv) {
                                    self.add_bound_strict(
                                        coeff, bt, true, true, is_integer, terms, lit,
                                    );
                                    return true;
                                }
                            }
                            // Not(<) is >=: non-strict lower (no tightening needed).
                            "<" => {
                                if let Some((coeff, bt)) = self.extract_bound(terms, lhs, rhs, pv) {
                                    self.add_bound(terms, coeff, bt, false, lit);
                                    return true;
                                }
                            }
                            // Not(>) is <=: non-strict upper (no tightening needed).
                            ">" => {
                                if let Some((coeff, bt)) = self.extract_bound(terms, lhs, rhs, pv) {
                                    self.add_bound(terms, coeff, bt, true, lit);
                                    return true;
                                }
                            }
                            // Not(=) is disequality: x != t → x > t OR x < t.
                            // Use add_bound_strict so integer tightening respects
                            // coefficient sign. CVC5 ceg_arith_instantiator.cpp:200-238.
                            "=" => {
                                if let Some((coeff, bt)) = self.extract_bound(terms, lhs, rhs, pv) {
                                    // x > t (strict lower) and x < t (strict upper).
                                    // add_bound_strict handles integer tightening after
                                    // determining final direction from coefficient sign.
                                    self.add_bound_strict(
                                        coeff.clone(),
                                        bt,
                                        false,
                                        true,
                                        is_integer,
                                        terms,
                                        lit,
                                    );
                                    self.add_bound_strict(
                                        coeff, bt, true, true, is_integer, terms, lit,
                                    );
                                    return true;
                                }
                            }
                            _ => {}
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }

        false
    }

    /// Classify a (coeff, bound_term) into upper or lower bounds.
    /// `upper_when_positive`: true for `<=`/`<` operators, false for `>=`/`>`.
    /// `is_strict`: true for `<`/`>` (strict inequalities). For integer variables,
    /// strict bounds are tightened: lower bounds get +1, upper bounds get -1.
    /// The tightening direction depends on the FINAL bound classification (after
    /// considering coefficient sign), not the operator name.
    fn add_bound_strict(
        &mut self,
        coeff: BigRational,
        bound_term: TermId,
        upper_when_positive: bool,
        is_strict: bool,
        is_integer: bool,
        terms: &mut TermStore,
        source_literal: TermId,
    ) {
        let zero_r = BigRational::from(BigInt::from(0));
        let (is_upper, abs_coeff, normalized_term) = if coeff > zero_r {
            (upper_when_positive, coeff, bound_term)
        } else {
            (
                !upper_when_positive,
                -coeff,
                Self::negated_bound_term(terms, bound_term),
            )
        };

        // For strict integer bounds, tighten: lower gets +1, upper gets -1.
        // This converts x < t to x <= t-1 and x > t to x >= t+1.
        let final_term = if is_strict && is_integer {
            let one = terms.mk_int(BigInt::from(1));
            if is_upper {
                terms.mk_sub(vec![normalized_term, one]) // upper: t - 1
            } else {
                terms.mk_add(vec![normalized_term, one]) // lower: t + 1
            }
        } else {
            normalized_term
        };
        let strict = is_strict && !is_integer;

        if is_upper {
            self.upper_bounds.push(Bound {
                coeff: abs_coeff,
                term: final_term,
                strict,
                source_literal: Some(source_literal),
                model_value: None,
            });
        } else {
            self.lower_bounds.push(Bound {
                coeff: abs_coeff,
                term: final_term,
                strict,
                source_literal: Some(source_literal),
                model_value: None,
            });
        }
    }

    /// Classify a (coeff, bound_term) into upper or lower bounds.
    /// `upper_when_positive`: true for `<=`/`<` operators, false for `>=`/`>`.
    fn add_bound(
        &mut self,
        terms: &mut TermStore,
        coeff: BigRational,
        bound_term: TermId,
        upper_when_positive: bool,
        source_literal: TermId,
    ) {
        let zero_r = BigRational::from(BigInt::from(0));
        let (is_upper, abs_coeff, normalized_term) = if coeff > zero_r {
            (upper_when_positive, coeff, bound_term)
        } else {
            (
                !upper_when_positive,
                -coeff,
                Self::negated_bound_term(terms, bound_term),
            )
        };

        let bound = Bound {
            coeff: abs_coeff,
            term: normalized_term,
            strict: false,
            source_literal: Some(source_literal),
            model_value: None,
        };
        if is_upper {
            self.upper_bounds.push(bound);
        } else {
            self.lower_bounds.push(bound);
        }
    }

    fn negated_bound_term(terms: &mut TermStore, bound_term: TermId) -> TermId {
        let zero = if matches!(terms.sort(bound_term), Sort::Real) {
            terms.mk_rational(BigRational::from(BigInt::from(0)))
        } else {
            terms.mk_int(BigInt::from(0))
        };
        terms.mk_sub(vec![zero, bound_term])
    }

    /// Extract coefficient and bound term from `lhs <> rhs` with respect to `pv`.
    ///
    /// For `c*pv + rest <> rhs`, returns `(c, rhs - rest)`.
    /// For `lhs <> c*pv + rest`, returns `(-c, lhs - rest)`.
    ///
    /// Safety: if the resulting bound term still contains `pv` (e.g., `pv` appears
    /// inside a `div`/`mod` that `extract_variable` couldn't decompose), the bound
    /// is rejected. This matches CVC5's `hasSubterm(val, pv)` guard in
    /// `ceg_arith_instantiator.cpp`.
    fn extract_bound(
        &self,
        terms: &mut TermStore,
        lhs: TermId,
        rhs: TermId,
        pv: TermId,
    ) -> Option<(BigRational, TermId)> {
        let zero_r = BigRational::from(BigInt::from(0));

        // Check if lhs contains pv
        let (lhs_coeff, lhs_remainder) = Self::extract_variable(terms, lhs, pv);

        if lhs_coeff != zero_r {
            // pv found in lhs with coefficient lhs_coeff.
            // Constraint: lhs_coeff*pv + lhs_remainder <> rhs
            // => lhs_coeff*pv <> rhs - lhs_remainder
            let bound_term = if let Some(rem) = lhs_remainder {
                terms.mk_sub(vec![rhs, rem])
            } else {
                rhs
            };
            // Safety: reject if pv still appears in the bound term (e.g., under div/mod)
            if Self::term_contains(terms, bound_term, pv) {
                return None;
            }
            return Some((lhs_coeff, bound_term));
        }

        // pv not in lhs, check rhs
        let (rhs_coeff, rhs_remainder) = Self::extract_variable(terms, rhs, pv);

        if rhs_coeff != zero_r {
            // pv found in rhs with coefficient rhs_coeff.
            // Constraint: lhs <> rhs_coeff*pv + rhs_remainder
            // We move pv to LHS: -rhs_coeff*pv <> rhs_remainder - lhs
            // Since the caller uses sign of coefficient to classify bounds,
            // we negate the coefficient to indicate pv was on the rhs.
            let lhs_minus_remainder = if let Some(rem) = rhs_remainder {
                terms.mk_sub(vec![lhs, rem])
            } else {
                lhs
            };
            let bound_term = Self::negated_bound_term(terms, lhs_minus_remainder);
            // Safety: reject if pv still appears in the bound term
            if Self::term_contains(terms, bound_term, pv) {
                return None;
            }
            return Some((-rhs_coeff, bound_term));
        }

        // pv not in either side
        None
    }

    // Variable extraction (extract_variable, term_contains) is in extraction.rs.
    // Selection logic (select_term, bound_selection_term, rho computation,
    // tightest-bound selection, divide_term) is in selection.rs.
}

impl Default for ArithInstantiator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests;
