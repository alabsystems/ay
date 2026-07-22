// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LIA integer bound extraction and analysis.
//!
//! Extracted from `lib.rs` (#2998 code-health, design #6859 Packet 4).
//! Methods for scanning asserted literals to find integer bounds on terms,
//! plus utility functions for integer ceiling/floor division.

use super::*;

impl LiaSolver<'_> {
    /// Get integer bounds for a term from the incremental assertion view (#C6).
    ///
    /// This looks for constraints of the form `x >= c`, `x > c`, `x <= c`, `x < c`
    /// where x is the target term and c is a constant.
    ///
    /// Served from `AssertionView.bounds_by_term` — an O(1) hash lookup —
    /// instead of the historical O(asserted) trail scan, which made callers
    /// like the per-substitution/per-pair dioph and two-var passes
    /// O(asserted × vars) per check (lia-hot-loop-plan §C6).
    ///
    /// Semantics are EXACTLY the historical scan's: the view classifies the
    /// same positive `>=`/`<=`/`>`/`<` atoms with the same integer-adjusted
    /// strict-bound arithmetic and the same constant extraction (including
    /// negation chains and integral rationals), and records both directions
    /// for constant-vs-constant atoms. Verified against a copy of the old
    /// implementation in `tests::bounds_view_equivalence` over randomized
    /// assertion sets with push/pop.
    pub(crate) fn get_integer_bounds_for_term(
        &self,
        term: Option<TermId>,
    ) -> (Option<BigInt>, Option<BigInt>) {
        let Some(tid) = term else {
            return (None, None);
        };
        match self.assertion_view().bounds_by_term.get(&tid) {
            Some(bounds) => (bounds.lower.clone(), bounds.upper.clone()),
            None => (None, None),
        }
    }

    /// Get integer bounds for a term, including implied bounds from linear
    /// expressions, plus the asserted literals that justify the returned bounds.
    ///
    /// This extends `get_integer_bounds_for_term` by also finding constraints of
    /// the form `a*x >= c` or `a*x <= c` in the trail and deriving `x >= ceil(c/a)`
    /// or `x <= floor(c/a)`. This is critical after VariableSubstitution replaces
    /// e.g. `xi = 3*mi`, leaving bounds like `3*mi <= 60000` which imply `mi <= 20000`.
    ///
    /// SOUNDNESS (seed-236 false UNSAT): any theory conflict derived from these
    /// bounds MUST include the returned reason literals. The historical bug was
    /// that `get_bound_reasons_for_term` only recognized direct `x OP c` atoms
    /// while the bounds used for infeasibility proofs also came from
    /// `a*x OP c` atoms, producing under-inclusive (theory-invalid) conflict
    /// clauses. Keeping the bound derivation and the reason collection in one
    /// scan prevents the two from drifting apart again.
    ///
    /// The reason list is a superset of the atoms that produced the final
    /// (tightest) bounds: every scanned atom that yields any bound candidate is
    /// included. Including extra genuinely-asserted literals in a conflict only
    /// weakens the learned clause, which is sound.
    pub(crate) fn get_integer_bounds_for_term_extended_with_reasons(
        &self,
        term: Option<TermId>,
    ) -> (Option<BigInt>, Option<BigInt>, Vec<TheoryLit>) {
        // Start with direct bounds. `get_bound_reasons_for_term` mirrors the
        // direct `x OP c` scan in `get_integer_bounds_for_term` exactly.
        let (mut lower, mut upper) = self.get_integer_bounds_for_term(term);
        let mut reasons = self.get_bound_reasons_for_term(term);

        let Some(tid) = term else {
            return (lower, upper, reasons);
        };

        // Scan for bounds on linear expressions containing tid
        for &(literal, value) in &self.asserted {
            if !value {
                continue;
            }

            let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                continue;
            };

            if args.len() != 2 {
                continue;
            }

            // Check both sides for a linear expression containing tid
            let (lin_term, const_term, is_lin_on_left) = if self.extract_constant(args[1]).is_some()
            {
                (args[0], args[1], true)
            } else if self.extract_constant(args[0]).is_some() {
                (args[1], args[0], false)
            } else {
                continue;
            };

            // Check if lin_term is `coeff * tid`
            let coeff = self.extract_linear_coeff_for(lin_term, tid);
            let Some(coeff) = coeff else {
                continue;
            };
            if coeff.is_zero() {
                continue;
            }

            let Some(c) = self.extract_constant(const_term) else {
                continue;
            };

            if !matches!(name.as_str(), ">=" | "<=" | ">" | "<") {
                continue;
            }
            // This atom produces a bound candidate below: record it as a reason.
            reasons.push(TheoryLit::new(literal, true));

            // Derive bound on tid from `coeff * tid OP c`
            // If coeff > 0: same direction. If coeff < 0: flip direction.
            match (name.as_str(), is_lin_on_left) {
                (">=", true) | ("<=", false) => {
                    // coeff*tid >= c => tid >= ceil(c/coeff) if coeff > 0
                    //                   tid <= floor(c/coeff) if coeff < 0
                    if coeff.is_positive() {
                        let bound = Self::ceil_bigint_div(&c, &coeff);
                        lower = Some(lower.map_or(bound.clone(), |l| l.max(bound)));
                    } else {
                        let bound = Self::floor_bigint_div(&c, &coeff);
                        upper = Some(upper.map_or(bound.clone(), |u| u.min(bound)));
                    }
                }
                ("<=", true) | (">=", false) => {
                    // coeff*tid <= c => tid <= floor(c/coeff) if coeff > 0
                    //                   tid >= ceil(c/coeff) if coeff < 0
                    if coeff.is_positive() {
                        let bound = Self::floor_bigint_div(&c, &coeff);
                        upper = Some(upper.map_or(bound.clone(), |u| u.min(bound)));
                    } else {
                        let bound = Self::ceil_bigint_div(&c, &coeff);
                        lower = Some(lower.map_or(bound.clone(), |l| l.max(bound)));
                    }
                }
                (">", true) | ("<", false) => {
                    // coeff*tid > c  for integers: coeff*tid >= c+1
                    let c_adj = &c + BigInt::one();
                    if coeff.is_positive() {
                        let bound = Self::ceil_bigint_div(&c_adj, &coeff);
                        lower = Some(lower.map_or(bound.clone(), |l| l.max(bound)));
                    } else {
                        let bound = Self::floor_bigint_div(&c_adj, &coeff);
                        upper = Some(upper.map_or(bound.clone(), |u| u.min(bound)));
                    }
                }
                ("<", true) | (">", false) => {
                    // coeff*tid < c  for integers: coeff*tid <= c-1
                    let c_adj = &c - BigInt::one();
                    if coeff.is_positive() {
                        let bound = Self::floor_bigint_div(&c_adj, &coeff);
                        upper = Some(upper.map_or(bound.clone(), |u| u.min(bound)));
                    } else {
                        let bound = Self::ceil_bigint_div(&c_adj, &coeff);
                        lower = Some(lower.map_or(bound.clone(), |l| l.max(bound)));
                    }
                }
                _ => {}
            }
        }

        (lower, upper, reasons)
    }

    /// Check if `expr` is a linear expression `coeff * target` (possibly with an
    /// additive constant). Returns the coefficient if found, None otherwise.
    ///
    /// Handles patterns: `(* c target)`, `(* target c)`, `target` (coeff=1),
    /// `(- target)` (coeff=-1).
    fn extract_linear_coeff_for(&self, expr: TermId, target: TermId) -> Option<BigInt> {
        if expr == target {
            return Some(BigInt::one());
        }

        match self.terms.get(expr) {
            TermData::App(Symbol::Named(name), args) => {
                if name == "*" && args.len() == 2 {
                    // (* c target) or (* target c)
                    if args[1] == target {
                        return self.extract_constant(args[0]);
                    } else if args[0] == target {
                        return self.extract_constant(args[1]);
                    }
                } else if name == "-" && args.len() == 1 {
                    // (- target) = -1 * target
                    if args[0] == target {
                        return Some(-BigInt::one());
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Extract an integer constant from a term, if it is one.
    pub(crate) fn extract_constant(&self, term: TermId) -> Option<BigInt> {
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => Some(n.clone()),
            TermData::Const(Constant::Rational(r)) => {
                if r.0.denom().is_one() {
                    Some(r.0.numer().clone())
                } else {
                    None
                }
            }
            TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 1 => {
                // Negation
                self.extract_constant(args[0]).map(|n| -n)
            }
            _ => None,
        }
    }

    /// Get bound reason literals for a term (for conflict generation).
    pub(crate) fn get_bound_reasons_for_term(&self, term: Option<TermId>) -> Vec<TheoryLit> {
        let mut reasons = Vec::new();
        let Some(tid) = term else {
            return reasons;
        };

        // Find bound assertions for this term
        for &(literal, value) in &self.asserted {
            if !value {
                continue;
            }

            let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                continue;
            };

            if args.len() != 2 {
                continue;
            }

            // Check if this involves our target term as a simple bound
            let is_bound = (args[0] == tid || args[1] == tid)
                && matches!(name.as_str(), ">=" | "<=" | ">" | "<");

            if is_bound {
                // Verify one side is a constant
                let const_side = if args[0] == tid { args[1] } else { args[0] };
                if self.extract_constant(const_side).is_some() {
                    reasons.push(TheoryLit::new(literal, true));
                }
            }
        }

        reasons
    }

    /// Integer ceiling division: ceil(a/b)
    pub(crate) fn ceil_bigint_div(a: &BigInt, b: &BigInt) -> BigInt {
        use num_integer::Integer;
        let (q, r) = a.div_rem(b);
        if r.is_zero() {
            q
        } else if (a.is_positive() && b.is_positive()) || (a.is_negative() && b.is_negative()) {
            q + BigInt::one()
        } else {
            q
        }
    }

    /// Integer floor division: floor(a/b)
    pub(crate) fn floor_bigint_div(a: &BigInt, b: &BigInt) -> BigInt {
        use num_integer::Integer;
        let (q, r) = a.div_rem(b);
        // Rust's div_rem truncates toward zero. For floor division, we only
        // need to adjust when there's a remainder AND the signs differ
        // (truncation rounded toward zero, but floor rounds down).
        if !r.is_zero()
            && ((a.is_negative() && b.is_positive()) || (a.is_positive() && b.is_negative()))
        {
            q - BigInt::one()
        } else {
            q
        }
    }
}
