// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sum-of-Monomials (SOM) normalization preprocessing pass
//!
//! Distributes multiplication over addition to produce canonical polynomial forms:
//! - `(* c (+ a b))` → `(+ (* c a) (* c b))`
//! - `(* (+ a b) (+ c d))` → `(+ (* a c) (* a d) (* b c) (* b d))`
//!
//! This matches Z3's `som = true` parameter for QF_LRA, which activates SOM
//! normalization during the simplifier pass. The canonical polynomial form
//! allows the simplex tableau to directly ingest terms without introducing
//! slack variables for nested multiplication-over-addition structures.
//!
//! # Blowup Guard
//!
//! Z3 uses `m_som_blowup = 10` (default) to abort SOM expansion if the
//! Cartesian product would produce more than `10 * num_factors` monomials.
//! We use the same guard to prevent exponential blowup.
//!
//! # Reference
//!
//! - Z3: `reference/z3/src/ast/rewriter/poly_rewriter_def.h:357-395`
//! - Z3 parameter: `reference/z3/src/params/poly_rewriter_params.pyg:5`

use super::PreprocessingPass;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Symbol, TermData};
use ay_core::{TermId, TermStore};

/// Maximum blowup factor for SOM expansion (matches Z3's default of 10).
const SOM_BLOWUP: usize = 10;

/// Red zone size for `stacker::maybe_grow` in SOM normalization recursion (#8414).
const SOM_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for SOM normalization recursion.
const SOM_STACK_SIZE: usize = 1024 * 1024;

/// Sum-of-Monomials normalization for arithmetic terms.
///
/// Recursively walks assertion terms and rebuilds arithmetic operations
/// through `mk_mul`/`mk_add` to trigger distribution and simplification.
pub(crate) struct NormalizeArithSom {
    /// Cache: original term -> normalized term
    cache: HashMap<TermId, TermId>,
}

impl NormalizeArithSom {
    /// Create a new SOM normalization pass.
    pub(crate) fn new() -> Self {
        Self {
            cache: HashMap::default(),
        }
    }

    /// Normalize a term recursively, returning the normalized TermId.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
    fn normalize(&mut self, terms: &mut TermStore, id: TermId) -> TermId {
        stacker::maybe_grow(SOM_STACK_RED_ZONE, SOM_STACK_SIZE, || {
            if let Some(&cached) = self.cache.get(&id) {
                return cached;
            }

            let result = match terms.get(id).clone() {
                TermData::App(sym, args) => {
                    let name = sym.name().to_owned();

                    // Recursively normalize children first (bottom-up)
                    let normalized_args: Vec<TermId> =
                        args.iter().map(|&a| self.normalize(terms, a)).collect();

                    if name == "*" && normalized_args.len() >= 2 {
                        // Check if any argument is an addition — SOM trigger
                        self.normalize_mul(terms, &normalized_args, id)
                    } else if name == "+" && normalized_args.len() >= 2 {
                        // Rebuild addition through mk_add for flattening/simplification
                        self.rebuild_add(terms, &normalized_args, id, &args)
                    } else if normalized_args != args {
                        // Children changed, rebuild the term
                        self.rebuild_app(terms, id, sym, normalized_args)
                    } else {
                        id
                    }
                }
                TermData::Not(inner) => {
                    let norm = self.normalize(terms, inner);
                    if norm != inner {
                        terms.mk_not(norm)
                    } else {
                        id
                    }
                }
                TermData::Ite(cond, then_br, else_br) => {
                    let nc = self.normalize(terms, cond);
                    let nt = self.normalize(terms, then_br);
                    let ne = self.normalize(terms, else_br);
                    if nc != cond || nt != then_br || ne != else_br {
                        terms.mk_ite(nc, nt, ne)
                    } else {
                        id
                    }
                }
                // Constants, variables, quantifiers — no normalization needed
                _ => id,
            };

            self.cache.insert(id, result);
            result
        }) // stacker::maybe_grow
    }

    /// Normalize a multiplication node. If any factor is an addition,
    /// expand via Cartesian product (SOM distribution).
    fn normalize_mul(&self, terms: &mut TermStore, args: &[TermId], _original: TermId) -> TermId {
        // Check if any argument is an addition
        let has_add = args.iter().any(|&a| {
            matches!(terms.get(a), TermData::App(Symbol::Named(name), children)
                if name == "+" && children.len() >= 2)
        });

        if !has_add {
            // No addition factors — just rebuild through mk_mul for other normalizations
            let rebuilt = terms.mk_mul(args.to_vec());
            return rebuilt;
        }

        // Collect factor groups: each factor is either a sum (list of addends)
        // or a single term (treated as a 1-element list).
        let mut factor_groups: Vec<Vec<TermId>> = Vec::with_capacity(args.len());
        for &arg in args {
            match terms.get(arg) {
                TermData::App(Symbol::Named(name), children)
                    if name == "+" && children.len() >= 2 =>
                {
                    factor_groups.push(children.clone());
                }
                _ => {
                    factor_groups.push(vec![arg]);
                }
            }
        }

        // Compute total number of monomials in the Cartesian product
        let total_monomials: usize = factor_groups.iter().map(Vec::len).product();

        // Blowup guard: if expansion exceeds SOM_BLOWUP * num_factors, skip
        if total_monomials > SOM_BLOWUP * factor_groups.len() {
            // Too large — just rebuild without expansion
            return terms.mk_mul(args.to_vec());
        }

        // Cartesian product expansion
        let mut sum_terms: Vec<TermId> = Vec::with_capacity(total_monomials);
        let mut indices = vec![0usize; factor_groups.len()];

        loop {
            // Collect one term from each factor at current indices
            let mut monomial_factors: Vec<TermId> = Vec::with_capacity(factor_groups.len());
            for (i, group) in factor_groups.iter().enumerate() {
                monomial_factors.push(group[indices[i]]);
            }

            // Create the monomial: multiply the selected terms
            let monomial = terms.mk_mul(monomial_factors);
            sum_terms.push(monomial);

            // Advance the odometer-style iterator
            if !Self::product_iterator_next(&factor_groups, &mut indices) {
                break;
            }
        }

        // Build the final sum of all monomials
        terms.mk_add(sum_terms)
    }

    /// Odometer-style Cartesian product iterator.
    /// Returns false when all combinations are exhausted.
    fn product_iterator_next(groups: &[Vec<TermId>], indices: &mut [usize]) -> bool {
        for i in 0..groups.len() {
            indices[i] += 1;
            if indices[i] < groups[i].len() {
                return true;
            }
            indices[i] = 0;
        }
        false
    }

    /// Rebuild addition through mk_add for flattening and coefficient collection.
    fn rebuild_add(
        &self,
        terms: &mut TermStore,
        normalized_args: &[TermId],
        original: TermId,
        original_args: &[TermId],
    ) -> TermId {
        if normalized_args == original_args {
            return original;
        }
        terms.mk_add(normalized_args.to_vec())
    }

    /// Rebuild an application term with new arguments.
    fn rebuild_app(
        &self,
        terms: &mut TermStore,
        original: TermId,
        sym: Symbol,
        args: Vec<TermId>,
    ) -> TermId {
        let name = sym.name();
        match name {
            "+" => terms.mk_add(args),
            "*" => terms.mk_mul(args),
            "-" if args.len() == 1 => terms.mk_neg(args[0]),
            "/" if args.len() == 2 => terms.mk_div(args[0], args[1]),
            "<" if args.len() == 2 => terms.mk_lt(args[0], args[1]),
            "<=" if args.len() == 2 => terms.mk_le(args[0], args[1]),
            "=" if args.len() == 2 => terms.mk_eq_coerce(args[0], args[1]),
            "and" => terms.mk_and(args),
            "or" => terms.mk_or(args),
            "not" if args.len() == 1 => terms.mk_not(args[0]),
            "ite" if args.len() == 3 => terms.mk_ite(args[0], args[1], args[2]),
            _ => terms.mk_app(sym, args, terms.sort(original).clone()),
        }
    }
}

impl Default for NormalizeArithSom {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for NormalizeArithSom {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        // Only apply to Int/Real sorts — skip if no arithmetic assertions
        let has_arith = assertions.iter().any(|&a| self.has_arithmetic(terms, a));
        if !has_arith {
            return false;
        }

        let mut modified = false;
        for assertion in assertions.iter_mut() {
            let normalized = self.normalize(terms, *assertion);
            if normalized != *assertion {
                *assertion = normalized;
                modified = true;
            }
        }
        modified
    }

    fn reset(&mut self) {
        self.cache.clear();
    }
}

impl NormalizeArithSom {
    /// Quick check if an assertion contains arithmetic operations.
    fn has_arithmetic(&self, terms: &TermStore, id: TermId) -> bool {
        Self::term_has_arithmetic(terms, id)
    }

    fn term_has_arithmetic(terms: &TermStore, id: TermId) -> bool {
        match terms.get(id) {
            TermData::App(Symbol::Named(name), args) => {
                if matches!(
                    name.as_str(),
                    "+" | "*" | "-" | "/" | "<" | "<=" | ">=" | ">"
                ) {
                    return true;
                }
                args.iter().any(|&a| Self::term_has_arithmetic(terms, a))
            }
            TermData::Not(inner) => Self::term_has_arithmetic(terms, *inner),
            TermData::Ite(c, t, e) => {
                Self::term_has_arithmetic(terms, *c)
                    || Self::term_has_arithmetic(terms, *t)
                    || Self::term_has_arithmetic(terms, *e)
            }
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests;
