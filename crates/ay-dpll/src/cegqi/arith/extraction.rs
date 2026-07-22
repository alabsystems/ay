// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Variable extraction from arithmetic terms for CEGQI.
//!
//! Given a term and a "processed variable" (pv), extracts the coefficient
//! and additive remainder: for `c*pv + rest`, returns `(c, Some(rest))`.
//!
//! Handles: direct pv, binary/n-ary/nested multiplication, addition,
//! subtraction (binary + unary negation), and ITE with matching coefficients.

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::ArithInstantiator;

impl ArithInstantiator {
    /// Extract the coefficient and remainder for `pv` in a term.
    ///
    /// For term `c*pv + rest`, returns `(c, Some(rest))`.
    /// For term `c*pv` (no additive rest), returns `(c, None)`.
    /// For term `pv`, returns `(1, None)`.
    /// For term without `pv`, returns `(0, None)`.
    pub(crate) fn extract_variable(
        terms: &mut TermStore,
        term: TermId,
        pv: TermId,
    ) -> (BigRational, Option<TermId>) {
        if term == pv {
            return (BigRational::from(BigInt::from(1)), None);
        }

        let data = terms.get(term).clone();
        match &data {
            // Check for c * pv (multiplication), including nested: (* c (* d pv))
            // Recursively extracts coefficient through nested multiplications.
            // (#5888 Finding 7)
            TermData::App(Symbol::Named(name), args) if name == "*" && args.len() == 2 => {
                let (first, second) = (args[0], args[1]);
                // Try: first is constant, second contains pv
                let first_const = match terms.get(first) {
                    TermData::Const(Constant::Int(c)) => Some(BigRational::from(c.clone())),
                    TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
                    _ => None,
                };
                if let Some(c) = &first_const {
                    if second == pv {
                        return (c.clone(), None);
                    }
                    // Recurse into second: (* c (* d pv)) → coeff = c * d
                    let (inner_coeff, inner_rem) = Self::extract_variable(terms, second, pv);
                    let zero_r = BigRational::from(BigInt::from(0));
                    if inner_coeff != zero_r {
                        let combined = c * &inner_coeff;
                        // Remainder gets scaled: (* c remainder)
                        let scaled_rem = inner_rem.map(|r| terms.mk_mul(vec![first, r]));
                        return (combined, scaled_rem);
                    }
                }
                // Try: second is constant, first contains pv
                let second_const = match terms.get(second) {
                    TermData::Const(Constant::Int(c)) => Some(BigRational::from(c.clone())),
                    TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
                    _ => None,
                };
                if let Some(c) = &second_const {
                    if first == pv {
                        return (c.clone(), None);
                    }
                    // Recurse into first: (* (* d pv) c) → coeff = d * c
                    let (inner_coeff, inner_rem) = Self::extract_variable(terms, first, pv);
                    let zero_r = BigRational::from(BigInt::from(0));
                    if inner_coeff != zero_r {
                        let combined = &inner_coeff * c;
                        let scaled_rem = inner_rem.map(|r| terms.mk_mul(vec![r, second]));
                        return (combined, scaled_rem);
                    }
                }
            }
            // N-ary multiplication: (* a b c ...) with 3+ args.
            // Scan for pv among args. If arg[i] contains pv with coeff c,
            // the product of all other (constant) args forms the outer coefficient.
            TermData::App(Symbol::Named(name), args) if name == "*" && args.len() > 2 => {
                let zero_r = BigRational::from(BigInt::from(0));
                let args_vec: Vec<TermId> = args.clone();
                for (i, &arg) in args_vec.iter().enumerate() {
                    let (coeff, _) = Self::extract_variable(terms, arg, pv);
                    if coeff != zero_r {
                        // pv found in arg[i]. Compute product of all other args as
                        // constant multiplier. If any non-pv arg is non-constant,
                        // we can't extract a clean coefficient — bail out.
                        let mut outer = BigRational::from(BigInt::from(1));
                        let mut all_const = true;
                        for (j, &other) in args_vec.iter().enumerate() {
                            if j == i {
                                continue;
                            }
                            match terms.get(other) {
                                TermData::Const(Constant::Int(c)) => {
                                    outer *= BigRational::from(c.clone());
                                }
                                TermData::Const(Constant::Rational(r)) => {
                                    outer *= &r.0;
                                }
                                _ => {
                                    all_const = false;
                                    break;
                                }
                            }
                        }
                        if all_const {
                            return (outer * coeff, None);
                        }
                        break;
                    }
                }
            }
            // Check for addition containing pv: (+ a1 a2 ... an)
            // If one arg has pv with coeff c, the rest form the remainder.
            TermData::App(Symbol::Named(name), args) if name == "+" => {
                let zero_r = BigRational::from(BigInt::from(0));
                let args_vec: Vec<TermId> = args.clone();
                for (i, &arg) in args_vec.iter().enumerate() {
                    let (coeff, _) = Self::extract_variable(terms, arg, pv);
                    if coeff != zero_r {
                        // Collect the other summands as the remainder
                        let others: Vec<TermId> = args_vec
                            .iter()
                            .enumerate()
                            .filter(|&(j, _)| j != i)
                            .map(|(_, &a)| a)
                            .collect();
                        let remainder = match others.len() {
                            0 => None,
                            1 => Some(others[0]),
                            _ => Some(terms.mk_add(others)),
                        };
                        return (coeff, remainder);
                    }
                }
            }
            // Check for subtraction: (- a b)
            // (- a pv) → coeff = -1, remainder = a
            // (- pv a) → coeff = 1, remainder = negated a
            // Also handles (- a c*pv) and (- c*pv a) recursively.
            TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 2 => {
                let zero_r = BigRational::from(BigInt::from(0));
                let (first, second) = (args[0], args[1]);

                // Check first arg (positive position)
                let (first_coeff, first_rem) = Self::extract_variable(terms, first, pv);
                if first_coeff != zero_r {
                    // pv is in first arg: (- (c*pv + rest) second)
                    // Result: coeff = c, remainder = rest - second
                    let neg_second = if let Some(rem) = first_rem {
                        Some(terms.mk_sub(vec![rem, second]))
                    } else {
                        // (- c*pv second) → remainder = -second
                        let zero = terms.mk_int(BigInt::from(0));
                        Some(terms.mk_sub(vec![zero, second]))
                    };
                    return (first_coeff, neg_second);
                }

                // Check second arg (negative position)
                let (second_coeff, second_rem) = Self::extract_variable(terms, second, pv);
                if second_coeff != zero_r {
                    // pv is in second arg: (- first (c*pv + rest))
                    // Result: coeff = -c, remainder = first - rest
                    let remainder = if let Some(rem) = second_rem {
                        Some(terms.mk_sub(vec![first, rem]))
                    } else {
                        Some(first)
                    };
                    return (-second_coeff, remainder);
                }
            }
            // Check for unary negation: (- pv) or (- c*pv)
            TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 1 => {
                let zero_r = BigRational::from(BigInt::from(0));
                let (coeff, rem) = Self::extract_variable(terms, args[0], pv);
                if coeff != zero_r {
                    // (- c*pv + rest) → coeff = -c, remainder = -rest
                    let neg_rem = rem.map(|r| {
                        let zero = terms.mk_int(BigInt::from(0));
                        terms.mk_sub(vec![zero, r])
                    });
                    return (-coeff, neg_rem);
                }
            }
            // ITE: (ite cond then_branch else_branch)
            // If pv appears with the same coefficient in both branches, extract it.
            // The remainder becomes (ite cond then_rem else_rem).
            // Common pattern: abs(x) = ite(x >= 0, x, -x) has coeff 1 in both branches.
            // (#5888 Finding 8 — deductive-checks generates ite extensively for truncation div)
            TermData::Ite(cond, then_branch, else_branch) => {
                let zero_r = BigRational::from(BigInt::from(0));
                let cond = *cond;
                let then_branch = *then_branch;
                let else_branch = *else_branch;
                let (then_coeff, then_rem) = Self::extract_variable(terms, then_branch, pv);
                if then_coeff != zero_r {
                    let (else_coeff, else_rem) = Self::extract_variable(terms, else_branch, pv);
                    if then_coeff == else_coeff {
                        // Same coefficient in both branches: factor out.
                        // remainder = ite(cond, then_rem, else_rem)
                        let then_r = then_rem.unwrap_or_else(|| terms.mk_int(BigInt::from(0)));
                        let else_r = else_rem.unwrap_or_else(|| terms.mk_int(BigInt::from(0)));
                        let ite_rem = terms.mk_ite(cond, then_r, else_r);
                        return (then_coeff, Some(ite_rem));
                    }
                }
            }
            _ => {}
        }

        // pv not found
        (BigRational::from(BigInt::from(0)), None)
    }

    /// Check if `target` appears anywhere in `term` (including as `term` itself).
    pub(super) fn term_contains(terms: &TermStore, term: TermId, target: TermId) -> bool {
        if term == target {
            return true;
        }
        match terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => false,
            TermData::App(_, args) => args.iter().any(|&a| Self::term_contains(terms, a, target)),
            TermData::Not(inner) => Self::term_contains(terms, *inner, target),
            TermData::Ite(c, t, e) => {
                Self::term_contains(terms, *c, target)
                    || Self::term_contains(terms, *t, target)
                    || Self::term_contains(terms, *e, target)
            }
            TermData::Let(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, val)| Self::term_contains(terms, *val, target))
                    || Self::term_contains(terms, *body, target)
            }
            _ => false, // Conservative: quantifiers etc. — don't recurse
        }
    }
}
