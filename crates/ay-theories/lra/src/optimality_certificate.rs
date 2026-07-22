// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dual (Farkas) certificates of optimality for LRA optimization (#lra-opt-cert).
//!
//! [`LraSolver::optimize_with_certificate`] returns, alongside the optimum of a
//! linear objective, an [`OptimalityCertificate`]: positive Farkas multipliers
//! over the *asserted atoms* whose linear combination syntactically entails the
//! bound inequality `objective >= bound` (minimize) or `objective <= bound`
//! (maximize). This is the dual solution of the primal simplex at the optimum:
//! each multiplier is `|objective-row coefficient| * bound reason scale` for a
//! non-basic variable stuck at the bound that blocks further improvement —
//! exactly the construction `farkas.rs`/`farkas_collect.rs` use for UNSAT
//! conflicts, applied to the terminal objective row instead of a conflict row.
//!
//! # Checking a certificate
//!
//! A certificate is checkable without trusting the simplex. Each entry
//! `(atom, value, coeff)` contributes `coeff * orient(atom, value)` where
//! `orient` rewrites the (possibly negated) atom as a `>= 0` fact:
//!
//! | atom        | value   | oriented fact  |
//! |-------------|---------|----------------|
//! | `(<= a b)`  | `true`  | `b - a >= 0`   |
//! | `(<= a b)`  | `false` | `a - b >  0`   |
//! | `(<  a b)`  | `true`  | `b - a >  0`   |
//! | `(<  a b)`  | `false` | `a - b >= 0`   |
//! | `(>= a b)`  | `true`  | `a - b >= 0`   |
//! | `(>= a b)`  | `false` | `b - a >  0`   |
//! | `(>  a b)`  | `true`  | `a - b >  0`   |
//! | `(>  a b)`  | `false` | `b - a >= 0`   |
//!
//! With all `coeff > 0`, summing the oriented linear forms must yield the
//! polynomial identity
//!
//! ```text
//! sum_i coeff_i * oriented_i  ==  objective - bound     (minimize)
//! sum_i coeff_i * oriented_i  ==  bound - objective     (maximize)
//! ```
//!
//! (identical variable coefficients AND constant). Since every oriented fact
//! is entailed `>= 0` by the corresponding asserted literal, the identity
//! entails `objective >= bound` (resp. `objective <= bound`).
//! [`OptimalityCertificate::verify`] performs exactly this check with its own
//! small linear-form evaluator over the term DAG; it never reads solver state.
//!
//! Equality atoms are deliberately *not* accepted as certificate reasons (their
//! orientation is ambiguous); extraction fails closed — returns `None` — rather
//! than emit a certificate it cannot verify.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use ay_core::kani_compat::DetHashMap;
use ay_core::term::TermData;
use ay_core::{TermId, TermStore};

use crate::types::VarStatus;
use crate::{LinearExpr, LraSolver, OptimizationSense};

/// One dual multiplier: an asserted literal and its Farkas coefficient.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateAtom {
    /// The atom term (an LRA inequality `<=`, `<`, `>=`, `>`).
    pub atom: TermId,
    /// The Boolean value the atom was asserted with (`false` = negated).
    pub value: bool,
    /// The Farkas multiplier, strictly positive.
    pub coeff: BigRational,
}

/// A dual certificate that `objective >= bound` (minimize) or
/// `objective <= bound` (maximize) is entailed by the asserted atoms.
///
/// See the module docs for the exact checkable identity and
/// [`Self::verify`] for the independent checker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OptimalityCertificate {
    /// The optimization direction the certificate was produced for.
    pub sense: OptimizationSense,
    /// The entailed bound on the objective (equal to the reported optimum).
    pub bound: BigRational,
    /// `true` if some contributing bound was strict, so the entailment is
    /// actually `objective > bound` / `objective < bound` (the optimum is an
    /// infimum/supremum that may not be attained). The weak-inequality claim
    /// certified by [`Self::verify`] holds either way.
    pub strict: bool,
    /// The dual multipliers over asserted atoms.
    pub atoms: Vec<CertificateAtom>,
}

/// A linear form over opaque term "variables": `sum(coeff * term) + constant`.
///
/// Subterms the evaluator does not understand (uninterpreted functions, `ite`,
/// non-linear products, ...) are treated as opaque variables keyed by their
/// `TermId`. This is sound for the identity check: if the certificate identity
/// holds with subterms treated as free variables, it holds for every valuation.
struct LinForm {
    coeffs: DetHashMap<TermId, BigRational>,
    constant: BigRational,
}

impl LinForm {
    fn zero() -> Self {
        Self {
            coeffs: DetHashMap::default(),
            constant: BigRational::zero(),
        }
    }

    fn add_var(&mut self, term: TermId, scale: &BigRational) {
        let entry = self.coeffs.entry(term).or_insert_with(BigRational::zero);
        *entry += scale;
    }

    /// Add `scale * term` to the form, linearizing what it can and treating
    /// the rest as opaque variables.
    fn add_term(&mut self, terms: &TermStore, term: TermId, scale: &BigRational) {
        if scale.is_zero() {
            return;
        }
        if let Some(c) = eval_const(terms, term) {
            self.constant += scale * c;
            return;
        }
        match terms.get(term) {
            TermData::App(sym, args) => match (sym.name(), args.len()) {
                ("+", _) => {
                    for &a in args {
                        self.add_term(terms, a, scale);
                    }
                }
                ("-", 1) => self.add_term(terms, args[0], &-scale),
                ("-", n) if n >= 2 => {
                    self.add_term(terms, args[0], scale);
                    let neg = -scale;
                    for &a in &args[1..] {
                        self.add_term(terms, a, &neg);
                    }
                }
                ("*", _) => {
                    // Constant factors multiply the scale; at most one
                    // non-constant factor keeps the term linear.
                    let mut factor = scale.clone();
                    let mut non_const: Option<TermId> = None;
                    let mut linear = true;
                    for &a in args {
                        if let Some(c) = eval_const(terms, a) {
                            factor *= c;
                        } else if non_const.is_none() {
                            non_const = Some(a);
                        } else {
                            linear = false;
                            break;
                        }
                    }
                    match (linear, non_const) {
                        (true, Some(t)) => self.add_term(terms, t, &factor),
                        (true, None) => self.constant += factor,
                        (false, _) => self.add_var(term, scale),
                    }
                }
                ("/", 2) => match eval_const(terms, args[1]) {
                    Some(d) if !d.is_zero() => {
                        self.add_term(terms, args[0], &(scale / d));
                    }
                    _ => self.add_var(term, scale),
                },
                ("to_real", 1) => self.add_term(terms, args[0], scale),
                _ => self.add_var(term, scale),
            },
            _ => self.add_var(term, scale),
        }
    }

    fn is_identically_zero(&self) -> bool {
        self.constant.is_zero() && self.coeffs.values().all(Zero::is_zero)
    }
}

/// Evaluate a term to a rational constant if it is a constant expression.
fn eval_const(terms: &TermStore, term: TermId) -> Option<BigRational> {
    use ay_core::term::Constant;
    match terms.get(term) {
        TermData::Const(Constant::Int(i)) => Some(BigRational::from(i.clone())),
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::App(sym, args) => match (sym.name(), args.len()) {
            ("-", 1) => Some(-eval_const(terms, args[0])?),
            ("-", n) if n >= 2 => {
                let mut v = eval_const(terms, args[0])?;
                for &a in &args[1..] {
                    v -= eval_const(terms, a)?;
                }
                Some(v)
            }
            ("+", _) => {
                let mut v = BigRational::zero();
                for &a in args {
                    v += eval_const(terms, a)?;
                }
                Some(v)
            }
            ("*", _) => {
                let mut v = BigRational::one();
                for &a in args {
                    v *= eval_const(terms, a)?;
                }
                Some(v)
            }
            ("/", 2) => {
                let n = eval_const(terms, args[0])?;
                let d = eval_const(terms, args[1])?;
                if d.is_zero() {
                    None
                } else {
                    Some(n / d)
                }
            }
            ("to_real", 1) => eval_const(terms, args[0]),
            _ => None,
        },
        _ => None,
    }
}

/// Orientation of a (possibly negated) inequality atom as a `>= 0` fact.
///
/// Returns `(sigma, strict, lhs, rhs)` such that asserting `atom = value`
/// entails `sigma * (lhs - rhs) >= 0` (`> 0` when `strict`). `sigma` is
/// `+1` or `-1`. Returns `None` for anything that is not a binary LRA
/// inequality (equalities included — their orientation is ambiguous).
fn orient_atom(terms: &TermStore, atom: TermId, value: bool) -> Option<(i8, bool, TermId, TermId)> {
    match terms.get(atom) {
        // `(not a)` asserted `v` is `a` asserted `!v`.
        TermData::Not(inner) => orient_atom(terms, *inner, !value),
        TermData::App(sym, args) if args.len() == 2 => {
            let (sigma, strict) = match (sym.name(), value) {
                ("<=", true) => (-1, false),
                ("<=", false) => (1, true),
                ("<", true) => (-1, true),
                ("<", false) => (1, false),
                (">=", true) => (1, false),
                (">=", false) => (-1, true),
                (">", true) => (1, true),
                (">", false) => (-1, false),
                _ => return None,
            };
            Some((sigma, strict, args[0], args[1]))
        }
        _ => None,
    }
}

impl OptimalityCertificate {
    /// Independently check this certificate against the term DAG.
    ///
    /// Verifies the polynomial identity from the module docs: the multiplier
    /// combination of the oriented atoms must equal `objective - bound`
    /// (minimize) / `bound - objective` (maximize) with every multiplier
    /// strictly positive. Does not read any solver state — only the terms.
    #[must_use]
    pub fn verify(&self, terms: &TermStore, objective: TermId) -> bool {
        let mut residual = LinForm::zero();

        // residual := sum_i coeff_i * sigma_i * (lhs_i - rhs_i)
        //             - sigma_obj * objective + sigma_obj * bound
        // must be identically zero, where sigma_obj = +1 (min) / -1 (max).
        let mut any_strict = false;
        for entry in &self.atoms {
            if entry.coeff <= BigRational::zero() {
                return false;
            }
            let Some((sigma, strict, lhs, rhs)) = orient_atom(terms, entry.atom, entry.value)
            else {
                return false;
            };
            any_strict |= strict;
            let scale = if sigma > 0 {
                entry.coeff.clone()
            } else {
                -entry.coeff.clone()
            };
            residual.add_term(terms, lhs, &scale);
            residual.add_term(terms, rhs, &-scale);
        }

        let sigma_obj = match self.sense {
            OptimizationSense::Minimize => BigRational::from(BigInt::from(1)),
            OptimizationSense::Maximize => BigRational::from(BigInt::from(-1)),
        };
        residual.add_term(terms, objective, &-sigma_obj.clone());
        residual.constant += sigma_obj * &self.bound;

        // The advertised strictness must not be weaker than the facts allow:
        // claiming a non-strict combination while using strict facts is fine
        // for the weak bound, but the flag must match what was combined.
        if self.strict != any_strict {
            return false;
        }

        residual.is_identically_zero()
    }
}

impl LraSolver {
    /// Extract the dual certificate at the primal-simplex optimum.
    ///
    /// Must be called while the objective row is still the last tableau row
    /// (before `optimize_with_max_iters` pops it) and no improving pivot
    /// exists. `opt_value_min` is the optimum of the *minimization form* of
    /// the objective (already negated for `Maximize`).
    ///
    /// Fails closed (returns `None`) whenever the certificate could not be
    /// grounded purely in single-reason inequality atoms:
    /// - a blocking bound has zero or multiple (or sentinel) reason atoms,
    /// - a reason atom is not a binary `<=`/`<`/`>=`/`>` (e.g. an equality),
    /// - a row variable is not non-basic (tableau invariant violation),
    /// - the recomputed bound disagrees with the simplex optimum.
    pub(crate) fn extract_optimality_certificate(
        &self,
        sense: OptimizationSense,
        opt_value_min: &BigRational,
    ) -> Option<OptimalityCertificate> {
        let terms = self.terms();
        let obj_row = self.rows.last()?;

        let mut bound_min = obj_row.constant.to_big();
        let mut strict = false;
        let mut atoms: Vec<CertificateAtom> = Vec::new();

        for &(var, ref coeff) in &obj_row.coeffs {
            if coeff.is_zero() {
                continue;
            }
            let info = self.vars.get(var as usize)?;
            if !matches!(info.status, Some(VarStatus::NonBasic)) {
                return None;
            }
            // Minimization form: a positive coefficient is blocked by the
            // variable's lower bound, a negative one by its upper bound.
            let bound = if coeff.is_positive() {
                info.lower.as_ref()?
            } else {
                info.upper.as_ref()?
            };

            bound_min += coeff.mul_bigrational(&bound.value.to_big());
            strict |= bound.strict;

            // Exactly one non-sentinel reason atom, or fail closed.
            let mut it = bound
                .reasons
                .iter()
                .zip(&bound.reason_values)
                .enumerate()
                .filter(|(_, (r, _))| !r.is_sentinel());
            let (idx, (&reason, &value)) = it.next()?;
            if it.next().is_some() {
                return None;
            }
            let scale = bound
                .reason_scales
                .get(idx)
                .map_or_else(BigRational::one, crate::rational::Rational::to_big);
            if !scale.is_positive() {
                return None;
            }

            // The reason must orient as an inequality consistent with the
            // bound's strictness (equalities and non-LRA atoms fail here).
            let (_, atom_strict, _, _) = orient_atom(terms, reason, value)?;
            if atom_strict != bound.strict {
                return None;
            }

            let lambda = coeff.abs().mul_bigrational(&scale);
            debug_assert!(lambda.is_positive());
            // Merge repeated (atom, value) entries by summing multipliers.
            match atoms
                .iter_mut()
                .find(|a| a.atom == reason && a.value == value)
            {
                Some(existing) => existing.coeff += lambda,
                None => atoms.push(CertificateAtom {
                    atom: reason,
                    value,
                    coeff: lambda,
                }),
            }
        }

        // The dual bound must reproduce the primal optimum exactly.
        if &bound_min != opt_value_min {
            return None;
        }

        let bound = match sense {
            OptimizationSense::Minimize => bound_min,
            OptimizationSense::Maximize => -bound_min,
        };
        Some(OptimalityCertificate {
            sense,
            bound,
            strict,
            atoms,
        })
    }

    /// Like [`LraSolver::optimize`], but also returns a dual (Farkas)
    /// certificate of optimality when one can be extracted.
    ///
    /// On `OptimizationResult::Optimal(v)`, the second component is
    /// `Some(cert)` with `cert.bound == v` whenever every blocking bound at
    /// the optimum traces to a single asserted inequality atom; the
    /// certificate then proves `objective >= v` (minimize) or
    /// `objective <= v` (maximize) — see [`OptimalityCertificate`]. It is
    /// `None` when extraction fails closed; the optimum itself is unaffected.
    pub fn optimize_with_certificate(
        &mut self,
        objective: &LinearExpr,
        sense: OptimizationSense,
    ) -> (crate::OptimizationResult, Option<OptimalityCertificate>) {
        self.optimize_impl(objective, sense, 10_000, true)
    }
}
