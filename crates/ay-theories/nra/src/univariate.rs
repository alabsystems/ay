// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sound univariate real-arithmetic decision procedure for QF_NRA.
//!
//! AY's default NRA engine linearizes nonlinear terms with tangent-plane /
//! McCormick lemmas. That is incomplete for genuinely nonlinear univariate
//! constraints such as `x*x > 2` — the tangent linearization at the current
//! model point excludes the feasible region near the irrational root
//! `sqrt(2)`, and the solver bails out to `unknown`.
//!
//! This module adds an *exact*, *sound* decision procedure that fires when the
//! problem (after the existing simplification) decomposes into independent
//! single-variable polynomial subproblems. For each variable we:
//!
//!   1. Turn every constraint mentioning that variable into a univariate
//!      polynomial `p(x) {<,<=,=,>=,>,!=} 0` with exact [`BigRational`]
//!      coefficients.
//!   2. Isolate the real roots of all those polynomials as exact rational
//!      points and/or disjoint isolating rational intervals using a Sturm
//!      sequence (degree <= 2 uses a closed form; higher degree bisects).
//!   3. The combined root set partitions the real line into sign-invariant
//!      cells. We sample an exact rational point from each cell and intersect
//!      the feasible cells across all of that variable's constraints.
//!   4. A variable is SAT iff its feasible set is non-empty; we pick an exact
//!      rational witness from a feasible cell.
//!
//! ## Soundness (the whole point)
//!
//! Every step uses exact [`BigRational`]/[`num_bigint::BigInt`] arithmetic —
//! never `f64`. The verdict is fail-closed:
//!
//!   * SAT is returned only if *every* constrained variable has a witness AND
//!     the assembled concrete model is re-checked by exact substitution into
//!     *every* original asserted atom. If substitution does not confirm, we
//!     return `unknown` and fall through to the tangent path.
//!   * UNSAT is returned only if the problem is genuinely univariate-
//!     decomposable and some single variable's feasible set is provably empty.
//!   * Any cross-variable nonlinear coupling, any unsupported operator, or any
//!     uncertainty => `unknown`.
//!
//! Reference grounding: Sturm/real-root isolation as in
//! `reference/z3-noodler/src/math/polynomial/{upolynomial,algebraic_numbers}`
//! and CAD sign-invariant cell sampling as in `reference/smtrat/smtrat-cad`.

use ay_core::term::{Constant, Symbol, TermData, TermId};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::NraSolver;

/// A dense univariate polynomial over the rationals, `coeffs[i]` is the
/// coefficient of `x^i`. The zero polynomial is the empty vector. By
/// construction (via [`UniPoly::normalize`]) the leading coefficient is
/// non-zero for a non-zero polynomial.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct UniPoly {
    coeffs: Vec<BigRational>,
}

impl UniPoly {
    pub(crate) fn zero() -> Self {
        Self { coeffs: Vec::new() }
    }

    pub(crate) fn constant(c: BigRational) -> Self {
        let mut p = Self { coeffs: vec![c] };
        p.normalize();
        p
    }

    /// The monomial `x` (degree-1 identity polynomial).
    pub(crate) fn x() -> Self {
        Self {
            coeffs: vec![BigRational::zero(), BigRational::one()],
        }
    }

    /// Construct from low-to-high coefficients, normalizing trailing zeros.
    pub(crate) fn from_coeffs(coeffs: Vec<BigRational>) -> Self {
        let mut p = Self { coeffs };
        p.normalize();
        p
    }

    /// Low-to-high coefficients (empty for the zero polynomial).
    pub(crate) fn coeffs(&self) -> &[BigRational] {
        &self.coeffs
    }

    /// Drop trailing zero coefficients so the leading coefficient is non-zero.
    fn normalize(&mut self) {
        while let Some(last) = self.coeffs.last() {
            if last.is_zero() {
                self.coeffs.pop();
            } else {
                break;
            }
        }
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// Degree, or `None` for the zero polynomial.
    pub(crate) fn degree(&self) -> Option<usize> {
        if self.coeffs.is_empty() {
            None
        } else {
            Some(self.coeffs.len() - 1)
        }
    }

    pub(crate) fn leading(&self) -> Option<&BigRational> {
        self.coeffs.last()
    }

    pub(crate) fn add(&self, other: &Self) -> Self {
        let n = self.coeffs.len().max(other.coeffs.len());
        let mut coeffs = Vec::with_capacity(n);
        for i in 0..n {
            let a = self
                .coeffs
                .get(i)
                .cloned()
                .unwrap_or_else(BigRational::zero);
            let b = other
                .coeffs
                .get(i)
                .cloned()
                .unwrap_or_else(BigRational::zero);
            coeffs.push(a + b);
        }
        let mut p = Self { coeffs };
        p.normalize();
        p
    }

    pub(crate) fn neg(&self) -> Self {
        Self {
            coeffs: self.coeffs.iter().map(|c| -c).collect(),
        }
    }

    pub(crate) fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    pub(crate) fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut coeffs = vec![BigRational::zero(); self.coeffs.len() + other.coeffs.len() - 1];
        for (i, a) in self.coeffs.iter().enumerate() {
            if a.is_zero() {
                continue;
            }
            for (j, b) in other.coeffs.iter().enumerate() {
                coeffs[i + j] += a * b;
            }
        }
        let mut p = Self { coeffs };
        p.normalize();
        p
    }

    pub(crate) fn scale(&self, s: &BigRational) -> Self {
        if s.is_zero() {
            return Self::zero();
        }
        Self {
            coeffs: self.coeffs.iter().map(|c| c * s).collect(),
        }
    }

    /// Evaluate the polynomial at an exact rational point (Horner).
    pub(crate) fn eval(&self, x: &BigRational) -> BigRational {
        let mut acc = BigRational::zero();
        for c in self.coeffs.iter().rev() {
            acc = acc * x + c;
        }
        acc
    }

    /// Formal derivative.
    pub(crate) fn derivative(&self) -> Self {
        if self.coeffs.len() <= 1 {
            return Self::zero();
        }
        let mut coeffs = Vec::with_capacity(self.coeffs.len() - 1);
        for (i, c) in self.coeffs.iter().enumerate().skip(1) {
            coeffs.push(c * BigRational::from_integer(BigInt::from(i)));
        }
        let mut p = Self { coeffs };
        p.normalize();
        p
    }

    /// Polynomial remainder `self mod other` (other must be non-zero).
    /// Standard long division over the rationals.
    pub(crate) fn rem(&self, other: &Self) -> Self {
        debug_assert!(!other.is_zero());
        let mut r = self.clone();
        let d_deg = match other.degree() {
            Some(d) => d,
            None => return Self::zero(),
        };
        let d_lead = other
            .leading()
            .expect("non-zero divisor has a leading coeff");
        while let Some(r_deg) = r.degree() {
            if r_deg < d_deg {
                break;
            }
            let r_lead = r.leading().expect("non-zero poly has a leading coeff");
            let factor = r_lead / d_lead;
            let shift = r_deg - d_deg;
            // Subtract factor * x^shift * other from r.
            let mut sub = vec![BigRational::zero(); shift];
            for c in &other.coeffs {
                sub.push(c * &factor);
            }
            let sub_poly = Self { coeffs: sub };
            r = r.sub(&sub_poly);
        }
        r
    }

    /// A canonical sign-preserving normal form for the leading coefficient.
    /// Divides through by the absolute value of the leading coefficient so the
    /// leading coefficient becomes +/-1; this never changes any root and keeps
    /// Sturm-sequence arithmetic small. (We do *not* force monic because the
    /// sign of the leading coefficient matters for limits at +/-inf.)
    fn primitive_like(&self) -> Self {
        match self.leading() {
            Some(lead) if !lead.is_zero() => {
                let inv_abs = BigRational::one() / lead.abs();
                self.scale(&inv_abs)
            }
            _ => self.clone(),
        }
    }
}

/// A constraint reduced to `poly REL 0` over a single variable.
#[derive(Clone, Debug)]
struct UniConstraint {
    poly: UniPoly,
    rel: Rel,
}

/// The six comparison relations against zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Rel {
    Lt,
    Le,
    Eq,
    Ge,
    Gt,
    Ne,
}

impl Rel {
    /// Does `sign(p) {rel} 0` hold, where `sign` is -1, 0 or +1?
    pub(crate) fn holds_for_sign(self, sign: i32) -> bool {
        match self {
            Self::Lt => sign < 0,
            Self::Le => sign <= 0,
            Self::Eq => sign == 0,
            Self::Ge => sign >= 0,
            Self::Gt => sign > 0,
            Self::Ne => sign != 0,
        }
    }
}

/// A single variable's model witness from the exact decision procedures.
#[derive(Clone, Debug)]
pub(crate) enum UniWitness {
    /// Exact rational witness.
    Rational(BigRational),
    /// Exact real algebraic witness: a polynomial expression over an
    /// irrational root (defining square-free polynomial + root index +
    /// isolating interval — the same information as z3's `root-obj` model
    /// values). Coupled variables share ONE root with different residues
    /// (a triangular assignment), so joint atoms still evaluate exactly.
    Algebraic(crate::algebraic::RealAlgebraicValue),
}

/// Outcome of the univariate decision procedure.
pub(crate) enum UniResult {
    /// Proven SAT with a concrete, substitution-verified rational model
    /// (variable -> witness value). Variables not present here are
    /// unconstrained by nonlinear/arithmetic atoms.
    Sat(Vec<(TermId, BigRational)>),
    /// Proven SAT by an exact Sturm / IVT real-root certificate where at
    /// least one witness is IRRATIONAL (e.g. `x*x = 2`). The sign-invariant
    /// cell analysis in [`decide_single_variable`] proves — with exact
    /// `BigRational` arithmetic — that a real solution exists, and the
    /// payload carries the FULL witness assignment: rational values for the
    /// rational variables plus exact [`crate::algebraic::RealAlgebraic`]
    /// values for the irrational ones. The caller injects the rational part
    /// into the LRA model and hands the algebraic part to the executor's
    /// model, where evaluation, printing (z3 `root-obj` parity) and full
    /// model validation handle it exactly. NEVER produced unless a feasible
    /// cell was certified to exist over the reals AND the assembled witness
    /// re-verified exactly against every asserted atom.
    SatAlgebraic(Vec<(TermId, UniWitness)>),
    /// Proven UNSAT (some variable's feasible set is provably empty).
    Unsat,
    /// Out of fragment / uncertain — caller must fall through unchanged.
    Unknown,
}

impl NraSolver<'_> {
    /// Attempt to decide the current assertion set with the exact univariate
    /// procedure. Returns [`UniResult::Unknown`] whenever anything is outside
    /// the supported fragment or cannot be confirmed exactly.
    pub(crate) fn try_univariate_decide(&self) -> UniResult {
        // Collect constraints grouped by their (single) free variable.
        // `per_var[var]` accumulates that variable's constraints.
        // We also remember the order assertions appeared so model assembly is
        // deterministic.
        let mut per_var: crate::HashMap<TermId, Vec<UniConstraint>> = crate::HashMap::default();
        let mut var_order: Vec<TermId> = Vec::new();

        for &(atom, value) in &self.asserted {
            match self.atom_to_univariate(atom, value) {
                // A pure-constant atom that is false makes the problem UNSAT.
                AtomClass::ConstFalse => return UniResult::Unsat,
                // A pure-constant atom that is true contributes nothing.
                AtomClass::ConstTrue => {}
                AtomClass::Univariate(var, c) => {
                    if !per_var.contains_key(&var) {
                        var_order.push(var);
                    }
                    per_var.entry(var).or_default().push(c);
                }
                AtomClass::OutOfScope => return UniResult::Unknown,
            }
        }

        if per_var.is_empty() {
            // No constrained variable in scope — nothing for us to decide.
            return UniResult::Unknown;
        }

        // Decide each variable independently.
        //
        // SOUNDNESS of independence: every atom in this fragment mentions AT MOST
        // ONE variable (`atom_to_univariate` returns `OutOfScope` for any atom
        // coupling two distinct variables), and the atoms are partitioned by that
        // single variable. Distinct variables therefore share NO constraint, so
        // the whole system is satisfiable iff every variable is individually
        // satisfiable, and any per-variable witnesses combine into a global model
        // without interaction. UNSAT of any single variable ⇒ global UNSAT.
        let mut model: Vec<(TermId, BigRational)> = Vec::new();
        // Variables satisfiable ONLY at an irrational point, with their exact
        // algebraic witnesses. When non-empty (and every variable is
        // satisfiable), the conjunction is SAT with a mixed rational/algebraic
        // model.
        let mut algebraic: Vec<(TermId, crate::algebraic::RealAlgebraic)> = Vec::new();
        for var in &var_order {
            let constraints = &per_var[var];
            match decide_single_variable(constraints) {
                SingleVarResult::Witness(w) => model.push((*var, w)),
                SingleVarResult::Empty => return UniResult::Unsat,
                // Satisfiable, but only at an irrational point. The exact
                // algebraic witness is carried along; keep deciding the rest
                // (a later variable could still be UNSAT, which would override
                // to a sound global UNSAT).
                SingleVarResult::IrrationalSat(alg) => algebraic.push((*var, alg)),
                SingleVarResult::Unknown => return UniResult::Unknown,
            }
        }

        if !algebraic.is_empty() {
            // At least one variable is satisfiable only at an irrational point
            // and NO variable is UNSAT (an Empty above would have returned).
            // SOUNDNESS GATE: re-verify the assembled mixed model against
            // EVERY asserted atom — rational witnesses by exact substitution,
            // algebraic witnesses by exact Sturm sign determination.
            if !self.verify_mixed_model(&model, &algebraic) {
                return UniResult::Unknown;
            }
            let mut witnesses: Vec<(TermId, UniWitness)> = Vec::new();
            for (v, w) in model {
                witnesses.push((v, UniWitness::Rational(w)));
            }
            for (v, a) in algebraic {
                witnesses.push((v, UniWitness::Algebraic(a.as_value())));
            }
            return UniResult::SatAlgebraic(witnesses);
        }

        // All witnesses are rational. SOUNDNESS GATE: re-verify the assembled model
        // against EVERY original asserted atom by exact substitution. Only emit SAT
        // if all confirm.
        if self.verify_model(&model) {
            UniResult::Sat(model)
        } else {
            UniResult::Unknown
        }
    }

    /// Verify a candidate model by exact rational substitution into every
    /// asserted atom. Returns false (→ unknown) if any atom is not confirmed
    /// true, including any atom we cannot evaluate exactly.
    pub(crate) fn verify_model(&self, model: &[(TermId, BigRational)]) -> bool {
        for &(atom, value) in &self.asserted {
            match self.eval_atom_under_model(atom, model) {
                Some(truth) => {
                    if truth != value {
                        return false;
                    }
                }
                None => return false, // could not evaluate exactly => not confirmed
            }
        }
        true
    }

    /// Verify a MIXED candidate model (rational witnesses + exact algebraic
    /// witnesses) against every asserted atom. Each atom in the univariate
    /// fragment mentions at most one variable: rational-variable atoms are
    /// checked by exact substitution, algebraic-variable atoms by exact Sturm
    /// sign determination of the constraint polynomial at the algebraic root.
    /// Returns false (→ unknown upstream) on any atom that is not confirmed.
    fn verify_mixed_model(
        &self,
        rational: &[(TermId, BigRational)],
        algebraic: &[(TermId, crate::algebraic::RealAlgebraic)],
    ) -> bool {
        for &(atom, value) in &self.asserted {
            match self.atom_to_univariate(atom, value) {
                AtomClass::ConstTrue => {}
                AtomClass::ConstFalse => return false,
                AtomClass::Univariate(var, c) => {
                    if let Some((_, alg)) = algebraic.iter().find(|(v, _)| *v == var) {
                        match alg.sign_of_poly(&c.poly) {
                            Some(sign) if c.rel.holds_for_sign(sign) => {}
                            _ => return false,
                        }
                    } else if let Some((_, w)) = rational.iter().find(|(v, _)| *v == var) {
                        let sign = rational_sign(&c.poly.eval(w));
                        if !c.rel.holds_for_sign(sign) {
                            return false;
                        }
                    } else {
                        return false; // unvalued variable: not confirmed
                    }
                }
                AtomClass::OutOfScope => return false,
            }
        }
        true
    }

    /// Evaluate a comparison atom under a model, returning its exact truth
    /// value, or `None` if it cannot be evaluated exactly (unsupported shape).
    fn eval_atom_under_model(&self, atom: TermId, model: &[(TermId, BigRational)]) -> Option<bool> {
        let (rel, lhs, rhs) = self.comparison_parts(atom)?;
        let lv = self.eval_term_under_model(lhs, model)?;
        let rv = self.eval_term_under_model(rhs, model)?;
        let diff = &lv - &rv;
        let sign = rational_sign(&diff);
        Some(rel.holds_for_sign(sign))
    }

    /// Evaluate an arithmetic term to an exact rational under the model.
    /// Variables in the model take their witness value; variables NOT in the
    /// model are treated as fully unknown and make evaluation fail (None).
    pub(crate) fn eval_term_under_model(
        &self,
        term: TermId,
        model: &[(TermId, BigRational)],
    ) -> Option<BigRational> {
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
            TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
            TermData::Var(_, _) => model
                .iter()
                .find(|(v, _)| *v == term)
                .map(|(_, val)| val.clone()),
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" if !args.is_empty() => {
                    let mut acc = BigRational::zero();
                    for &a in args {
                        acc += self.eval_term_under_model(a, model)?;
                    }
                    Some(acc)
                }
                "*" if !args.is_empty() => {
                    let mut acc = BigRational::one();
                    for &a in args {
                        acc *= self.eval_term_under_model(a, model)?;
                    }
                    Some(acc)
                }
                "-" if args.len() == 1 => Some(-self.eval_term_under_model(args[0], model)?),
                "-" if args.len() >= 2 => {
                    let mut acc = self.eval_term_under_model(args[0], model)?;
                    for &a in &args[1..] {
                        acc -= self.eval_term_under_model(a, model)?;
                    }
                    Some(acc)
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Classify an asserted atom: turn `lhs cmp rhs` (under polarity `value`)
    /// into `poly REL 0` over at most one variable.
    fn atom_to_univariate(&self, atom: TermId, value: bool) -> AtomClass {
        let Some((rel0, lhs, rhs)) = self.comparison_parts(atom) else {
            return AtomClass::OutOfScope;
        };
        // Apply polarity: a false-asserted atom negates the relation.
        let rel = if value { rel0 } else { negate_rel(rel0) };

        // Build poly = lhs - rhs as a univariate polynomial.
        let lhs_poly = match self.term_to_unipoly(lhs) {
            Some(p) => p,
            None => return AtomClass::OutOfScope,
        };
        let rhs_poly = match self.term_to_unipoly(rhs) {
            Some(p) => p,
            None => return AtomClass::OutOfScope,
        };

        // Merge variable identity. Each side carries an optional variable; they
        // must agree (or one be constant) for the difference to stay univariate.
        let var = match (lhs_poly.var, rhs_poly.var) {
            (None, None) => None,
            (Some(v), None) | (None, Some(v)) => Some(v),
            (Some(a), Some(b)) if a == b => Some(a),
            // Two distinct variables coupled in one atom => not univariate.
            (Some(_), Some(_)) => return AtomClass::OutOfScope,
        };

        let poly = lhs_poly.poly.sub(&rhs_poly.poly);

        match var {
            None => {
                // Pure-constant constraint: evaluate the constant's sign.
                let sign = match poly.degree() {
                    None => 0,                                 // zero polynomial
                    Some(0) => rational_sign(&poly.coeffs[0]), // constant
                    Some(_) => unreachable!("var=None implies degree<=0"),
                };
                if rel.holds_for_sign(sign) {
                    AtomClass::ConstTrue
                } else {
                    AtomClass::ConstFalse
                }
            }
            Some(v) => AtomClass::Univariate(v, UniConstraint { poly, rel }),
        }
    }

    /// Extract `(rel, lhs, rhs)` from a binary comparison atom, or `None` if
    /// the atom is not a recognized arithmetic comparison.
    fn comparison_parts(&self, atom: TermId) -> Option<(Rel, TermId, TermId)> {
        match self.terms.get(atom) {
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                let rel = match name.as_str() {
                    "<" => Rel::Lt,
                    "<=" => Rel::Le,
                    "=" => Rel::Eq,
                    ">=" => Rel::Ge,
                    ">" => Rel::Gt,
                    "distinct" | "!=" => Rel::Ne,
                    _ => return None,
                };
                Some((rel, args[0], args[1]))
            }
            _ => None,
        }
    }

    /// Convert an arithmetic term into a univariate polynomial together with
    /// the (at most one) variable it depends on. Returns `None` if the term
    /// uses an unsupported operator or mentions two distinct variables.
    fn term_to_unipoly(&self, term: TermId) -> Option<VarPoly> {
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => Some(VarPoly {
                poly: UniPoly::constant(BigRational::from_integer(n.clone())),
                var: None,
            }),
            TermData::Const(Constant::Rational(r)) => Some(VarPoly {
                poly: UniPoly::constant(r.0.clone()),
                var: None,
            }),
            TermData::Var(_, _) => Some(VarPoly {
                poly: UniPoly::x(),
                var: Some(term),
            }),
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" if !args.is_empty() => {
                    let mut acc = VarPoly {
                        poly: UniPoly::zero(),
                        var: None,
                    };
                    for &a in args {
                        let p = self.term_to_unipoly(a)?;
                        acc = acc.combine_add(p)?;
                    }
                    Some(acc)
                }
                "-" if args.len() == 1 => {
                    let p = self.term_to_unipoly(args[0])?;
                    Some(VarPoly {
                        poly: p.poly.neg(),
                        var: p.var,
                    })
                }
                "-" if args.len() >= 2 => {
                    let mut acc = self.term_to_unipoly(args[0])?;
                    for &a in &args[1..] {
                        let p = self.term_to_unipoly(a)?;
                        let negated = VarPoly {
                            poly: p.poly.neg(),
                            var: p.var,
                        };
                        acc = acc.combine_add(negated)?;
                    }
                    Some(acc)
                }
                "*" if !args.is_empty() => {
                    let mut acc = VarPoly {
                        poly: UniPoly::constant(BigRational::one()),
                        var: None,
                    };
                    for &a in args {
                        let p = self.term_to_unipoly(a)?;
                        acc = acc.combine_mul(p)?;
                    }
                    Some(acc)
                }
                // Unsupported: /, div, mod, abs, transcendental, etc.
                _ => None,
            },
            _ => None,
        }
    }
}

// ============================================================================
// Exact `is_int` decision over an affine/univariate real fragment (#9139).
//
// SMT-LIB `is_int(r)` holds iff the real `r` is an integer. Pure LRA reasons
// over the rationals and cannot decide it; the NRA tangent linearization does
// not model integrality either. This section adds a *sound*, *exact*
// (`BigRational`-only) decision procedure for the fragment where:
//
//   * every asserted comparison atom is LINEAR (degree <= 1) over a single
//     shared real variable `x` (or constant), and
//   * every `is_int(E)` / `(not (is_int E))` atom reduces — after a SOUND
//     division-by-self simplification `(/ e e) -> 1` performed ONLY when the
//     divisor `e` is PROVABLY nonzero in the feasible region — to an affine
//     form `a*x + c` (degree <= 1) over the same variable.
//
// Decision:
//   * The linear comparisons define a feasible interval `[lo, hi]` (with
//     open/closed endpoints) plus a set of excluded points (`!=`) and an
//     optional forced point (`=`).
//   * A witness `x = w` is SAT iff, by EXACT substitution, EVERY asserted atom
//     holds — including every `is_int` integrality requirement and every
//     division guard (`denom(w) != 0`). The verdict is re-verified against the
//     ORIGINAL asserted atoms before SAT is returned.
//   * UNSAT is returned only in the unambiguous cases: a constant `is_int` that
//     is false; a forced point that fails some atom; or a single positive
//     non-constant `is_int(a*x+c)` whose value-range over a BOUNDED feasible
//     interval contains NO integer (and there are no negated `is_int` atoms).
//   * Anything outside the fragment, or any uncertainty, => Unknown, and the
//     caller falls through to the existing paths unchanged (never a wrong
//     verdict).
//
// SOUNDNESS of `(/ e e) -> 1`: `e/e = 1` is valid ONLY when `e != 0` (the SMT
// theory leaves `0/0` underspecified). We simplify only when `e` is a nonzero
// rational constant, or `e` is the variable form `a*x+b` proven nonzero over
// the whole feasible interval (the interval excludes the root `x = -b/a`). If
// nonzero-ness cannot be established we do NOT simplify and the whole procedure
// returns Unknown for that atom — never a wrong answer.
// ============================================================================

/// A linear (degree <= 1) form `slope * x + intercept` over the single decision
/// variable, or a pure constant when `slope == 0`.
#[derive(Clone, Debug)]
struct Affine {
    slope: BigRational,
    intercept: BigRational,
}

impl Affine {
    pub(crate) fn constant(c: BigRational) -> Self {
        Self {
            slope: BigRational::zero(),
            intercept: c,
        }
    }

    fn eval(&self, x: &BigRational) -> BigRational {
        &self.slope * x + &self.intercept
    }

    fn is_constant(&self) -> bool {
        self.slope.is_zero()
    }
}

/// A division-guard obligation: the term `denom` must be nonzero at the witness.
#[derive(Clone, Debug)]
struct DivGuard {
    denom: TermId,
}

/// One classified `is_int` atom: `is_int(form)` required to equal `polarity`.
#[derive(Clone, Debug)]
struct IsIntReq {
    form: Affine,
    /// `true`: the integer-ness must HOLD; `false`: it must FAIL (`not is_int`).
    polarity: bool,
}

/// A half-line / point constraint on the decision variable from a linear
/// comparison atom.
#[derive(Clone, Debug)]
enum LinAtom {
    /// `x` lies on the side of `bound` given by `rel` (a one-sided bound).
    Bound { rel: Rel, bound: BigRational },
    /// `x == point`.
    Eq(BigRational),
    /// `x != point`.
    Ne(BigRational),
    /// Constraint with no variable; already evaluated to this truth value.
    Const(bool),
}

/// Result of reducing the whole assertion set to the `is_int` fragment.
struct IsIntProblem {
    var: Option<TermId>,
    lin_atoms: Vec<LinAtom>,
    is_int_reqs: Vec<IsIntReq>,
    guards: Vec<DivGuard>,
}

impl NraSolver<'_> {
    /// Attempt to decide the current assertion set with the exact `is_int`
    /// procedure. Returns [`UniResult::Unknown`] for anything outside the
    /// supported affine/univariate `is_int` fragment, or whenever a verdict
    /// cannot be confirmed by exact substitution. Sound and fail-closed.
    pub(crate) fn try_is_int_decide(&self) -> UniResult {
        let problem = match self.collect_is_int_problem() {
            Some(p) => p,
            None => return UniResult::Unknown,
        };

        // Only run when there is at least one `is_int` requirement — otherwise
        // this fragment has nothing to add over the existing paths.
        if problem.is_int_reqs.is_empty() {
            return UniResult::Unknown;
        }

        // Resolve constant (variable-free) constraints up front.
        let mut lo: Option<(BigRational, bool)> = None; // (value, inclusive)
        let mut hi: Option<(BigRational, bool)> = None;
        let mut excluded: Vec<BigRational> = Vec::new();
        let mut forced: Option<BigRational> = None;

        for atom in &problem.lin_atoms {
            match atom {
                LinAtom::Const(true) => {}
                LinAtom::Const(false) => return UniResult::Unsat,
                LinAtom::Eq(p) => {
                    if let Some(prev) = &forced {
                        if prev != p {
                            return UniResult::Unsat; // x = p and x = prev, p != prev
                        }
                    } else {
                        forced = Some(p.clone());
                    }
                }
                LinAtom::Ne(p) => excluded.push(p.clone()),
                LinAtom::Bound { rel, bound } => {
                    update_interval(&mut lo, &mut hi, *rel, bound);
                }
            }
        }

        // If a comparison fixed `x`, decide by exact substitution at that point.
        if let Some(point) = forced {
            return self.decide_is_int_at_point(&problem, &point);
        }

        // No variable at all (all `is_int` forms constant): decide directly.
        if problem.var.is_none() {
            // Any rational works for `x`; use 0. All forms are constant.
            let zero = BigRational::zero();
            return self.decide_is_int_at_point(&problem, &zero);
        }

        // Check the interval is non-degenerate; an empty interval => UNSAT.
        if let (Some((l, li)), Some((h, hi_inc))) = (&lo, &hi) {
            match l.cmp(h) {
                std::cmp::Ordering::Greater => return UniResult::Unsat,
                std::cmp::Ordering::Equal => {
                    if *li && *hi_inc {
                        // Single feasible point [l, l]; decide there.
                        let p = l.clone();
                        if excluded.contains(&p) {
                            return UniResult::Unsat;
                        }
                        return self.decide_is_int_at_point(&problem, &p);
                    }
                    // (l, l) / [l, l) / (l, l] are all empty.
                    return UniResult::Unsat;
                }
                std::cmp::Ordering::Less => {}
            }
        }

        self.decide_is_int_on_interval(&problem, &lo, &hi, &excluded)
    }

    /// Decide the problem at a single fixed rational point `x = point`, by exact
    /// substitution into every asserted atom (comparisons, `is_int`, guards).
    fn decide_is_int_at_point(&self, problem: &IsIntProblem, point: &BigRational) -> UniResult {
        let model = match problem.var {
            Some(v) => vec![(v, point.clone())],
            None => Vec::new(),
        };
        // Guards must hold (denominator nonzero) for the substitution to be
        // meaningful; a zero denominator at the point means `e/e` is `0/0`,
        // which we never simplified soundly — bail to Unknown.
        for g in &problem.guards {
            match self.eval_term_under_model(g.denom, &model) {
                Some(d) if !d.is_zero() => {}
                Some(_) => return UniResult::Unknown, // 0/0 at this point: cannot decide
                None => return UniResult::Unknown,
            }
        }
        // Re-verify EVERY original asserted atom by exact substitution.
        match self.verify_is_int_model(&model) {
            Some(true) => UniResult::Sat(model),
            Some(false) => UniResult::Unsat,
            None => UniResult::Unknown,
        }
    }

    /// Decide the problem when `x` ranges over an interval `(lo, hi)`.
    fn decide_is_int_on_interval(
        &self,
        problem: &IsIntProblem,
        lo: &Option<(BigRational, bool)>,
        hi: &Option<(BigRational, bool)>,
        excluded: &[BigRational],
    ) -> UniResult {
        // Reject constant positive `is_int` forms that are false, and split the
        // requirements into non-constant positive / negative forms.
        let mut pos_forms: Vec<Affine> = Vec::new();
        let mut has_negative = false;
        for req in &problem.is_int_reqs {
            if req.form.is_constant() {
                let is_int = req.form.intercept.is_integer();
                if is_int != req.polarity {
                    return UniResult::Unsat;
                }
                continue;
            }
            if req.polarity {
                pos_forms.push(req.form.clone());
            } else {
                has_negative = true;
            }
        }

        // Candidate witness search. We try witnesses derived from each positive
        // non-constant form (integer values of `a*x + c`), plus a few generic
        // interior points for the negative-only / no-positive case. Every
        // candidate is fully re-verified by exact substitution, so the search is
        // sound regardless of which heuristics produce the candidates.
        let candidates = self.is_int_witness_candidates(&pos_forms, lo, hi, excluded);
        for w in &candidates {
            if !point_in_interval(w, lo, hi) || excluded.iter().any(|e| e == w) {
                continue;
            }
            match self.decide_is_int_at_point(problem, w) {
                UniResult::Sat(m) => return UniResult::Sat(m),
                // A point that fails is not a global UNSAT; keep searching.
                // `decide_is_int_at_point` decides a fixed RATIONAL point, so it
                // never yields an algebraic certificate; the arm is inert here.
                UniResult::SatAlgebraic(_) | UniResult::Unsat | UniResult::Unknown => {}
            }
        }

        // No witness verified. We may only declare UNSAT in the unambiguous
        // case: exactly one positive non-constant form, no negative forms, and a
        // BOUNDED feasible interval whose value-range under the form contains no
        // integer (so `is_int` is impossible). Otherwise Unknown (sound).
        if !has_negative && pos_forms.len() == 1 {
            let form = &pos_forms[0];
            if let (Some((l, l_inc)), Some((h, h_inc))) = (lo, hi) {
                // Map the x-interval to the y = a*x + c interval, accounting for
                // the sign of the slope (which may flip endpoint roles).
                let yl = form.eval(l);
                let yh = form.eval(h);
                let (ymin, ymin_inc, ymax, ymax_inc) = if form.slope.is_positive() {
                    (yl, *l_inc, yh, *h_inc)
                } else {
                    (yh, *h_inc, yl, *l_inc)
                };
                if !interval_contains_integer(&ymin, ymin_inc, &ymax, ymax_inc) {
                    return UniResult::Unsat;
                }
            }
        }

        UniResult::Unknown
    }

    /// Generate candidate witnesses for the interval search.
    fn is_int_witness_candidates(
        &self,
        pos_forms: &[Affine],
        lo: &Option<(BigRational, bool)>,
        hi: &Option<(BigRational, bool)>,
        excluded: &[BigRational],
    ) -> Vec<BigRational> {
        let mut out: Vec<BigRational> = Vec::new();

        // For each positive non-constant form `a*x + c`, the values of x that
        // make it an integer are x = (k - c)/a for integer k. Enumerate the
        // integers k whose pre-image lies in the feasible interval.
        for form in pos_forms {
            // The form's value-range over the feasible interval.
            let yl = lo.as_ref().map(|(l, _)| form.eval(l));
            let yh = hi.as_ref().map(|(h, _)| form.eval(h));
            let (ymin, ymax) = if form.slope.is_positive() {
                (yl, yh)
            } else {
                (yh, yl)
            };
            // Determine the integer scan range. If unbounded on a side, scan a
            // bounded window around the available bound (a single integer
            // witness suffices for SAT, and an unbounded side always admits one
            // — the verification gate keeps us honest).
            let k_lo = match &ymin {
                Some(v) => v.ceil().to_integer(),
                None => match &ymax {
                    Some(v) => v.floor().to_integer() - BigInt::from(2),
                    None => BigInt::from(-2),
                },
            };
            let k_hi = match &ymax {
                Some(v) => v.floor().to_integer(),
                None => &k_lo + BigInt::from(4),
            };
            // Cap the scan to a sane window to avoid pathological enumeration.
            let span = &k_hi - &k_lo;
            let capped_hi = if span > BigInt::from(1024) {
                &k_lo + BigInt::from(1024)
            } else {
                k_hi.clone()
            };
            let mut k = k_lo.clone();
            while k <= capped_hi {
                // x = (k - c) / a
                let kr = BigRational::from_integer(k.clone());
                let x = (&kr - &form.intercept) / &form.slope;
                out.push(x);
                k += BigInt::from(1);
            }
        }

        // Generic interior samples (useful when only negated `is_int` atoms are
        // present, or to perturb away from excluded points). These are filtered
        // and re-verified by the caller.
        if let Some(mid) = interval_sample(lo, hi, excluded) {
            out.push(mid);
        }

        out
    }

    /// Reduce the whole assertion set into the `is_int` fragment, or `None` if
    /// any atom is outside it (non-linear comparison, multivariate coupling,
    /// unsupported operator, unguarded division, ...).
    fn collect_is_int_problem(&self) -> Option<IsIntProblem> {
        let mut var: Option<TermId> = None;
        let mut lin_atoms: Vec<LinAtom> = Vec::new();
        let mut is_int_reqs: Vec<IsIntReq> = Vec::new();
        let mut guards: Vec<DivGuard> = Vec::new();

        let mut note_var = |v: TermId, var: &mut Option<TermId>| -> bool {
            match var {
                None => {
                    *var = Some(v);
                    true
                }
                Some(existing) => *existing == v,
            }
        };

        for &(atom, value) in &self.asserted {
            // `is_int(E)` atom?
            if let Some(inner) = self.as_is_int_app(atom) {
                let (form, v, mut g) = self.term_to_affine_guarded(inner)?;
                if let Some(fv) = v {
                    if !note_var(fv, &mut var) {
                        return None;
                    }
                }
                guards.append(&mut g);
                is_int_reqs.push(IsIntReq {
                    form,
                    polarity: value,
                });
                continue;
            }

            // Otherwise it must be a linear comparison atom in the fragment.
            let lin = self.comparison_to_linatom(atom, value, &mut var, &mut note_var)?;
            lin_atoms.push(lin);
        }

        Some(IsIntProblem {
            var,
            lin_atoms,
            is_int_reqs,
            guards,
        })
    }

    /// If `atom` is `(is_int E)`, return `E`.
    fn as_is_int_app(&self, atom: TermId) -> Option<TermId> {
        match self.terms.get(atom) {
            TermData::App(Symbol::Named(name), args)
                if name.as_str() == "is_int" && args.len() == 1 =>
            {
                Some(args[0])
            }
            _ => None,
        }
    }

    /// Convert a comparison atom (under polarity `value`) into a [`LinAtom`],
    /// requiring it to be linear over the single shared variable. Returns `None`
    /// if the atom is not a linear comparison in the fragment.
    fn comparison_to_linatom(
        &self,
        atom: TermId,
        value: bool,
        var: &mut Option<TermId>,
        note_var: &mut impl FnMut(TermId, &mut Option<TermId>) -> bool,
    ) -> Option<LinAtom> {
        let (rel0, lhs, rhs) = self.comparison_parts(atom)?;
        let rel = if value { rel0 } else { negate_rel(rel0) };

        // Reduce both sides to affine forms (division-guarded). Comparisons must
        // stay linear for this fragment.
        let (lhs_aff, lv, lg) = self.term_to_affine_guarded(lhs)?;
        let (rhs_aff, rv, rg) = self.term_to_affine_guarded(rhs)?;
        // Comparisons carrying their own division guards are out of this simple
        // fragment (we do not track per-atom guards for comparisons); bail. The
        // `is_int`-bearing atoms keep their guards; only the comparison path is
        // restricted to guard-free linear forms.
        if !lg.is_empty() || !rg.is_empty() {
            return None;
        }
        // Merge variable identity.
        for v in [lv, rv].into_iter().flatten() {
            if !note_var(v, var) {
                return None;
            }
        }
        // diff = lhs - rhs = (sl - sr) x + (il - ir). Constraint: diff REL 0.
        let slope = &lhs_aff.slope - &rhs_aff.slope;
        let intercept = &lhs_aff.intercept - &rhs_aff.intercept;

        if slope.is_zero() {
            // Constant comparison.
            let sign = rational_sign(&intercept);
            return Some(LinAtom::Const(rel.holds_for_sign(sign)));
        }

        // Solve `slope * x + intercept REL 0` for x: x REL' (-intercept/slope),
        // where REL' is mirrored when slope < 0.
        let root = -(&intercept) / &slope;
        let rel_for_x = if slope.is_positive() {
            rel
        } else {
            mirror_rel(rel)
        };
        Some(match rel_for_x {
            Rel::Eq => LinAtom::Eq(root),
            Rel::Ne => LinAtom::Ne(root),
            r => LinAtom::Bound {
                rel: r,
                bound: root,
            },
        })
    }

    /// Reduce a real term to an affine form `slope * x + intercept` over at most
    /// one variable, performing the SOUND division-by-self simplification and
    /// constant-denominator division. Returns the affine form, the (optional)
    /// variable, and any division-guard obligations. `None` if the term is
    /// outside the affine/division fragment.
    fn term_to_affine_guarded(
        &self,
        term: TermId,
    ) -> Option<(Affine, Option<TermId>, Vec<DivGuard>)> {
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => Some((
                Affine::constant(BigRational::from_integer(n.clone())),
                None,
                Vec::new(),
            )),
            TermData::Const(Constant::Rational(r)) => {
                Some((Affine::constant(r.0.clone()), None, Vec::new()))
            }
            TermData::Var(_, _) => Some((
                Affine {
                    slope: BigRational::one(),
                    intercept: BigRational::zero(),
                },
                Some(term),
                Vec::new(),
            )),
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" if !args.is_empty() => {
                    let mut acc = Affine::constant(BigRational::zero());
                    let mut var: Option<TermId> = None;
                    let mut guards = Vec::new();
                    for &a in args {
                        let (aff, v, mut g) = self.term_to_affine_guarded(a)?;
                        acc = affine_add(&acc, &aff);
                        var = merge_opt_var(var, v)?;
                        guards.append(&mut g);
                    }
                    Some((acc, var, guards))
                }
                "-" if args.len() == 1 => {
                    let (aff, v, g) = self.term_to_affine_guarded(args[0])?;
                    Some((affine_neg(&aff), v, g))
                }
                "-" if args.len() >= 2 => {
                    let (mut acc, mut var, mut guards) = self.term_to_affine_guarded(args[0])?;
                    for &a in &args[1..] {
                        let (aff, v, mut g) = self.term_to_affine_guarded(a)?;
                        acc = affine_add(&acc, &affine_neg(&aff));
                        var = merge_opt_var(var, v)?;
                        guards.append(&mut g);
                    }
                    Some((acc, var, guards))
                }
                "*" if !args.is_empty() => {
                    // Stay affine: at most one non-constant factor.
                    let mut coeff = Affine::constant(BigRational::one());
                    let mut var_factor: Option<(Affine, Option<TermId>)> = None;
                    let mut guards = Vec::new();
                    for &a in args {
                        let (aff, v, mut g) = self.term_to_affine_guarded(a)?;
                        guards.append(&mut g);
                        if aff.is_constant() && v.is_none() {
                            coeff = affine_mul_const(&coeff, &aff.intercept);
                        } else if var_factor.is_none() {
                            var_factor = Some((aff, v));
                        } else {
                            // Two non-constant factors => nonlinear; out.
                            return None;
                        }
                    }
                    match var_factor {
                        None => Some((coeff, None, guards)),
                        Some((aff, v)) => {
                            // coeff is constant here (a constant Affine).
                            let scaled = affine_mul_const(&aff, &coeff.intercept);
                            Some((scaled, v, guards))
                        }
                    }
                }
                "/" if args.len() == 2 => self.div_to_affine_guarded(args[0], args[1]),
                _ => None,
            },
            _ => None,
        }
    }

    /// Reduce `(/ num denom)` to an affine form when SOUND:
    ///   * `denom` is a nonzero rational constant `d`: result = num_affine / d.
    ///   * `num` and `denom` reduce to the SAME affine form `e` (provably
    ///     nonzero, recorded as a guard): result = 1.
    /// Otherwise `None` (out of fragment / not provably nonzero).
    fn div_to_affine_guarded(
        &self,
        num: TermId,
        denom: TermId,
    ) -> Option<(Affine, Option<TermId>, Vec<DivGuard>)> {
        let (num_aff, num_v, mut num_g) = self.term_to_affine_guarded(num)?;
        let (den_aff, den_v, mut den_g) = self.term_to_affine_guarded(denom)?;

        // Case 1: constant nonzero denominator.
        if den_aff.is_constant() && den_v.is_none() {
            if den_aff.intercept.is_zero() {
                return None; // division by zero: never simplify
            }
            let inv = BigRational::one() / &den_aff.intercept;
            let result = affine_mul_const(&num_aff, &inv);
            let mut guards = Vec::new();
            guards.append(&mut num_g);
            guards.append(&mut den_g);
            return Some((result, num_v, guards));
        }

        // Case 2: e / e -> 1, when numerator and denominator are the SAME affine
        // form over the SAME variable AND that form is PROVABLY nonzero. We
        // record the divisor as a guard so the witness check confirms `e != 0`
        // (the per-point guard check rejects any witness where the denominator
        // is zero, keeping `0/0` out). Soundness is enforced at the witness:
        // SAT is only emitted when the guard holds at the verified point.
        // clippy::suspicious_operation_groupings false positive: its suggested
        // `num_v.is_constant()` does not type-check (`num_v` is an `Option`, not an
        // affine form). The `&& num_v.is_none()` clause is intentional.
        #[allow(clippy::suspicious_operation_groupings)]
        let same_form = num_v == den_v
            && num_aff.slope == den_aff.slope
            && num_aff.intercept == den_aff.intercept
            && !(num_aff.is_constant() && num_v.is_none());
        if same_form {
            let mut guards = Vec::new();
            guards.append(&mut num_g);
            guards.append(&mut den_g);
            guards.push(DivGuard { denom });
            return Some((Affine::constant(BigRational::one()), None, guards));
        }

        None
    }

    /// Re-verify a candidate model against EVERY original asserted atom by exact
    /// substitution, including `is_int` integrality and division guards. Returns
    /// `Some(true)` if all confirm, `Some(false)` if some atom is exactly
    /// refuted, `None` if any atom cannot be evaluated exactly.
    fn verify_is_int_model(&self, model: &[(TermId, BigRational)]) -> Option<bool> {
        let mut all_true = true;
        for &(atom, value) in &self.asserted {
            let truth = self.eval_is_int_atom_under_model(atom, model)?;
            if truth != value {
                all_true = false;
            }
        }
        Some(all_true)
    }

    /// Evaluate an atom (comparison or `is_int`) under the model, exactly.
    fn eval_is_int_atom_under_model(
        &self,
        atom: TermId,
        model: &[(TermId, BigRational)],
    ) -> Option<bool> {
        if let Some(inner) = self.as_is_int_app(atom) {
            let v = self.eval_real_term_with_div(inner, model)?;
            return Some(v.is_integer());
        }
        // Comparison atom.
        let (rel, lhs, rhs) = self.comparison_parts(atom)?;
        let lv = self.eval_real_term_with_div(lhs, model)?;
        let rv = self.eval_real_term_with_div(rhs, model)?;
        let sign = rational_sign(&(&lv - &rv));
        Some(rel.holds_for_sign(sign))
    }

    /// Evaluate a real term to an exact rational under the model, supporting
    /// `+ - *` and `/` (division). Returns `None` if any variable is missing, an
    /// unsupported operator appears, or a division by zero is encountered (a
    /// zero denominator makes the value undefined — fail closed).
    fn eval_real_term_with_div(
        &self,
        term: TermId,
        model: &[(TermId, BigRational)],
    ) -> Option<BigRational> {
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
            TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
            TermData::Var(_, _) => model
                .iter()
                .find(|(v, _)| *v == term)
                .map(|(_, val)| val.clone()),
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" if !args.is_empty() => {
                    let mut acc = BigRational::zero();
                    for &a in args {
                        acc += self.eval_real_term_with_div(a, model)?;
                    }
                    Some(acc)
                }
                "*" if !args.is_empty() => {
                    let mut acc = BigRational::one();
                    for &a in args {
                        acc *= self.eval_real_term_with_div(a, model)?;
                    }
                    Some(acc)
                }
                "-" if args.len() == 1 => Some(-self.eval_real_term_with_div(args[0], model)?),
                "-" if args.len() >= 2 => {
                    let mut acc = self.eval_real_term_with_div(args[0], model)?;
                    for &a in &args[1..] {
                        acc -= self.eval_real_term_with_div(a, model)?;
                    }
                    Some(acc)
                }
                "/" if args.len() == 2 => {
                    let n = self.eval_real_term_with_div(args[0], model)?;
                    let d = self.eval_real_term_with_div(args[1], model)?;
                    if d.is_zero() {
                        // Undefined (0/0 or x/0): fail closed.
                        return None;
                    }
                    Some(n / d)
                }
                _ => None,
            },
            _ => None,
        }
    }
}

/// Add two affine forms. (Both must be over the same variable; the slopes add.)
fn affine_add(a: &Affine, b: &Affine) -> Affine {
    Affine {
        slope: &a.slope + &b.slope,
        intercept: &a.intercept + &b.intercept,
    }
}

/// Negate an affine form.
fn affine_neg(a: &Affine) -> Affine {
    Affine {
        slope: -(&a.slope),
        intercept: -(&a.intercept),
    }
}

/// Scale an affine form by a rational constant.
fn affine_mul_const(a: &Affine, c: &BigRational) -> Affine {
    Affine {
        slope: &a.slope * c,
        intercept: &a.intercept * c,
    }
}

/// Merge two optional variable identities, failing (`None`) if they are two
/// DISTINCT variables. Mirrors [`merge_var`] but returns the merged identity in
/// a single `Option` (failure is encoded by the function returning `None`).
fn merge_opt_var(a: Option<TermId>, b: Option<TermId>) -> Option<Option<TermId>> {
    match (a, b) {
        (None, None) => Some(None),
        (Some(v), None) | (None, Some(v)) => Some(Some(v)),
        (Some(x), Some(y)) if x == y => Some(Some(x)),
        (Some(_), Some(_)) => None,
    }
}

/// Mirror a relation (used when dividing an inequality by a negative slope).
fn mirror_rel(rel: Rel) -> Rel {
    match rel {
        Rel::Lt => Rel::Gt,
        Rel::Le => Rel::Ge,
        Rel::Gt => Rel::Lt,
        Rel::Ge => Rel::Le,
        Rel::Eq => Rel::Eq,
        Rel::Ne => Rel::Ne,
    }
}

/// Tighten `(lo, hi)` with a one-sided bound `x REL bound`.
fn update_interval(
    lo: &mut Option<(BigRational, bool)>,
    hi: &mut Option<(BigRational, bool)>,
    rel: Rel,
    bound: &BigRational,
) {
    match rel {
        Rel::Gt | Rel::Ge => {
            let inclusive = matches!(rel, Rel::Ge);
            let tighter = match lo {
                None => true,
                Some((cur, cur_inc)) => bound > cur || (bound == cur && !inclusive && *cur_inc),
            };
            if tighter {
                *lo = Some((bound.clone(), inclusive));
            }
        }
        Rel::Lt | Rel::Le => {
            let inclusive = matches!(rel, Rel::Le);
            let tighter = match hi {
                None => true,
                Some((cur, cur_inc)) => bound < cur || (bound == cur && !inclusive && *cur_inc),
            };
            if tighter {
                *hi = Some((bound.clone(), inclusive));
            }
        }
        Rel::Eq | Rel::Ne => {
            // Handled by the caller as LinAtom::Eq / LinAtom::Ne.
        }
    }
}

/// Is `x` inside the (possibly open / half-bounded) interval?
fn point_in_interval(
    x: &BigRational,
    lo: &Option<(BigRational, bool)>,
    hi: &Option<(BigRational, bool)>,
) -> bool {
    if let Some((l, inc)) = lo {
        if *inc {
            if x < l {
                return false;
            }
        } else if x <= l {
            return false;
        }
    }
    if let Some((h, inc)) = hi {
        if *inc {
            if x > h {
                return false;
            }
        } else if x >= h {
            return false;
        }
    }
    true
}

/// Does the closed/open value-interval `[ymin, ymax]` contain an integer?
/// `*_inc` flags mark whether the corresponding endpoint is included.
fn interval_contains_integer(
    ymin: &BigRational,
    ymin_inc: bool,
    ymax: &BigRational,
    ymax_inc: bool,
) -> bool {
    // Smallest integer >= ymin (respecting inclusivity at the lower end).
    let mut k = ymin.ceil().to_integer();
    if !ymin_inc && BigRational::from_integer(k.clone()) == *ymin {
        // ymin itself excluded; the next integer up is the candidate.
        k += BigInt::from(1);
    }
    let kr = BigRational::from_integer(k);
    if ymax_inc {
        kr <= *ymax
    } else {
        kr < *ymax
    }
}

/// Pick a rational interior sample of `(lo, hi)` avoiding the excluded points,
/// or `None` if no clearly-interior rational is available.
fn interval_sample(
    lo: &Option<(BigRational, bool)>,
    hi: &Option<(BigRational, bool)>,
    excluded: &[BigRational],
) -> Option<BigRational> {
    let two = BigRational::from_integer(BigInt::from(2));
    let base = match (lo, hi) {
        (Some((l, _)), Some((h, _))) => (l + h) / &two,
        (Some((l, _)), None) => l + BigRational::one(),
        (None, Some((h, _))) => h - BigRational::one(),
        (None, None) => BigRational::zero(),
    };
    // Choose a perturbation anchor strictly toward the interior so that nudging
    // the candidate moves it OFF excluded points / endpoints (rather than back
    // to `base`). The step direction is toward the lower endpoint if present,
    // else toward the upper endpoint, else +1.
    let anchor = match (lo, hi) {
        (Some((l, _)), _) => l.clone(),
        (None, Some((h, _))) => h.clone(),
        (None, None) => &base - BigRational::one(),
    };
    let mut cand = base;
    for _ in 0..16 {
        let on_excluded = excluded.contains(&cand);
        if point_in_interval(&cand, lo, hi) && !on_excluded {
            return Some(cand);
        }
        // Move the candidate halfway toward the anchor (a feasible-interior
        // direction), which always changes its value and stays inside the
        // interval when the anchor is an endpoint.
        cand = (&cand + &anchor) / &two;
    }
    None
}

// ============================================================================
// Multivariate linear-equality substitution (multivariate subclass).
//
// Many multivariate QF_NRA problems become decidable once a *linear* equality
// `xi = (linear expr in other vars)` eliminates a variable, reducing the
// remaining system to a single variable that the exact univariate decider above
// already settles. This section adds that substitution phase. Everything is
// exact [`BigRational`]; the verdict is fail-closed in exactly the same way as
// the univariate path:
//
//   * SAT only after the FULL assembled model (univariate witness + every
//     back-substituted eliminated variable) is re-verified by exact
//     substitution into EVERY ORIGINAL asserted atom (`verify_model`).
//   * UNSAT only when the substituted univariate system is genuinely UNSAT
//     (an equality `xi = e` forces `xi = e` in every model, so substitution is
//     satisfiability-preserving — see module-level reasoning below).
//   * Anything uncertain (cycle, irrational substitution value, remaining
//     cross-variable coupling, unsupported op) => Unknown, and the caller falls
//     through to the existing univariate / tangent paths unchanged.
// ============================================================================

/// A sparse multivariate polynomial over the rationals. Each entry maps a
/// *monomial* — a sorted multiset of variables represented as a sorted
/// `Vec<TermId>` (with repetition for powers, e.g. `[x, x]` is `x^2`) — to a
/// non-zero rational coefficient. The empty monomial `[]` is the constant term.
#[derive(Clone, Debug)]
pub(crate) struct MultiPoly {
    /// Invariant: every stored coefficient is non-zero; monomials are sorted.
    pub(crate) terms: Vec<(Vec<TermId>, BigRational)>,
}

impl MultiPoly {
    pub(crate) fn zero() -> Self {
        Self { terms: Vec::new() }
    }

    pub(crate) fn constant(c: BigRational) -> Self {
        if c.is_zero() {
            Self::zero()
        } else {
            Self {
                terms: vec![(Vec::new(), c)],
            }
        }
    }

    /// The degree-1 monomial for a single variable.
    fn var(v: TermId) -> Self {
        Self {
            terms: vec![(vec![v], BigRational::one())],
        }
    }

    /// Find the coefficient of a (sorted) monomial, or zero.
    fn coeff_index(&self, mono: &[TermId]) -> Option<usize> {
        self.terms.iter().position(|(m, _)| m.as_slice() == mono)
    }

    /// Add `coeff * mono` into the polynomial, preserving the non-zero invariant.
    pub(crate) fn add_term(&mut self, mono: Vec<TermId>, coeff: BigRational) {
        if coeff.is_zero() {
            return;
        }
        match self.coeff_index(&mono) {
            Some(i) => {
                self.terms[i].1 += coeff;
                if self.terms[i].1.is_zero() {
                    self.terms.remove(i);
                }
            }
            None => self.terms.push((mono, coeff)),
        }
    }

    pub(crate) fn add(&self, other: &Self) -> Self {
        let mut out = self.clone();
        for (m, c) in &other.terms {
            out.add_term(m.clone(), c.clone());
        }
        out
    }

    pub(crate) fn neg(&self) -> Self {
        Self {
            terms: self.terms.iter().map(|(m, c)| (m.clone(), -c)).collect(),
        }
    }

    pub(crate) fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    pub(crate) fn mul(&self, other: &Self) -> Self {
        let mut out = Self::zero();
        for (ma, ca) in &self.terms {
            for (mb, cb) in &other.terms {
                let mut mono = ma.clone();
                mono.extend_from_slice(mb);
                mono.sort_unstable();
                out.add_term(mono, ca * cb);
            }
        }
        out
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// The set of distinct variables appearing in any monomial.
    pub(crate) fn variables(&self) -> Vec<TermId> {
        let mut vars: Vec<TermId> = Vec::new();
        for (m, _) in &self.terms {
            for &v in m {
                if !vars.contains(&v) {
                    vars.push(v);
                }
            }
        }
        vars
    }

    /// If the polynomial is purely linear (every monomial has degree <= 1),
    /// return `(constant, [(var, coeff), ...])`; otherwise `None`.
    pub(crate) fn as_linear(&self) -> Option<(BigRational, Vec<(TermId, BigRational)>)> {
        let mut constant = BigRational::zero();
        let mut linear: Vec<(TermId, BigRational)> = Vec::new();
        for (m, c) in &self.terms {
            match m.len() {
                0 => constant += c,
                1 => linear.push((m[0], c.clone())),
                _ => return None,
            }
        }
        Some((constant, linear))
    }

    /// Substitute `var := replacement` (a linear expression `LinExpr`) into the
    /// polynomial, returning a fresh `MultiPoly`. Each occurrence of `var` in
    /// every monomial is replaced by the linear expression and the products are
    /// expanded exactly. Monomials not mentioning `var` are copied unchanged.
    pub(crate) fn substitute(&self, var: TermId, replacement: &LinExpr) -> Self {
        let repl_poly = replacement.to_multipoly();
        let mut out = Self::zero();
        for (mono, coeff) in &self.terms {
            // Split the monomial into the power of `var` and the rest.
            let mut rest: Vec<TermId> = Vec::new();
            let mut power = 0usize;
            for &v in mono {
                if v == var {
                    power += 1;
                } else {
                    rest.push(v);
                }
            }
            if power == 0 {
                out.add_term(mono.clone(), coeff.clone());
                continue;
            }
            // term = coeff * (rest monomial) * replacement^power.
            let mut acc = Self {
                terms: vec![(rest, coeff.clone())],
            };
            for _ in 0..power {
                acc = acc.mul(&repl_poly);
            }
            out = out.add(&acc);
        }
        out
    }

    /// Lower a polynomial that mentions at most ONE variable to a dense
    /// [`UniPoly`] in that variable. Returns `None` if it mentions two or more
    /// distinct variables (not univariate). A constant polynomial lowers to a
    /// constant `UniPoly` (the caller supplies the variable identity separately
    /// when needed); here we only need the polynomial shape.
    pub(crate) fn to_unipoly(&self) -> Option<UniPoly> {
        let vars = self.variables();
        if vars.len() > 1 {
            return None;
        }
        // Highest power = degree.
        let mut deg = 0usize;
        for (m, _) in &self.terms {
            deg = deg.max(m.len());
        }
        let mut coeffs = vec![BigRational::zero(); deg + 1];
        for (m, c) in &self.terms {
            // All entries in `m` are the same single variable (len == power).
            coeffs[m.len()] += c;
        }
        let mut p = UniPoly { coeffs };
        p.normalize();
        Some(p)
    }
}

/// A linear expression `const + sum(coeff_i * var_i)` over exact rationals.
/// Used to represent the value an eliminated variable is fixed to by a linear
/// equality (e.g. `y = 2*x + 1`).
#[derive(Clone, Debug)]
pub(crate) struct LinExpr {
    pub(crate) constant: BigRational,
    pub(crate) terms: Vec<(TermId, BigRational)>,
}

impl LinExpr {
    fn to_multipoly(&self) -> MultiPoly {
        let mut p = MultiPoly::constant(self.constant.clone());
        for (v, c) in &self.terms {
            p.add_term(vec![*v], c.clone());
        }
        p
    }

    /// Variables referenced by this linear expression.
    pub(crate) fn variables(&self) -> Vec<TermId> {
        self.terms.iter().map(|(v, _)| *v).collect()
    }

    /// Substitute `var := replacement` into this linear expression. Both are
    /// linear, so the result stays linear (used to resolve substitution chains
    /// to a fixpoint).
    fn substitute(&self, var: TermId, replacement: &Self) -> Self {
        let mut out = Self {
            constant: self.constant.clone(),
            terms: Vec::new(),
        };
        for (v, c) in &self.terms {
            if *v == var {
                // Replace c*var with c*(replacement).
                out.constant += c * &replacement.constant;
                for (rv, rc) in &replacement.terms {
                    add_linear_term(&mut out.terms, *rv, c * rc);
                }
            } else {
                add_linear_term(&mut out.terms, *v, c.clone());
            }
        }
        out
    }
}

/// Add `coeff * var` into a linear-term list, combining like terms and dropping
/// zero coefficients.
fn add_linear_term(terms: &mut Vec<(TermId, BigRational)>, var: TermId, coeff: BigRational) {
    if coeff.is_zero() {
        return;
    }
    if let Some(slot) = terms.iter_mut().find(|(v, _)| *v == var) {
        slot.1 += coeff;
        if slot.1.is_zero() {
            terms.retain(|(_, c)| !c.is_zero());
        }
    } else {
        terms.push((var, coeff));
    }
}

/// A multivariate constraint reduced to `poly REL 0`.
#[derive(Clone, Debug)]
pub(crate) struct MultiConstraint {
    pub(crate) poly: MultiPoly,
    pub(crate) rel: Rel,
}

impl NraSolver<'_> {
    /// Attempt to decide the current assertion set via LINEAR-EQUALITY
    /// SUBSTITUTION followed by the exact univariate decider. Returns
    /// [`UniResult::Unknown`] whenever anything is outside the supported
    /// fragment or cannot be confirmed exactly.
    ///
    /// This NEVER produces a wrong verdict: SAT is gated by re-verification of
    /// the FULL model against every original atom; UNSAT only propagates a
    /// genuine univariate UNSAT through a satisfiability-preserving
    /// substitution; everything else is Unknown.
    pub(crate) fn try_linear_substitution_decide(&self) -> UniResult {
        // 1. Convert every asserted atom to a multivariate `poly REL 0`.
        let mut constraints: Vec<MultiConstraint> = Vec::new();
        for &(atom, value) in &self.asserted {
            match self.atom_to_multi(atom, value) {
                Some(MultiAtom::ConstFalse) => return UniResult::Unsat,
                Some(MultiAtom::ConstTrue) => {}
                Some(MultiAtom::Constraint(c)) => constraints.push(c),
                // Unsupported atom shape => out of fragment.
                None => return UniResult::Unknown,
            }
        }

        // 2. Extract linear equalities `var = (linear expr)` to build a
        //    substitution map. We only treat an equality atom (Rel::Eq, asserted
        //    true) as an elimination if, after moving everything to one side,
        //    the polynomial is linear and some variable has a non-zero
        //    coefficient we can solve for.
        let mut subst: Vec<(TermId, LinExpr)> = Vec::new();
        for c in &constraints {
            if c.rel != Rel::Eq {
                continue;
            }
            let Some((constant, linear)) = c.poly.as_linear() else {
                continue; // nonlinear equality (e.g. y = x^2) — not an elimination
            };
            if linear.is_empty() {
                continue; // pure constant equality (handled by ConstTrue/False)
            }
            // Pick an elimination target: a variable not already eliminated.
            // Solve `coeff*var + (rest) + constant = 0` for `var`:
            //   var = -(rest + constant) / coeff.
            let Some((idx, (target, tcoeff))) = linear
                .iter()
                .enumerate()
                .find(|(_, (v, _))| !subst.iter().any(|(s, _)| s == v))
                .map(|(i, vc)| (i, vc.clone()))
            else {
                continue; // every variable here already has a substitution
            };
            let inv = BigRational::one() / &tcoeff;
            let mut expr = LinExpr {
                constant: -(&constant) * &inv,
                terms: Vec::new(),
            };
            for (j, (v, co)) in linear.iter().enumerate() {
                if j == idx {
                    continue;
                }
                add_linear_term(&mut expr.terms, *v, -(co) * &inv);
            }
            subst.push((target, expr));
        }

        if subst.is_empty() {
            // No linear equality to eliminate with — out of this subclass.
            return UniResult::Unknown;
        }

        // 3. Resolve the substitution map to a fixpoint so chains
        //    (z=2; y=z+1; ...) collapse. Detect cycles / non-terminating
        //    resolution and bail to Unknown.
        let resolved = match resolve_substitutions(&subst) {
            Some(r) => r,
            None => return UniResult::Unknown, // cycle or unresolved coupling
        };

        // 4. Apply the resolved substitution to every constraint. After this,
        //    no eliminated variable appears in any constraint polynomial.
        let mut substituted: Vec<MultiConstraint> = Vec::with_capacity(constraints.len());
        for c in &constraints {
            let mut poly = c.poly.clone();
            for (var, expr) in &resolved {
                poly = poly.substitute(*var, expr);
            }
            substituted.push(MultiConstraint { poly, rel: c.rel });
        }

        // 5. Determine the remaining (non-eliminated) variable support across
        //    ALL substituted constraints. We require exactly one remaining
        //    variable for the univariate decider; >= 2 coupled vars => Unknown.
        let mut remaining: Vec<TermId> = Vec::new();
        for c in &substituted {
            for v in c.poly.variables() {
                if !remaining.contains(&v) {
                    remaining.push(v);
                }
            }
        }

        if remaining.len() > 1 {
            // Still coupled across >= 2 variables — out of scope.
            return UniResult::Unknown;
        }

        // 6. Lower the substituted constraints to univariate constraints. With
        //    at most one variable remaining, every constraint polynomial is
        //    univariate (or constant). A constant constraint is checked for
        //    truth directly; a false constant constraint => UNSAT.
        let the_var = remaining.first().copied();
        let mut uni: Vec<UniConstraint> = Vec::new();
        for c in &substituted {
            let Some(poly) = c.poly.to_unipoly() else {
                // Should not happen (remaining.len() <= 1), but stay fail-closed.
                return UniResult::Unknown;
            };
            if poly.degree().is_none() {
                // Zero polynomial: `0 REL 0`.
                if c.rel.holds_for_sign(0) {
                    continue;
                } else {
                    return UniResult::Unsat;
                }
            }
            if the_var.is_none() {
                // Constant constraint with no variable: evaluate its sign.
                let sign = rational_sign(&poly.eval(&BigRational::zero()));
                if c.rel.holds_for_sign(sign) {
                    continue;
                } else {
                    return UniResult::Unsat;
                }
            }
            uni.push(UniConstraint { poly, rel: c.rel });
        }

        let Some(var) = the_var else {
            // No remaining variable and no falsified constant constraint: the
            // substituted system is trivially satisfiable. Recover the model
            // purely from the substitution constants and re-verify.
            return self.assemble_and_verify(var_value_none(), &resolved);
        };

        if uni.is_empty() {
            // The single remaining variable is wholly unconstrained: pick 0 and
            // let the full re-verification confirm the assembled model.
            return self.assemble_and_verify(Some((var, BigRational::zero())), &resolved);
        }

        // 7. Decide the univariate system exactly.
        match decide_single_variable(&uni) {
            SingleVarResult::Witness(w) => self.assemble_and_verify(Some((var, w)), &resolved),
            // UNSAT of the substituted univariate system => UNSAT of the
            // original (substitution is satisfiability-preserving).
            SingleVarResult::Empty => UniResult::Unsat,
            // SAT only at an irrational point. The linear substitution is
            // satisfiability-preserving, and the reduced univariate system was
            // proven SAT over the reals by the exact IVT certificate. The
            // back-substituted variables are linear functions of the (algebraic)
            // primary witness, so their exact values are affine expressions in
            // the algebraic root — assemble the full mixed model and re-verify
            // it exactly before reporting SAT with witnesses.
            SingleVarResult::IrrationalSat(alg) => {
                self.assemble_and_verify_algebraic(var, alg, &uni, &resolved)
            }
            SingleVarResult::Unknown => UniResult::Unknown,
        }
    }

    /// Assemble and exactly re-verify a MIXED model for the linear-substitution
    /// path when the primary witness is algebraic: the primary variable takes
    /// the exact algebraic root; every eliminated variable's value is its
    /// (affine) substitution expression evaluated at that root — an exact
    /// rational or a derived algebraic number. Every substituted constraint is
    /// re-checked by exact Sturm sign determination at the root; any failure
    /// returns Unknown (fail closed).
    fn assemble_and_verify_algebraic(
        &self,
        var: TermId,
        alg: crate::algebraic::RealAlgebraic,
        uni: &[UniConstraint],
        resolved: &[(TermId, LinExpr)],
    ) -> UniResult {
        use crate::algebraic::RealScalar;
        // SOUNDNESS GATE: re-verify every substituted constraint at the root.
        // (The substitution equalities `y_i = expr_i(x)` hold by construction
        // of the assembled model below, so these checks cover the originals.)
        for c in uni {
            match alg.sign_of_poly(&c.poly) {
                Some(s) if c.rel.holds_for_sign(s) => {}
                _ => return UniResult::Unknown,
            }
        }
        let value = alg.as_value();
        let mut witnesses: Vec<(TermId, UniWitness)> =
            vec![(var, UniWitness::Algebraic(value.clone()))];
        for (v, expr) in resolved {
            let mut acc = RealScalar::Rational(expr.constant.clone());
            for (tv, coeff) in &expr.terms {
                if coeff.is_zero() {
                    continue;
                }
                if *tv != var {
                    // Fixpoint-resolved expressions reference only the primary
                    // variable; anything else is out of scope. Fail closed.
                    return UniResult::Unknown;
                }
                let scaled = value.mul_rational(coeff);
                acc = match (acc, scaled) {
                    (RealScalar::Rational(a), RealScalar::Rational(b)) => {
                        RealScalar::Rational(a + b)
                    }
                    (RealScalar::Rational(a), RealScalar::Algebraic(b)) => {
                        RealScalar::Algebraic(b.add_rational(&a))
                    }
                    (RealScalar::Algebraic(a), RealScalar::Rational(b)) => {
                        RealScalar::Algebraic(a.add_rational(&b))
                    }
                    (RealScalar::Algebraic(a), RealScalar::Algebraic(b)) => match a.try_add(&b) {
                        Some(sum) => sum,
                        None => return UniResult::Unknown,
                    },
                };
            }
            match acc {
                RealScalar::Rational(r) => witnesses.push((*v, UniWitness::Rational(r))),
                // Keep the eliminated variable's value as a residue over the
                // SAME algebraic point (triangular assignment): joint atoms
                // over the primary and eliminated variables then evaluate
                // exactly through shared-point arithmetic.
                RealScalar::Algebraic(a) => witnesses.push((*v, UniWitness::Algebraic(a))),
            }
        }
        UniResult::SatAlgebraic(witnesses)
    }

    /// Assemble the full model from the univariate witness (if any) plus the
    /// back-substituted values of every eliminated variable, then re-verify it
    /// against EVERY ORIGINAL asserted atom. Emits SAT only if every original
    /// atom holds exactly; otherwise Unknown.
    fn assemble_and_verify(
        &self,
        primary: Option<(TermId, BigRational)>,
        resolved: &[(TermId, LinExpr)],
    ) -> UniResult {
        let mut model: Vec<(TermId, BigRational)> = Vec::new();
        if let Some((v, w)) = primary {
            model.push((v, w));
        }
        // Back-substitute the eliminated variables. Because `resolved` is a
        // fixpoint, each eliminated variable's expression references ONLY
        // non-eliminated variables, all of which are either the primary witness
        // or absent. An expression that references a variable not present in the
        // model cannot be evaluated => bail to Unknown (sound).
        for (var, expr) in resolved {
            match eval_linexpr(expr, &model) {
                Some(val) => {
                    // Avoid duplicate/conflicting entries (shouldn't happen).
                    if model.iter().any(|(v, _)| v == var) {
                        return UniResult::Unknown;
                    }
                    model.push((*var, val));
                }
                None => return UniResult::Unknown,
            }
        }

        // SOUNDNESS GATE: re-verify the full assembled model against every
        // ORIGINAL asserted atom by exact substitution.
        if self.verify_model(&model) {
            UniResult::Sat(model)
        } else {
            UniResult::Unknown
        }
    }

    /// Classify an asserted atom into a multivariate `poly REL 0` form, or
    /// `None` if it is not a recognized arithmetic comparison / uses an
    /// unsupported operator.
    pub(crate) fn atom_to_multi(&self, atom: TermId, value: bool) -> Option<MultiAtom> {
        let (rel0, lhs, rhs) = self.comparison_parts(atom)?;
        let rel = if value { rel0 } else { negate_rel(rel0) };
        let lhs_poly = self.term_to_multipoly(lhs)?;
        let rhs_poly = self.term_to_multipoly(rhs)?;
        let poly = lhs_poly.sub(&rhs_poly);
        if poly.variables().is_empty() {
            // Pure constant constraint.
            let sign = if poly.is_zero() {
                0
            } else {
                // Single constant term.
                rational_sign(&poly.terms[0].1)
            };
            if rel.holds_for_sign(sign) {
                Some(MultiAtom::ConstTrue)
            } else {
                Some(MultiAtom::ConstFalse)
            }
        } else {
            Some(MultiAtom::Constraint(MultiConstraint { poly, rel }))
        }
    }

    /// Convert an arithmetic term to a multivariate polynomial, or `None` for
    /// unsupported operators (/, div, mod, abs, transcendental, ...).
    fn term_to_multipoly(&self, term: TermId) -> Option<MultiPoly> {
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => {
                Some(MultiPoly::constant(BigRational::from_integer(n.clone())))
            }
            TermData::Const(Constant::Rational(r)) => Some(MultiPoly::constant(r.0.clone())),
            TermData::Var(_, _) => Some(MultiPoly::var(term)),
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" if !args.is_empty() => {
                    let mut acc = MultiPoly::zero();
                    for &a in args {
                        acc = acc.add(&self.term_to_multipoly(a)?);
                    }
                    Some(acc)
                }
                "-" if args.len() == 1 => Some(self.term_to_multipoly(args[0])?.neg()),
                "-" if args.len() >= 2 => {
                    let mut acc = self.term_to_multipoly(args[0])?;
                    for &a in &args[1..] {
                        acc = acc.sub(&self.term_to_multipoly(a)?);
                    }
                    Some(acc)
                }
                "*" if !args.is_empty() => {
                    let mut acc = MultiPoly::constant(BigRational::one());
                    for &a in args {
                        acc = acc.mul(&self.term_to_multipoly(a)?);
                    }
                    Some(acc)
                }
                _ => None,
            },
            _ => None,
        }
    }
}

/// Marker for the "no primary variable" model-assembly path.
fn var_value_none() -> Option<(TermId, BigRational)> {
    None
}

/// Evaluate a linear expression under a (partial) model, returning `None` if any
/// referenced variable is absent.
fn eval_linexpr(expr: &LinExpr, model: &[(TermId, BigRational)]) -> Option<BigRational> {
    let mut acc = expr.constant.clone();
    for (v, c) in &expr.terms {
        let val = model.iter().find(|(mv, _)| mv == v).map(|(_, x)| x)?;
        acc += c * val;
    }
    Some(acc)
}

/// Resolve a raw substitution list `[(var, LinExpr)]` to a fixpoint where every
/// expression references ONLY variables that are NOT themselves eliminated.
/// Returns `None` on a cycle (e.g. `y = x` and `x = y`) or if resolution does
/// not terminate within a generous bound.
///
/// Soundness: the returned map, applied to any constraint, yields a system
/// equisatisfiable with the original under the asserted equalities — each
/// equality `xi = e` holds in every model, so replacing `xi` by `e` everywhere
/// preserves the solution set restricted to the non-eliminated variables, and
/// the eliminated values are recovered by back-substitution.
fn resolve_substitutions(raw: &[(TermId, LinExpr)]) -> Option<Vec<(TermId, LinExpr)>> {
    let eliminated: Vec<TermId> = raw.iter().map(|(v, _)| *v).collect();
    // De-duplicate: a variable solved for twice (two equalities) means the
    // system pins it twice; keep the first and treat the rest as ordinary
    // constraints handled by the univariate decider. So we only resolve the
    // FIRST occurrence per variable.
    let mut map: Vec<(TermId, LinExpr)> = Vec::new();
    for (v, e) in raw {
        if map.iter().any(|(mv, _)| mv == v) {
            continue;
        }
        map.push((*v, e.clone()));
    }

    // Iteratively substitute eliminated variables appearing on the right-hand
    // sides until no RHS references an eliminated variable (fixpoint), bounded
    // to guard against cycles.
    let bound = (map.len() + 1) * (map.len() + 1) + 16;
    for _ in 0..bound {
        let mut changed = false;
        // Snapshot the current map so substitutions within this pass use a
        // consistent view.
        let snapshot = map.clone();
        for (target, rhs) in &mut map {
            // Does this entry's RHS still reference an eliminated variable?
            for rv in rhs.variables() {
                if rv == *target {
                    // Self-reference (e.g. x = x + 1 reduces to 0 = 1, or
                    // x = 2x): a degenerate/cyclic equality — bail.
                    return None;
                }
                if let Some((_, repl)) = snapshot.iter().find(|(mv, _)| *mv == rv) {
                    *rhs = rhs.substitute(rv, repl);
                    changed = true;
                }
            }
        }
        if !changed {
            // Fixpoint: verify no RHS references any eliminated variable.
            let clean = map
                .iter()
                .all(|(_, e)| e.variables().iter().all(|rv| !eliminated.contains(rv)));
            if clean {
                return Some(map);
            }
            // A reference to an eliminated variable remained but nothing changed
            // => unresolved cycle.
            return None;
        }
    }
    None
}

/// Classification of an atom for the multivariate substitution procedure.
pub(crate) enum MultiAtom {
    Constraint(MultiConstraint),
    ConstTrue,
    ConstFalse,
}

/// A polynomial together with the single variable it depends on (if any).
struct VarPoly {
    poly: UniPoly,
    var: Option<TermId>,
}

impl VarPoly {
    /// Add two var-polynomials, failing if they reference two distinct vars.
    fn combine_add(self, other: Self) -> Option<Self> {
        let var = merge_var(self.var, other.var)?;
        Some(Self {
            poly: self.poly.add(&other.poly),
            var,
        })
    }

    /// Multiply two var-polynomials, failing if they reference two distinct
    /// vars (which would make the product bivariate, e.g. `x*y`).
    fn combine_mul(self, other: Self) -> Option<Self> {
        let var = merge_var(self.var, other.var)?;
        Some(Self {
            poly: self.poly.mul(&other.poly),
            var,
        })
    }
}

/// Merge the variable identities of two subterms. The outer `Option` encodes
/// success/failure (failure = two distinct variables, i.e. bivariate); the
/// inner `Option<TermId>` encodes the merged identity (`None` = constant). The
/// nesting is deliberate and the two layers mean different things.
#[allow(clippy::option_option)]
fn merge_var(a: Option<TermId>, b: Option<TermId>) -> Option<Option<TermId>> {
    match (a, b) {
        (None, None) => Some(None),
        (Some(v), None) | (None, Some(v)) => Some(Some(v)),
        (Some(x), Some(y)) if x == y => Some(Some(x)),
        (Some(_), Some(_)) => None,
    }
}

/// Classification of an atom for the univariate procedure.
enum AtomClass {
    /// Constraint over exactly one variable.
    Univariate(TermId, UniConstraint),
    /// Constraint with no variables that evaluates true.
    ConstTrue,
    /// Constraint with no variables that evaluates false.
    ConstFalse,
    /// Out of fragment (unsupported operator, multivariate coupling, ...).
    OutOfScope,
}

enum SingleVarResult {
    /// SAT with an exact rational witness.
    Witness(BigRational),
    /// SAT, but the only feasible points are irrational. The procedure proved
    /// satisfiability exactly via closed-cell sign analysis and carries the
    /// exact algebraic witness (defining square-free polynomial, 1-based root
    /// index, isolating interval — z3 `root-obj` data) for the feasible root.
    IrrationalSat(crate::algebraic::RealAlgebraic),
    /// Provably empty feasible set (over ALL of R, not just the rationals).
    Empty,
    /// Out of fragment / could not isolate exactly.
    Unknown,
}

/// A real root marker: either an exact rational root, or an open isolating
/// interval `(lo, hi)` that contains exactly one (irrational) root and whose
/// endpoints are NOT roots of the combined polynomial.
#[derive(Clone, Debug)]
pub(crate) enum RootMarker {
    Rational(BigRational),
    Interval(BigRational, BigRational),
}

impl RootMarker {
    /// A rational ordering key strictly below the represented root (its left
    /// edge). For a rational root it is the root itself; for an interval it is
    /// the (non-root) lower endpoint, which lies strictly below the root.
    fn left_edge(&self) -> BigRational {
        match self {
            Self::Rational(r) => r.clone(),
            Self::Interval(lo, _) => lo.clone(),
        }
    }

    /// A rational at-or-above the represented root (its right edge). For a
    /// rational root it is the root; for an interval the (non-root) upper
    /// endpoint, which lies strictly above the root.
    fn right_edge(&self) -> BigRational {
        match self {
            Self::Rational(r) => r.clone(),
            Self::Interval(_, hi) => hi.clone(),
        }
    }

    /// A rational ordering key (left edge) used to sort markers. Distinct roots
    /// have disjoint markers, so left edges order the markers correctly.
    fn locator(&self) -> BigRational {
        self.left_edge()
    }
}

/// Decide a single variable's constraints by exact sign-invariant cell
/// analysis over the reals.
///
/// Construction:
///   * Let `P` be the product of the square-free parts of all distinct
///     constraint polynomials. Its real roots are exactly the union of all
///     constraint roots, each simple.
///   * Isolate `P`'s roots into mutually-disjoint markers (exact rationals or
///     isolating open intervals containing exactly one irrational root).
///   * The markers partition R into open cells and the closed cells at each
///     root. On every cell, the sign of every constraint polynomial is
///     constant, so the truth of each constraint is constant on the cell.
///   * Determine each constraint's sign on every cell EXACTLY (interval
///     refinement gives the sign of any polynomial at an irrational root).
///   * Feasible iff some cell satisfies all constraints. SAT verdict; if the
///     only feasible cells are irrational closed cells, report IrrationalSat.
///   * If NO cell is feasible, the feasible set is provably empty ⇒ UNSAT.
fn decide_single_variable(constraints: &[UniConstraint]) -> SingleVarResult {
    // Build the combined square-free product polynomial P.
    let mut combined = UniPoly::constant(BigRational::one());
    let mut seen: Vec<UniPoly> = Vec::new();
    for c in constraints {
        // Skip the zero polynomial (constant atom; handled earlier).
        if c.poly.is_zero() {
            return SingleVarResult::Unknown;
        }
        let sf = match square_free_part(&c.poly) {
            Some(s) => s,
            None => return SingleVarResult::Unknown,
        };
        if sf.degree() == Some(0) {
            continue; // never zero ⇒ contributes no roots
        }
        // Deduplicate identical square-free factors so P stays small and stays
        // square-free across the product (distinct irreducible factors are
        // coprime; identical factors must not be multiplied in twice).
        if seen.contains(&sf) {
            continue;
        }
        seen.push(sf.clone());
        combined = combined.mul(&sf);
    }

    // After multiplying coprime square-free factors the product can still share
    // roots between *different* constraint polynomials (e.g. x^2-2 and x^2-2
    // dedup'd, but x^2-2 and 2x^2-4 are scalar multiples ⇒ same primitive form
    // and dedup'd via primitive_like in square_free_part). Re-take the
    // square-free part of the product to guarantee simple roots for Sturm.
    let combined = match square_free_part(&combined) {
        Some(s) => s,
        None => return SingleVarResult::Unknown,
    };

    let markers = match isolate_roots(&combined) {
        Some(m) => m,
        None => return SingleVarResult::Unknown,
    };

    // Build the ordered list of cell representatives:
    //   open cell sample, closed cell (root marker), open cell sample, ...
    // Open-cell samples are exact rationals strictly between consecutive roots
    // (and beyond the extremes); their sign for any constraint poly is exact.
    let cells = build_cells(&markers);

    let mut irrational_cell: Option<(BigRational, BigRational)> = None;
    for cell in &cells {
        // Determine whether all constraints hold on this cell.
        let mut all_ok = true;
        for c in constraints {
            let sign = match cell_constraint_sign(cell, c) {
                Some(s) => s,
                None => return SingleVarResult::Unknown, // could not decide exactly
            };
            if !c.rel.holds_for_sign(sign) {
                all_ok = false;
                break;
            }
        }
        if all_ok {
            match cell {
                Cell::Point(r) => return SingleVarResult::Witness(r.clone()),
                Cell::Open(r) => return SingleVarResult::Witness(r.clone()),
                Cell::IrrationalPoint((lo, hi)) => {
                    // Feasible, but witness is irrational. Keep scanning in case
                    // a later cell yields a rational witness (preferred), but
                    // remember the first feasible irrational cell.
                    if irrational_cell.is_none() {
                        irrational_cell = Some((lo.clone(), hi.clone()));
                    }
                }
            }
        }
    }

    if let Some((lo, hi)) = irrational_cell {
        // Build the exact algebraic witness for the feasible irrational root.
        // Prefer the LOWEST-DEGREE constraint factor that vanishes at the root
        // as the defining polynomial (this matches z3's `root-obj` output —
        // e.g. `x^2 - 2` rather than the combined product `x^3 - 2x` for
        // `x*x = 2 ∧ x > 0`); fall back to the combined polynomial. The cell
        // interval isolates the root within the union of ALL factor roots, so
        // it isolates it for any single vanishing factor too.
        let mut defining: Option<&UniPoly> = None;
        for f in &seen {
            let fseq = sturm_sequence(f);
            // Cell endpoints are non-roots of `combined`, hence of every
            // factor (factor roots ⊆ combined roots).
            if sturm_count(&fseq, &lo, &hi) == 1
                && defining.is_none_or(|best| f.degree() < best.degree())
            {
                defining = Some(f);
            }
        }
        let poly = defining.unwrap_or(&combined);
        match crate::algebraic::RealAlgebraic::from_isolating_interval(poly, &lo, &hi) {
            Some(alg) => SingleVarResult::IrrationalSat(alg),
            // Witness construction failed (should not happen for a certified
            // cell): fail closed rather than claim an uncarryable SAT.
            None => SingleVarResult::Unknown,
        }
    } else {
        // No cell — open or closed, rational or irrational — is feasible.
        // Since the cells cover all of R and each constraint's sign is constant
        // per cell, the feasible set over R is provably empty.
        SingleVarResult::Empty
    }
}

/// A sign-invariant cell with an exact representative.
enum Cell {
    /// Open cell sampled at an exact interior rational `r`.
    Open(BigRational),
    /// Closed cell at an exact rational root `r`.
    Point(BigRational),
    /// Closed cell at an irrational root isolated by `(lo, hi)`.
    IrrationalPoint((BigRational, BigRational)),
}

/// Build the ordered cells from the sorted, disjoint root markers.
///
/// Markers come from Sturm isolation of a single square-free polynomial, so
/// their intervals tile `[-B, B]`: consecutive markers either share a non-root
/// endpoint or are separated by a non-root gap. For each pair of consecutive
/// roots we sample the open cell between them at a rational that is strictly
/// between the two roots and is NOT a root of the combined polynomial (no root
/// lies strictly between two consecutive isolated roots).
fn build_cells(markers: &[RootMarker]) -> Vec<Cell> {
    let two = BigRational::from_integer(BigInt::from(2));
    let mut cells = Vec::new();
    if markers.is_empty() {
        cells.push(Cell::Open(BigRational::zero()));
        return cells;
    }

    // Left unbounded open cell: strictly below the first root's left edge.
    cells.push(Cell::Open(markers[0].left_edge() - BigRational::one()));

    for (i, marker) in markers.iter().enumerate() {
        // Closed cell at this root.
        match marker {
            RootMarker::Rational(r) => cells.push(Cell::Point(r.clone())),
            RootMarker::Interval(lo, hi) => {
                cells.push(Cell::IrrationalPoint((lo.clone(), hi.clone())))
            }
        }
        // Open cell between this root and the next, or beyond the last root.
        if i + 1 < markers.len() {
            let right = marker.right_edge();
            let next_left = markers[i + 1].left_edge();
            // A non-root point strictly between the two roots:
            //   * if the markers share an endpoint (right == next_left), that
            //     shared value is itself a non-root strictly between the roots;
            //   * otherwise the midpoint of [right, next_left] lies in the gap,
            //     and the gap contains no root of the combined poly.
            let sample = if right == next_left {
                right
            } else {
                (&right + &next_left) / &two
            };
            cells.push(Cell::Open(sample));
        } else {
            cells.push(Cell::Open(marker.right_edge() + BigRational::one()));
        }
    }
    cells
}

/// Exact sign of a constraint polynomial on a cell.
///   * Open / rational-point cells: evaluate the polynomial at the exact
///     representative.
///   * Irrational-point cells: the representative root `r` is irrational. The
///     sign of the constraint poly `c` at `r` is constant on a sufficiently
///     tight isolating interval that contains no root of `c` (refine until
///     `c` is sign-constant there), or exactly 0 if `c` vanishes at `r`
///     (detected because `r` is a root of the combined poly and `c`'s
///     square-free part divides the combined poly — we test by checking
///     whether `c` has a root inside the interval via Sturm on `c`).
fn cell_constraint_sign(cell: &Cell, c: &UniConstraint) -> Option<i32> {
    match cell {
        Cell::Open(r) | Cell::Point(r) => Some(rational_sign(&c.poly.eval(r))),
        Cell::IrrationalPoint((lo, hi)) => sign_of_poly_at_isolated_root(&c.poly, lo, hi),
    }
}

/// Determine the exact sign of polynomial `p` at the single root of the
/// COMBINED polynomial isolated by the open interval `(lo, hi)`.
///
/// The interval contains exactly one real number that is a root of the combined
/// polynomial (the value the cell represents). Two cases:
///   * `p` has a root inside `(lo, hi)`: since the interval isolates a single
///     combined-root, that root must be the same point, so `p` vanishes there
///     ⇒ sign 0.
///   * `p` has no root inside `(lo, hi)`: `p` is sign-constant on the interval,
///     so its sign at the represented root equals its sign at any interior
///     rational (use the midpoint).
///
/// Returns `None` only if the exact analysis cannot be completed.
fn sign_of_poly_at_isolated_root(p: &UniPoly, lo: &BigRational, hi: &BigRational) -> Option<i32> {
    if p.is_zero() {
        return Some(0);
    }
    // Square-free part of p so Sturm counts simple roots.
    let sf = square_free_part(p)?;
    if sf.degree() == Some(0) {
        // p never zero ⇒ sign constant everywhere; evaluate at midpoint.
        let mid = (lo + hi) / BigRational::from_integer(BigInt::from(2));
        return Some(rational_sign(&p.eval(&mid)));
    }
    let seq = sturm_sequence(&sf);
    // Count roots of p in the open interval (lo, hi). Sturm counts (lo, hi];
    // the endpoints are non-roots of the combined poly, but they could still be
    // roots of p. Guard the endpoints explicitly.
    if p.eval(lo).is_zero() || p.eval(hi).is_zero() {
        // Endpoint is a root of p. Shrink the interval inward and retry: the
        // combined root is strictly interior, so we can always find a sub-
        // interval excluding the endpoint. Use a few bisections toward the
        // interior. (Endpoints are non-roots of the combined poly, so the
        // combined root differs from them and lies strictly inside.)
        // Conservatively bail to keep soundness simple; the caller treats None
        // as unknown.
        return None;
    }
    let count = sturm_count(&seq, lo, hi);
    if count == 0 {
        // p is sign-constant on (lo, hi); evaluate at midpoint.
        let mid = (lo + hi) / BigRational::from_integer(BigInt::from(2));
        Some(rational_sign(&p.eval(&mid)))
    } else if count == 1 {
        // The single root of p in (lo, hi) coincides with the combined root
        // isolated here ⇒ p vanishes at that point.
        Some(0)
    } else {
        // Should not happen: the interval isolates a single combined root, and
        // every root of p is a root of the combined poly. More than one would
        // contradict isolation. Bail to be safe.
        None
    }
}

/// Sign of a rational: -1, 0, or +1.
pub(crate) fn rational_sign(r: &BigRational) -> i32 {
    if r.is_zero() {
        0
    } else if r.is_positive() {
        1
    } else {
        -1
    }
}

/// Negate a comparison relation (used when an atom is asserted false).
fn negate_rel(rel: Rel) -> Rel {
    match rel {
        Rel::Lt => Rel::Ge,
        Rel::Le => Rel::Gt,
        Rel::Eq => Rel::Ne,
        Rel::Ge => Rel::Lt,
        Rel::Gt => Rel::Le,
        Rel::Ne => Rel::Eq,
    }
}

/// Isolate the real roots of a SQUARE-FREE univariate polynomial into ordered,
/// mutually-disjoint markers (exact rational roots and isolating open intervals
/// for irrational roots).
///
/// `p` MUST be square-free (every real root simple); the caller guarantees this
/// by passing `square_free_part`. All arithmetic is exact [`BigRational`].
///
/// Returns `None` if isolation cannot be completed exactly within budget (we
/// then return `unknown` upstream). We never approximate with floats.
pub(crate) fn isolate_roots(p: &UniPoly) -> Option<Vec<RootMarker>> {
    match p.degree() {
        None => None,                // zero polynomial — should be filtered earlier
        Some(0) => Some(Vec::new()), // non-zero constant: no roots
        Some(1) => {
            // a*x + b = 0 => x = -b/a, exact rational root.
            let a = &p.coeffs[1];
            let b = &p.coeffs[0];
            Some(vec![RootMarker::Rational(-b / a)])
        }
        Some(2) => isolate_quadratic(p),
        Some(_) => isolate_sturm(p),
    }
}

/// Markers for the roots of `a*x^2 + b*x + c` (already square-free, so the
/// discriminant is non-zero unless there is a single rational double-root which
/// the square-free reduction collapses to a simple root).
fn isolate_quadratic(p: &UniPoly) -> Option<Vec<RootMarker>> {
    let a = &p.coeffs[2];
    let b = &p.coeffs[1];
    let c = &p.coeffs[0];
    // Discriminant D = b^2 - 4ac.
    let four = BigRational::from_integer(BigInt::from(4));
    let disc = b * b - &four * a * c;
    let dsign = rational_sign(&disc);
    if dsign < 0 {
        return Some(Vec::new()); // no real roots
    }
    if dsign == 0 {
        // Double rational root x = -b/(2a) — but a square-free quadratic cannot
        // have a double root, so this only happens if the caller passed a
        // non-square-free poly. Handle it anyway, soundly: single rational root.
        let two_a = BigRational::from_integer(BigInt::from(2)) * a;
        return Some(vec![RootMarker::Rational(-b / &two_a)]);
    }
    // D > 0: two distinct real roots at (-b ± sqrt(D)) / (2a).
    if let Some(sqrt_d) = exact_rational_sqrt(&disc) {
        let two_a = BigRational::from_integer(BigInt::from(2)) * a;
        let r1 = (-b - &sqrt_d) / &two_a;
        let r2 = (-b + &sqrt_d) / &two_a;
        let (lo, hi) = if r1 <= r2 { (r1, r2) } else { (r2, r1) };
        return Some(vec![RootMarker::Rational(lo), RootMarker::Rational(hi)]);
    }
    // Irrational roots: fall back to the generic Sturm isolation, which yields
    // disjoint isolating intervals with exact rational endpoints.
    isolate_sturm(p)
}

/// Exact rational square root of a non-negative rational, or `None` if it is
/// not a perfect square. Works by taking integer square roots of numerator and
/// denominator after reducing to lowest terms.
pub fn exact_rational_sqrt(r: &BigRational) -> Option<BigRational> {
    if r.is_zero() {
        return Some(BigRational::zero());
    }
    if r.is_negative() {
        return None;
    }
    let num = r.numer();
    let den = r.denom();
    let num_sqrt = integer_sqrt_exact(num)?;
    let den_sqrt = integer_sqrt_exact(den)?;
    Some(BigRational::new(num_sqrt, den_sqrt))
}

/// Exact integer square root of a non-negative integer, or `None` if it is not
/// a perfect square. Implemented with a self-contained binary search on BigInt
/// (no float involved) so the crate needs no extra dependency.
fn integer_sqrt_exact(n: &BigInt) -> Option<BigInt> {
    if n.is_negative() {
        return None;
    }
    if n.is_zero() {
        return Some(BigInt::zero());
    }
    let one = BigInt::one();
    let two = BigInt::from(2);
    // Binary search for floor(sqrt(n)) in [1, n].
    let mut lo = one.clone();
    let mut hi = n.clone();
    let mut floor_sqrt = one.clone();
    while lo <= hi {
        let mid = (&lo + &hi) / &two;
        let sq = &mid * &mid;
        match sq.cmp(n) {
            std::cmp::Ordering::Equal => return Some(mid),
            std::cmp::Ordering::Less => {
                floor_sqrt = mid.clone();
                lo = &mid + &one;
            }
            std::cmp::Ordering::Greater => {
                hi = &mid - &one;
            }
        }
    }
    // n was not a perfect square (floor_sqrt^2 < n < (floor_sqrt+1)^2).
    let _ = floor_sqrt;
    None
}

/// Isolate the real roots of a SQUARE-FREE polynomial of arbitrary degree
/// using a Sturm sequence, returning ordered, mutually-disjoint markers.
///
/// All arithmetic is exact [`BigRational`]. The number of sign variations of
/// the Sturm sequence at a point `t` is `V(t)`; the number of distinct real
/// roots in `(a, b]` is `V(a) - V(b)`. We bound all roots via Cauchy, then
/// bisect, counting roots per subinterval, until each contains exactly one
/// root. A subinterval whose midpoint is exactly a root yields a `Rational`
/// marker; otherwise an `Interval(lo, hi)` whose endpoints are non-roots of
/// `p` (guaranteed because we never split at a root without peeling it off).
///
/// Returns `None` if bisection exceeds a generous budget (then `unknown`).
fn isolate_sturm(p: &UniPoly) -> Option<Vec<RootMarker>> {
    let sqfree = square_free_part(p)?;
    let deg = sqfree.degree()?;
    if deg == 0 {
        return Some(Vec::new());
    }

    let seq = sturm_sequence(&sqfree);

    // Cauchy bound: every real root x satisfies |x| < bound. We use [-B, B] as
    // the master interval; B is not a root (strict inequality), but guard it.
    let bound = cauchy_bound(&sqfree);
    let mut lo_master = -&bound;
    let mut hi_master = bound;
    // Ensure the master endpoints are not roots (they should not be, but be
    // safe: nudge outward by 1 if they are).
    if sqfree.eval(&lo_master).is_zero() {
        lo_master -= BigRational::one();
    }
    if sqfree.eval(&hi_master).is_zero() {
        hi_master += BigRational::one();
    }

    let total = sturm_count(&seq, &lo_master, &hi_master);
    if total == 0 {
        return Some(Vec::new());
    }

    // (lo, hi, count): count roots in (lo, hi]; lo and hi are guaranteed
    // non-roots of `sqfree`. Invariant maintained by choosing split points that
    // are not roots (see `split_point`).
    let mut markers: Vec<RootMarker> = Vec::new();
    let mut work: Vec<(BigRational, BigRational, usize)> = vec![(lo_master, hi_master, total)];

    let mut budget: usize = 200_000;

    while let Some((lo, hi, count)) = work.pop() {
        if budget == 0 {
            return None;
        }
        budget -= 1;

        if count == 0 {
            continue;
        }
        if count == 1 {
            // Tighten the isolating interval until it is narrow (width <= 1/2),
            // keeping a single root inside and non-root endpoints. This yields a
            // representative close to the true root and lets `try_rational_root_in`
            // target a small window. If during tightening the midpoint lands
            // exactly on the root, emit an exact rational marker.
            match tighten_isolating(&sqfree, &seq, lo, hi, &mut budget) {
                Some(Tightened::Rational(r)) => markers.push(RootMarker::Rational(r)),
                Some(Tightened::Interval(lo, hi)) => {
                    // Try to recover an exact rational root for a nicer witness.
                    if let Some(r) = try_rational_root_in(&sqfree, &lo, &hi) {
                        markers.push(RootMarker::Rational(r));
                    } else {
                        markers.push(RootMarker::Interval(lo, hi));
                    }
                }
                None => return None,
            }
            continue;
        }
        // Choose a split point in (lo, hi) that is NOT a root of sqfree, so both
        // recursive subintervals keep non-root endpoints.
        let split = split_point(&sqfree, &lo, &hi, &mut budget)?;
        let left = sturm_count(&seq, &lo, &split);
        let right = count - left;
        if left > 0 {
            work.push((lo, split.clone(), left));
        }
        if right > 0 {
            work.push((split, hi, right));
        }
    }

    markers.sort_by_key(RootMarker::locator);
    Some(markers)
}

/// Pick a rational point strictly inside `(lo, hi)` that is NOT a root of `p`.
/// Starts at the midpoint and, if that is a root, perturbs by successively
/// smaller offsets toward `lo`. Since `p` has finitely many roots, a non-root
/// is found quickly. Returns `None` only if the budget is exhausted.
fn split_point(
    p: &UniPoly,
    lo: &BigRational,
    hi: &BigRational,
    budget: &mut usize,
) -> Option<BigRational> {
    let two = BigRational::from_integer(BigInt::from(2));
    let mid = (lo + hi) / &two;
    if !p.eval(&mid).is_zero() {
        return Some(mid);
    }
    // mid is a root; try midpoints of the lower sub-halves, which converge into
    // (lo, mid) and avoid the root at mid.
    let mut hi_local = mid;
    for _ in 0..256 {
        if *budget == 0 {
            return None;
        }
        *budget -= 1;
        let t = (lo + &hi_local) / &two;
        if !p.eval(&t).is_zero() {
            return Some(t);
        }
        hi_local = t;
    }
    None
}

/// Result of tightening an isolating interval.
enum Tightened {
    /// The single root is exactly this rational (the midpoint hit it).
    Rational(BigRational),
    /// A narrower isolating interval `(lo, hi)` with non-root endpoints.
    Interval(BigRational, BigRational),
}

/// Tighten an isolating interval `(lo, hi]` (containing exactly one root of the
/// square-free `p`, with non-root endpoints) until its width is at most 1/2.
/// Bisects at the midpoint; if the midpoint is the root, returns it exactly.
/// All arithmetic exact. Returns `None` only if the budget is exhausted.
fn tighten_isolating(
    p: &UniPoly,
    seq: &[UniPoly],
    mut lo: BigRational,
    mut hi: BigRational,
    budget: &mut usize,
) -> Option<Tightened> {
    let two = BigRational::from_integer(BigInt::from(2));
    let half = BigRational::new(BigInt::one(), BigInt::from(2));
    // Up to ~60 bisections gives width <= initial/2^60; we stop early at 1/2.
    for _ in 0..200 {
        if &hi - &lo <= half {
            return Some(Tightened::Interval(lo, hi));
        }
        if *budget == 0 {
            return None;
        }
        *budget -= 1;
        let mid = (&lo + &hi) / &two;
        if p.eval(&mid).is_zero() {
            return Some(Tightened::Rational(mid));
        }
        // Count roots of p in (lo, mid]. Exactly one root total in (lo, hi].
        let left = sturm_count(seq, &lo, &mid);
        if left == 1 {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    Some(Tightened::Interval(lo, hi))
}

/// Attempt to recover an exact rational root of `p` inside the open interval
/// `(lo, hi)` using the rational root theorem. `p` has rational coefficients;
/// clear denominators to an integer polynomial, then test candidates `±a/b`
/// with `a | constant`, `b | leading`. Returns the unique such root in range,
/// or `None` if none (the root in `(lo, hi)` is then irrational). Bounded work.
fn try_rational_root_in(p: &UniPoly, lo: &BigRational, hi: &BigRational) -> Option<BigRational> {
    // Clear denominators: multiply by the LCM of all denominators.
    let mut lcm = BigInt::one();
    for c in &p.coeffs {
        lcm = lcm_bigint(&lcm, c.denom());
    }
    let int_coeffs: Vec<BigInt> = p.coeffs.iter().map(|c| (c * &lcm).to_integer()).collect();
    // Trim leading zeros (shouldn't be any after normalize, but be safe).
    let n = int_coeffs.len();
    if n == 0 {
        return None;
    }
    let leading = &int_coeffs[n - 1];
    if leading.is_zero() {
        return None;
    }
    // If the constant term is zero, x=0 is a root.
    if int_coeffs[0].is_zero() {
        let zero = BigRational::zero();
        if &zero > lo && &zero < hi {
            return Some(zero);
        }
    }
    // Factor out the power of x dividing `p`: if the lowest coefficients are
    // zero (constant term 0), then `p(x) = x^k * g(x)` with `g(0) != 0`. The
    // NONZERO rational roots of `p` are exactly those of `g`, and the rational
    // root theorem must use `g`'s constant term — the lowest-degree NONZERO
    // coefficient of `p` — not the literal (zero) constant term. Using 0 here
    // would make `small_divisors(0)` yield only {1}, so any nonzero rational
    // root like 2 (e.g. when `p = x^3 - 4x` arising from `x^2=4 AND x>0`) would
    // be missed and mislabeled as an irrational isolating interval.
    let constant = int_coeffs
        .iter()
        .find(|c| !c.is_zero())
        .expect("non-zero leading coeff guarantees a non-zero coefficient exists");
    // Enumerate divisors of |constant| and |leading|. Cap the magnitude to keep
    // this cheap; if the numbers are huge, skip (returns None ⇒ interval marker,
    // still sound).
    let p_div = small_divisors(constant)?;
    let q_div = small_divisors(leading)?;
    for a in &p_div {
        for b in &q_div {
            if b.is_zero() {
                continue;
            }
            for sign in [BigInt::one(), -BigInt::one()] {
                let cand = BigRational::new(&sign * a, b.clone());
                if &cand > lo && &cand < hi && p.eval(&cand).is_zero() {
                    return Some(cand);
                }
            }
        }
    }
    None
}

/// Divisors of |n| up to a small cap, or `None` if |n| is too large to
/// enumerate cheaply (caller then skips rational-root recovery).
fn small_divisors(n: &BigInt) -> Option<Vec<BigInt>> {
    let an = n.abs();
    if an.is_zero() {
        return Some(vec![BigInt::one()]);
    }
    // Cap: only enumerate when |n| fits in a u64 and is not enormous.
    let limit = BigInt::from(1_000_000u64);
    if an > limit {
        return None;
    }
    let small = an.to_u64()?;
    let mut divs = Vec::new();
    let mut d: u64 = 1;
    while d * d <= small {
        if small % d == 0 {
            divs.push(BigInt::from(d));
            divs.push(BigInt::from(small / d));
        }
        d += 1;
    }
    Some(divs)
}

/// Least common multiple of two BigInts (treating sign as positive).
fn lcm_bigint(a: &BigInt, b: &BigInt) -> BigInt {
    if a.is_zero() || b.is_zero() {
        return BigInt::zero();
    }
    let g = gcd_bigint(a, b);
    (a / &g * b).abs()
}

/// Greatest common divisor of two BigInts (Euclid).
fn gcd_bigint(a: &BigInt, b: &BigInt) -> BigInt {
    let mut a = a.abs();
    let mut b = b.abs();
    while !b.is_zero() {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

/// Square-free part of `p`: `p / gcd(p, p')`. Returns `None` if degree drops to
/// nothing unexpectedly (shouldn't happen for non-constant `p`).
pub(crate) fn square_free_part(p: &UniPoly) -> Option<UniPoly> {
    let dp = p.derivative();
    if dp.is_zero() {
        // p is a constant; no roots concern us.
        return Some(p.clone());
    }
    let g = poly_gcd(p, &dp);
    if g.degree() == Some(0) || g.is_zero() {
        // Already square-free (gcd is a non-zero constant).
        return Some(p.primitive_like());
    }
    let q = poly_div_exact(p, &g)?;
    Some(q.primitive_like())
}

/// Exact polynomial division `num / den` assuming `den` divides `num` exactly.
/// Returns `None` if the remainder is not zero (defensive; shouldn't happen for
/// the square-free quotient).
fn poly_div_exact(num: &UniPoly, den: &UniPoly) -> Option<UniPoly> {
    debug_assert!(!den.is_zero());
    let mut r = num.clone();
    let d_deg = den.degree()?;
    let d_lead = den.leading()?.clone();
    let mut quotient_coeffs = vec![BigRational::zero(); num.degree().unwrap_or(0) + 1];
    while let Some(r_deg) = r.degree() {
        if r_deg < d_deg {
            break;
        }
        let r_lead = r.leading()?.clone();
        let factor = &r_lead / &d_lead;
        let shift = r_deg - d_deg;
        if shift < quotient_coeffs.len() {
            quotient_coeffs[shift] = factor.clone();
        }
        let mut sub = vec![BigRational::zero(); shift];
        for c in &den.coeffs {
            sub.push(c * &factor);
        }
        r = r.sub(&UniPoly { coeffs: sub });
    }
    if !r.is_zero() {
        return None;
    }
    let mut q = UniPoly {
        coeffs: quotient_coeffs,
    };
    q.normalize();
    Some(q)
}

/// Polynomial GCD via the Euclidean algorithm over the rationals.
pub(crate) fn poly_gcd(a: &UniPoly, b: &UniPoly) -> UniPoly {
    let mut a = a.clone();
    let mut b = b.clone();
    while !b.is_zero() {
        let r = a.rem(&b);
        a = b;
        b = r;
    }
    // Normalize to a leading-coefficient-1 form for stability.
    if let Some(lead) = a.leading() {
        if !lead.is_zero() {
            let inv = BigRational::one() / lead;
            a = a.scale(&inv);
        }
    }
    a
}

/// Build the Sturm sequence of a square-free polynomial `p`:
/// `p_0 = p`, `p_1 = p'`, `p_{k+1} = -(p_{k-1} mod p_k)`, until zero.
pub(crate) fn sturm_sequence(p: &UniPoly) -> Vec<UniPoly> {
    let mut seq = vec![p.clone(), p.derivative()];
    if seq[1].is_zero() {
        // p is constant; sequence is just [p].
        seq.pop();
        return seq;
    }
    loop {
        let n = seq.len();
        let prev = &seq[n - 2];
        let cur = &seq[n - 1];
        let rem = prev.rem(cur);
        if rem.is_zero() {
            break;
        }
        seq.push(rem.neg());
    }
    seq
}

/// Number of sign variations of the Sturm sequence evaluated at `t`.
fn sign_variations_at(seq: &[UniPoly], t: &BigRational) -> usize {
    let mut last_sign = 0i32;
    let mut variations = 0usize;
    for poly in seq {
        let s = rational_sign(&poly.eval(t));
        if s == 0 {
            continue;
        }
        if last_sign != 0 && s != last_sign {
            variations += 1;
        }
        last_sign = s;
    }
    variations
}

/// Number of distinct real roots of the square-free `p` in the half-open
/// interval `(a, b]`, computed as `V(a) - V(b)` (Sturm's theorem).
pub(crate) fn sturm_count(seq: &[UniPoly], a: &BigRational, b: &BigRational) -> usize {
    let va = sign_variations_at(seq, a);
    let vb = sign_variations_at(seq, b);
    va.saturating_sub(vb)
}

/// Cauchy's bound: every real root `x` of `p` satisfies `|x| < bound`, where
/// `bound = 1 + max_i |a_i / a_n|` over the non-leading coefficients.
pub(crate) fn cauchy_bound(p: &UniPoly) -> BigRational {
    let lead = match p.leading() {
        Some(l) if !l.is_zero() => l.clone(),
        _ => return BigRational::one(),
    };
    let mut max_ratio = BigRational::zero();
    let n = p.coeffs.len();
    for c in &p.coeffs[..n - 1] {
        let ratio = (c / &lead).abs();
        if ratio > max_ratio {
            max_ratio = ratio;
        }
    }
    BigRational::one() + max_ratio
}

// ============================================================================
// Interval-propagation UNSAT pre-phase (bounded multivariate QF_NRA).
//
// Many multivariate QF_NRA infeasibilities are decidable by a SINGLE forward
// pass of exact interval arithmetic, with NO full CAD. Example:
//
//     x > 2  ∧  x^2 + y^2 < 1                                   (UNSAT)
//
// `x > 2` bounds `x` to `(2, +inf)`, so `x^2` lies in `(4, +inf)` and
// `x^2 + y^2` lies in `(4, +inf)` (since `y^2 >= 0`). The constraint demands
// `x^2 + y^2 < 1`, i.e. the value must be `< 0` after moving 1 across; but its
// range is entirely `>= 4 > 0`. The constraint is unsatisfiable over the box,
// hence the whole problem is UNSAT.
//
// ALGORITHM
//   1. Collect per-variable bounds from LINEAR comparison atoms. A linear atom
//      mentioning exactly one variable yields a one-sided (or, via `=`, a
//      two-sided) bound on that variable. Bounds use exact `BigRational`
//      endpoints with open/closed flags and explicit +/- infinity. A variable
//      with no bound has the box `(-inf, +inf)`.
//   2. For each NON-linear (or any) constraint `poly REL 0`, compute an exact
//      interval OVER-APPROXIMATION of `poly`'s value over the variable box:
//        * constant `c`            -> `[c, c]`
//        * `var`                   -> its box interval
//        * `var^k`                 -> interval power (even `k` over an interval
//                                     straddling 0 gives `[0, max(|lo|^k,
//                                     |hi|^k)]`)
//        * product of factors      -> interval multiply (sign-correct: the four
//                                     endpoint products, with infinity and
//                                     inclusivity handled)
//        * sum of monomials        -> interval add
//      The result `[lo, hi]` is a SOUND over-approximation: the true range of
//      `poly` over the box is a SUBSET of `[lo, hi]`. (Interval arithmetic
//      ignores variable dependency — e.g. `x - x` evaluates to a non-point
//      interval — which only ever makes `[lo, hi]` WIDER, never narrower, so
//      it stays sound for proving UNSAT.)
//   3. INFEASIBILITY: `poly REL 0` is UNSAT over the box iff `[lo, hi]` lies
//      ENTIRELY on the wrong side of the relation (handling strictness and
//      endpoint inclusivity exactly — see `constraint_is_infeasible`).
//   4. If ANY single constraint is infeasible over the box, the whole problem
//      is UNSAT. Otherwise (any constraint feasible-or-uncertain, any
//      unsupported op, etc.) we return Unknown and FALL THROUGH unchanged.
//
// SOUNDNESS-FIRST: this phase emits UNSAT, so a wrong-UNSAT is the only risk.
// The interval is always a correct over-approximation, so "interval excludes
// the REL region" => genuinely infeasible => sound UNSAT. We NEVER emit SAT
// (interval feasibility gives no witness): SAT falls through. When in ANY doubt
// about an endpoint we are conservative and do NOT conclude UNSAT. All
// arithmetic is exact `BigRational`; never `f64`.
// ============================================================================

/// One endpoint of an interval over the extended reals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Endpoint {
    /// Negative infinity (only valid as a lower endpoint).
    NegInf,
    /// Positive infinity (only valid as an upper endpoint).
    PosInf,
    /// A finite rational endpoint together with whether it is INCLUDED.
    Finite(BigRational, bool),
}

/// A non-empty interval over the extended reals: a sound over-approximation of
/// some quantity's true range. `lo` is the lower endpoint (`NegInf` or
/// `Finite`), `hi` the upper (`PosInf` or `Finite`).
#[derive(Clone, Debug)]
pub(crate) struct Interval {
    pub(crate) lo: Endpoint,
    pub(crate) hi: Endpoint,
}

impl Interval {
    /// The whole real line `(-inf, +inf)`.
    pub(crate) fn whole() -> Self {
        Self {
            lo: Endpoint::NegInf,
            hi: Endpoint::PosInf,
        }
    }

    /// The single point `[c, c]`.
    pub(crate) fn point(c: BigRational) -> Self {
        Self {
            lo: Endpoint::Finite(c.clone(), true),
            hi: Endpoint::Finite(c, true),
        }
    }

    /// Interval addition: `[a,b] + [c,d] = [a+c, b+d]`. An endpoint is included
    /// in the sum iff BOTH contributing endpoints are included (and neither is
    /// infinite). Infinity dominates.
    pub(crate) fn add(&self, other: &Self) -> Self {
        Self {
            lo: add_lo(&self.lo, &other.lo),
            hi: add_hi(&self.hi, &other.hi),
        }
    }

    /// Interval multiplication, sign-correct over the four endpoint products
    /// (with infinity and inclusivity handled). Sound over-approximation.
    pub(crate) fn mul(&self, other: &Self) -> Self {
        // The four corner products. Each corner is a `(value, inclusive)` over
        // the extended reals, where `value` is `Option<BigRational>` (None =>
        // an infinity whose sign is tracked separately by which bound list it
        // lands in). We compute all four signed products and take the min for
        // `lo` and the max for `hi`, with inclusivity = product of the two
        // contributing inclusivities (an infinite product is never included).
        let corners = [
            mul_endpoints(&self.lo, &other.lo),
            mul_endpoints(&self.lo, &other.hi),
            mul_endpoints(&self.hi, &other.lo),
            mul_endpoints(&self.hi, &other.hi),
        ];
        let lo = corners
            .iter()
            .cloned()
            .reduce(min_signed)
            .expect("4 corners");
        let hi = corners
            .iter()
            .cloned()
            .reduce(max_signed)
            .expect("4 corners");
        Self {
            lo: lo.to_lo_endpoint(),
            hi: hi.to_hi_endpoint(),
        }
    }

    /// Interval power `self^k` for `k >= 1`, exact, with even-power
    /// non-negativity. For even `k` over an interval straddling 0, the result is
    /// `[0, max(|lo|^k, |hi|^k)]` (0 included). Otherwise the monotone image of
    /// the endpoints under `t |-> t^k`.
    pub(crate) fn pow(&self, k: usize) -> Self {
        debug_assert!(k >= 1);
        if k == 1 {
            return self.clone();
        }
        if k.is_multiple_of(2) {
            // Even power: result is non-negative. The maximum magnitude endpoint
            // dictates the upper bound; the lower bound is 0 if the interval
            // straddles (or touches) 0, else the smaller-magnitude endpoint^k.
            let straddles = self.contains_zero();
            // Upper endpoint: max over endpoints of |t|^k.
            let hi = pow_even_hi(&self.lo, &self.hi, k);
            let lo = if straddles {
                // 0 is in the value range. It is INCLUDED iff some real `t` in
                // the box has `t = 0` AND that point is in the box — i.e. 0 is
                // actually attained. `contains_zero` reports membership, so the
                // 0 here is genuinely attained and thus included.
                Endpoint::Finite(BigRational::zero(), true)
            } else {
                // 0 not in the box: both endpoints are on the same side, so the
                // even power is monotone in |t|; the min is the smaller-|t|
                // endpoint raised to k.
                pow_even_lo(&self.lo, &self.hi, k)
            };
            Self { lo, hi }
        } else {
            // Odd power: monotone increasing, so the image of `[lo, hi]` is
            // `[lo^k, hi^k]` (endpoints in order, inclusivity preserved).
            Self {
                lo: pow_endpoint(&self.lo, k),
                hi: pow_endpoint(&self.hi, k),
            }
        }
    }

    /// Does the interval contain the real number 0 (as a member)?
    pub(crate) fn contains_zero(&self) -> bool {
        let lo_ok = match &self.lo {
            Endpoint::NegInf => true,
            Endpoint::PosInf => false, // lo is never +inf for a valid interval
            Endpoint::Finite(v, inc) => {
                if *inc {
                    v <= &BigRational::zero()
                } else {
                    v < &BigRational::zero()
                }
            }
        };
        let hi_ok = match &self.hi {
            Endpoint::PosInf => true,
            Endpoint::NegInf => false,
            Endpoint::Finite(v, inc) => {
                if *inc {
                    v >= &BigRational::zero()
                } else {
                    v > &BigRational::zero()
                }
            }
        };
        lo_ok && hi_ok
    }
}

/// A signed corner value used inside interval multiplication. `Inf(sign)` is
/// +/- infinity (`sign` = +1 / -1); `Fin(v, inc)` is a finite value with an
/// inclusivity flag.
#[derive(Clone, Debug)]
enum Corner {
    Inf(i32),
    Fin(BigRational, bool),
}

impl Corner {
    fn to_lo_endpoint(self) -> Endpoint {
        match self {
            Self::Inf(s) if s < 0 => Endpoint::NegInf,
            // A +inf lower endpoint cannot arise for a non-empty product range
            // we form here (we always take the min for lo); guard conservatively.
            Self::Inf(_) => Endpoint::PosInf,
            Self::Fin(v, inc) => Endpoint::Finite(v, inc),
        }
    }

    fn to_hi_endpoint(self) -> Endpoint {
        match self {
            Self::Inf(s) if s > 0 => Endpoint::PosInf,
            Self::Inf(_) => Endpoint::NegInf,
            Self::Fin(v, inc) => Endpoint::Finite(v, inc),
        }
    }
}

/// Compare two corners and return the smaller (for the lower endpoint). On a tie
/// in value, the result is INCLUDED iff either is included (the point is in the
/// range via at least one corner). Infinities order as expected.
fn min_signed(a: Corner, b: Corner) -> Corner {
    match (corner_cmp(&a, &b), &a, &b) {
        (std::cmp::Ordering::Less, _, _) => a,
        (std::cmp::Ordering::Greater, _, _) => b,
        // Equal values: merge inclusivity (included if either is).
        (std::cmp::Ordering::Equal, Corner::Fin(v, ia), Corner::Fin(_, ib)) => {
            Corner::Fin(v.clone(), *ia || *ib)
        }
        (std::cmp::Ordering::Equal, _, _) => a,
    }
}

/// Compare two corners and return the larger (for the upper endpoint), merging
/// inclusivity on a tie.
fn max_signed(a: Corner, b: Corner) -> Corner {
    match (corner_cmp(&a, &b), &a, &b) {
        (std::cmp::Ordering::Greater, _, _) => a,
        (std::cmp::Ordering::Less, _, _) => b,
        (std::cmp::Ordering::Equal, Corner::Fin(v, ia), Corner::Fin(_, ib)) => {
            Corner::Fin(v.clone(), *ia || *ib)
        }
        (std::cmp::Ordering::Equal, _, _) => a,
    }
}

/// Order two corners by VALUE on the extended real line (ignoring inclusivity).
fn corner_cmp(a: &Corner, b: &Corner) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    match (a, b) {
        (Corner::Inf(sa), Corner::Inf(sb)) => sa.cmp(sb),
        (Corner::Inf(s), Corner::Fin(_, _)) => {
            if *s < 0 {
                Ordering::Less
            } else {
                Ordering::Greater
            }
        }
        (Corner::Fin(_, _), Corner::Inf(s)) => {
            if *s < 0 {
                Ordering::Greater
            } else {
                Ordering::Less
            }
        }
        (Corner::Fin(va, _), Corner::Fin(vb, _)) => va.cmp(vb),
    }
}

/// Multiply two endpoints (each a lower or upper endpoint of some interval),
/// producing a signed corner. The product of a zero finite endpoint with an
/// infinity is the finite value 0 (`0 * inf = 0` in interval arithmetic when the
/// zero is exact), INCLUDED iff the finite 0 endpoint was included.
fn mul_endpoints(a: &Endpoint, b: &Endpoint) -> Corner {
    match (a, b) {
        (Endpoint::Finite(va, ia), Endpoint::Finite(vb, ib)) => {
            // ZERO-ANNIHILATION inclusivity (the soundness fix). The corner
            // VALUE is `va * vb`. Whether that value is ATTAINED — which drives
            // the `inclusive` flag, and an unsound `inclusive = false` is the
            // only wrong-UNSAT risk — depends on the factors:
            //   * Generic (both nonzero): the corner value `va * vb` is attained
            //     only at the simultaneous point `(va, vb)`, i.e. iff BOTH
            //     endpoints are attainable -> `ia && ib`.
            //   * Zero factor: if `va == 0` (with `ia`, so x = 0 is attained),
            //     then `0 * y = 0` for EVERY y in the other factor's (non-empty)
            //     range, so the product value 0 is attained regardless of the
            //     other factor's inclusivity. Symmetric for `vb == 0`. The
            //     product 0 is thus attained iff EITHER zero-valued endpoint is
            //     itself attained: `(va == 0 && ia) || (vb == 0 && ib)`.
            // This is exactly the degenerate case behind the reverted wrong-
            // UNSAT: x in (0,1) (open) times y in [0,0] (closed) yields the
            // product point [0,0] CLOSED (0 attained), so `x*y = 0` stays
            // feasible. We only ever ADD inclusivity here vs. the plain
            // `ia && ib`, never remove it, so the result remains a sound
            // over-approximation.
            let val = va * vb;
            let inc = if val.is_zero() {
                let va_zero_attained = va.is_zero() && *ia;
                let vb_zero_attained = vb.is_zero() && *ib;
                va_zero_attained || vb_zero_attained
            } else {
                *ia && *ib
            };
            Corner::Fin(val, inc)
        }
        // Infinity times a finite value.
        (Endpoint::Finite(v, inc), inf) | (inf, Endpoint::Finite(v, inc)) => {
            let s = rational_sign(v);
            if s == 0 {
                // 0 * (+/-inf): treat as the finite point 0, included iff the
                // finite 0 endpoint was included. (Sound: any value the product
                // takes when one factor's range includes 0 and the other is
                // unbounded still has 0 as a limit point; for over-approximation
                // we keep 0 with the finite endpoint's inclusivity.)
                Corner::Fin(BigRational::zero(), *inc)
            } else {
                let inf_sign = inf_sign(inf);
                Corner::Inf(s * inf_sign)
            }
        }
        // Infinity times infinity: sign is the product of signs.
        (a, b) => Corner::Inf(inf_sign(a) * inf_sign(b)),
    }
}

/// The sign (+1 / -1) of an infinite endpoint. Panics-free: a finite endpoint
/// returns +1 but this is only ever called on infinite endpoints.
fn inf_sign(e: &Endpoint) -> i32 {
    match e {
        Endpoint::NegInf => -1,
        Endpoint::PosInf => 1,
        Endpoint::Finite(_, _) => 1,
    }
}

/// Lower-endpoint addition `a + b`. Infinity dominates; inclusivity is the AND.
fn add_lo(a: &Endpoint, b: &Endpoint) -> Endpoint {
    match (a, b) {
        (Endpoint::NegInf, _) | (_, Endpoint::NegInf) => Endpoint::NegInf,
        (Endpoint::Finite(va, ia), Endpoint::Finite(vb, ib)) => {
            Endpoint::Finite(va + vb, *ia && *ib)
        }
        // +inf should not appear as a lower endpoint; be conservative.
        _ => Endpoint::NegInf,
    }
}

/// Upper-endpoint addition `a + b`. Infinity dominates; inclusivity is the AND.
fn add_hi(a: &Endpoint, b: &Endpoint) -> Endpoint {
    match (a, b) {
        (Endpoint::PosInf, _) | (_, Endpoint::PosInf) => Endpoint::PosInf,
        (Endpoint::Finite(va, ia), Endpoint::Finite(vb, ib)) => {
            Endpoint::Finite(va + vb, *ia && *ib)
        }
        _ => Endpoint::PosInf,
    }
}

/// Raise a single endpoint to the power `k` (used for odd `k`, monotone).
fn pow_endpoint(e: &Endpoint, k: usize) -> Endpoint {
    match e {
        Endpoint::NegInf => Endpoint::NegInf, // odd power of -inf is -inf
        Endpoint::PosInf => Endpoint::PosInf,
        Endpoint::Finite(v, inc) => Endpoint::Finite(pow_rational(v, k), *inc),
    }
}

/// Upper endpoint of an EVEN power `[lo, hi]^k`: `max(|lo|^k, |hi|^k)`. If either
/// endpoint is infinite, the result is `+inf`. Inclusivity follows the dominating
/// endpoint (or merged on a tie).
fn pow_even_hi(lo: &Endpoint, hi: &Endpoint, k: usize) -> Endpoint {
    let lo_mag = endpoint_abs_pow(lo, k);
    let hi_mag = endpoint_abs_pow(hi, k);
    match (lo_mag, hi_mag) {
        (None, _) | (_, None) => Endpoint::PosInf,
        (Some((vl, il)), Some((vh, ih))) => match vl.cmp(&vh) {
            std::cmp::Ordering::Greater => Endpoint::Finite(vl, il),
            std::cmp::Ordering::Less => Endpoint::Finite(vh, ih),
            std::cmp::Ordering::Equal => Endpoint::Finite(vl, il || ih),
        },
    }
}

/// Lower endpoint of an EVEN power when 0 is NOT in `[lo, hi]` (both endpoints on
/// the same side of 0): `min(|lo|^k, |hi|^k)`. Endpoints here are both finite
/// (an unbounded side would make the box straddle/extend to include 0 only when
/// the finite side is on the opposite sign; we are only called when
/// `contains_zero` is false, which for an infinite side means the finite side is
/// strictly away from 0 — but the infinite side then drives the MIN magnitude to
/// 0 in the limit). To stay sound we treat any infinite endpoint's magnitude as
/// 0 (the smallest possible), yielding a lower bound of 0 — always sound.
fn pow_even_lo(lo: &Endpoint, hi: &Endpoint, k: usize) -> Endpoint {
    let lo_mag = endpoint_abs_pow(lo, k);
    let hi_mag = endpoint_abs_pow(hi, k);
    match (lo_mag, hi_mag) {
        // An infinite endpoint: its values extend toward infinity, but the box
        // does NOT contain 0, so the value range is `[m^k, +inf)` where `m` is
        // the finite endpoint magnitude. The MIN is the finite endpoint^k.
        (None, Some((v, i))) | (Some((v, i)), None) => Endpoint::Finite(v, i),
        (Some((vl, il)), Some((vh, ih))) => match vl.cmp(&vh) {
            std::cmp::Ordering::Less => Endpoint::Finite(vl, il),
            std::cmp::Ordering::Greater => Endpoint::Finite(vh, ih),
            std::cmp::Ordering::Equal => Endpoint::Finite(vl, il || ih),
        },
        // Both infinite cannot happen when contains_zero is false; be safe.
        (None, None) => Endpoint::Finite(BigRational::zero(), true),
    }
}

/// `(|value|^k, inclusive)` for a finite endpoint, or `None` for an infinite one.
fn endpoint_abs_pow(e: &Endpoint, k: usize) -> Option<(BigRational, bool)> {
    match e {
        Endpoint::NegInf | Endpoint::PosInf => None,
        Endpoint::Finite(v, inc) => Some((pow_rational(&v.abs(), k), *inc)),
    }
}

/// Exact `v^k` for `k >= 0` over the rationals (binary exponentiation).
fn pow_rational(v: &BigRational, k: usize) -> BigRational {
    let mut acc = BigRational::one();
    let mut base = v.clone();
    let mut e = k;
    while e > 0 {
        if e & 1 == 1 {
            acc *= &base;
        }
        e >>= 1;
        if e > 0 {
            base = &base * &base;
        }
    }
    acc
}

impl NraSolver<'_> {
    /// Interval-propagation UNSAT pre-phase. Returns [`UniResult::Unsat`] when a
    /// single constraint is provably infeasible over the box of per-variable
    /// bounds; otherwise [`UniResult::Unknown`] (fall through). NEVER emits SAT.
    /// Sound: the interval over-approximation always contains the true range, so
    /// a constraint excluded by its interval is genuinely infeasible.
    pub(crate) fn try_interval_unsat(&self) -> UniResult {
        // 1. Convert every asserted atom to a multivariate `poly REL 0`.
        let mut constraints: Vec<MultiConstraint> = Vec::new();
        for &(atom, value) in &self.asserted {
            match self.atom_to_multi(atom, value) {
                // A pure-constant false atom is an immediate UNSAT.
                Some(MultiAtom::ConstFalse) => return UniResult::Unsat,
                Some(MultiAtom::ConstTrue) => {}
                Some(MultiAtom::Constraint(c)) => constraints.push(c),
                // Unsupported atom (division, abs, transcendental, ...). We can
                // still try to prove UNSAT from the OTHER constraints, but only
                // if their bounds do not depend on this atom. Bounds are derived
                // only from linear `poly REL 0` constraints we DO parse, so an
                // unsupported atom simply contributes nothing; skip it.
                None => {}
            }
        }

        if constraints.is_empty() {
            return UniResult::Unknown;
        }

        // 2. Collect per-variable bounds from LINEAR single-variable atoms.
        //    Every other variable defaults to the whole line.
        let bounds = collect_variable_bounds(&constraints);

        // 3. For each constraint, compute the interval over-approximation of its
        //    polynomial over the box, and test infeasibility. The FIRST provably
        //    infeasible constraint proves the whole problem UNSAT.
        for c in &constraints {
            if let Some(interval) = eval_poly_interval(&c.poly, &bounds) {
                if constraint_is_infeasible(c.rel, &interval) {
                    return UniResult::Unsat;
                }
            }
            // An interval we could not compute (unsupported shape — should not
            // happen since `term_to_multipoly` already succeeded) leaves this
            // constraint as "uncertain"; we just do not conclude UNSAT from it.
        }

        UniResult::Unknown
    }
}

/// Collect a box of per-variable bounds from the LINEAR single-variable
/// constraints. A constraint `a*x + b REL 0` (exactly one variable, degree 1)
/// solves to a one-sided bound on `x` (or, for `=`, both sides). Constraints
/// that are not linear-univariate contribute no bound. Variables with no bound
/// map to `(-inf, +inf)` implicitly (looked up via `Interval::whole`).
pub(crate) fn collect_variable_bounds(
    constraints: &[MultiConstraint],
) -> crate::HashMap<TermId, Interval> {
    let mut bounds: crate::HashMap<TermId, Interval> = crate::HashMap::default();
    for c in constraints {
        let vars = c.poly.variables();
        if vars.len() != 1 {
            continue; // not univariate
        }
        let Some((constant, linear)) = c.poly.as_linear() else {
            continue; // nonlinear in this variable
        };
        if linear.len() != 1 {
            continue; // safety: as_linear guarantees len matches vars here
        }
        let (var, coeff) = (linear[0].0, linear[0].1.clone());
        if coeff.is_zero() {
            continue;
        }
        // Solve `coeff*x + constant REL 0` for `x`: `x REL' root` where
        // `root = -constant/coeff` and REL' is mirrored when `coeff < 0`.
        let root = -(&constant) / &coeff;
        let rel = if coeff.is_positive() {
            c.rel
        } else {
            mirror_rel(c.rel)
        };
        let entry = bounds.entry(var).or_insert_with(Interval::whole);
        apply_bound_to_interval(entry, rel, &root);
    }
    bounds
}

/// Tighten an interval with a one-sided (or equality) bound `x REL root`.
/// `Rel::Ne` is ignored (a single excluded point does not shrink the hull, and
/// keeping the hull sound for over-approximation is all we need).
fn apply_bound_to_interval(iv: &mut Interval, rel: Rel, root: &BigRational) {
    match rel {
        Rel::Gt | Rel::Ge => {
            let inc = matches!(rel, Rel::Ge);
            tighten_lo(&mut iv.lo, root, inc);
        }
        Rel::Lt | Rel::Le => {
            let inc = matches!(rel, Rel::Le);
            tighten_hi(&mut iv.hi, root, inc);
        }
        Rel::Eq => {
            tighten_lo(&mut iv.lo, root, true);
            tighten_hi(&mut iv.hi, root, true);
        }
        Rel::Ne => {}
    }
}

/// Raise the lower endpoint to `max(current, root)` with inclusivity `inc` at
/// `root`. Keeps the TIGHTER (larger) lower bound; on a tie, exclusivity wins
/// (a strict bound is tighter than a non-strict one at the same value).
fn tighten_lo(lo: &mut Endpoint, root: &BigRational, inc: bool) {
    let replace = match &*lo {
        Endpoint::NegInf => true,
        Endpoint::PosInf => false,
        Endpoint::Finite(cur, cur_inc) => root > cur || (root == cur && *cur_inc && !inc),
    };
    if replace {
        *lo = Endpoint::Finite(root.clone(), inc);
    }
}

/// Lower the upper endpoint to `min(current, root)` with inclusivity `inc`.
/// Keeps the TIGHTER (smaller) upper bound; on a tie, exclusivity wins.
fn tighten_hi(hi: &mut Endpoint, root: &BigRational, inc: bool) {
    let replace = match &*hi {
        Endpoint::PosInf => true,
        Endpoint::NegInf => false,
        Endpoint::Finite(cur, cur_inc) => root < cur || (root == cur && *cur_inc && !inc),
    };
    if replace {
        *hi = Endpoint::Finite(root.clone(), inc);
    }
}

/// Compute a SOUND interval over-approximation of `poly`'s value over the box.
/// Returns `None` only if a variable cannot be looked up (never, with the
/// whole-line default). Each monomial's interval is the product of its variable
/// powers scaled by its coefficient; the polynomial interval is the sum.
pub(crate) fn eval_poly_interval(
    poly: &MultiPoly,
    bounds: &crate::HashMap<TermId, Interval>,
) -> Option<Interval> {
    let mut acc = Interval::point(BigRational::zero());
    for (mono, coeff) in &poly.terms {
        // Group the monomial's variables into (var, power) pairs.
        let mut iv = Interval::point(coeff.clone());
        // Count powers per variable.
        let mut i = 0;
        while i < mono.len() {
            let v = mono[i];
            let mut power = 0usize;
            while i < mono.len() && mono[i] == v {
                power += 1;
                i += 1;
            }
            let var_iv = bounds.get(&v).cloned().unwrap_or_else(Interval::whole);
            iv = iv.mul(&var_iv.pow(power));
        }
        acc = acc.add(&iv);
    }
    Some(acc)
}

/// Is the constraint `poly REL 0` UNSAT given that `poly`'s value is contained
/// in `interval`? True iff `interval` lies ENTIRELY on the wrong side of the
/// relation. We over-approximate, so a "definitely on the wrong side" interval
/// proves genuine infeasibility (sound). Any uncertainty => false (no UNSAT).
///
/// ROBUSTLY-SOUND ENDPOINT TREATMENT (conservative inclusivity). The decision
/// reads each endpoint's `inclusive` flag, but that flag is maintained as a
/// CONSERVATIVE under-claim of non-attainment: an endpoint is marked
/// `inclusive = false` (open / strictly excluded) ONLY when the extreme value
/// is PROVABLY not attained anywhere in the box; whenever there is any doubt
/// the endpoint stays `inclusive = true` (closed / attainable). In particular,
/// a product whose extreme `0` is reached because a `[0,0]` factor annihilates
/// the other factor's whole range keeps that `0` endpoint CLOSED (see
/// `mul_endpoints`). Treating an endpoint as closed only ever WIDENS the
/// feasible region, so a wrong `inclusive = false` is the sole soundness risk —
/// and the interval primitives guarantee `inclusive = false` implies genuine
/// strict separation. Consequently:
///   * `poly <  0` UNSAT iff every value `>= 0`  (lo value `>= 0`)
///   * `poly <= 0` UNSAT iff every value `>  0`  (lo `> 0`, or lo `>= 0` & open)
///   * `poly >  0` UNSAT iff every value `<= 0`  (hi value `<= 0`)
///   * `poly >= 0` UNSAT iff every value `<  0`  (hi `< 0`, or hi `<= 0` & open)
///   * `poly =  0` UNSAT iff `0` is NOT in the (inclusivity-aware) hull
///   * `poly != 0` UNSAT iff the value range is the single attained point `{0}`
pub(crate) fn constraint_is_infeasible(rel: Rel, interval: &Interval) -> bool {
    match rel {
        // poly < 0 is impossible iff every value is >= 0, i.e. lo value >= 0
        // (a closed 0 lower endpoint still refutes `< 0`).
        Rel::Lt => interval_is_nonneg(interval),
        // poly <= 0 impossible iff every value is strictly > 0.
        Rel::Le => interval_is_pos(interval),
        // poly > 0 impossible iff every value is <= 0, i.e. hi value <= 0.
        Rel::Gt => interval_is_nonpos(interval),
        // poly >= 0 impossible iff every value is strictly < 0.
        Rel::Ge => interval_is_neg(interval),
        // poly = 0 impossible iff 0 is not in the (inclusivity-aware) interval.
        Rel::Eq => !interval.contains_zero(),
        // poly != 0 impossible iff the ONLY value is exactly 0 (the attained
        // single point [0,0]). Otherwise some non-zero value remains feasible.
        Rel::Ne => interval_is_exactly_zero(interval),
    }
}

/// Every value in the interval is `>= 0` (so `poly < 0` is impossible). A
/// closed-or-open lower endpoint with value `>= 0` suffices: every value is
/// `>= lo value >= 0`.
fn interval_is_nonneg(iv: &Interval) -> bool {
    match &iv.lo {
        Endpoint::NegInf => false,
        Endpoint::PosInf => true,
        Endpoint::Finite(v, _) => v >= &BigRational::zero(),
    }
}

/// Every value in the interval is strictly `> 0` (so `poly <= 0` is impossible).
/// A CLOSED lower endpoint needs value `> 0`; an OPEN lower endpoint (value not
/// attained, all values strictly greater) needs only value `>= 0`. The open
/// branch is sound because `inclusive = false` is a PROVEN non-attainment.
fn interval_is_pos(iv: &Interval) -> bool {
    match &iv.lo {
        Endpoint::NegInf => false,
        Endpoint::PosInf => true,
        Endpoint::Finite(v, inc) => {
            if *inc {
                v > &BigRational::zero()
            } else {
                v >= &BigRational::zero()
            }
        }
    }
}

/// Every value in the interval is `<= 0` (so `poly > 0` is impossible).
fn interval_is_nonpos(iv: &Interval) -> bool {
    match &iv.hi {
        Endpoint::PosInf => false,
        Endpoint::NegInf => true,
        Endpoint::Finite(v, _) => v <= &BigRational::zero(),
    }
}

/// Every value in the interval is strictly `< 0` (so `poly >= 0` is impossible).
/// A CLOSED upper endpoint needs value `< 0`; an OPEN upper endpoint (value not
/// attained) needs only value `<= 0`. Sound by the same proven-non-attainment
/// guarantee on `inclusive = false`.
fn interval_is_neg(iv: &Interval) -> bool {
    match &iv.hi {
        Endpoint::PosInf => false,
        Endpoint::NegInf => true,
        Endpoint::Finite(v, inc) => {
            if *inc {
                v < &BigRational::zero()
            } else {
                v <= &BigRational::zero()
            }
        }
    }
}

/// The interval is exactly the single ATTAINED point `[0, 0]` (both endpoints
/// finite 0 and inclusive). Used for `poly != 0` infeasibility. Requiring BOTH
/// endpoints inclusive is conservative: it fires only when `0` is the sole value
/// AND `0` is marked attained, so `poly != 0` is genuinely impossible.
fn interval_is_exactly_zero(iv: &Interval) -> bool {
    matches!(
        (&iv.lo, &iv.hi),
        (Endpoint::Finite(l, true), Endpoint::Finite(h, true))
            if l.is_zero() && h.is_zero()
    )
}

// ============================================================================
// MULTIVARIATE SUM-OF-SQUARES / QUADRATIC-FORM POSITIVITY UNSAT (sound).
//
// The interval pre-phase cannot refute a constraint whose polynomial couples
// two variables through a cross term, because each variable ranges over the
// whole line and the cross term `x*y` then ranges over `(-inf, +inf)`. A
// classic example is `(x + y)^2 < 0`, i.e. `x^2 + 2*x*y + y^2 < 0`: the
// quadratic form is a perfect square (always >= 0), so the constraint is UNSAT,
// yet interval arithmetic over the cross term gives `(-inf, +inf)` and proves
// nothing.
//
// This phase computes, for a SINGLE multivariate constraint polynomial of total
// degree at most 2 with NO linear (degree-1) terms — i.e. a *homogeneous*
// quadratic form plus a constant `c` — a SOUND global bound on its value over
// all of R^n:
//
//   * If the symmetric quadratic-form matrix `Q` is positive semidefinite
//     (PSD), the minimum of `x^T Q x` over R^n is exactly 0 (attained at the
//     origin), so the polynomial's range is `[c, +inf)` and its minimum is `c`.
//   * If `Q` is negative semidefinite (NSD), the maximum is `c` and the range
//     is `(-inf, c]`.
//   * Otherwise (indefinite) the form is unbounded in both directions and we
//     conclude nothing.
//
// PSD/NSD is decided EXACTLY over the rationals by an LDL^T-style symmetric
// elimination (no floats). With the exact range in hand, a constraint whose
// range lies entirely on the wrong side of its relation is UNSAT. We never emit
// SAT and never widen the true range, so this is sound and fail-closed.
//
// Restricting to the no-linear-term (homogeneous + constant) case keeps the
// minimum computation a triviality (the form's min/max is 0/0 plus `c`) while
// still covering the sum-of-squares and conic-positivity infeasibilities the
// targets care about (`x^2 + y^2 < 0`, `(x+y)^2 < 0`, `x^2 + y^2 + 1 = 0`,
// ...). A linear part would shift the extremum off the origin and require
// solving `Q v = -b/2`; we deliberately leave that to Unknown rather than risk
// an unsound bound. Reference grounding: positivstellensatz / SOS certificates
// (`reference/smtrat`), and the LDL^T PSD test (`reference/z3` dense LA).
// ============================================================================

/// The decided global range shape of a homogeneous-quadratic-plus-constant
/// polynomial over all of R^n.
enum QuadRange {
    /// Range is `[c, +inf)`; the minimum value is `c` (PSD form).
    MinIs(BigRational),
    /// Range is `(-inf, c]`; the maximum value is `c` (NSD form).
    MaxIs(BigRational),
    /// Indefinite / out of fragment — no sound bound.
    Unbounded,
}

impl NraSolver<'_> {
    /// SUM-OF-SQUARES / quadratic-form positivity UNSAT pre-phase. Returns
    /// [`UniResult::Unsat`] when a single constraint's polynomial is a
    /// homogeneous quadratic form plus a constant whose SOUND global range lies
    /// entirely on the wrong side of the relation; otherwise
    /// [`UniResult::Unknown`]. NEVER emits SAT. Exact `BigRational` throughout.
    pub(crate) fn try_sos_unsat(&self) -> UniResult {
        let mut constraints: Vec<MultiConstraint> = Vec::new();
        for &(atom, value) in &self.asserted {
            match self.atom_to_multi(atom, value) {
                Some(MultiAtom::ConstFalse) => return UniResult::Unsat,
                Some(MultiAtom::ConstTrue) => {}
                Some(MultiAtom::Constraint(c)) => constraints.push(c),
                // Unsupported atom contributes nothing; a single self-contained
                // constraint still suffices to prove UNSAT.
                None => {}
            }
        }

        for c in &constraints {
            // Require at least two distinct variables: the univariate / interval
            // phases already cover the single-variable case exactly.
            if c.poly.variables().len() < 2 {
                continue;
            }
            let Some(range) = quadratic_form_range(&c.poly) else {
                continue;
            };
            if quad_range_refutes(c.rel, &range) {
                return UniResult::Unsat;
            }
        }

        UniResult::Unknown
    }
}

/// Is the constraint `poly REL 0` refuted by the SOUND global range of `poly`?
/// Mirrors [`constraint_is_infeasible`] but for the closed-form quadratic range.
fn quad_range_refutes(rel: Rel, range: &QuadRange) -> bool {
    let zero = BigRational::zero();
    match range {
        // Range is `[m, +inf)`: every value is `>= m`.
        QuadRange::MinIs(m) => match rel {
            // `poly < 0` impossible iff m >= 0.
            Rel::Lt => *m >= zero,
            // `poly <= 0` impossible iff m > 0.
            Rel::Le => *m > zero,
            // `poly = 0` impossible iff m > 0 (0 below the whole range).
            Rel::Eq => *m > zero,
            // `> 0`, `>= 0`, `!= 0` can all still hold (large x) — no refute.
            _ => false,
        },
        // Range is `(-inf, M]`: every value is `<= M`.
        QuadRange::MaxIs(mx) => match rel {
            // `poly > 0` impossible iff M <= 0.
            Rel::Gt => *mx <= zero,
            // `poly >= 0` impossible iff M < 0.
            Rel::Ge => *mx < zero,
            // `poly = 0` impossible iff M < 0 (0 above the whole range).
            Rel::Eq => *mx < zero,
            _ => false,
        },
        QuadRange::Unbounded => false,
    }
}

/// Compute the SOUND global range of a polynomial that is a HOMOGENEOUS
/// quadratic form (every non-constant monomial has total degree exactly 2) plus
/// a constant term. Returns `None` if the polynomial has any monomial of degree
/// 1 or degree >= 3 (out of fragment), or if the quadratic form is indefinite.
fn quadratic_form_range(poly: &MultiPoly) -> Option<QuadRange> {
    // Split into the constant term and the degree-2 part; reject anything else.
    let mut constant = BigRational::zero();
    // Collect the distinct variables in a stable order for matrix indexing.
    let vars = poly.variables();
    if vars.is_empty() {
        return None;
    }
    let n = vars.len();
    let index = |v: TermId| vars.iter().position(|&u| u == v).expect("var in support");

    // Symmetric matrix Q with `x^T Q x` reproducing the quadratic part:
    //   coeff of x_i^2  -> Q[i][i]
    //   coeff of x_i x_j (i<j) -> split as Q[i][j] = Q[j][i] = coeff/2.
    let mut q = vec![vec![BigRational::zero(); n]; n];
    for (mono, coeff) in &poly.terms {
        match mono.len() {
            0 => constant += coeff,
            2 => {
                let a = index(mono[0]);
                let b = index(mono[1]);
                if a == b {
                    // x_i^2 term.
                    q[a][a] += coeff;
                } else {
                    // x_i x_j cross term: symmetric split.
                    let half = coeff / BigRational::from_integer(BigInt::from(2));
                    q[a][b] += &half;
                    q[b][a] += half;
                }
            }
            // Degree 1 (linear) or degree >= 3: out of this fragment.
            _ => return None,
        }
    }

    // Classify Q by exact PSD / NSD tests.
    if matrix_is_psd(&q) {
        Some(QuadRange::MinIs(constant))
    } else if matrix_is_psd(&negate_matrix(&q)) {
        // -Q PSD  <=>  Q NSD  <=>  x^T Q x <= 0 everywhere, so max is `constant`.
        Some(QuadRange::MaxIs(constant))
    } else {
        Some(QuadRange::Unbounded)
    }
}

/// Negate every entry of a square matrix.
fn negate_matrix(m: &[Vec<BigRational>]) -> Vec<Vec<BigRational>> {
    m.iter()
        .map(|row| row.iter().map(|x| -x).collect())
        .collect()
}

/// EXACT positive-semidefiniteness test for a symmetric rational matrix via
/// LDL^T-style symmetric Gaussian elimination (no pivoting on magnitude; we use
/// a symmetric permutation only to skip zero pivots).
///
/// A symmetric matrix `A` is PSD iff it has an `L D L^T` factorization with
/// every diagonal entry of `D` non-negative AND, whenever a pivot is zero, the
/// entire remaining row/column of that variable is zero (no "free" direction
/// with a non-zero coupling, which would make the form indefinite). This is the
/// exact-arithmetic analogue of the Cholesky existence test.
///
/// Soundness: the procedure either proves PSD (returns true) or leaves it
/// unproven (returns false). A `false` only ever blocks the UNSAT conclusion
/// (fail-closed), so a conservative `false` can never cause a wrong verdict.
fn matrix_is_psd(input: &[Vec<BigRational>]) -> bool {
    let n = input.len();
    if n == 0 {
        return true;
    }
    // Work on a mutable copy; we perform symmetric Schur-complement updates.
    let mut a: Vec<Vec<BigRational>> = input.to_vec();
    // Track which rows/cols remain active (not yet pivoted or skipped).
    for k in 0..n {
        let pivot = a[k][k].clone();
        if pivot.is_negative() {
            // Negative pivot -> not PSD (the form is negative along e_k after
            // elimination).
            return false;
        }
        if pivot.is_zero() {
            // Zero pivot: PSD requires the whole remaining row & column for k to
            // be zero. If any coupling remains, the form is indefinite along a
            // 2D subspace (a zero diagonal with a non-zero off-diagonal yields a
            // negative eigenvalue). Skip this index when clean.
            if a[k][k + 1..].iter().any(|entry| !entry.is_zero())
                || a[k + 1..].iter().any(|row| !row[k].is_zero())
            {
                return false;
            }
            continue;
        }
        // Positive pivot: eliminate column k from the trailing submatrix via the
        // exact Schur complement  A'[i][j] = A[i][j] - A[i][k]*A[k][j]/pivot.
        let (upper, lower) = a.split_at_mut(k + 1);
        let pivot_row = &upper[k];
        for row in &mut *lower {
            let factor = &row[k] / &pivot;
            if factor.is_zero() {
                continue;
            }
            for (entry, pivot_entry) in row[k + 1..].iter_mut().zip(&pivot_row[k + 1..]) {
                let delta = &factor * pivot_entry;
                *entry -= delta;
            }
        }
    }
    true
}

// ============================================================================
// BOUNDED MULTIVARIATE RATIONAL-WITNESS SEARCH (sound, SAT only).
//
// For genuinely coupled two-variable problems that no exact phase above can
// decide — e.g. the unit circle `x^2 + y^2 = 1 ∧ x > 1/2`, or `x^2+y^2=25 ∧
// x>0 ∧ y>0` — this phase looks for a CONCRETE rational witness by GROUNDING
// one variable to a candidate rational `v` and then solving the resulting
// single-variable system EXACTLY with the existing univariate decider. If a
// rational witness `(x=v, y=w)` is found, the FULL model is re-verified by
// exact substitution against EVERY original asserted atom (`verify_model`)
// before SAT is returned.
//
// SOUNDNESS: SAT is emitted ONLY through `verify_model`, which recomputes every
// atom (including every nonlinear product) under the concrete rational model.
// The grounding grid only affects COMPLETENESS — a wrong or unlucky grid simply
// fails to find a witness and returns Unknown; it can never produce a wrong
// SAT. We never emit UNSAT here (absence of a witness in a bounded grid proves
// nothing). Everything is exact `BigRational`.
//
// The candidate grid for the grounding variable is taken from a SOUND feasible
// box (single-variable linear bounds intersected with quadratic-implied bounds)
// and enumerated at bounded denominators, capped to a small budget so the
// debug build stays fast. Reference grounding: ICP / interval-constraint
// propagation with rational sampling (`reference/smtrat`, dReal-style search,
// but kept exact and witness-verified).
// ============================================================================

/// Maximum denominator used when enumerating rational grounding candidates.
const WITNESS_MAX_DENOM: i64 = 40;
/// Hard cap on the number of grounding candidates tried (keeps debug fast).
const WITNESS_MAX_CANDIDATES: usize = 4000;
/// Sampling radius used for a grounding axis whose SOUND feasible interval is
/// unbounded on a side. This is a SAMPLING choice only — never a soundness
/// claim: every candidate is exactly substituted and the final model is gated
/// by full exact re-verification, so the window merely decides which rational
/// points get tried before the phase gives up (Unknown).
const WITNESS_FALLBACK_RADIUS: i64 = 12;

impl NraSolver<'_> {
    /// Bounded multivariate rational-witness search. Returns
    /// [`UniResult::Sat`] with a substitution-verified model when a concrete
    /// rational witness is found for a coupled two-variable system; otherwise
    /// [`UniResult::Unknown`]. NEVER emits UNSAT. Sound: SAT is gated by full
    /// model re-verification.
    pub(crate) fn try_multivariate_witness_search(&self) -> UniResult {
        // 1. Collect multivariate constraints; bail out of fragment on any
        //    unsupported atom (we need the FULL system to ground correctly).
        let mut constraints: Vec<MultiConstraint> = Vec::new();
        for &(atom, value) in &self.asserted {
            match self.atom_to_multi(atom, value) {
                // A definitely-false constant atom is handled by the UNSAT
                // phases; here we just decline (never claim SAT).
                Some(MultiAtom::ConstFalse) => return UniResult::Unknown,
                Some(MultiAtom::ConstTrue) => {}
                Some(MultiAtom::Constraint(c)) => constraints.push(c),
                None => return UniResult::Unknown,
            }
        }
        if constraints.is_empty() {
            return UniResult::Unknown;
        }

        // 2. Variable support across all constraints. We handle the SMALL
        //    coupled case: 2 or 3 variables (grounded one at a time down to an
        //    exactly-decided univariate residual).
        let mut vars: Vec<TermId> = Vec::new();
        for c in &constraints {
            for v in c.poly.variables() {
                if !vars.contains(&v) {
                    vars.push(v);
                }
            }
        }
        if vars.len() < 2 || vars.len() > 3 {
            return UniResult::Unknown;
        }

        // 2b. SQUARE (and over-determined) systems are the interval
        //     branch-and-prune decider's job, not this SAT-only rational grid's.
        //     When there are at least as many equalities as variables the
        //     solution set is a finite set of ISOLATED points, so a rational
        //     grid can only land a witness by luck while paying a full
        //     `WITNESS_MAX_CANDIDATES` sweep of exact univariate solves — and it
        //     can NEVER refute. That sweep was the entire cost of the geometry_consumer-sketch
        //     "block every branch" refutation stall: a two-circle system
        //     (2 equalities, 2 unknowns) plus blocking balls is UNSAT, but this
        //     phase burned the whole budget enumerating ~thousands of candidates
        //     before ICP — which DOES decide it by exact interval refutation —
        //     ever ran. Defer such systems to ICP (`try_icp_branch_and_prune`,
        //     which runs immediately after and both certifies SAT and refutes
        //     UNSAT). Under-determined systems (fewer equalities than variables)
        //     have a solution MANIFOLD the grid genuinely helps sample, so they
        //     still run below.
        let eq_count = constraints
            .iter()
            .filter(|c| matches!(c.rel, Rel::Eq))
            .count();

        // 3. Compute a SOUND feasible box (per-variable interval) by a few passes
        //    of exact interval propagation. A genuinely coupled equality like
        //    `x^2 + y^2 = 25` bounds BOTH variables once one is bounded; the
        //    initial linear bounds seed the propagation.
        let bounds = propagate_box(&constraints, &vars);

        // 3b. Square (and over-determined) systems whose box is FULLY BOUNDED
        //     are ICP's job (see the deferral rationale above): ICP both
        //     certifies SAT and refutes UNSAT there, and the grid would burn
        //     its whole budget first. But when any variable is UNBOUNDED, ICP
        //     itself falls through (it needs a finite box), so the grid is the
        //     ONLY sampler that can still exhibit a witness — run it.
        let box_fully_bounded = vars.iter().all(|v| {
            bounds
                .get(v)
                .is_some_and(|iv| finite_interval(iv).is_some())
        });
        if eq_count >= vars.len() && box_fully_bounded {
            return UniResult::Unknown;
        }

        // 4. Recursive grounding: fix one variable at a rational grid point,
        //    substitute exactly, and repeat until a single variable remains,
        //    which the exact univariate decider settles (rational witness or
        //    Sturm/IVT-certified irrational witness). The candidate budget is
        //    shared across the whole tree.
        let mut budget = WITNESS_MAX_CANDIDATES;
        let mut assignment: Vec<(TermId, BigRational)> = Vec::new();
        let Some(witnesses) = self.search_witness_rec(&constraints, &mut assignment, &mut budget)
        else {
            return UniResult::Unknown;
        };

        // Assemble verdict. All-rational models go through the ORIGINAL-atom
        // verifier (SOUNDNESS GATE). Mixed models were exactly verified at the
        // leaf: every original constraint either collapsed to a checked
        // constant under the exact rational substitutions or reached the leaf
        // as a univariate polynomial whose sign at the exact algebraic root
        // was confirmed by Sturm sign determination.
        let mut rational: Vec<(TermId, BigRational)> = Vec::new();
        let mut has_algebraic = false;
        for (v, w) in &witnesses {
            match w {
                UniWitness::Rational(r) => rational.push((*v, r.clone())),
                UniWitness::Algebraic(_) => has_algebraic = true,
            }
        }
        if !has_algebraic {
            // Give any variable that dropped out of every constraint (fully
            // unconstrained after collapses) the value 0 so the verifier can
            // evaluate every original atom.
            let mut model = rational;
            for &v in &vars {
                if !model.iter().any(|(mv, _)| *mv == v) {
                    model.push((v, BigRational::zero()));
                }
            }
            if self.verify_model(&model) {
                return UniResult::Sat(model);
            }
            return UniResult::Unknown;
        }
        UniResult::SatAlgebraic(witnesses)
    }

    /// Recursive grounded witness search. `constraints` is the current
    /// (exactly substituted) system, `assignment` the rational values fixed so
    /// far. Returns the FULL mixed witness list for the variables of the
    /// current system (plus the fixed ones) on success. SAT-only: never
    /// refutes anything; exhausting the budget returns `None` (→ Unknown).
    fn search_witness_rec(
        &self,
        constraints: &[MultiConstraint],
        assignment: &mut Vec<(TermId, BigRational)>,
        budget: &mut usize,
    ) -> Option<Vec<(TermId, UniWitness)>> {
        // Variable support of the current residual system.
        let mut vars: Vec<TermId> = Vec::new();
        for c in constraints {
            for v in c.poly.variables() {
                if !vars.contains(&v) {
                    vars.push(v);
                }
            }
        }

        // Base case: at most one variable left — decide exactly.
        if vars.len() <= 1 {
            return self.decide_witness_leaf(constraints, vars.first().copied(), assignment);
        }

        // Recursive case: pick a grounding axis (tighter finite interval
        // first), enumerate rational candidates, substitute, recurse.
        let bounds = propagate_box(constraints, &vars);
        let order = ground_order(&vars, &bounds);
        for &gvar in &order {
            let gbox = bounds.get(&gvar).cloned().unwrap_or_else(Interval::whole);
            let Some((lo, hi)) = sampling_window(&gbox) else {
                continue;
            };
            for v in rational_grid(&lo, &hi) {
                if *budget == 0 {
                    return None;
                }
                *budget -= 1;
                // Substitute gvar := v (a constant LinExpr) into every
                // constraint; drop collapsed-to-constant constraints after
                // checking them (a falsified constant kills this candidate).
                let subst = LinExpr {
                    constant: v.clone(),
                    terms: Vec::new(),
                };
                let mut residual: Vec<MultiConstraint> = Vec::new();
                let mut feasible = true;
                for c in constraints {
                    let poly = c.poly.substitute(gvar, &subst);
                    if poly.variables().is_empty() {
                        // Constant after substitution: check its sign exactly.
                        let Some((constant, _)) = poly.as_linear() else {
                            feasible = false;
                            break;
                        };
                        if !c.rel.holds_for_sign(rational_sign(&constant)) {
                            feasible = false;
                            break;
                        }
                    } else {
                        residual.push(MultiConstraint { poly, rel: c.rel });
                    }
                }
                if !feasible {
                    continue;
                }
                assignment.push((gvar, v));
                if let Some(w) = self.search_witness_rec(&residual, assignment, budget) {
                    return Some(w);
                }
                assignment.pop();
            }
        }
        None
    }

    /// Leaf of the grounded search: at most one variable remains. Decide the
    /// residual univariate system exactly and assemble the mixed witness list.
    /// An irrational leaf witness is re-verified constraint-by-constraint via
    /// exact Sturm sign determination before being accepted.
    fn decide_witness_leaf(
        &self,
        constraints: &[MultiConstraint],
        var: Option<TermId>,
        assignment: &[(TermId, BigRational)],
    ) -> Option<Vec<(TermId, UniWitness)>> {
        let mut uni: Vec<UniConstraint> = Vec::new();
        for c in constraints {
            let upoly = c.poly.to_unipoly()?;
            match upoly.degree() {
                None => {
                    // 0 REL 0.
                    if !c.rel.holds_for_sign(0) {
                        return None;
                    }
                }
                Some(0) => {
                    let sign = rational_sign(&upoly.eval(&BigRational::zero()));
                    if !c.rel.holds_for_sign(sign) {
                        return None;
                    }
                }
                Some(_) => uni.push(UniConstraint {
                    poly: upoly,
                    rel: c.rel,
                }),
            }
        }
        let mut witnesses: Vec<(TermId, UniWitness)> = assignment
            .iter()
            .map(|(v, w)| (*v, UniWitness::Rational(w.clone())))
            .collect();
        let Some(var) = var else {
            return Some(witnesses);
        };
        if uni.is_empty() {
            // The remaining variable is unconstrained: pick 0 (the outer
            // verifier confirms all-rational models against every atom).
            witnesses.push((var, UniWitness::Rational(BigRational::zero())));
            return Some(witnesses);
        }
        match decide_single_variable(&uni) {
            SingleVarResult::Witness(w) => {
                witnesses.push((var, UniWitness::Rational(w)));
                Some(witnesses)
            }
            SingleVarResult::IrrationalSat(alg) => {
                // SOUNDNESS GATE (mixed model): confirm every residual
                // constraint's sign at the exact algebraic root.
                for c in &uni {
                    match alg.sign_of_poly(&c.poly) {
                        Some(s) if c.rel.holds_for_sign(s) => {}
                        _ => return None,
                    }
                }
                witnesses.push((var, UniWitness::Algebraic(alg.as_value())));
                Some(witnesses)
            }
            SingleVarResult::Empty | SingleVarResult::Unknown => None,
        }
    }
}

/// Derive a finite sampling window from a (possibly unbounded) sound interval.
/// Finite intervals are used as-is; a half-bounded interval extends
/// `2 * WITNESS_FALLBACK_RADIUS` from its finite edge; a whole-line interval
/// becomes `[-R, R]`. Sampling only — the exact verification gates any SAT.
fn sampling_window(iv: &Interval) -> Option<(BigRational, BigRational)> {
    let r = BigRational::from_integer(BigInt::from(WITNESS_FALLBACK_RADIUS));
    let two_r = &r + &r;
    let lo = match &iv.lo {
        Endpoint::Finite(v, _) => Some(v.clone()),
        _ => None,
    };
    let hi = match &iv.hi {
        Endpoint::Finite(v, _) => Some(v.clone()),
        _ => None,
    };
    let (lo, hi) = match (lo, hi) {
        (Some(l), Some(h)) => (l, h),
        (Some(l), None) => {
            let h = &l + &two_r;
            (l, h)
        }
        (None, Some(h)) => {
            let l = &h - &two_r;
            (l, h)
        }
        (None, None) => (-r.clone(), r),
    };
    if lo > hi {
        return None;
    }
    Some((lo, hi))
}

/// Choose the order in which to try grounding the two variables: the variable
/// with the narrower finite interval first (its grid is more likely to hit a
/// rational witness with small denominators). Variables with an unbounded
/// interval are tried last.
fn ground_order(vars: &[TermId], bounds: &crate::HashMap<TermId, Interval>) -> Vec<TermId> {
    let mut order: Vec<TermId> = vars.to_vec();
    order.sort_by(|&a, &b| {
        let wa = interval_width_key(bounds.get(&a));
        let wb = interval_width_key(bounds.get(&b));
        wa.cmp(&wb)
    });
    order
}

/// A sort key that ranks NARROWER finite intervals first. Unbounded intervals
/// sort last (a large sentinel). Width is compared as an exact rational, encoded
/// by `(is_unbounded, width)`.
fn interval_width_key(iv: Option<&Interval>) -> (bool, BigRational) {
    match iv.and_then(finite_interval) {
        Some((lo, hi)) => (false, hi - lo),
        None => (true, BigRational::zero()),
    }
}

/// Extract a finite `[lo, hi]` from an interval, or `None` if either endpoint is
/// infinite. Inclusivity is ignored: the rational grid samples interior points
/// and the verifier confirms the actual atoms, so endpoint-openness is handled
/// by re-verification (an excluded endpoint that slips in fails verification).
fn finite_interval(iv: &Interval) -> Option<(BigRational, BigRational)> {
    let lo = match &iv.lo {
        Endpoint::Finite(v, _) => v.clone(),
        _ => return None,
    };
    let hi = match &iv.hi {
        Endpoint::Finite(v, _) => v.clone(),
        _ => return None,
    };
    if lo > hi {
        return None;
    }
    Some((lo, hi))
}

/// Generate an ordered list of rational candidates in `[lo, hi]` at bounded
/// denominators. For each denominator `q` in `1..=WITNESS_MAX_DENOM` we emit
/// every `p/q` with `lo <= p/q <= hi`. Smaller denominators come first (more
/// likely to be a clean witness). Duplicates across denominators are acceptable;
/// the verifier deduplicates by effect (a repeat just re-checks the same point).
fn rational_grid(lo: &BigRational, hi: &BigRational) -> Vec<BigRational> {
    let mut out: Vec<BigRational> = Vec::new();
    for q in 1..=WITNESS_MAX_DENOM {
        let qd = BigRational::from_integer(BigInt::from(q));
        // Smallest integer p with p/q >= lo  ->  p = ceil(lo*q).
        let lo_scaled = lo * &qd;
        let hi_scaled = hi * &qd;
        let p_lo = rational_ceil(&lo_scaled);
        let p_hi = rational_floor(&hi_scaled);
        let mut p = p_lo;
        while p <= p_hi {
            let cand = BigRational::new(p.clone(), BigInt::from(q));
            out.push(cand);
            p += BigInt::one();
            if out.len() >= WITNESS_MAX_CANDIDATES {
                return out;
            }
        }
    }
    out
}

/// Ceiling of a rational to the nearest integer (toward +inf), as a `BigInt`.
fn rational_ceil(r: &BigRational) -> BigInt {
    let q = r.numer() / r.denom(); // truncated toward zero
    let rem = r.numer() % r.denom();
    if rem.is_zero() {
        q
    } else if r.is_positive() {
        q + BigInt::one()
    } else {
        q
    }
}

/// Floor of a rational to the nearest integer (toward -inf), as a `BigInt`.
fn rational_floor(r: &BigRational) -> BigInt {
    let q = r.numer() / r.denom();
    let rem = r.numer() % r.denom();
    if rem.is_zero() {
        q
    } else if r.is_negative() {
        q - BigInt::one()
    } else {
        q
    }
}

/// Compute a SOUND feasible box for the given variables by a few passes of exact
/// interval propagation over the constraints. Seeds with linear single-variable
/// bounds, then iteratively tightens: for each constraint and each variable, the
/// constraint's interval over the current box (with the variable left whole)
/// bounds that variable. We keep this conservative — every interval is a sound
/// over-approximation, so every derived bound is sound.
fn propagate_box(
    constraints: &[MultiConstraint],
    vars: &[TermId],
) -> crate::HashMap<TermId, Interval> {
    // Seed from linear single-variable bounds (reuses the interval-phase logic).
    let mut bounds = collect_variable_bounds(constraints);
    for &v in vars {
        bounds.entry(v).or_insert_with(Interval::whole);
    }

    // A few tightening passes. Each pass bounds a variable from an EQUALITY (or
    // a one-sided inequality) of the form `a*x^2 + (terms in other var) REL 0`
    // by isolating `x^2` against the interval of the rest. We only handle the
    // common conic shape `c2*x^2 + rest(other) REL 0` soundly; anything else
    // leaves the bound unchanged.
    for _ in 0..4 {
        let snapshot = bounds.clone();
        for c in constraints {
            for &x in vars {
                if let Some(iv) = bound_var_from_constraint(c, x, &snapshot) {
                    let entry = bounds.entry(x).or_insert_with(Interval::whole);
                    *entry = intersect_intervals(entry, &iv);
                }
            }
        }
    }
    bounds
}

/// Derive a SOUND interval for variable `x` from a single constraint, given the
/// current box for the OTHER variables. Handles the conic shape where, after
/// moving everything to one side, the polynomial is
/// `a * x^2 + (polynomial with no x) REL 0` with `a != 0`. Then
/// `x^2 REL' (-rest)/a`, and if the right side has a finite non-negative upper
/// bound `U`, we get `|x| <= sqrt(U)`, i.e. `x in [-sqrt(U), sqrt(U)]`. Returns
/// `None` when no sound bound can be derived.
fn bound_var_from_constraint(
    c: &MultiConstraint,
    x: TermId,
    box_bounds: &crate::HashMap<TermId, Interval>,
) -> Option<Interval> {
    // Only equalities and `<=/<` give an UPPER bound on x^2; `>=/>` give lower
    // bounds on x^2 (a hole around 0) which do not bound the box. Keep to the
    // upper-bounding relations for a sound outer box.
    if !matches!(c.rel, Rel::Eq | Rel::Le | Rel::Lt) {
        return None;
    }
    // Split poly into the x^2 coefficient (must be the ONLY x-monomial) and the
    // rest (no x). Reject if x appears in any other-degree monomial (x, x^3,
    // x*y, ...), which would make this isolation unsound.
    let mut a_sq = BigRational::zero();
    let mut rest = MultiPoly::zero();
    for (mono, coeff) in &c.poly.terms {
        let x_power = mono.iter().filter(|&&v| v == x).count();
        if x_power == 0 {
            rest.add_term(mono.clone(), coeff.clone());
        } else if x_power == 2 && mono.len() == 2 {
            // Pure x^2 monomial (both factors are x).
            a_sq += coeff;
        } else {
            // x appears coupled or at another power: not the clean conic shape.
            return None;
        }
    }
    if a_sq.is_zero() {
        return None;
    }
    // Interval of `rest` over the current box.
    let rest_iv = eval_poly_interval(&rest, box_bounds)?;
    // Constraint: a_sq*x^2 + rest REL 0  =>  x^2 REL'' (-rest)/a_sq.
    // For Eq:  x^2 = -rest/a_sq, so x^2 <= max((-rest)/a_sq).
    // For Le/Lt with a_sq>0: x^2 <= (-rest)/a_sq (use the sup of RHS).
    // We need a sound UPPER bound on x^2. Compute the interval of (-rest)/a_sq
    // and take its hi endpoint as U.
    let neg_rest = Interval {
        lo: negate_endpoint_to_lo(&rest_iv.hi),
        hi: negate_endpoint_to_hi(&rest_iv.lo),
    };
    let scaled = scale_interval(&neg_rest, &(BigRational::one() / &a_sq));
    // For a_sq < 0 the relation flips; scale_interval already handled the sign of
    // the bound by multiplying. But the DIRECTION of the inequality also flips
    // for Le/Lt when a_sq < 0, which would give a LOWER bound on x^2 (a hole),
    // not an upper bound. Only conclude an upper bound when a_sq > 0, or for Eq
    // (equality is direction-agnostic).
    if matches!(c.rel, Rel::Le | Rel::Lt) && a_sq.is_negative() {
        return None;
    }
    let u = match &scaled.hi {
        Endpoint::Finite(v, _) => v.clone(),
        _ => return None, // unbounded RHS: no box bound
    };
    if u.is_negative() {
        // x^2 <= U < 0 is impossible; the constraint is infeasible. Return an
        // empty-ish bound (lo > hi) so intersection makes the box empty — sound
        // (the UNSAT phases would also catch this; here we just stop searching).
        return Some(Interval {
            lo: Endpoint::Finite(BigRational::one(), true),
            hi: Endpoint::Finite(BigRational::zero(), true),
        });
    }
    // |x| <= sqrt(U). Use an exact rational sqrt when U is a perfect square;
    // otherwise round UP to a sound rational over-bound on sqrt(U).
    let bound = rational_sqrt_upper(&u);
    Some(Interval {
        lo: Endpoint::Finite(-(&bound), true),
        hi: Endpoint::Finite(bound, true),
    })
}

/// A SOUND rational upper bound on `sqrt(u)` for `u >= 0`: exact when `u` is a
/// perfect rational square, else the next rational with denominator
/// `WITNESS_MAX_DENOM` that is `>= sqrt(u)`. Always satisfies `result^2 >= u`.
fn rational_sqrt_upper(u: &BigRational) -> BigRational {
    if let Some(s) = exact_rational_sqrt(u) {
        return s;
    }
    // Find the smallest p/q (q = WITNESS_MAX_DENOM) with (p/q)^2 >= u.
    let q = BigInt::from(WITNESS_MAX_DENOM);
    let q_sq = BigRational::from_integer(&q * &q);
    // Need p^2 >= u * q^2  =>  p >= sqrt(u*q^2). Use integer ceil sqrt.
    let target = (u * &q_sq).ceil(); // a BigRational that is an integer value
    let target_int = target.numer() / target.denom();
    let p = integer_sqrt_ceil(&target_int);
    BigRational::new(p, q)
}

/// Smallest integer `>= sqrt(n)` for `n >= 0` (ceil of the integer square root).
fn integer_sqrt_ceil(n: &BigInt) -> BigInt {
    if n.is_zero() {
        return BigInt::zero();
    }
    // floor sqrt via the existing exact helper's binary search shape.
    let mut lo = BigInt::one();
    let mut hi = n.clone();
    let two = BigInt::from(2);
    let mut floor_sqrt = BigInt::one();
    while lo <= hi {
        let mid = (&lo + &hi) / &two;
        let sq = &mid * &mid;
        match sq.cmp(n) {
            std::cmp::Ordering::Equal => return mid,
            std::cmp::Ordering::Less => {
                floor_sqrt = mid.clone();
                lo = &mid + BigInt::one();
            }
            std::cmp::Ordering::Greater => hi = &mid - BigInt::one(),
        }
    }
    // Not a perfect square: ceil = floor + 1.
    floor_sqrt + BigInt::one()
}

/// Negate the (upper) endpoint of an interval to produce a LOWER endpoint of the
/// negated interval. `-(+inf) = -inf`, `-(finite v) = finite -v`.
pub(crate) fn negate_endpoint_to_lo(e: &Endpoint) -> Endpoint {
    match e {
        Endpoint::PosInf => Endpoint::NegInf,
        Endpoint::NegInf => Endpoint::PosInf,
        Endpoint::Finite(v, inc) => Endpoint::Finite(-v, *inc),
    }
}

/// Negate the (lower) endpoint of an interval to produce an UPPER endpoint of the
/// negated interval.
pub(crate) fn negate_endpoint_to_hi(e: &Endpoint) -> Endpoint {
    match e {
        Endpoint::NegInf => Endpoint::PosInf,
        Endpoint::PosInf => Endpoint::NegInf,
        Endpoint::Finite(v, inc) => Endpoint::Finite(-v, *inc),
    }
}

/// Scale an interval by a POSITIVE OR NEGATIVE rational, preserving soundness.
/// For a positive scalar the endpoints keep order; for a negative scalar they
/// swap. Infinity maps to infinity (with sign flip for negative scalars).
pub(crate) fn scale_interval(iv: &Interval, s: &BigRational) -> Interval {
    if s.is_zero() {
        return Interval::point(BigRational::zero());
    }
    let scale_ep = |e: &Endpoint| -> Endpoint {
        match e {
            Endpoint::Finite(v, inc) => Endpoint::Finite(v * s, *inc),
            Endpoint::PosInf => {
                if s.is_positive() {
                    Endpoint::PosInf
                } else {
                    Endpoint::NegInf
                }
            }
            Endpoint::NegInf => {
                if s.is_positive() {
                    Endpoint::NegInf
                } else {
                    Endpoint::PosInf
                }
            }
        }
    };
    if s.is_positive() {
        Interval {
            lo: scale_ep(&iv.lo),
            hi: scale_ep(&iv.hi),
        }
    } else {
        // Negative scalar swaps lo/hi.
        Interval {
            lo: scale_ep(&iv.hi),
            hi: scale_ep(&iv.lo),
        }
    }
}

/// Intersect two intervals, taking the TIGHTER endpoints. The result is a sound
/// box for the conjunction of both constraints. Inclusivity is conservative
/// (closed wins on ties), which only ever WIDENS the box — sound for a search
/// box that is re-verified downstream.
pub(crate) fn intersect_intervals(a: &Interval, b: &Interval) -> Interval {
    let lo = max_lo(&a.lo, &b.lo);
    let hi = min_hi(&a.hi, &b.hi);
    Interval { lo, hi }
}

/// The larger of two lower endpoints (tighter lower bound).
fn max_lo(a: &Endpoint, b: &Endpoint) -> Endpoint {
    match (a, b) {
        (Endpoint::NegInf, _) => b.clone(),
        (_, Endpoint::NegInf) => a.clone(),
        (Endpoint::PosInf, _) | (_, Endpoint::PosInf) => Endpoint::PosInf,
        (Endpoint::Finite(va, ia), Endpoint::Finite(vb, ib)) => {
            if va > vb {
                Endpoint::Finite(va.clone(), *ia)
            } else if vb > va {
                Endpoint::Finite(vb.clone(), *ib)
            } else {
                Endpoint::Finite(va.clone(), *ia || *ib)
            }
        }
    }
}

/// The smaller of two upper endpoints (tighter upper bound).
fn min_hi(a: &Endpoint, b: &Endpoint) -> Endpoint {
    match (a, b) {
        (Endpoint::PosInf, _) => b.clone(),
        (_, Endpoint::PosInf) => a.clone(),
        (Endpoint::NegInf, _) | (_, Endpoint::NegInf) => Endpoint::NegInf,
        (Endpoint::Finite(va, ia), Endpoint::Finite(vb, ib)) => {
            if va < vb {
                Endpoint::Finite(va.clone(), *ia)
            } else if vb < va {
                Endpoint::Finite(vb.clone(), *ib)
            } else {
                Endpoint::Finite(va.clone(), *ia || *ib)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    fn ratfrac(n: i64, d: i64) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }

    /// Build a UniPoly from ascending coefficients.
    fn poly(coeffs: &[i64]) -> UniPoly {
        let mut p = UniPoly {
            coeffs: coeffs.iter().map(|&c| rat(c)).collect(),
        };
        p.normalize();
        p
    }

    #[test]
    fn test_eval_and_derivative() {
        // p = x^2 - 2
        let p = poly(&[-2, 0, 1]);
        assert_eq!(p.eval(&rat(0)), rat(-2));
        assert_eq!(p.eval(&rat(2)), rat(2));
        // p' = 2x
        let dp = p.derivative();
        assert_eq!(dp.coeffs, vec![rat(0), rat(2)]);
    }

    /// Helper: number of real roots for a (possibly non-square-free) polynomial
    /// by isolating its square-free part.
    fn roots_of(p: &UniPoly) -> Vec<RootMarker> {
        let sf = square_free_part(p).unwrap();
        isolate_roots(&sf).unwrap()
    }

    /// Helper: is `r` a marker located exactly at the rational `target`?
    fn marker_is(m: &RootMarker, target: &BigRational) -> bool {
        matches!(m, RootMarker::Rational(r) if r == target)
    }

    #[test]
    fn test_linear_root() {
        // 2x + 6 = 0 => x = -3
        let p = poly(&[6, 2]);
        let roots = isolate_roots(&p).unwrap();
        assert_eq!(roots.len(), 1);
        assert!(marker_is(&roots[0], &rat(-3)));
    }

    #[test]
    fn test_quadratic_rational_roots() {
        // x^2 - 4 = 0 => x = -2, 2
        let p = poly(&[-4, 0, 1]);
        let roots = isolate_roots(&p).unwrap();
        assert_eq!(roots.len(), 2);
        assert!(marker_is(&roots[0], &rat(-2)));
        assert!(marker_is(&roots[1], &rat(2)));
    }

    #[test]
    fn test_quadratic_double_root() {
        // x^2 - 2x + 1 = (x-1)^2 => x = 1 (double). Square-free part is (x-1).
        let p = poly(&[1, -2, 1]);
        let roots = roots_of(&p);
        assert_eq!(roots.len(), 1);
        assert!(marker_is(&roots[0], &rat(1)));
    }

    #[test]
    fn test_quadratic_no_real_roots() {
        // x^2 + 1 => no real roots
        let p = poly(&[1, 0, 1]);
        let roots = isolate_roots(&p).unwrap();
        assert!(roots.is_empty());
    }

    #[test]
    fn test_quadratic_irrational_roots_are_intervals() {
        // x^2 - 2 => roots ±sqrt(2). Both irrational => isolating intervals,
        // each containing exactly the true root and with non-root endpoints.
        let p = poly(&[-2, 0, 1]);
        let roots = isolate_roots(&p).unwrap();
        assert_eq!(roots.len(), 2, "expected two markers for ±sqrt(2)");
        for m in &roots {
            match m {
                RootMarker::Interval(lo, hi) => {
                    assert!(lo < hi);
                    // p has exactly one root in (lo, hi): the sign flips across.
                    assert!(
                        rational_sign(&p.eval(lo)) != rational_sign(&p.eval(hi)),
                        "isolating interval must bracket a sign change"
                    );
                }
                RootMarker::Rational(_) => panic!("sqrt(2) is irrational"),
            }
        }
        // Ordered: first marker is the negative root, second the positive.
        assert!(roots[0].locator() < roots[1].locator());
    }

    #[test]
    fn test_exact_rational_sqrt() {
        assert_eq!(exact_rational_sqrt(&rat(4)), Some(rat(2)));
        assert_eq!(exact_rational_sqrt(&rat(9)), Some(rat(3)));
        assert_eq!(exact_rational_sqrt(&ratfrac(1, 4)), Some(ratfrac(1, 2)));
        assert_eq!(exact_rational_sqrt(&rat(2)), None);
        assert_eq!(exact_rational_sqrt(&rat(0)), Some(rat(0)));
        assert_eq!(exact_rational_sqrt(&rat(-1)), None);
    }

    #[test]
    fn test_cubic_roots_via_sturm() {
        // (x-1)(x-2)(x-3) = x^3 - 6x^2 + 11x - 6
        let p = poly(&[-6, 11, -6, 1]);
        let roots = isolate_roots(&p).unwrap();
        assert_eq!(roots.len(), 3, "cubic with three real roots");
        // Each true root is rational and should be recovered exactly.
        assert!(marker_is(&roots[0], &rat(1)));
        assert!(marker_is(&roots[1], &rat(2)));
        assert!(marker_is(&roots[2], &rat(3)));
    }

    #[test]
    fn test_cubic_one_real_root() {
        // x^3 + x + 1: one real root near -0.68, two complex.
        let p = poly(&[1, 1, 0, 1]);
        let roots = isolate_roots(&p).unwrap();
        assert_eq!(roots.len(), 1, "x^3 + x + 1 has exactly one real root");
        // The isolating interval must bracket the true root near -0.68.
        match &roots[0] {
            RootMarker::Interval(lo, hi) => {
                assert!(*lo < rat(0) && *hi <= rat(0));
                assert!(p.eval(lo) * p.eval(hi) < rat(0), "interval brackets root");
            }
            RootMarker::Rational(_) => panic!("root is irrational"),
        }
    }

    #[test]
    fn test_sturm_sign_variations_endpoints() {
        // x^2 - 2, square-free; V(-B) - V(B) should equal 2.
        let p = poly(&[-2, 0, 1]);
        let sf = square_free_part(&p).unwrap();
        let seq = sturm_sequence(&sf);
        let bound = cauchy_bound(&sf);
        let count = sturm_count(&seq, &(-&bound), &bound);
        assert_eq!(count, 2);
    }

    #[test]
    fn test_build_cells_empty() {
        let cells = build_cells(&[]);
        assert_eq!(cells.len(), 1);
        match &cells[0] {
            Cell::Open(r) => assert_eq!(*r, rat(0)),
            _ => panic!("expected single open cell"),
        }
    }

    #[test]
    fn test_build_cells_one_rational_root() {
        // root at 0 => cells (-inf,0), {0}, (0,+inf)
        let cells = build_cells(&[RootMarker::Rational(rat(0))]);
        assert_eq!(cells.len(), 3);
        match &cells[0] {
            Cell::Open(r) => assert!(*r < rat(0)),
            _ => panic!(),
        }
        match &cells[1] {
            Cell::Point(r) => assert_eq!(*r, rat(0)),
            _ => panic!(),
        }
        match &cells[2] {
            Cell::Open(r) => assert!(*r > rat(0)),
            _ => panic!(),
        }
    }

    #[test]
    fn test_square_free_part_removes_multiplicity() {
        // (x-1)^2 (x-2) = x^3 -4x^2 +5x -2; square-free part is (x-1)(x-2).
        let p = poly(&[-2, 5, -4, 1]);
        let sf = square_free_part(&p).unwrap();
        // sf should have degree 2 and roots at 1 and 2.
        assert_eq!(sf.degree(), Some(2));
        assert!(sf.eval(&rat(1)).is_zero());
        assert!(sf.eval(&rat(2)).is_zero());
    }

    // -- End-to-end single-variable decisions --

    /// Build a UniConstraint `poly REL 0` from ascending coeffs.
    fn constr(coeffs: &[i64], rel: Rel) -> UniConstraint {
        UniConstraint {
            poly: poly(coeffs),
            rel,
        }
    }

    fn witness_value(r: SingleVarResult) -> Option<BigRational> {
        match r {
            SingleVarResult::Witness(w) => Some(w),
            _ => None,
        }
    }

    #[test]
    fn test_decide_x2_lt_2_sat_rational_witness() {
        // x^2 < 2  =>  x^2 - 2 < 0. Witness 0 works (0 - 2 < 0).
        let c = constr(&[-2, 0, 1], Rel::Lt);
        let w = witness_value(decide_single_variable(&[c])).expect("sat");
        // Verify the witness exactly satisfies x^2 < 2.
        assert!(&w * &w < rat(2));
    }

    #[test]
    fn test_decide_x2_gt_2_sat_rational_witness() {
        // x^2 > 2  =>  x^2 - 2 > 0. A rational witness like 2 (4>2) exists.
        let c = constr(&[-2, 0, 1], Rel::Gt);
        let w = witness_value(decide_single_variable(&[c])).expect("sat");
        assert!(&w * &w > rat(2));
    }

    #[test]
    fn test_decide_conjunction_unsat() {
        // x^2 > 2 AND x^2 < 1: empty.
        let c1 = constr(&[-2, 0, 1], Rel::Gt);
        let c2 = constr(&[-1, 0, 1], Rel::Lt);
        assert!(matches!(
            decide_single_variable(&[c1, c2]),
            SingleVarResult::Empty
        ));
    }

    #[test]
    fn test_decide_x2_lt_0_unsat() {
        // x^2 < 0: empty over R.
        let c = constr(&[0, 0, 1], Rel::Lt);
        assert!(matches!(
            decide_single_variable(&[c]),
            SingleVarResult::Empty
        ));
    }

    #[test]
    fn test_decide_x2_ge_0_sat() {
        // x^2 >= 0: always true; any witness works.
        let c = constr(&[0, 0, 1], Rel::Ge);
        let w = witness_value(decide_single_variable(&[c])).expect("sat");
        assert!(&w * &w >= rat(0));
    }

    #[test]
    fn test_decide_x2_eq_2_irrational_sat_not_unsat() {
        // x^2 = 2: only irrational solutions. MUST NOT be reported Empty
        // (that would be a wrong UNSAT). Should be IrrationalSat.
        let c = constr(&[-2, 0, 1], Rel::Eq);
        match decide_single_variable(&[c]) {
            SingleVarResult::IrrationalSat(alg) => {
                // The witness is a root of x^2 - 2 with a certified interval.
                assert_eq!(
                    alg.poly_coeffs(),
                    vec![(-2).into(), 0.into(), 1.into()],
                    "defining polynomial must be x^2 - 2"
                );
            }
            _ => panic!("x^2 = 2 is satisfiable (at sqrt 2); must never be Empty"),
        }
    }

    #[test]
    fn test_decide_x2_le_2_and_ge_2_irrational_sat() {
        // x^2 <= 2 AND x^2 >= 2  <=>  x^2 = 2: irrational-only solution.
        let c1 = constr(&[-2, 0, 1], Rel::Le);
        let c2 = constr(&[-2, 0, 1], Rel::Ge);
        assert!(matches!(
            decide_single_variable(&[c1, c2]),
            SingleVarResult::IrrationalSat(_)
        ));
    }

    #[test]
    fn test_decide_eq_rational_root_sat() {
        // x^2 = 4 => x in {-2, 2}. Rational witness exists.
        let c = constr(&[-4, 0, 1], Rel::Eq);
        let w = witness_value(decide_single_variable(&[c])).expect("sat");
        assert_eq!(&w * &w, rat(4));
    }

    #[test]
    fn test_decide_eq_rational_root_and_strict_ineq_sat() {
        // Regression: x^2 = 4 AND x > 0. The combined product polynomial is
        // (x^2-4)*x = x^3 - 4x, whose CONSTANT TERM IS ZERO (the `x > 0`
        // constraint contributes the factor `x`). The nonzero rational root
        // x = 2 must still be recovered as an exact Rational marker so the
        // closed cell at 2 yields a rational witness — previously the zero
        // constant term made the rational-root recovery miss it and the root
        // was mislabeled as an irrational isolating interval, yielding `unknown`.
        let eq = constr(&[-4, 0, 1], Rel::Eq); // x^2 - 4 = 0
        let gt = constr(&[0, 1], Rel::Gt); // x > 0
        let w = witness_value(decide_single_variable(&[eq, gt])).expect("sat");
        // Witness must satisfy BOTH constraints exactly.
        assert_eq!(&w * &w, rat(4));
        assert!(w > rat(0));
        assert_eq!(w, rat(2));

        // Mirror: x^2 = 4 AND x < 0 picks the negative rational root -2.
        let eq2 = constr(&[-4, 0, 1], Rel::Eq);
        let lt = constr(&[0, 1], Rel::Lt); // x < 0
        let w2 = witness_value(decide_single_variable(&[eq2, lt])).expect("sat");
        assert_eq!(w2, rat(-2));
    }

    #[test]
    fn test_decide_eq_irrational_root_and_strict_ineq_stays_irrational() {
        // Soundness guard for the irrational trap: x^2 = 2 AND x > 0 has the
        // single solution sqrt(2), which is irrational. Even though the combined
        // poly (x^2-2)*x = x^3 - 2x also has a zero constant term, NO rational
        // root satisfies the equality, so this must report IrrationalSat (=>
        // `unknown` upstream), never a (nonexistent) rational Witness and never
        // a wrong Empty/UNSAT.
        let eq = constr(&[-2, 0, 1], Rel::Eq); // x^2 - 2 = 0
        let gt = constr(&[0, 1], Rel::Gt); // x > 0
        match decide_single_variable(&[eq, gt]) {
            SingleVarResult::IrrationalSat(alg) => {
                // z3-parity witness: the POSITIVE root of x^2 - 2 (index 2),
                // using the vanishing constraint FACTOR as the defining
                // polynomial, not the combined product x^3 - 2x.
                assert_eq!(alg.to_smtlib(), "(root-obj (+ (^ x 2) (- 2)) 2)");
            }
            _ => panic!("x^2 = 2 AND x > 0 is satisfiable only at irrational sqrt(2)"),
        }
    }

    #[test]
    fn test_decide_eq_rational_root_strict_ineq_excludes_all_roots_unsat() {
        // x^2 = 4 AND x > 2: roots are exactly {-2, 2}; neither is > 2, so the
        // feasible set over R is empty => Empty (UNSAT). Guards against the fix
        // over-eagerly admitting a root that the strict inequality excludes.
        let eq = constr(&[-4, 0, 1], Rel::Eq); // x^2 - 4 = 0
        let gt = constr(&[-2, 1], Rel::Gt); // x - 2 > 0
        assert!(matches!(
            decide_single_variable(&[eq, gt]),
            SingleVarResult::Empty
        ));
    }

    #[test]
    fn test_try_rational_root_in_zero_constant_term() {
        // Unit-level guard on the recovery routine: p = x^3 - 4x has a zero
        // constant term but a nonzero rational root at 2. Recovery inside a
        // tight isolating interval around 2 must return exactly 2.
        let p = poly(&[0, -4, 0, 1]); // x^3 - 4x
        let lo = ratfrac(3, 2); // 1.5
        let hi = ratfrac(5, 2); // 2.5  (isolates the root x = 2)
        assert_eq!(try_rational_root_in(&p, &lo, &hi), Some(rat(2)));
    }

    #[test]
    fn test_decide_gt_sqrt2_and_lt_sqrt3() {
        // x^2 > 2 AND x^2 < 3: the band (sqrt2, sqrt3) and its mirror contain
        // rationals (e.g. 1.5 => 2.25). Must be SAT with a rational witness.
        let c1 = constr(&[-2, 0, 1], Rel::Gt);
        let c2 = constr(&[-3, 0, 1], Rel::Lt);
        let w = witness_value(decide_single_variable(&[c1, c2])).expect("sat");
        let sq = &w * &w;
        assert!(sq > rat(2) && sq < rat(3));
    }

    // -- Multivariate linear-equality substitution --

    fn tid(n: u32) -> TermId {
        TermId(n)
    }

    #[test]
    fn test_multipoly_substitute_linear_into_quadratic() {
        // p = x^2 + y^2 - 5, substitute y := 2 (constant LinExpr) gives
        // x^2 + 4 - 5 = x^2 - 1, a univariate poly in x.
        let x = tid(1);
        let y = tid(2);
        // Build x^2 + y^2 - 5.
        let mut p = MultiPoly::zero();
        p.add_term(vec![x, x], rat(1));
        p.add_term(vec![y, y], rat(1));
        p.add_term(Vec::new(), rat(-5));
        let repl = LinExpr {
            constant: rat(2),
            terms: Vec::new(),
        };
        let q = p.substitute(y, &repl);
        // q must mention only x.
        assert_eq!(q.variables(), vec![x]);
        let uni = q.to_unipoly().expect("univariate");
        // x^2 - 1: roots at +/-1.
        assert_eq!(uni.eval(&rat(1)), rat(0));
        assert_eq!(uni.eval(&rat(-1)), rat(0));
        assert_eq!(uni.eval(&rat(0)), rat(-1));
    }

    #[test]
    fn test_multipoly_substitute_linear_expr() {
        // p = y, substitute y := 2*x + 1. Result is 2x + 1 (linear in x).
        let x = tid(1);
        let y = tid(2);
        let p = MultiPoly::var(y);
        let repl = LinExpr {
            constant: rat(1),
            terms: vec![(x, rat(2))],
        };
        let q = p.substitute(y, &repl);
        let (c, lin) = q.as_linear().expect("linear");
        assert_eq!(c, rat(1));
        assert_eq!(lin, vec![(x, rat(2))]);
    }

    #[test]
    fn test_resolve_substitutions_chain() {
        // z = 2 ; y = z + 1. After resolution y must be the constant 3.
        let y = tid(1);
        let z = tid(2);
        let raw = vec![
            (
                z,
                LinExpr {
                    constant: rat(2),
                    terms: Vec::new(),
                },
            ),
            (
                y,
                LinExpr {
                    constant: rat(1),
                    terms: vec![(z, rat(1))],
                },
            ),
        ];
        let resolved = resolve_substitutions(&raw).expect("resolves");
        // y's resolved expression must be constant 3, with no var references.
        let y_expr = &resolved.iter().find(|(v, _)| *v == y).unwrap().1;
        assert!(y_expr.terms.is_empty());
        assert_eq!(y_expr.constant, rat(3));
        // Evaluating with z already in the model.
        let model = vec![(z, rat(2))];
        assert_eq!(eval_linexpr(y_expr, &model), Some(rat(3)));
    }

    #[test]
    fn test_resolve_substitutions_cycle_bails() {
        // y = x ; x = y is a cycle. Must return None (=> Unknown upstream).
        let x = tid(1);
        let y = tid(2);
        let raw = vec![
            (
                y,
                LinExpr {
                    constant: rat(0),
                    terms: vec![(x, rat(1))],
                },
            ),
            (
                x,
                LinExpr {
                    constant: rat(0),
                    terms: vec![(y, rat(1))],
                },
            ),
        ];
        assert!(resolve_substitutions(&raw).is_none());
    }

    #[test]
    fn test_resolve_substitutions_self_reference_bails() {
        // x = x + 1 (or x = 2x) is degenerate/self-referential. Must bail.
        let x = tid(1);
        let raw = vec![(
            x,
            LinExpr {
                constant: rat(1),
                terms: vec![(x, rat(1))],
            },
        )];
        assert!(resolve_substitutions(&raw).is_none());
    }

    #[test]
    fn test_linexpr_eval_missing_var_is_none() {
        // Evaluating a LinExpr whose variable is absent from the model => None.
        let x = tid(1);
        let expr = LinExpr {
            constant: rat(0),
            terms: vec![(x, rat(1))],
        };
        assert_eq!(eval_linexpr(&expr, &[]), None);
        assert_eq!(eval_linexpr(&expr, &[(x, rat(7))]), Some(rat(7)));
    }

    // ---- is_int fragment helper tests (#9139) ----

    #[test]
    fn test_interval_contains_integer_closed_open() {
        // [0, 1] contains 0 and 1.
        assert!(interval_contains_integer(&rat(0), true, &rat(1), true));
        // (0, 1) contains no integer.
        assert!(!interval_contains_integer(&rat(0), false, &rat(1), false));
        // (0, 1] contains 1.
        assert!(interval_contains_integer(&rat(0), false, &rat(1), true));
        // [0, 1) contains 0.
        assert!(interval_contains_integer(&rat(0), true, &rat(1), false));
        // (1/3, 2/3) contains no integer.
        assert!(!interval_contains_integer(
            &ratfrac(1, 3),
            false,
            &ratfrac(2, 3),
            false
        ));
        // [1/2, 5/2] contains 1 and 2.
        assert!(interval_contains_integer(
            &ratfrac(1, 2),
            true,
            &ratfrac(5, 2),
            true
        ));
        // Degenerate closed point [2, 2] contains 2.
        assert!(interval_contains_integer(&rat(2), true, &rat(2), true));
        // Degenerate open point (2, 2) contains nothing.
        assert!(!interval_contains_integer(&rat(2), false, &rat(2), false));
        // Endpoint integer excluded on a strict lower side: (0, 1/2) -> none.
        assert!(!interval_contains_integer(
            &rat(0),
            false,
            &ratfrac(1, 2),
            false
        ));
    }

    #[test]
    fn test_point_in_interval() {
        let lo = Some((rat(0), false)); // x > 0
        let hi = Some((rat(2), true)); // x <= 2
        assert!(!point_in_interval(&rat(0), &lo, &hi)); // excluded (strict)
        assert!(point_in_interval(&ratfrac(1, 2), &lo, &hi));
        assert!(point_in_interval(&rat(2), &lo, &hi)); // included (<=)
        assert!(!point_in_interval(&rat(3), &lo, &hi));
        // Unbounded below.
        assert!(point_in_interval(&rat(-100), &None, &hi));
    }

    #[test]
    fn test_update_interval_tightening() {
        let mut lo = None;
        let mut hi = None;
        update_interval(&mut lo, &mut hi, Rel::Gt, &rat(0)); // x > 0
        update_interval(&mut lo, &mut hi, Rel::Lt, &rat(5)); // x < 5
        update_interval(&mut lo, &mut hi, Rel::Ge, &rat(1)); // x >= 1 (tighter lower)
        update_interval(&mut lo, &mut hi, Rel::Le, &rat(3)); // x <= 3 (tighter upper)
        assert_eq!(lo, Some((rat(1), true)));
        assert_eq!(hi, Some((rat(3), true)));
        // A looser bound must NOT loosen the interval.
        update_interval(&mut lo, &mut hi, Rel::Gt, &rat(-10));
        assert_eq!(lo, Some((rat(1), true)));
        // Same value, strict vs non-strict: strict is tighter.
        update_interval(&mut lo, &mut hi, Rel::Gt, &rat(1));
        assert_eq!(lo, Some((rat(1), false)));
    }

    #[test]
    fn test_affine_arithmetic() {
        // a = 2x + 1
        let a = Affine {
            slope: rat(2),
            intercept: rat(1),
        };
        // b = -x + 3
        let b = Affine {
            slope: rat(-1),
            intercept: rat(3),
        };
        let sum = affine_add(&a, &b); // x + 4
        assert_eq!(sum.slope, rat(1));
        assert_eq!(sum.intercept, rat(4));
        let neg = affine_neg(&a); // -2x - 1
        assert_eq!(neg.slope, rat(-2));
        assert_eq!(neg.intercept, rat(-1));
        let scaled = affine_mul_const(&a, &ratfrac(1, 2)); // x + 1/2
        assert_eq!(scaled.slope, rat(1));
        assert_eq!(scaled.intercept, ratfrac(1, 2));
        // eval: a(3) = 7.
        assert_eq!(a.eval(&rat(3)), rat(7));
        assert!(!a.is_constant());
        assert!(Affine::constant(rat(4)).is_constant());
    }

    #[test]
    fn test_mirror_rel() {
        assert_eq!(mirror_rel(Rel::Lt), Rel::Gt);
        assert_eq!(mirror_rel(Rel::Le), Rel::Ge);
        assert_eq!(mirror_rel(Rel::Gt), Rel::Lt);
        assert_eq!(mirror_rel(Rel::Ge), Rel::Le);
        assert_eq!(mirror_rel(Rel::Eq), Rel::Eq);
        assert_eq!(mirror_rel(Rel::Ne), Rel::Ne);
    }

    #[test]
    fn test_merge_opt_var() {
        let x = tid(1);
        let y = tid(2);
        assert_eq!(merge_opt_var(None, None), Some(None));
        assert_eq!(merge_opt_var(Some(x), None), Some(Some(x)));
        assert_eq!(merge_opt_var(None, Some(y)), Some(Some(y)));
        assert_eq!(merge_opt_var(Some(x), Some(x)), Some(Some(x)));
        // Two distinct variables => failure (would be bivariate).
        assert_eq!(merge_opt_var(Some(x), Some(y)), None);
    }

    #[test]
    fn test_interval_sample_avoids_excluded() {
        // (0, 2) excluding {1}: a sample must be in (0,2) and not equal 1.
        let lo = Some((rat(0), false));
        let hi = Some((rat(2), false));
        let s = interval_sample(&lo, &hi, &[rat(1)]).unwrap();
        assert!(point_in_interval(&s, &lo, &hi));
        assert_ne!(s, rat(1));
    }

    // -- Interval-propagation UNSAT pre-phase --

    fn fin(v: i64, inc: bool) -> Endpoint {
        Endpoint::Finite(rat(v), inc)
    }

    fn iv(lo: Endpoint, hi: Endpoint) -> Interval {
        Interval { lo, hi }
    }

    #[test]
    fn test_interval_even_power_straddle_zero() {
        // [-3, 2]^2 = [0, 9]: even power over an interval straddling 0.
        let i = iv(fin(-3, true), fin(2, true));
        let p = i.pow(2);
        assert_eq!(p.lo, Endpoint::Finite(rat(0), true));
        assert_eq!(p.hi, Endpoint::Finite(rat(9), true));
    }

    #[test]
    fn test_interval_even_power_no_straddle() {
        // [2, +inf)^2 = [4, +inf): both endpoints positive, even power monotone.
        let i = iv(fin(2, false), Endpoint::PosInf);
        let p = i.pow(2);
        // 2 is open, so 4 is open (the infimum 4 is not attained).
        assert_eq!(p.lo, Endpoint::Finite(rat(4), false));
        assert_eq!(p.hi, Endpoint::PosInf);
    }

    #[test]
    fn test_interval_even_power_whole_line() {
        // (-inf, +inf)^2 = [0, +inf): the canonical sum-of-squares non-negativity.
        let p = Interval::whole().pow(2);
        assert_eq!(p.lo, Endpoint::Finite(rat(0), true));
        assert_eq!(p.hi, Endpoint::PosInf);
    }

    #[test]
    fn test_interval_odd_power_monotone() {
        // [-2, 3]^3 = [-8, 27].
        let i = iv(fin(-2, true), fin(3, true));
        let p = i.pow(3);
        assert_eq!(p.lo, Endpoint::Finite(rat(-8), true));
        assert_eq!(p.hi, Endpoint::Finite(rat(27), true));
    }

    #[test]
    fn test_interval_mul_positive_boxes() {
        // (0,1) * (0,1) = (0,1): all corner products lie in [0,1], open ends.
        let a = iv(fin(0, false), fin(1, false));
        let b = iv(fin(0, false), fin(1, false));
        let p = a.mul(&b);
        assert_eq!(p.lo, Endpoint::Finite(rat(0), false));
        assert_eq!(p.hi, Endpoint::Finite(rat(1), false));
    }

    #[test]
    fn test_interval_mul_two_negatives_positive() {
        // (-inf,0) * (-inf,0): product of two negatives is positive.
        // Here we use [-3,-2] * [-3,-2] = [4, 9].
        let a = iv(fin(-3, true), fin(-2, true));
        let b = iv(fin(-3, true), fin(-2, true));
        let p = a.mul(&b);
        assert_eq!(p.lo, Endpoint::Finite(rat(4), true));
        assert_eq!(p.hi, Endpoint::Finite(rat(9), true));
    }

    #[test]
    fn test_interval_mul_zero_times_unbounded() {
        // [0,0] * (-inf,+inf) = [0,0] (sound: 0 annihilates everything).
        let a = Interval::point(rat(0));
        let p = a.mul(&Interval::whole());
        assert_eq!(p.lo, Endpoint::Finite(rat(0), true));
        assert_eq!(p.hi, Endpoint::Finite(rat(0), true));
    }

    #[test]
    fn test_interval_mul_open_factor_times_zero_point_is_closed_zero() {
        // REGRESSION for the reverted wrong-UNSAT. x in (0,1) OPEN times y in
        // [0,0] CLOSED: the product is identically 0 (0 annihilates the whole
        // open range of x), so the value range is the CLOSED point [0,0] — 0 is
        // ATTAINED. The buggy `ia && ib` inclusivity produced an OPEN [0,0]
        // that excluded 0, making `x*y = 0` look infeasible (wrong UNSAT).
        let x = iv(fin(0, false), fin(1, false)); // (0, 1)
        let y = Interval::point(rat(0)); // [0, 0]
        let p = x.mul(&y);
        assert_eq!(
            p.lo,
            Endpoint::Finite(rat(0), true),
            "0 must be attained (closed)"
        );
        assert_eq!(
            p.hi,
            Endpoint::Finite(rat(0), true),
            "0 must be attained (closed)"
        );
        // `x*y = 0` is FEASIBLE (0 in the closed point) -> NOT unsat.
        assert!(!constraint_is_infeasible(Rel::Eq, &p));
        // `x*y != 0` IS infeasible (the only value is the attained 0).
        assert!(constraint_is_infeasible(Rel::Ne, &p));
        // The product is also feasible for <=, >=, <, >: it is exactly {0}.
        assert!(!constraint_is_infeasible(Rel::Le, &p)); // 0 <= 0 holds
        assert!(!constraint_is_infeasible(Rel::Ge, &p)); // 0 >= 0 holds
                                                         // `x*y < 0` and `x*y > 0` ARE infeasible (only value is 0).
        assert!(constraint_is_infeasible(Rel::Lt, &p));
        assert!(constraint_is_infeasible(Rel::Gt, &p));
    }

    #[test]
    fn test_interval_mul_mixed_sign_open_factor_times_zero_point() {
        // x in (-1, 1) OPEN straddling 0 times y in [0,0]: product still the
        // closed point [0,0] (every corner annihilated by the closed 0 factor).
        let x = iv(fin(-1, false), fin(1, false));
        let y = Interval::point(rat(0));
        let p = x.mul(&y);
        assert_eq!(p.lo, Endpoint::Finite(rat(0), true));
        assert_eq!(p.hi, Endpoint::Finite(rat(0), true));
        assert!(!constraint_is_infeasible(Rel::Eq, &p));
    }

    #[test]
    fn test_constraint_infeasible_lt_when_nonneg() {
        // poly in [3, +inf): `poly < 0` is impossible.
        let i = iv(fin(3, false), Endpoint::PosInf);
        assert!(constraint_is_infeasible(Rel::Lt, &i));
        // `poly <= 0` also impossible (all > 0).
        assert!(constraint_is_infeasible(Rel::Le, &i));
        // `poly = 0` impossible (0 not in interval).
        assert!(constraint_is_infeasible(Rel::Eq, &i));
        // `poly > 0` is FEASIBLE (not infeasible).
        assert!(!constraint_is_infeasible(Rel::Gt, &i));
    }

    #[test]
    fn test_constraint_feasible_straddling_zero() {
        // poly in (-1, 3): no relation is provably infeasible.
        let i = iv(fin(-1, false), fin(3, false));
        for rel in [Rel::Lt, Rel::Le, Rel::Gt, Rel::Ge, Rel::Eq, Rel::Ne] {
            assert!(
                !constraint_is_infeasible(rel, &i),
                "rel {rel:?} must be feasible over (-1, 3)"
            );
        }
    }

    #[test]
    fn test_constraint_lt_open_zero_lower_bound() {
        // poly in (0, +inf): `poly < 0` is impossible (every value > 0 >= 0),
        // and `poly <= 0` is impossible too.
        let i = iv(fin(0, false), Endpoint::PosInf);
        assert!(constraint_is_infeasible(Rel::Lt, &i));
        assert!(constraint_is_infeasible(Rel::Le, &i));
        // But poly = 0 is NOT provably impossible: 0 is a limit point. Our
        // contains_zero treats an open 0 endpoint as NOT containing 0, so we
        // would report Eq infeasible. That is still SOUND for `Eq` because the
        // value range is open at 0 (0 is never attained), so `poly = 0` truly
        // cannot hold. Confirm.
        assert!(constraint_is_infeasible(Rel::Eq, &i));
    }

    #[test]
    fn test_constraint_ne_only_zero_point() {
        // poly in [0,0]: `poly != 0` is impossible.
        let i = Interval::point(rat(0));
        assert!(constraint_is_infeasible(Rel::Ne, &i));
        // poly in [0, 1]: `poly != 0` is FEASIBLE (1 != 0).
        let j = iv(fin(0, true), fin(1, true));
        assert!(!constraint_is_infeasible(Rel::Ne, &j));
    }

    #[test]
    fn test_eval_poly_interval_sum_of_squares() {
        // x^2 + y^2 + 1 over the whole box: interval [1, +inf), so `< 0` (i.e.
        // poly with a -? no) — here we directly build x^2 + y^2 + 1 and check
        // its interval is [1, +inf).
        let x = tid(1);
        let y = tid(2);
        let mut p = MultiPoly::zero();
        p.add_term(vec![x, x], rat(1));
        p.add_term(vec![y, y], rat(1));
        p.add_term(Vec::new(), rat(1));
        let bounds: crate::HashMap<TermId, Interval> = crate::HashMap::default();
        let interval = eval_poly_interval(&p, &bounds).unwrap();
        assert_eq!(interval.lo, Endpoint::Finite(rat(1), true));
        assert_eq!(interval.hi, Endpoint::PosInf);
        // `poly < 0` is impossible.
        assert!(constraint_is_infeasible(Rel::Lt, &interval));
    }

    #[test]
    fn test_eval_poly_interval_xy_minus_one_over_unit_box() {
        // (x*y - 1) over x,y in (0,1): xy in (0,1), so xy-1 in (-1,0). The
        // dependency-free interval is a sound over-approximation, and `xy-1 > 0`
        // (i.e. xy>1) is correctly refuted (interval hi = 0 open <= 0).
        let x = tid(1);
        let y = tid(2);
        let mut p = MultiPoly::zero();
        p.add_term(vec![x, y], rat(1));
        p.add_term(Vec::new(), rat(-1));
        let bounds: crate::HashMap<TermId, Interval> = {
            let mut b = crate::HashMap::default();
            b.insert(x, iv(fin(0, false), fin(1, false)));
            b.insert(y, iv(fin(0, false), fin(1, false)));
            b
        };
        let interval = eval_poly_interval(&p, &bounds).unwrap();
        // xy in (0,1) -> xy-1 in (-1, 0), upper endpoint 0 (open).
        assert_eq!(interval.lo, Endpoint::Finite(rat(-1), false));
        assert_eq!(interval.hi, Endpoint::Finite(rat(0), false));
        // `xy - 1 > 0` is impossible over the unit box (UNSAT for xy>1).
        assert!(constraint_is_infeasible(Rel::Gt, &interval));
    }

    #[test]
    fn test_collect_variable_bounds_open_and_closed() {
        // x > 2  ->  x in (2, +inf) ;  y <= 5  ->  y in (-inf, 5].
        let x = tid(1);
        let y = tid(2);
        // Constraint x - 2 > 0.
        let mut px = MultiPoly::zero();
        px.add_term(vec![x], rat(1));
        px.add_term(Vec::new(), rat(-2));
        // Constraint y - 5 <= 0.
        let mut py = MultiPoly::zero();
        py.add_term(vec![y], rat(1));
        py.add_term(Vec::new(), rat(-5));
        let cons = vec![
            MultiConstraint {
                poly: px,
                rel: Rel::Gt,
            },
            MultiConstraint {
                poly: py,
                rel: Rel::Le,
            },
        ];
        let bounds = collect_variable_bounds(&cons);
        let bx = bounds.get(&x).unwrap();
        assert_eq!(bx.lo, Endpoint::Finite(rat(2), false));
        assert_eq!(bx.hi, Endpoint::PosInf);
        let by = bounds.get(&y).unwrap();
        assert_eq!(by.lo, Endpoint::NegInf);
        assert_eq!(by.hi, Endpoint::Finite(rat(5), true));
    }

    // ---- Sum-of-squares / quadratic-form positivity (try_sos_unsat) ----

    #[test]
    fn test_matrix_is_psd_identity_and_perfect_square() {
        // Identity is PSD.
        let id = vec![vec![rat(1), rat(0)], vec![rat(0), rat(1)]];
        assert!(matrix_is_psd(&id));
        // [[1,1],[1,1]] = (x+y)^2 form is PSD (rank 1, det 0).
        let sq = vec![vec![rat(1), rat(1)], vec![rat(1), rat(1)]];
        assert!(matrix_is_psd(&sq));
        // Negated identity is NOT PSD.
        let neg = vec![vec![rat(-1), rat(0)], vec![rat(0), rat(-1)]];
        assert!(!matrix_is_psd(&neg));
        // Indefinite x^2 - y^2: [[1,0],[0,-1]] not PSD.
        let indef = vec![vec![rat(1), rat(0)], vec![rat(0), rat(-1)]];
        assert!(!matrix_is_psd(&indef));
    }

    #[test]
    fn test_matrix_is_psd_zero_pivot_with_coupling_is_indefinite() {
        // [[0,1],[1,0]] = 2xy: zero diagonal with a nonzero off-diagonal is
        // indefinite (eigenvalues +1, -1). Must NOT be reported PSD.
        let m = vec![vec![rat(0), rat(1)], vec![rat(1), rat(0)]];
        assert!(!matrix_is_psd(&m));
    }

    #[test]
    fn test_quadratic_form_range_sum_of_squares() {
        let x = tid(1);
        let y = tid(2);
        // x^2 + y^2 + 1: PSD form, constant 1, so range [1, +inf).
        let mut p = MultiPoly::zero();
        p.add_term(vec![x, x], rat(1));
        p.add_term(vec![y, y], rat(1));
        p.add_term(Vec::new(), rat(1));
        match quadratic_form_range(&p) {
            Some(QuadRange::MinIs(c)) => assert_eq!(c, rat(1)),
            _ => panic!("expected MinIs(1) for x^2+y^2+1"),
        }
        // `= 0` is refuted (min 1 > 0); `< 0` refuted; `> 0` NOT refuted.
        let r = quadratic_form_range(&p).unwrap();
        assert!(quad_range_refutes(Rel::Eq, &r));
        assert!(quad_range_refutes(Rel::Lt, &r));
        assert!(!quad_range_refutes(Rel::Gt, &r));
    }

    #[test]
    fn test_quadratic_form_range_perfect_square_cross_term() {
        let x = tid(1);
        let y = tid(2);
        // (x+y)^2 = x^2 + 2xy + y^2: PSD, constant 0, range [0, +inf).
        let mut p = MultiPoly::zero();
        p.add_term(vec![x, x], rat(1));
        p.add_term(vec![x, y], rat(2));
        p.add_term(vec![y, y], rat(1));
        let r = quadratic_form_range(&p).unwrap();
        match &r {
            QuadRange::MinIs(c) => assert_eq!(*c, rat(0)),
            _ => panic!("expected MinIs(0) for (x+y)^2"),
        }
        // `(x+y)^2 < 0` is UNSAT; `<= 0` is SAT (origin) so NOT refuted.
        assert!(quad_range_refutes(Rel::Lt, &r));
        assert!(!quad_range_refutes(Rel::Le, &r));
        // `= 0` is SAT (x=-y) so must NOT be refuted (min == 0).
        assert!(!quad_range_refutes(Rel::Eq, &r));
    }

    #[test]
    fn test_quadratic_form_range_indefinite_unbounded() {
        let x = tid(1);
        let y = tid(2);
        // x^2 - y^2: indefinite -> Unbounded, refutes nothing.
        let mut p = MultiPoly::zero();
        p.add_term(vec![x, x], rat(1));
        p.add_term(vec![y, y], rat(-1));
        let r = quadratic_form_range(&p).unwrap();
        assert!(matches!(r, QuadRange::Unbounded));
        assert!(!quad_range_refutes(Rel::Lt, &r));
        assert!(!quad_range_refutes(Rel::Gt, &r));
        assert!(!quad_range_refutes(Rel::Eq, &r));
    }

    #[test]
    fn test_quadratic_form_range_rejects_linear_term() {
        let x = tid(1);
        let y = tid(2);
        // x^2 + y (has a degree-1 monomial) -> out of fragment -> None.
        let mut p = MultiPoly::zero();
        p.add_term(vec![x, x], rat(1));
        p.add_term(vec![y], rat(1));
        assert!(quadratic_form_range(&p).is_none());
    }

    // ---- Rational grid / sqrt-upper helpers (witness search) ----

    #[test]
    fn test_rational_grid_contains_expected_points() {
        // [0, 1] should include 1/2 (q=2), and 24/25 (q=25) within (0.9, 1).
        let grid = rational_grid(&rat(0), &rat(1));
        assert!(grid.contains(&ratfrac(1, 2)));
        let grid2 = rational_grid(&ratfrac(9, 10), &rat(1));
        assert!(grid2.contains(&ratfrac(24, 25)));
        // Every candidate is within the requested range.
        for c in &grid {
            assert!(*c >= rat(0) && *c <= rat(1));
        }
    }

    #[test]
    fn test_rational_sqrt_upper_is_sound() {
        // Perfect square: exact.
        assert_eq!(rational_sqrt_upper(&rat(25)), rat(5));
        assert_eq!(rational_sqrt_upper(&rat(0)), rat(0));
        // Non-perfect square: an OVER-bound (result^2 >= u).
        let u = rat(2);
        let s = rational_sqrt_upper(&u);
        assert!(&s * &s >= u, "sqrt-upper must satisfy s^2 >= u");
        let u2 = ratfrac(7, 3);
        let s2 = rational_sqrt_upper(&u2);
        assert!(&s2 * &s2 >= u2);
    }

    #[test]
    fn test_rational_ceil_floor() {
        assert_eq!(rational_ceil(&ratfrac(7, 2)), BigInt::from(4)); // 3.5 -> 4
        assert_eq!(rational_ceil(&ratfrac(-7, 2)), BigInt::from(-3)); // -3.5 -> -3
        assert_eq!(rational_ceil(&rat(3)), BigInt::from(3));
        assert_eq!(rational_floor(&ratfrac(7, 2)), BigInt::from(3)); // 3.5 -> 3
        assert_eq!(rational_floor(&ratfrac(-7, 2)), BigInt::from(-4)); // -3.5 -> -4
        assert_eq!(rational_floor(&rat(3)), BigInt::from(3));
    }

    #[test]
    fn test_bound_var_from_constraint_circle() {
        let x = tid(1);
        let y = tid(2);
        // x^2 + y^2 - 25 = 0, with y in [-5, 5] already: x in [-5, 5].
        let mut p = MultiPoly::zero();
        p.add_term(vec![x, x], rat(1));
        p.add_term(vec![y, y], rat(1));
        p.add_term(Vec::new(), rat(-25));
        let c = MultiConstraint {
            poly: p,
            rel: Rel::Eq,
        };
        let mut box_bounds: crate::HashMap<TermId, Interval> = crate::HashMap::default();
        box_bounds.insert(y, iv(fin(-5, true), fin(5, true)));
        let bx = bound_var_from_constraint(&c, x, &box_bounds).unwrap();
        // -rest = -(y^2 - 25) over y in [-5,5] -> -(0..25 - 25) = -([-25,0]) = [0,25].
        // x^2 <= 25 -> |x| <= 5.
        assert_eq!(bx.lo, Endpoint::Finite(rat(-5), true));
        assert_eq!(bx.hi, Endpoint::Finite(rat(5), true));
    }
}
