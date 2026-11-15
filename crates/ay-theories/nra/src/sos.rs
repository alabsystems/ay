// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rational sum-of-squares / Positivstellensatz certificates for NRA UNSAT.
//!
//! The interval branch-and-prune procedure in [`crate::icp`] and the exact
//! univariate/linear-substitution deciders can prove a polynomial system
//! `{ g_i ⋈ 0 }` infeasible by exhaustion, but the resulting Alethe proof for
//! that theory conflict still contains a `:rule hole`. This module builds and
//! independently checks a private algebraic witness when possible; its public
//! rendering retains rational data as comments, not a portable proof rule.
//!
//! ## The certificate
//!
//! A degree-bounded rational Positivstellensatz refutation of `{ g_i ⋈ 0 }` is an
//! identity over the rationals
//!
//! ```text
//!     σ0(x)  +  Σ_i  c_i · g_i(x)   =   R
//! ```
//!
//! where
//!
//! * `σ0` is a **sum of squares**, presented as a symmetric **PSD** rational
//!   Gram matrix `Q` over a monomial `basis` `m` of degree at most two, i.e.
//!   `σ0 = mᵀ Q m`. Because `Q ⪰ 0`, `σ0(x) ≥ 0` for every real `x`.
//! * each `g_i` is an **oriented** constraint polynomial: the asserted atom
//!   `p ⋈ 0` is rewritten to `g ≥ 0` (nonstrict), `g > 0` (strict), or `g = 0`
//!   (equality). Inequality multipliers `c_i ≥ 0`; equality multipliers are
//!   free. A `g_i` may also be a **product** `g_a · g_b` of two original
//!   inequality constraints whose degrees sum to at most four —
//!   this is what lets box bounds cancel the `x²` terms of a quadratic
//!   lower-bound cluster.
//! * `R ≤ 0` is a rational constant.
//!
//! **Why it refutes.** Evaluate the identity at any point of the feasible set:
//! every `g_i ≥ 0` (strict ones `> 0`), every `h_j = 0`, and `σ0 ≥ 0`, so the
//! left side is `≥ 0`, and *strictly* `> 0` when some strict inequality carries
//! a positive multiplier. That contradicts the right side `R` whenever
//! `R < 0`, or `R = 0` with a strict-positive term present. Hence the feasible
//! set is empty. The two trivial shapes fall straight out:
//!
//! * `{ x ≥ 1, x ≤ 0 }`: `1·(x−1) + 1·(0−x) = −1` (linear Farkas, `σ0 = 0`).
//! * `{ x²+y² < 0 }`: `(x²+y²) + 1·(−(x²+y²)) = 0` with the `−(x²+y²) > 0` term
//!   strict — the classic `x²+y²` sum-of-squares.
//!
//! ## Search vs. checking (soundness / completeness split)
//!
//! * [`search`] first tries the established homogeneous degree-2 square
//!   dictionary, then a bounded degree-4 DSOS dictionary over all monomials of
//!   degree at most two, including the constant. Nonnegative combinations of
//!   single-monomial squares and pairwise sum/difference squares restrict the
//!   full PSD cone: this is sound but incomplete, not full SOS or SDSOS.
//!   Coefficient matching uses bounded exact-rational Phase-1 simplex with
//!   Bland's rule. Limits on dimensions, polynomial work, pivots, and rational
//!   sizes are completeness limits only. The caller currently asks for this
//!   evidence after another route has decided UNSAT; a declined search does
//!   not change that verdict or establish a portable public proof.
//! * The caller uses a separately bounded SOS-only source-to-polynomial
//!   translator; general NRA polynomial translation remains a different lane.
//! * [`SosCertificate::verify`] is the **independent checker**: it re-derives
//!   the oriented polynomials from the original constraints, verifies `Q` is
//!   PSD by exact rational LDLᵀ, checks the multiplier signs, and confirms the
//!   polynomial identity by exact coefficient matching. It is deliberately
//!   ignorant of *how* the certificate was found, so a tampered certificate is
//!   rejected. [`search`] runs the checker on its own output before returning,
//!   so an emitted certificate is always independently valid.

use ay_core::term::TermId;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::univariate::{MultiConstraint, MultiPoly, Rel};

/// Orientation of a constraint into the `g ≥ 0` / `g > 0` / `g = 0` normal form
/// used by the certificate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OrientedKind {
    /// Nonstrict inequality `g ≥ 0` (multiplier must be ≥ 0).
    Ge,
    /// Strict inequality `g > 0` (multiplier must be ≥ 0).
    Gt,
    /// Equality `g = 0` (multiplier is free).
    Eq,
}

impl OrientedKind {
    fn is_strict(self) -> bool {
        matches!(self, OrientedKind::Gt)
    }
    fn is_inequality(self) -> bool {
        matches!(self, OrientedKind::Ge | OrientedKind::Gt)
    }
}

/// Where a certificate term's oriented polynomial comes from, so the checker can
/// re-derive it from the original constraint list rather than trusting a stored
/// copy.
#[derive(Clone, Copy, Debug, Eq)]
pub(crate) enum CertOrigin {
    /// The oriented form of `constraints[i]`.
    Constraint(usize),
    /// The product `orient(constraints[i]).g · orient(constraints[j]).g` of two
    /// oriented *inequality* constraints (a valid nonnegative atom).
    Product(usize, usize),
}

// Written out rather than derived: the derived `eq` compares discriminants and
// then matches the pair with an `unreachable` arm for mismatched variants, an
// arm Level-0 verification cannot rule out. Matching the pair directly is the
// same relation with no unreachable arm.
impl PartialEq for CertOrigin {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Constraint(a), Self::Constraint(b)) => a == b,
            (Self::Product(a, b), Self::Product(c, d)) => a == c && b == d,
            _ => false,
        }
    }
}

/// One `c · g` term of the certificate's constraint combination.
#[derive(Clone, Debug)]
pub(crate) struct CertTerm {
    pub(crate) origin: CertOrigin,
    pub(crate) multiplier: BigRational,
}

/// A degree-bounded rational Positivstellensatz certificate of infeasibility.
#[derive(Clone, Debug)]
pub(crate) struct SosCertificate {
    /// Monomial basis for `σ0`: `basis[0] = []` (the constant `1`), then one
    /// entry per linear or quadratic monomial. Each entry is sorted.
    pub(crate) basis: Vec<Vec<TermId>>,
    /// Symmetric PSD Gram matrix `Q` with `σ0 = basisᵀ Q basis`.
    pub(crate) gram: Vec<Vec<BigRational>>,
    /// The `Σ c_i g_i` combination.
    pub(crate) terms: Vec<CertTerm>,
    /// The right-hand-side constant `R ≤ 0`.
    pub(crate) rhs: BigRational,
}

/// Why an independent check rejected a certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SosError {
    /// Search/replay dimensions or exact arithmetic exceed the bounded envelope.
    ResourceLimit,
    /// Basis is noncanonical or mentions a variable absent from the source.
    InvalidBasis,
    /// The Gram matrix is not square / does not match the basis length.
    GramShape,
    /// The Gram matrix is not symmetric.
    GramAsymmetric,
    /// The Gram matrix is not positive semidefinite.
    GramNotPsd,
    /// A term references a constraint index outside the constraint list.
    BadConstraintIndex,
    /// A term's constraint cannot be oriented to `g ⋈ 0` (e.g. a `≠` atom), or a
    /// product term references a non-inequality factor.
    NotOrientable,
    /// An inequality multiplier is negative.
    NegativeMultiplier,
    /// The right-hand side `R` is positive.
    PositiveRhs,
    /// `R = 0` but no strict inequality carries a positive multiplier, so the
    /// identity `Σ(nonneg) = 0` proves nothing.
    NonStrictZeroRhs,
    /// `σ0 + Σ c_i g_i` does not equal the constant `R`.
    IdentityMismatch,
}

impl core::fmt::Display for SosError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s = match self {
            SosError::ResourceLimit => "certificate exceeds the bounded SOS checker envelope",
            SosError::InvalidBasis => "certificate basis is noncanonical or not source-bound",
            SosError::GramShape => "Gram matrix shape does not match basis",
            SosError::GramAsymmetric => "Gram matrix is not symmetric",
            SosError::GramNotPsd => "Gram matrix is not positive semidefinite",
            SosError::BadConstraintIndex => "certificate references an out-of-range constraint",
            SosError::NotOrientable => "constraint cannot be oriented to g >|=|> 0",
            SosError::NegativeMultiplier => "an inequality multiplier is negative",
            SosError::PositiveRhs => "right-hand side R is positive",
            SosError::NonStrictZeroRhs => "R = 0 without a strict-positive term",
            SosError::IdentityMismatch => "polynomial identity does not hold",
        };
        f.write_str(s)
    }
}

fn zero() -> BigRational {
    BigRational::zero()
}
fn one() -> BigRational {
    BigRational::one()
}

/// Orient a single constraint `p ⋈ 0` to a `g ⋈ 0` normal form with `g ≥ 0`,
/// `g > 0`, or `g = 0`. Returns `None` for `≠` atoms (a disjunction, not a
/// single nonnegative/zero atom).
pub(crate) fn orient(c: &MultiConstraint) -> Option<(MultiPoly, OrientedKind)> {
    match c.rel {
        Rel::Ge => Some((c.poly.clone(), OrientedKind::Ge)),
        Rel::Gt => Some((c.poly.clone(), OrientedKind::Gt)),
        Rel::Le => Some((c.poly.neg(), OrientedKind::Ge)),
        Rel::Lt => Some((c.poly.neg(), OrientedKind::Gt)),
        Rel::Eq => Some((c.poly.clone(), OrientedKind::Eq)),
        Rel::Ne => None,
    }
}

impl SosCertificate {
    /// Render the certificate as an Alethe-style proof step for the certificate
    /// stream. The clause is empty (`(cl)`, i.e. `false`) because the identity
    /// refutes the asserted conjunction. Rational data is preserved as comments;
    /// the emitted rule remains `hole`, not strict portable evidence. `name(v)`
    /// resolves a variable's print name.
    pub(crate) fn render_alethe(&self, step: &str, name: impl Fn(TermId) -> String) -> String {
        let mut out = String::new();
        // Basis.
        out.push_str("  (:basis");
        for m in &self.basis {
            out.push(' ');
            out.push_str(&render_monomial(m, &name));
        }
        out.push_str(")\n");
        // Gram matrix rows.
        out.push_str("  (:gram");
        for row in &self.gram {
            out.push_str(" (");
            for (k, c) in row.iter().enumerate() {
                if k > 0 {
                    out.push(' ');
                }
                out.push_str(&render_rat(c));
            }
            out.push(')');
        }
        out.push_str(")\n");
        // Constraint multipliers.
        out.push_str("  (:mult");
        for t in &self.terms {
            out.push(' ');
            match t.origin {
                CertOrigin::Constraint(i) => {
                    out.push_str(&format!("(g{} {})", i, render_rat(&t.multiplier)));
                }
                CertOrigin::Product(i, j) => {
                    out.push_str(&format!("(g{}*g{} {})", i, j, render_rat(&t.multiplier)));
                }
            }
        }
        out.push_str(")\n");
        out.push_str(&format!("  (:rhs {})", render_rat(&self.rhs)));

        // `nra_positivstellensatz` is AY's own calculus, not Alethe's: no
        // Alethe checker implements it, and a step naming it is not a weaker
        // proof but *no* proof — carcara answers `unknown rule` / `invalid`
        // for the whole document. The Gram matrix, multipliers and rhs are
        // still the whole point of this certificate, so they are preserved
        // verbatim as SMT-LIB line comments (which every Alethe parser skips)
        // and the step itself is the honest `hole`.
        let mut doc = String::new();
        doc.push_str(
            "; ay-nra Positivstellensatz certificate (replayable, but not an Alethe rule)\n",
        );
        for line in out.lines() {
            doc.push_str("; ");
            doc.push_str(line);
            doc.push('\n');
        }
        doc.push_str(&format!(
            "(step {step} (cl) :rule {})",
            ay_core::UNPROVED_STEP_RULE
        ));
        doc
    }

    /// One-line human summary (for the NRA debug channel).
    pub(crate) fn summary(&self) -> String {
        let squares = self
            .gram
            .iter()
            .enumerate()
            .filter(|(i, row)| row[*i] != zero())
            .count();
        format!(
            "SOS Positivstellensatz cert: sigma0 over {}-monomial basis (~{} nonzero diag), {} constraint terms, R = {}",
            self.basis.len(),
            squares,
            self.terms.len(),
            render_rat(&self.rhs),
        )
    }
}

fn render_rat(r: &BigRational) -> String {
    if r.denom() == &BigInt::one() {
        r.numer().to_string()
    } else {
        format!("(/ {} {})", r.numer(), r.denom())
    }
}

fn render_monomial(m: &[TermId], name: &impl Fn(TermId) -> String) -> String {
    if m.is_empty() {
        return "1".to_string();
    }
    if m.len() == 1 {
        return name(m[0]);
    }
    let mut s = String::from("(*");
    for &v in m {
        s.push(' ');
        s.push_str(&name(v));
    }
    s.push(')');
    s
}

pub(crate) mod budget;
mod checker;
mod lp;
mod portable;
mod search;

pub(crate) use portable::SosClauseSource;

#[cfg(test)]
use checker::is_psd;
#[cfg(test)]
use lp::lp_phase1_feasible;
pub(crate) use search::{search, search_with_progress};

/// Maximum source variables in the bounded certificate lane.
pub(crate) const MAX_VARS: usize = 8;
/// Maximum retained inequality atoms, including source products.
const MAX_ATOMS: usize = 400;
/// Maximum structural LP columns.
const MAX_LP_COLS: usize = 700;
/// Complete quadratic monomial basis for eight variables, including constant.
const MAX_BASIS: usize = (MAX_VARS + 1) * (MAX_VARS + 2) / 2;

fn poly_degree(poly: &MultiPoly) -> usize {
    poly.terms
        .iter()
        .map(|(monomial, _)| monomial.len())
        .max()
        .unwrap_or(0)
}

#[cfg(test)]
mod tests;
