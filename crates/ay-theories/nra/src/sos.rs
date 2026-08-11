// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rational sum-of-squares / Positivstellensatz certificates for NRA UNSAT.
//!
//! The interval branch-and-prune procedure in [`crate::icp`] and the exact
//! univariate/linear-substitution deciders can prove a polynomial system
//! `{ g_i ⋈ 0 }` infeasible by exhaustion, but the resulting Alethe proof for
//! that theory conflict rides an audited `:rule trust` hole: there is no
//! replayable *algebraic* witness of emptiness. This module produces one when
//! it can.
//!
//! ## The certificate
//!
//! A degree-2 rational Positivstellensatz refutation of `{ g_i ⋈ 0 }` is an
//! identity over the rationals
//!
//! ```text
//!     σ0(x)  +  Σ_i  c_i · g_i(x)   =   R
//! ```
//!
//! where
//!
//! * `σ0` is a **sum of squares**, presented as a symmetric **PSD** rational
//!   Gram matrix `Q` over a monomial `basis` `m = (1, x_1, …, x_n)`, i.e.
//!   `σ0 = mᵀ Q m`. Because `Q ⪰ 0`, `σ0(x) ≥ 0` for every real `x`.
//! * each `g_i` is an **oriented** constraint polynomial: the asserted atom
//!   `p ⋈ 0` is rewritten to `g ≥ 0` (nonstrict), `g > 0` (strict), or `g = 0`
//!   (equality). Inequality multipliers `c_i ≥ 0`; equality multipliers are
//!   free. A `g_i` may also be a **product** `g_a · g_b` of two linear
//!   inequality constraints (a nonnegative combination closed to degree 2 —
//!   this is what lets box bounds cancel the `x²` terms of a quadratic
//!   lower-bound cluster).
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
//! * [`search`] looks for a certificate by a degree-2 **LP** relaxation: `σ0`
//!   is restricted to a nonnegative combination of a fixed dictionary of
//!   squares (a DSOS-style restriction of the full PSD cone), the inequality
//!   multipliers are nonnegative constants over the constraint set closed under
//!   pairwise products of linear atoms, and coefficient-matching the identity
//!   is an exact rational linear program solved by a Phase-1 simplex. This is
//!   **sound but incomplete**: not every degree-2 SOS certificate is a
//!   nonnegative combination of the fixed square dictionary, and certificates
//!   of degree > 2 are out of reach entirely. When the search fails, the caller
//!   keeps the interval-exhaustion UNSAT with its existing `:rule trust`; no
//!   verdict is regressed.
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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CertOrigin {
    /// The oriented form of `constraints[i]`.
    Constraint(usize),
    /// The product `orient(constraints[i]).g · orient(constraints[j]).g` of two
    /// oriented *inequality* constraints (a valid nonnegative atom).
    Product(usize, usize),
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
    /// entry `[x_k]` per variable. A monomial is a sorted `Vec<TermId>`.
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

/// Re-derive a certificate term's oriented polynomial and kind from the original
/// constraints (used by the independent checker).
fn derive_oriented(
    origin: CertOrigin,
    constraints: &[MultiConstraint],
) -> Result<(MultiPoly, OrientedKind), SosError> {
    match origin {
        CertOrigin::Constraint(i) => {
            let c = constraints.get(i).ok_or(SosError::BadConstraintIndex)?;
            orient(c).ok_or(SosError::NotOrientable)
        }
        CertOrigin::Product(i, j) => {
            let ci = constraints.get(i).ok_or(SosError::BadConstraintIndex)?;
            let cj = constraints.get(j).ok_or(SosError::BadConstraintIndex)?;
            let (gi, ki) = orient(ci).ok_or(SosError::NotOrientable)?;
            let (gj, kj) = orient(cj).ok_or(SosError::NotOrientable)?;
            if !ki.is_inequality() || !kj.is_inequality() {
                return Err(SosError::NotOrientable);
            }
            let kind = if ki.is_strict() && kj.is_strict() {
                OrientedKind::Gt
            } else {
                OrientedKind::Ge
            };
            Ok((gi.mul(&gj), kind))
        }
    }
}

/// The monomial `basis[a] · basis[b]` as a sorted `Vec<TermId>`.
fn mono_product(a: &[TermId], b: &[TermId]) -> Vec<TermId> {
    let mut m = Vec::with_capacity(a.len() + b.len());
    m.extend_from_slice(a);
    m.extend_from_slice(b);
    m.sort_unstable();
    m
}

/// Scale every coefficient of a polynomial by a rational.
fn scale(p: &MultiPoly, k: &BigRational) -> MultiPoly {
    if k.is_zero() {
        return MultiPoly::zero();
    }
    let mut out = MultiPoly::zero();
    for (m, c) in &p.terms {
        out.add_term(m.clone(), c * k);
    }
    out
}

/// Expand `σ0 = basisᵀ Q basis` into a [`MultiPoly`].
fn sigma0_poly(basis: &[Vec<TermId>], gram: &[Vec<BigRational>]) -> MultiPoly {
    let mut out = MultiPoly::zero();
    for (a, ba) in basis.iter().enumerate() {
        for (b, bb) in basis.iter().enumerate() {
            let q = &gram[a][b];
            if q.is_zero() {
                continue;
            }
            out.add_term(mono_product(ba, bb), q.clone());
        }
    }
    out
}

/// Exact rational positive-semidefiniteness test via symmetric Schur-complement
/// (LDLᵀ-style) elimination. No floating point: every pivot decision is an exact
/// rational sign test.
///
/// A symmetric matrix is PSD iff this elimination completes with every pivot
/// `≥ 0` and every **zero** pivot sitting on an all-zero remaining row/column
/// (a zero diagonal with a nonzero off-diagonal forces a `−a² < 0` 2×2 minor,
/// so it is not PSD).
#[allow(clippy::needless_range_loop)] // Schur complement: index is the pivot/row/col identity.
pub(crate) fn is_psd(matrix: &[Vec<BigRational>]) -> bool {
    let n = matrix.len();
    if matrix.iter().any(|row| row.len() != n) {
        return false;
    }
    // Work on a mutable copy of the trailing submatrix.
    let mut m: Vec<Vec<BigRational>> = matrix.to_vec();
    for k in 0..n {
        let pivot = m[k][k].clone();
        if pivot.is_negative() {
            return false;
        }
        if pivot.is_zero() {
            // The remaining row/column at k must be entirely zero.
            for i in (k + 1)..n {
                if !m[k][i].is_zero() || !m[i][k].is_zero() {
                    return false;
                }
            }
            continue;
        }
        // Schur complement update of the trailing block (keeps symmetry).
        for i in (k + 1)..n {
            if m[i][k].is_zero() {
                continue;
            }
            let factor = &m[i][k] / &pivot;
            for j in (k + 1)..n {
                let d = &factor * &m[k][j];
                m[i][j] -= d;
            }
        }
    }
    true
}

impl SosCertificate {
    /// Independently verify this certificate against the original constraints.
    ///
    /// Checks, using only exact rational arithmetic and *without* trusting how
    /// the certificate was produced:
    /// 1. the Gram matrix is square, symmetric, and PSD (exact LDLᵀ);
    /// 2. every constraint term re-orients cleanly, with a nonnegative
    ///    multiplier for inequalities;
    /// 3. `R ≤ 0`, and if `R = 0` some strict inequality carries a positive
    ///    multiplier;
    /// 4. the polynomial identity `σ0 + Σ c_i g_i ≡ R` holds by coefficient
    ///    matching.
    pub(crate) fn verify(&self, constraints: &[MultiConstraint]) -> Result<(), SosError> {
        let n = self.basis.len();
        if self.gram.len() != n || self.gram.iter().any(|r| r.len() != n) {
            return Err(SosError::GramShape);
        }
        for i in 0..n {
            for j in 0..n {
                if self.gram[i][j] != self.gram[j][i] {
                    return Err(SosError::GramAsymmetric);
                }
            }
        }
        if !is_psd(&self.gram) {
            return Err(SosError::GramNotPsd);
        }
        if self.rhs.is_positive() {
            return Err(SosError::PositiveRhs);
        }

        let mut lhs = sigma0_poly(&self.basis, &self.gram);
        let mut has_strict_positive = false;
        for term in &self.terms {
            let (g, kind) = derive_oriented(term.origin, constraints)?;
            if kind.is_inequality() && term.multiplier.is_negative() {
                return Err(SosError::NegativeMultiplier);
            }
            if kind.is_strict() && term.multiplier.is_positive() {
                has_strict_positive = true;
            }
            lhs = lhs.add(&scale(&g, &term.multiplier));
        }

        if self.rhs.is_zero() && !has_strict_positive {
            return Err(SosError::NonStrictZeroRhs);
        }

        // Identity: lhs - R must be the zero polynomial.
        let diff = lhs.sub(&MultiPoly::constant(self.rhs.clone()));
        if !diff.is_zero() {
            return Err(SosError::IdentityMismatch);
        }
        Ok(())
    }

    /// Render the certificate as an Alethe-style proof step for the certificate
    /// stream. The clause is empty (`(cl)`, i.e. `false`) because the identity
    /// refutes the asserted conjunction; the `:args` carry the machine-checkable
    /// Gram matrix, multipliers, and right-hand side. `name(v)` resolves a
    /// variable's print name.
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

// ============================================================================
// The degree-2 LP search.
// ============================================================================

/// Cap on the number of variables the search considers.
const MAX_VARS: usize = 8;
/// Cap on the number of nonnegative atoms (base + products) fed to the LP.
const MAX_ATOMS: usize = 400;
/// Cap on the total number of LP columns (structural variables).
const MAX_LP_COLS: usize = 700;

/// A nonnegative atom `g ⋈ 0` (`⋈ ∈ {≥, >}`) usable with a nonnegative
/// multiplier, together with its provenance and monomial expansion.
struct Atom {
    origin: CertOrigin,
    kind: OrientedKind,
    poly: MultiPoly,
}

/// An equality atom `h = 0` usable with a free multiplier.
struct EqAtom {
    index: usize,
    poly: MultiPoly,
}

/// A dictionary square `q(x)²` for `σ0`, carrying the linear form `q`'s
/// coefficient vector over the basis so the PSD Gram can be reconstructed.
struct Square {
    /// Coefficient of each basis monomial in the linear form `q`.
    form: Vec<BigRational>,
    /// Expanded `q²` as a polynomial (for coefficient matching).
    poly: MultiPoly,
}

/// Search for a degree-2 rational Positivstellensatz certificate refuting the
/// conjunction `{ constraints }`. Returns a certificate only if it *also passes
/// the independent checker* ([`SosCertificate::verify`]); otherwise `None`
/// (caller keeps the interval-exhaustion UNSAT with its `:rule trust`).
pub(crate) fn search(constraints: &[MultiConstraint], vars: &[TermId]) -> Option<SosCertificate> {
    if vars.is_empty() || vars.len() > MAX_VARS {
        return None;
    }

    // Basis for σ0: [1, x_1, …, x_n].
    let mut basis: Vec<Vec<TermId>> = Vec::with_capacity(vars.len() + 1);
    basis.push(Vec::new());
    for &v in vars {
        basis.push(vec![v]);
    }
    let basis_len = basis.len();
    // Position of variable v within the basis (index 1..=n).
    let var_pos = |v: TermId| -> usize { vars.iter().position(|&u| u == v).unwrap() + 1 };

    // 1. Orient constraints into nonnegative / equality atoms.
    let mut atoms: Vec<Atom> = Vec::new();
    let mut eqs: Vec<EqAtom> = Vec::new();
    // Linear inequality atoms (degree ≤ 1) eligible for pairwise products.
    let mut linear_ineqs: Vec<usize> = Vec::new();
    for (i, c) in constraints.iter().enumerate() {
        let Some((g, kind)) = orient(c) else {
            continue; // ≠ atom: not usable.
        };
        // Reject anything above degree 2 (cannot participate in a degree-2
        // identity as a base atom).
        if poly_degree(&g) > 2 {
            continue;
        }
        match kind {
            OrientedKind::Eq => eqs.push(EqAtom { index: i, poly: g }),
            OrientedKind::Ge | OrientedKind::Gt => {
                if poly_degree(&g) <= 1 {
                    linear_ineqs.push(atoms.len());
                }
                atoms.push(Atom {
                    origin: CertOrigin::Constraint(i),
                    kind,
                    poly: g,
                });
            }
        }
    }

    // 2. Close the linear inequalities under pairwise products (including
    //    squares): a product of two nonnegatives is nonnegative, and this is
    //    what supplies the `−x²` terms that cancel a quadratic lower bound.
    'outer: for a_idx in 0..linear_ineqs.len() {
        for b_idx in a_idx..linear_ineqs.len() {
            if atoms.len() >= MAX_ATOMS {
                break 'outer;
            }
            let ia = linear_ineqs[a_idx];
            let ib = linear_ineqs[b_idx];
            let (CertOrigin::Constraint(ci), CertOrigin::Constraint(cj)) =
                (atoms[ia].origin, atoms[ib].origin)
            else {
                continue;
            };
            let prod = atoms[ia].poly.mul(&atoms[ib].poly);
            let kind = if atoms[ia].kind.is_strict() && atoms[ib].kind.is_strict() {
                OrientedKind::Gt
            } else {
                OrientedKind::Ge
            };
            atoms.push(Atom {
                origin: CertOrigin::Product(ci, cj),
                kind,
                poly: prod,
            });
        }
    }

    // 3. Dictionary of squares for σ0: x_i², (x_i ± x_j)². All homogeneous
    //    degree-2, so their Gram lives in the `x` block of the basis.
    let mut squares: Vec<Square> = Vec::new();
    for &v in vars {
        let mut form = vec![zero(); basis_len];
        form[var_pos(v)] = one();
        squares.push(make_square(form, &basis));
    }
    for a in 0..vars.len() {
        for b in (a + 1)..vars.len() {
            for sign in [one(), -one()] {
                let mut form = vec![zero(); basis_len];
                form[var_pos(vars[a])] = one();
                form[var_pos(vars[b])] = sign;
                squares.push(make_square(form, &basis));
            }
        }
    }

    // 4. Try template A (R = −1), then template B (R = 0 with a forced strict
    //    positive term).
    let has_strict = atoms.iter().any(|a| a.kind.is_strict());
    if let Some(cert) = try_template(&basis, &squares, &atoms, &eqs, false) {
        if cert.verify(constraints).is_ok() {
            return Some(cert);
        }
    }
    if has_strict {
        if let Some(cert) = try_template(&basis, &squares, &atoms, &eqs, true) {
            if cert.verify(constraints).is_ok() {
                return Some(cert);
            }
        }
    }
    None
}

/// Build `q²` for a linear form and package it as a [`Square`].
fn make_square(form: Vec<BigRational>, basis: &[Vec<TermId>]) -> Square {
    // q = Σ_k form[k] · basis[k].
    let mut q = MultiPoly::zero();
    for (k, coeff) in form.iter().enumerate() {
        if !coeff.is_zero() {
            q.add_term(basis[k].clone(), coeff.clone());
        }
    }
    let poly = q.mul(&q);
    Square { form, poly }
}

/// Total degree of a polynomial (max monomial length).
fn poly_degree(p: &MultiPoly) -> usize {
    p.terms.iter().map(|(m, _)| m.len()).max().unwrap_or(0)
}

/// Return the row index of monomial `m`, appending it if unseen.
fn intern_mono(monos: &mut Vec<Vec<TermId>>, m: &[TermId]) -> usize {
    if let Some(p) = monos.iter().position(|x| x.as_slice() == m) {
        p
    } else {
        monos.push(m.to_vec());
        monos.len() - 1
    }
}

/// Assemble and solve the coefficient-matching LP for one template, returning a
/// certificate on feasibility. `strict_template` selects `R = 0` with the added
/// row `Σ_{strict atoms} c = 1` (else `R = −1`).
#[allow(clippy::needless_range_loop)] // Gram reconstruction: multi-array index access.
fn try_template(
    basis: &[Vec<TermId>],
    squares: &[Square],
    atoms: &[Atom],
    eqs: &[EqAtom],
    strict_template: bool,
) -> Option<SosCertificate> {
    let rhs_const = if strict_template { zero() } else { -one() };

    // Column layout (all structural columns are ≥ 0):
    //   [ s_0 .. s_{S-1} ]  square coefficients
    //   [ c_0 .. c_{A-1} ]  atom multipliers
    //   [ surplus ]         only in the strict template
    //   [ lp_0+, lp_0-, .. ] free equality multipliers, split into ±.
    let n_sq = squares.len();
    let n_at = atoms.len();
    let n_surplus = if strict_template { 1 } else { 0 };
    let n_eq = eqs.len();
    let col_sq = 0;
    let col_at = col_sq + n_sq;
    let col_surplus = col_at + n_at;
    let col_eq = col_surplus + n_surplus;
    let n_cols = col_eq + 2 * n_eq;
    if n_cols > MAX_LP_COLS {
        return None;
    }

    // Collect the monomial support (one equation per monomial).
    let mut monos: Vec<Vec<TermId>> = Vec::new();
    // Seed the constant monomial as row 0 so the R term lands cleanly.
    intern_mono(&mut monos, &[]);
    for sq in squares {
        for (m, _) in &sq.poly.terms {
            intern_mono(&mut monos, m);
        }
    }
    for a in atoms {
        for (m, _) in &a.poly.terms {
            intern_mono(&mut monos, m);
        }
    }
    for e in eqs {
        for (m, _) in &e.poly.terms {
            intern_mono(&mut monos, m);
        }
    }
    let n_rows_ident = monos.len();
    let total_rows = n_rows_ident + n_surplus;

    // Build A (total_rows × n_cols) and b.
    let mut a: Vec<Vec<BigRational>> = vec![vec![zero(); n_cols]; total_rows];
    let mut b: Vec<BigRational> = vec![zero(); total_rows];

    let row_of = |m: &[TermId]| monos.iter().position(|x| x.as_slice() == m).unwrap();

    for (sidx, sq) in squares.iter().enumerate() {
        for (m, c) in &sq.poly.terms {
            a[row_of(m)][col_sq + sidx] += c;
        }
    }
    for (aidx, at) in atoms.iter().enumerate() {
        for (m, c) in &at.poly.terms {
            a[row_of(m)][col_at + aidx] += c;
        }
    }
    for (eidx, e) in eqs.iter().enumerate() {
        for (m, c) in &e.poly.terms {
            let r = row_of(m);
            a[r][col_eq + 2 * eidx] += c; // λ⁺
            a[r][col_eq + 2 * eidx + 1] -= c; // λ⁻
        }
    }
    // RHS: constant-monomial equation equals R; all others 0.
    b[0] = rhs_const.clone();

    // Strict template: Σ_{strict atoms} c = 1 (via a surplus variable).
    if strict_template {
        let r = n_rows_ident; // last row
        for (aidx, at) in atoms.iter().enumerate() {
            if at.kind.is_strict() {
                a[r][col_at + aidx] += one();
            }
        }
        a[r][col_surplus] -= one();
        b[r] = one();
    }

    let solution = lp_phase1_feasible(a, b, n_cols)?;

    // Reconstruct the certificate from the LP solution.
    // Gram = Σ_s s_s · outer(form_s, form_s).
    let basis_len = basis.len();
    let mut gram = vec![vec![zero(); basis_len]; basis_len];
    for (sidx, sq) in squares.iter().enumerate() {
        let s = &solution[col_sq + sidx];
        if s.is_zero() {
            continue;
        }
        for i in 0..basis_len {
            if sq.form[i].is_zero() {
                continue;
            }
            for j in 0..basis_len {
                if sq.form[j].is_zero() {
                    continue;
                }
                let d = s * &sq.form[i] * &sq.form[j];
                gram[i][j] += d;
            }
        }
    }

    let mut terms: Vec<CertTerm> = Vec::new();
    for (aidx, at) in atoms.iter().enumerate() {
        let c = solution[col_at + aidx].clone();
        if !c.is_zero() {
            terms.push(CertTerm {
                origin: at.origin,
                multiplier: c,
            });
        }
    }
    for (eidx, e) in eqs.iter().enumerate() {
        let net = &solution[col_eq + 2 * eidx] - &solution[col_eq + 2 * eidx + 1];
        if !net.is_zero() {
            terms.push(CertTerm {
                origin: CertOrigin::Constraint(e.index),
                multiplier: net,
            });
        }
    }

    Some(SosCertificate {
        basis: basis.to_vec(),
        gram,
        terms,
        rhs: rhs_const,
    })
}

// ============================================================================
// Exact rational Phase-1 simplex (LP feasibility).
// ============================================================================

/// Decide feasibility of `{ A x = b, x ≥ 0 }` over the rationals and return a
/// feasible `x` if one exists. Standard two-phase artificial-variable Phase-1
/// simplex with **Bland's rule** for guaranteed termination; all arithmetic is
/// exact `BigRational`.
#[allow(clippy::needless_range_loop)] // Tableau pivoting: index into rows/columns is intrinsic.
fn lp_phase1_feasible(
    mut a: Vec<Vec<BigRational>>,
    mut b: Vec<BigRational>,
    n: usize,
) -> Option<Vec<BigRational>> {
    let m = a.len();
    if m == 0 {
        return Some(vec![zero(); n]);
    }
    // Normalize b ≥ 0.
    for i in 0..m {
        if b[i].is_negative() {
            for j in 0..n {
                a[i][j] = -&a[i][j];
            }
            b[i] = -&b[i];
        }
    }
    // Tableau columns: n structural + m artificials + 1 RHS.
    let total = n + m;
    let mut t: Vec<Vec<BigRational>> = vec![vec![zero(); total + 1]; m];
    for i in 0..m {
        for j in 0..n {
            t[i][j] = a[i][j].clone();
        }
        t[i][n + i] = one();
        t[i][total] = b[i].clone();
    }
    let mut basis: Vec<usize> = (0..m).map(|i| n + i).collect();

    // cost[k] = 1 for artificial columns, 0 otherwise (minimize Σ artificials).
    let is_artificial = |k: usize| k >= n;

    loop {
        // Bland's rule: entering = smallest-index column with negative reduced
        // cost. reduced_cost(j) = cost[j] − Σ_i cost[basis[i]] · t[i][j].
        let mut entering = None;
        for j in 0..total {
            let cj = if is_artificial(j) { one() } else { zero() };
            let mut rc = cj;
            for i in 0..m {
                if is_artificial(basis[i]) {
                    rc -= &t[i][j];
                }
            }
            if rc.is_negative() {
                entering = Some(j);
                break;
            }
        }
        let Some(e) = entering else { break };

        // Ratio test with Bland tie-break (smallest leaving basis index).
        let mut leave: Option<usize> = None;
        let mut best: Option<BigRational> = None;
        for i in 0..m {
            if t[i][e].is_positive() {
                let ratio = &t[i][total] / &t[i][e];
                let take = match &best {
                    None => true,
                    Some(br) => ratio < *br || (ratio == *br && basis[i] < basis[leave.unwrap()]),
                };
                if take {
                    best = Some(ratio);
                    leave = Some(i);
                }
            }
        }
        let l = leave?; // no positive pivot ⇒ unbounded (should not occur in Phase 1)

        // Pivot on (l, e).
        let piv = t[l][e].clone();
        for j in 0..=total {
            t[l][j] = &t[l][j] / &piv;
        }
        for i in 0..m {
            if i != l && !t[i][e].is_zero() {
                let factor = t[i][e].clone();
                for j in 0..=total {
                    let d = &factor * &t[l][j];
                    t[i][j] -= d;
                }
            }
        }
        basis[l] = e;
    }

    // Objective = Σ artificial basic values; feasible iff 0.
    let mut obj = zero();
    for i in 0..m {
        if is_artificial(basis[i]) {
            obj += &t[i][total];
        }
    }
    if !obj.is_zero() {
        return None;
    }
    // Read off structural values.
    let mut x = vec![zero(); n];
    for i in 0..m {
        if basis[i] < n {
            x[basis[i]] = t[i][total].clone();
        }
    }
    Some(x)
}

#[cfg(test)]
mod tests;
