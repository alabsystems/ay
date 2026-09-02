// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rational sum-of-squares / Positivstellensatz certificates for NIA UNSAT.
//!
//! This is the **nia-local fork** of the audited NRA checker
//! (`crates/ay-theories/nra/src/sos.rs`). The multivariate-polynomial types
//! (`MultiPoly`, `Rel`, `MultiConstraint`) and the whole LP/PSD/verify machinery
//! are copied verbatim here (with slim reps identical to NRA's) so NIA gains the
//! same certificate-gated UNSAT pre-phase without a risky cross-crate migration.
//! The NIA copy now adds deterministic bounds around translation, search, and
//! replay; NRA is left completely untouched. A future cohesion pass should
//! extract the common audited checker into a shared crate instead of maintaining
//! two copies.
//!
//! ## Why a REAL SOS refutation is sound for INTEGER UNSAT
//!
//! A degree-2 rational Positivstellensatz certificate refutes a polynomial
//! system over the **reals**. Since the integers are a subset of the reals, a
//! system that is infeasible over ℝ is a fortiori infeasible over ℤ. So an
//! emitted certificate is a genuine witness of NIA (integer) infeasibility. The
//! converse does not hold (an integer-only infeasibility need not have a real
//! refutation), which is exactly why this is a *sound-but-incomplete* pre-phase
//! that only ever answers UNSAT-or-decline (`None`), never SAT.
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
//!   inequality constraints (a nonnegative combination closed to degree 2).
//! * `R ≤ 0` is a rational constant.
//!
//! ## Search vs. checking (soundness / completeness split)
//!
//! * [`search`] looks for a certificate by a degree-2 **LP** relaxation and is
//!   **sound but incomplete**.
//! * [`SosCertificate::verify`] is the **independent checker**: it re-derives the
//!   oriented polynomials from the original constraints, verifies `Q` is PSD by
//!   exact rational LDLᵀ, checks the multiplier signs, and confirms the
//!   polynomial identity by exact coefficient matching. It is deliberately
//!   ignorant of *how* the certificate was found, so a tampered certificate is
//!   rejected. [`search`] runs the checker on its own output before returning.

use ay_core::term::TermId;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

pub(crate) mod budget;
mod lp;

use budget::{
    checked_poly_add, checked_poly_mul, checked_poly_sub, polynomial_fits, rational_fits,
    SosLpBudget, SosPolynomialBudget, MAX_SOS_ASSERTED_LITERALS, MAX_SOS_LP_CELLS,
    MAX_SOS_TOTAL_POLY_TERMS,
};
use lp::{lp_add, lp_mul, lp_phase1_feasible, lp_sub};

// ============================================================================
// nia-local slim copies of NRA's MultiPoly / Rel / MultiConstraint.
//
// The representations are byte-for-byte identical to
// `crate::univariate::{MultiPoly, Rel, MultiConstraint}` in the NRA crate; only
// the methods the SOS machinery actually needs are carried over (the
// `as_linear` / `substitute` / `to_unipoly` helpers are dropped).
// ============================================================================

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
    pub(crate) fn var(v: TermId) -> Self {
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

    pub(crate) fn neg(&self) -> Self {
        Self {
            terms: self.terms.iter().map(|(m, c)| (m.clone(), -c)).collect(),
        }
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
}

/// A multivariate constraint reduced to `poly REL 0`.
#[derive(Clone, Debug)]
pub(crate) struct MultiConstraint {
    pub(crate) poly: MultiPoly,
    pub(crate) rel: Rel,
}

// ============================================================================
// The certificate + independent checker (verbatim from NRA).
// ============================================================================

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
    /// A deterministic checker resource bound was exceeded.
    ResourceLimit,
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

include!("sos/certificate_polynomial.rs");

/// Exact rational positive-semidefiniteness test via symmetric Schur-complement
/// (LDLᵀ-style) elimination. No floating point: every pivot decision is an exact
/// rational sign test.
///
/// A symmetric matrix is PSD iff this elimination completes with every pivot
/// `≥ 0` and every **zero** pivot sitting on an all-zero remaining row/column
/// (a zero diagonal with a nonzero off-diagonal forces a `−a² < 0` 2×2 minor,
/// so it is not PSD).
#[cfg(test)]
pub(crate) fn is_psd(matrix: &[Vec<BigRational>]) -> bool {
    is_psd_bounded(matrix).unwrap_or(false)
}

#[allow(clippy::needless_range_loop)] // Schur complement: index is the pivot/row/col identity.
fn is_psd_bounded(matrix: &[Vec<BigRational>]) -> Result<bool, SosError> {
    let n = matrix.len();
    if matrix.iter().any(|row| row.len() != n) {
        return Ok(false);
    }
    if !matrix.iter().flatten().all(rational_fits) {
        return Err(SosError::ResourceLimit);
    }
    // Work on a mutable copy of the trailing submatrix.
    let mut m: Vec<Vec<BigRational>> = matrix.to_vec();
    for k in 0..n {
        let pivot = m[k][k].clone();
        if pivot.is_negative() {
            return Ok(false);
        }
        if pivot.is_zero() {
            // The remaining row/column at k must be entirely zero.
            for i in (k + 1)..n {
                if !m[k][i].is_zero() || !m[i][k].is_zero() {
                    return Ok(false);
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
            if !rational_fits(&factor) {
                return Err(SosError::ResourceLimit);
            }
            for j in (k + 1)..n {
                let d = &factor * &m[k][j];
                if !rational_fits(&d) {
                    return Err(SosError::ResourceLimit);
                }
                m[i][j] -= d;
                if !rational_fits(&m[i][j]) {
                    return Err(SosError::ResourceLimit);
                }
            }
        }
    }
    Ok(true)
}

fn certificate_input_fits(certificate: &SosCertificate, constraints: &[MultiConstraint]) -> bool {
    if certificate.basis.len() > MAX_VARS + 1
        || certificate.terms.len() > MAX_ATOMS
        || constraints.len() > MAX_SOS_ASSERTED_LITERALS
        || !rational_fits(&certificate.rhs)
        || !certificate.gram.iter().flatten().all(rational_fits)
        || !certificate
            .terms
            .iter()
            .all(|term| rational_fits(&term.multiplier))
        || !certificate.basis.iter().all(|monomial| {
            monomial.len() <= 1 && monomial.windows(2).all(|pair| pair[0] <= pair[1])
        })
    {
        return false;
    }
    let Some(total_terms) = constraints.iter().try_fold(0usize, |total, constraint| {
        total.checked_add(constraint.poly.terms.len())
    }) else {
        return false;
    };
    if total_terms > MAX_SOS_TOTAL_POLY_TERMS
        || !constraints
            .iter()
            .all(|constraint| polynomial_fits(&constraint.poly, None))
    {
        return false;
    }
    let mut variables = Vec::new();
    for constraint in constraints {
        for variable in constraint.poly.variables() {
            if !variables.contains(&variable) {
                variables.push(variable);
                if variables.len() > MAX_VARS {
                    return false;
                }
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
        if !certificate_input_fits(self, constraints) {
            return Err(SosError::ResourceLimit);
        }
        for i in 0..n {
            for j in 0..n {
                if self.gram[i][j] != self.gram[j][i] {
                    return Err(SosError::GramAsymmetric);
                }
            }
        }
        if !is_psd_bounded(&self.gram)? {
            return Err(SosError::GramNotPsd);
        }
        if self.rhs.is_positive() {
            return Err(SosError::PositiveRhs);
        }

        let mut budget = SosPolynomialBudget::default();
        let mut lhs = sigma0_poly(&self.basis, &self.gram, &mut budget)?;
        let mut has_strict_positive = false;
        for term in &self.terms {
            let (g, kind) = derive_oriented(term.origin, constraints, &mut budget)?;
            if kind.is_inequality() && term.multiplier.is_negative() {
                return Err(SosError::NegativeMultiplier);
            }
            if kind.is_strict() && term.multiplier.is_positive() {
                has_strict_positive = true;
            }
            let scaled = scale(&g, &term.multiplier, &mut budget)?;
            lhs = checked_poly_add(&lhs, &scaled, &mut budget).ok_or(SosError::ResourceLimit)?;
        }

        if self.rhs.is_zero() && !has_strict_positive {
            return Err(SosError::NonStrictZeroRhs);
        }

        // Identity: lhs - R must be the zero polynomial.
        let diff = checked_poly_sub(&lhs, &MultiPoly::constant(self.rhs.clone()), &mut budget)
            .ok_or(SosError::ResourceLimit)?;
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

        // `nia_positivstellensatz` is AY's own calculus, not Alethe's: no
        // Alethe checker implements it, and a step naming it is not a weaker
        // proof but *no* proof — carcara answers `unknown rule` / `invalid`
        // for the whole document. The Gram matrix, multipliers and rhs are
        // still the whole point of this certificate, so they are preserved
        // verbatim as SMT-LIB line comments (which every Alethe parser skips)
        // and the step itself is the honest `hole`.
        let mut doc = String::new();
        doc.push_str(
            "; ay-nia Positivstellensatz certificate (replayable, but not an Alethe rule)\n",
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

    /// One-line human summary (for the NIA debug channel).
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
/// the independent checker* ([`SosCertificate::verify`]); otherwise `None`.
pub(crate) fn search(constraints: &[MultiConstraint], vars: &[TermId]) -> Option<SosCertificate> {
    if !search_input_fits(constraints, vars) {
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

    let (atoms, eqs) = collect_certificate_atoms(constraints)?;

    // 3. Dictionary of squares for σ0: x_i², (x_i ± x_j)². All homogeneous
    //    degree-2, so their Gram lives in the `x` block of the basis.
    let mut squares: Vec<Square> = Vec::new();
    for &v in vars {
        let mut form = vec![zero(); basis_len];
        form[var_pos(v)] = one();
        squares.push(make_square(form, &basis)?);
    }
    for a in 0..vars.len() {
        for b in (a + 1)..vars.len() {
            for sign in [one(), -one()] {
                let mut form = vec![zero(); basis_len];
                form[var_pos(vars[a])] = one();
                form[var_pos(vars[b])] = sign;
                squares.push(make_square(form, &basis)?);
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

fn search_input_fits(constraints: &[MultiConstraint], vars: &[TermId]) -> bool {
    if vars.is_empty()
        || vars.len() > MAX_VARS
        || constraints.len() > MAX_SOS_ASSERTED_LITERALS
        || vars
            .iter()
            .enumerate()
            .any(|(index, var)| vars[..index].contains(var))
    {
        return false;
    }
    let Some(total_terms) = constraints.iter().try_fold(0usize, |total, constraint| {
        total.checked_add(constraint.poly.terms.len())
    }) else {
        return false;
    };
    total_terms <= MAX_SOS_TOTAL_POLY_TERMS
        && constraints
            .iter()
            .all(|constraint| polynomial_fits(&constraint.poly, Some(vars)))
}

fn collect_certificate_atoms(constraints: &[MultiConstraint]) -> Option<(Vec<Atom>, Vec<EqAtom>)> {
    let mut atoms = Vec::new();
    let mut eqs = Vec::new();
    let mut linear_ineqs = Vec::new();
    for (index, constraint) in constraints.iter().enumerate() {
        let Some((poly, kind)) = orient(constraint) else {
            continue;
        };
        match kind {
            OrientedKind::Eq => eqs.push(EqAtom { index, poly }),
            OrientedKind::Ge | OrientedKind::Gt => {
                if atoms.len() >= MAX_ATOMS {
                    return None;
                }
                if poly_degree(&poly) <= 1 {
                    linear_ineqs.push(atoms.len());
                }
                atoms.push(Atom {
                    origin: CertOrigin::Constraint(index),
                    kind,
                    poly,
                });
            }
        }
    }

    let mut budget = SosPolynomialBudget::default();
    'outer: for (position, &left) in linear_ineqs.iter().enumerate() {
        for &right in &linear_ineqs[position..] {
            if atoms.len() >= MAX_ATOMS {
                break 'outer;
            }
            let (CertOrigin::Constraint(left_index), CertOrigin::Constraint(right_index)) =
                (atoms[left].origin, atoms[right].origin)
            else {
                return None;
            };
            let poly = checked_poly_mul(&atoms[left].poly, &atoms[right].poly, &mut budget)?;
            let kind = if atoms[left].kind.is_strict() && atoms[right].kind.is_strict() {
                OrientedKind::Gt
            } else {
                OrientedKind::Ge
            };
            atoms.push(Atom {
                origin: CertOrigin::Product(left_index, right_index),
                kind,
                poly,
            });
        }
    }
    Some((atoms, eqs))
}

/// Build `q²` for a linear form and package it as a [`Square`].
fn make_square(form: Vec<BigRational>, basis: &[Vec<TermId>]) -> Option<Square> {
    // q = Σ_k form[k] · basis[k].
    let mut q = MultiPoly::zero();
    for (k, coeff) in form.iter().enumerate() {
        if !coeff.is_zero() {
            q.add_term(basis[k].clone(), coeff.clone());
        }
    }
    let mut budget = SosPolynomialBudget::default();
    let poly = checked_poly_mul(&q, &q, &mut budget)?;
    Some(Square { form, poly })
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
    let tableau_cols = n_cols.checked_add(total_rows)?.checked_add(1)?;
    if total_rows.checked_mul(tableau_cols)? > MAX_SOS_LP_CELLS {
        return None;
    }

    // Build A (total_rows × n_cols) and b.
    let mut a: Vec<Vec<BigRational>> = vec![vec![zero(); n_cols]; total_rows];
    let mut b: Vec<BigRational> = vec![zero(); total_rows];
    let mut arithmetic_budget = SosLpBudget::default();

    let row_of = |m: &[TermId]| monos.iter().position(|x| x.as_slice() == m);

    for (sidx, sq) in squares.iter().enumerate() {
        for (m, c) in &sq.poly.terms {
            let row = row_of(m)?;
            a[row][col_sq + sidx] = lp_add(&a[row][col_sq + sidx], c, &mut arithmetic_budget)?;
        }
    }
    for (aidx, at) in atoms.iter().enumerate() {
        for (m, c) in &at.poly.terms {
            let row = row_of(m)?;
            a[row][col_at + aidx] = lp_add(&a[row][col_at + aidx], c, &mut arithmetic_budget)?;
        }
    }
    for (eidx, e) in eqs.iter().enumerate() {
        for (m, c) in &e.poly.terms {
            let r = row_of(m)?;
            a[r][col_eq + 2 * eidx] = lp_add(&a[r][col_eq + 2 * eidx], c, &mut arithmetic_budget)?; // λ⁺
            a[r][col_eq + 2 * eidx + 1] =
                lp_sub(&a[r][col_eq + 2 * eidx + 1], c, &mut arithmetic_budget)?;
            // λ⁻
        }
    }
    // RHS: constant-monomial equation equals R; all others 0.
    b[0] = rhs_const.clone();

    // Strict template: Σ_{strict atoms} c = 1 (via a surplus variable).
    if strict_template {
        let r = n_rows_ident; // last row
        for (aidx, at) in atoms.iter().enumerate() {
            if at.kind.is_strict() {
                a[r][col_at + aidx] = lp_add(&a[r][col_at + aidx], &one(), &mut arithmetic_budget)?;
            }
        }
        a[r][col_surplus] = lp_sub(&a[r][col_surplus], &one(), &mut arithmetic_budget)?;
        b[r] = one();
    }

    let solution = lp_phase1_feasible(a, b, n_cols)?;
    reconstruct_certificate(
        basis,
        squares,
        atoms,
        eqs,
        &solution,
        col_sq,
        col_at,
        col_eq,
        rhs_const,
        &mut arithmetic_budget,
    )
}

/// Rebuild the exact Gram matrix and constraint multipliers from one feasible
/// coefficient-matching solution. Every rational operation remains metered.
#[allow(clippy::needless_range_loop)] // Gram reconstruction: multi-array index access.
fn reconstruct_certificate(
    basis: &[Vec<TermId>],
    squares: &[Square],
    atoms: &[Atom],
    eqs: &[EqAtom],
    solution: &[BigRational],
    col_sq: usize,
    col_at: usize,
    col_eq: usize,
    rhs: BigRational,
    budget: &mut SosLpBudget,
) -> Option<SosCertificate> {
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
                let left = lp_mul(s, &sq.form[i], budget)?;
                let delta = lp_mul(&left, &sq.form[j], budget)?;
                gram[i][j] = lp_add(&gram[i][j], &delta, budget)?;
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
        let net = lp_sub(
            &solution[col_eq + 2 * eidx],
            &solution[col_eq + 2 * eidx + 1],
            budget,
        )?;
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
        rhs,
    })
}

#[cfg(test)]
mod tests;
