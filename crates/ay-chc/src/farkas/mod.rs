// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Farkas lemma based constraint combination
//!
//! This module implements Farkas-based combination of linear constraints
//! for generating interpolants in PDR. When a set of linear inequalities
//! is UNSAT, Farkas' lemma guarantees there exist non-negative coefficients
//! that when used to combine the inequalities, produce a contradiction.
//!
//! The combined constraint is often more general than the original constraints,
//! making it useful for lemma generalization in PDR.
//!
//! ## Algorithm
//!
//! Given constraints: a₁·x ≤ b₁, a₂·x ≤ b₂, ..., aₙ·x ≤ bₙ that are UNSAT,
//! find λ₁, ..., λₙ ≥ 0 such that:
//! - Σᵢ λᵢ·aᵢ = 0  (coefficients cancel)
//! - Σᵢ λᵢ·bᵢ < 0  (RHS is negative)
//!
//! The combined constraint Σᵢ λᵢ·(aᵢ·x - bᵢ) ≤ 0 is a valid lemma.

mod combine;
mod interpolant;
mod linear;
mod normalize;

pub(crate) use combine::farkas_combine;
pub(crate) use interpolant::{compute_interpolant, compute_interpolant_until};
pub(crate) use linear::{
    checked_r64_add, checked_r64_mul, parse_linear_constraint, parse_linear_constraints_split_eq,
    LinearConstraint,
};

// Re-exports for tests (visible via `use super::*` in tests.rs)
#[cfg(test)]
use crate::proof_interpolation::rational64_abs;
#[cfg(test)]
use interpolant::{is_valid_interpolant, try_pairwise_eliminate_non_shared};
#[cfg(test)]
use linear::{
    ceil_rational64, floor_rational64, linear_constraint_to_int_bound,
    parse_linear_constraints_flat, IntBound,
};

use crate::smt::{SmtContext, SmtResult};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;
#[cfg(test)]
use ay_core::kani_compat::DetHashSet as FxHashSet;
use num_rational::Rational64;
use std::sync::Arc;

/// Explicit validation request for a linear-arithmetic Farkas/template lemma.
///
/// This is intentionally only a substrate: callers must provide the exact
/// obligations they want checked, and acceptance is based on SMT validity rather
/// than trusting a syntactic Farkas construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LiaFarkasCertificate {
    pub(crate) lemma: ChcExpr,
    pub(crate) premises: Vec<ChcExpr>,
    pub(crate) original_clause: Option<ChcExpr>,
    pub(crate) inductive_step: Option<LiaFarkasInductiveStep>,
    pub(crate) template_kind: Option<LiaFarkasTemplateKind>,
}

#[allow(dead_code)]
impl LiaFarkasCertificate {
    pub(crate) fn new(lemma: ChcExpr, premises: Vec<ChcExpr>) -> Self {
        Self {
            lemma,
            premises,
            original_clause: None,
            inductive_step: None,
            template_kind: None,
        }
    }

    pub(crate) fn with_original_clause(mut self, original_clause: ChcExpr) -> Self {
        self.original_clause = Some(original_clause);
        self
    }

    #[allow(dead_code)]
    pub(crate) fn with_inductive_step(mut self, inductive_step: LiaFarkasInductiveStep) -> Self {
        self.inductive_step = Some(inductive_step);
        self
    }

    pub(crate) fn with_template_kind(mut self, template_kind: LiaFarkasTemplateKind) -> Self {
        self.template_kind = Some(template_kind);
        self
    }
}

/// Arithmetic template family that produced a candidate LIA/Farkas lemma.
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LiaFarkasTemplateKind {
    AffineEquality,
    Interval,
    DifferenceBound,
    ScaledLinearCombination,
}

/// Relative-inductiveness obligation for a candidate lemma.
///
/// The checked implication is:
/// `frame_lemmas AND lemma AND transition => next_lemma`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LiaFarkasInductiveStep {
    pub(crate) frame_lemmas: Vec<ChcExpr>,
    pub(crate) transition: ChcExpr,
    pub(crate) next_lemma: ChcExpr,
}

#[allow(dead_code)]
impl LiaFarkasInductiveStep {
    pub(crate) fn new(
        frame_lemmas: Vec<ChcExpr>,
        transition: ChcExpr,
        next_lemma: ChcExpr,
    ) -> Self {
        Self {
            frame_lemmas,
            transition,
            next_lemma,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AcceptedLiaFarkasCertificate {
    lemma: ChcExpr,
}

#[allow(dead_code)]
impl AcceptedLiaFarkasCertificate {
    pub(crate) fn lemma(&self) -> &ChcExpr {
        &self.lemma
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LiaFarkasCertificateError {
    EmptyPremises,
    MissingValidationObligation,
    NonLinearFormula,
    PremisesDoNotImplyLemma,
    OriginalClauseDoesNotImplyLemma,
    LemmaNotInductive,
    ValidationUnknown,
}

/// Counters for the LIA/Farkas template/certificate admission surface.
///
/// `checks` counts certificate admission attempts. `accepted + rejected` should
/// equal `checks`; `validation_failures` is the subset of rejections where a
/// semantic proof obligation was missing, failed, or returned `Unknown`.
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct LiaFarkasCertificateStats {
    pub(crate) templates_generated: u64,
    pub(crate) checks: u64,
    pub(crate) accepted: u64,
    pub(crate) rejected: u64,
    pub(crate) validation_failures: u64,
}

#[allow(dead_code)]
impl LiaFarkasCertificateStats {
    pub(crate) fn merge(&mut self, other: &Self) {
        self.templates_generated = self
            .templates_generated
            .saturating_add(other.templates_generated);
        self.checks = self.checks.saturating_add(other.checks);
        self.accepted = self.accepted.saturating_add(other.accepted);
        self.rejected = self.rejected.saturating_add(other.rejected);
        self.validation_failures = self
            .validation_failures
            .saturating_add(other.validation_failures);
    }

    fn record_template(&mut self) {
        self.templates_generated = self.templates_generated.saturating_add(1);
    }

    fn record_check(&mut self) {
        self.checks = self.checks.saturating_add(1);
    }

    fn record_accept(&mut self) {
        self.accepted = self.accepted.saturating_add(1);
    }

    fn record_reject(&mut self, error: LiaFarkasCertificateError) {
        self.rejected = self.rejected.saturating_add(1);
        if error.is_validation_failure() {
            self.validation_failures = self.validation_failures.saturating_add(1);
        }
    }
}

impl LiaFarkasCertificateError {
    fn is_validation_failure(self) -> bool {
        matches!(
            self,
            Self::MissingValidationObligation
                | Self::PremisesDoNotImplyLemma
                | Self::OriginalClauseDoesNotImplyLemma
                | Self::LemmaNotInductive
                | Self::ValidationUnknown
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EntailmentResult {
    Entailed,
    Refuted,
    Unknown,
}

/// Validate a small LIA/Farkas lemma certificate before a caller accepts it.
///
/// All supplied formulas must be conjunctions of supported linear arithmetic
/// atoms. Each semantic obligation is discharged by SMT and `Unknown` is
/// treated as rejection.
#[allow(dead_code)]
pub(crate) fn validate_lia_farkas_certificate(
    certificate: &LiaFarkasCertificate,
    smt: &mut SmtContext,
) -> Result<AcceptedLiaFarkasCertificate, LiaFarkasCertificateError> {
    let mut stats = LiaFarkasCertificateStats::default();
    validate_lia_farkas_certificate_with_stats(certificate, smt, &mut stats)
}

/// Validate a certificate while updating admission counters for route evidence.
#[allow(dead_code)]
pub(crate) fn validate_lia_farkas_certificate_with_stats(
    certificate: &LiaFarkasCertificate,
    smt: &mut SmtContext,
    stats: &mut LiaFarkasCertificateStats,
) -> Result<AcceptedLiaFarkasCertificate, LiaFarkasCertificateError> {
    if certificate.template_kind.is_some() {
        stats.record_template();
    }
    stats.record_check();

    let result = validate_lia_farkas_certificate_inner(certificate, smt);
    match result {
        Ok(accepted) => {
            stats.record_accept();
            Ok(accepted)
        }
        Err(error) => {
            stats.record_reject(error);
            Err(error)
        }
    }
}

fn validate_lia_farkas_certificate_inner(
    certificate: &LiaFarkasCertificate,
    smt: &mut SmtContext,
) -> Result<AcceptedLiaFarkasCertificate, LiaFarkasCertificateError> {
    if certificate.premises.is_empty() {
        return Err(LiaFarkasCertificateError::EmptyPremises);
    }

    if !is_linear_formula(&certificate.lemma)
        || !certificate.premises.iter().all(is_linear_formula)
        || !certificate
            .original_clause
            .as_ref()
            .is_none_or(is_linear_formula)
        || !certificate
            .inductive_step
            .as_ref()
            .is_none_or(is_linear_inductive_step)
    {
        return Err(LiaFarkasCertificateError::NonLinearFormula);
    }

    if certificate.original_clause.is_none() && certificate.inductive_step.is_none() {
        return Err(LiaFarkasCertificateError::MissingValidationObligation);
    }

    let premises = ChcExpr::and_all(certificate.premises.iter().cloned());
    match entails(smt, &premises, &certificate.lemma) {
        EntailmentResult::Entailed => {}
        EntailmentResult::Refuted => {
            return Err(LiaFarkasCertificateError::PremisesDoNotImplyLemma);
        }
        EntailmentResult::Unknown => return Err(LiaFarkasCertificateError::ValidationUnknown),
    }

    if let Some(original_clause) = &certificate.original_clause {
        match entails(smt, original_clause, &certificate.lemma) {
            EntailmentResult::Entailed => {}
            EntailmentResult::Refuted => {
                return Err(LiaFarkasCertificateError::OriginalClauseDoesNotImplyLemma);
            }
            EntailmentResult::Unknown => return Err(LiaFarkasCertificateError::ValidationUnknown),
        }
    }

    if let Some(step) = &certificate.inductive_step {
        let antecedent = ChcExpr::and_all(
            step.frame_lemmas
                .iter()
                .cloned()
                .chain(std::iter::once(certificate.lemma.clone()))
                .chain(std::iter::once(step.transition.clone())),
        );
        match entails(smt, &antecedent, &step.next_lemma) {
            EntailmentResult::Entailed => {}
            EntailmentResult::Refuted => {
                return Err(LiaFarkasCertificateError::LemmaNotInductive);
            }
            EntailmentResult::Unknown => return Err(LiaFarkasCertificateError::ValidationUnknown),
        }
    }

    Ok(AcceptedLiaFarkasCertificate {
        lemma: certificate.lemma.clone(),
    })
}

#[allow(dead_code)]
fn is_linear_inductive_step(step: &LiaFarkasInductiveStep) -> bool {
    step.frame_lemmas.iter().all(is_linear_formula)
        && is_linear_formula(&step.transition)
        && is_linear_formula(&step.next_lemma)
}

#[allow(dead_code)]
fn is_linear_formula(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Bool(_) => true,
        ChcExpr::Op(ChcOp::And, args) => args.iter().all(|arg| is_linear_formula(arg.as_ref())),
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => parse_linear_constraint(expr).is_some(),
        ChcExpr::Op(ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt, args) if args.len() == 2 => {
            parse_linear_constraint(expr).is_some()
        }
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            matches!(
                args[0].as_ref(),
                ChcExpr::Op(ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt, inner)
                    if inner.len() == 2
            ) && parse_linear_constraint(expr).is_some()
        }
        _ => false,
    }
}

#[allow(dead_code)]
fn entails(smt: &mut SmtContext, antecedent: &ChcExpr, consequent: &ChcExpr) -> EntailmentResult {
    let query = ChcExpr::and(antecedent.clone(), ChcExpr::not(consequent.clone()));
    smt.reset();
    match smt.check_sat(&query) {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
            EntailmentResult::Entailed
        }
        SmtResult::Sat(_) => EntailmentResult::Refuted,
        SmtResult::Unknown => EntailmentResult::Unknown,
    }
}

/// Exact LCM of two positive i128 values; `None` on i128 overflow.
///
/// i128-lockstep: replaces the saturating i64 `lcm` for interpolant scaling —
/// a saturated LCM is not a common multiple, so downstream `lcm / denom`
/// scaling would silently produce WRONG coefficients (the ex-falso bug class).
fn checked_lcm_i128(a: i128, b: i128) -> Option<i128> {
    debug_assert!(a > 0 && b > 0, "LCM operands must be positive denominators");
    let g = num_integer::gcd(a, b);
    (a / g).checked_mul(b)
}

/// Build a ChcExpr from a linear constraint: Σᵢ aᵢ·xᵢ ≤ b (or <)
///
/// Per Z3's `normalize_coeffs()` in smt_farkas_util.cpp, we scale the entire
/// constraint by the LCM of all denominators to produce integer coefficients.
/// This is necessary because Farkas combination can produce rational coefficients
/// even from integer input constraints.
///
/// i128-lockstep: returns `None` (abstention — the caller skips this
/// interpolant candidate) when scaling overflows i128. The previous version
/// SATURATED out-of-range coefficients/bounds to `i64::MAX`/`i64::MIN+1`,
/// which changes the inequality — with the widened `ChcExpr::Int(i128)` the
/// scaling is exact-or-refused, never clamped.
pub(crate) fn build_linear_inequality(
    coeffs: &FxHashMap<String, Rational64>,
    bound: Rational64,
    strict: bool,
) -> Option<ChcExpr> {
    build_linear_inequality_sorted(coeffs, bound, strict, ChcSort::Int)
}

/// Sort-aware variant of [`build_linear_inequality`] (#chc25-lra-convergence).
///
/// For `ChcSort::Int` the emission is byte-identical to the historical
/// behaviour (LCM-clear denominators, emit `ChcExpr::Int` coefficients/bound
/// over `Int`-sorted variables).
///
/// For `ChcSort::Real` the atom is emitted directly over the rationals — no
/// denominator clearing (unnecessary over ℝ and avoids i128 overflow) and no
/// integer rounding (which is unsound over ℝ). Coefficients and the bound are
/// emitted as `ChcExpr::Real(num, den)` and variables as `Real`-sorted, so the
/// Craig-validation query is correctly typed. Every candidate is still
/// SMT-validated over the real theory before acceptance.
pub(crate) fn build_linear_inequality_sorted(
    coeffs: &FxHashMap<String, Rational64>,
    bound: Rational64,
    strict: bool,
    var_sort: ChcSort,
) -> Option<ChcExpr> {
    if matches!(var_sort, ChcSort::Real) {
        return build_linear_inequality_real(coeffs, bound, strict);
    }
    if coeffs.is_empty() {
        // Pure constant comparison: 0 ≤ bound or 0 < bound
        let result = if strict {
            Rational64::from_integer(0) < bound
        } else {
            Rational64::from_integer(0) <= bound
        };
        return Some(ChcExpr::Bool(result));
    }

    // Compute LCM of all denominators (coefficients and bound) per Z3 pattern
    // Reference: z3/src/smt/smt_farkas_util.cpp:100-108
    // Rational64 keeps denominators positive, so the LCM operands are > 0.
    let mut denom_lcm: i128 = 1;
    for coeff in coeffs.values() {
        denom_lcm = checked_lcm_i128(denom_lcm, i128::from(*coeff.denom()))?;
    }
    denom_lcm = checked_lcm_i128(denom_lcm, i128::from(*bound.denom()))?;

    // Build LHS: Σᵢ (aᵢ * lcm)·xᵢ (now with integer coefficients)
    let mut terms: Vec<ChcExpr> = Vec::new();
    let mut sorted_vars: Vec<_> = coeffs.iter().collect();
    sorted_vars.sort_by(|a, b| a.0.cmp(b.0));

    for (var_name, coeff) in sorted_vars {
        let var = ChcVar::new(var_name, ChcSort::Int);
        let var_expr = ChcExpr::var(var);

        // Scale coefficient by LCM to get an exact integer: the denominator
        // divides the LCM by construction, so divide first (exact), then
        // multiply with checked i128 arithmetic (abstain on overflow).
        let cn = i128::from(*coeff.numer());
        let cd = i128::from(*coeff.denom());
        debug_assert_eq!(denom_lcm % cd, 0, "denominator must divide the LCM");
        let scaled = (denom_lcm / cd).checked_mul(cn)?;

        if scaled == 0 {
            continue; // Skip zero coefficients
        } else if scaled == 1 {
            terms.push(var_expr);
        } else if scaled == -1 {
            terms.push(ChcExpr::neg(var_expr));
        } else {
            // Handle both positive (> 1) and negative (< -1) cases
            terms.push(ChcExpr::mul(ChcExpr::Int(scaled), var_expr));
        }
    }

    // Scale bound by LCM, exactly (divide-first, checked multiply).
    let bn = i128::from(*bound.numer());
    let bd = i128::from(*bound.denom());
    debug_assert_eq!(denom_lcm % bd, 0, "bound denominator must divide the LCM");
    let scaled_bound = (denom_lcm / bd).checked_mul(bn)?;

    // Handle case where all coefficients became zero after scaling
    if terms.is_empty() {
        let result = if strict {
            0 < scaled_bound
        } else {
            0 <= scaled_bound
        };
        return Some(ChcExpr::Bool(result));
    }

    let lhs = if terms.len() == 1 {
        terms.pop().expect("len == 1")
    } else {
        ChcExpr::Op(ChcOp::Add, terms.into_iter().map(Arc::new).collect())
    };

    let rhs = ChcExpr::Int(scaled_bound);

    // Build comparison
    Some(if strict {
        ChcExpr::lt(lhs, rhs)
    } else {
        ChcExpr::le(lhs, rhs)
    })
}

/// Emit `Σᵢ aᵢ·xᵢ  <op>  b` over `Real`-sorted variables with exact rational
/// coefficients (`ChcExpr::Real`), for LRA-Lin interpolants
/// (#chc25-lra-convergence). No LCM denominator clearing (unnecessary over ℝ)
/// and no integer rounding (unsound over ℝ); `Rational64` num/den already fit
/// `i64`, so there is no overflow path here.
fn build_linear_inequality_real(
    coeffs: &FxHashMap<String, Rational64>,
    bound: Rational64,
    strict: bool,
) -> Option<ChcExpr> {
    let mut sorted_vars: Vec<_> = coeffs.iter().collect();
    sorted_vars.sort_by(|a, b| a.0.cmp(b.0));

    let mut terms: Vec<ChcExpr> = Vec::new();
    for (var_name, coeff) in sorted_vars {
        let n = *coeff.numer();
        let d = *coeff.denom();
        if n == 0 {
            continue;
        }
        let var_expr = ChcExpr::var(ChcVar::new(var_name, ChcSort::Real));
        if d == 1 && n == 1 {
            terms.push(var_expr);
        } else if d == 1 && n == -1 {
            terms.push(ChcExpr::neg(var_expr));
        } else {
            terms.push(ChcExpr::mul(ChcExpr::Real(n, d), var_expr));
        }
    }

    if terms.is_empty() {
        // Pure constant comparison: 0 <op> bound.
        let result = if strict {
            Rational64::from_integer(0) < bound
        } else {
            Rational64::from_integer(0) <= bound
        };
        return Some(ChcExpr::Bool(result));
    }

    let lhs = if terms.len() == 1 {
        terms.pop().expect("len == 1")
    } else {
        ChcExpr::Op(ChcOp::Add, terms.into_iter().map(Arc::new).collect())
    };
    let rhs = ChcExpr::Real(*bound.numer(), *bound.denom());

    Some(if strict {
        ChcExpr::lt(lhs, rhs)
    } else {
        ChcExpr::le(lhs, rhs)
    })
}

/// Normalize a linear inequality expression by clearing fractions and dividing
/// integer coefficients by their GCD when possible.
///
/// Returns `None` when `expr` is not a supported linear inequality or when the
/// normalized form is identical to the parsed constraint.
pub(crate) fn normalize_linear_inequality_expr(expr: &ChcExpr) -> Option<ChcExpr> {
    let parsed = match expr {
        ChcExpr::Op(ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt, args) if args.len() == 2 => {
            parse_linear_constraint(expr)?
        }
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match args[0].as_ref() {
            ChcExpr::Op(ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt, inner)
                if inner.len() == 2 =>
            {
                parse_linear_constraint(expr)?
            }
            _ => return None,
        },
        _ => return None,
    };

    let normalized = normalize::normalize_constraint(parsed.clone());
    if normalized == parsed {
        return None;
    }

    Some(
        build_linear_inequality(&normalized.coeffs, normalized.bound, normalized.strict)?
            .simplify_constants(),
    )
}

#[cfg(test)]
mod tests;
