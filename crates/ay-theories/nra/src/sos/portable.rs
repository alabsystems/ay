// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Private exact-clause source and candidate conversion. Nothing here publishes
//! a verdict, exports a public search API, or substitutes for ay-proof replay.

use super::budget::{rational_fits, SosPolynomialBudget, SosProgress};
use super::*;
use ay_core::{NraSosCertificate, NraSosOrigin, NraSosRational, NraSosTerm, ProofStep, TermStore};
use num_integer::Integer;
use std::mem::size_of;

/// Bytes of one basis monomial: its vector header plus at most two factors.
/// Evaluated at compile time, so it cannot overflow at run time.
const BASIS_ENTRY_BYTES: usize = size_of::<Vec<TermId>>() + 2 * size_of::<TermId>();

/// Keep the unfiltered factor namespace inseparable from its exact clause.
/// Accessors are borrowed; no caller can mutate the stored source mapping.
pub(crate) struct SosClauseSource<'a> {
    // Keep the term universe immutably borrowed until conversion finishes;
    // rollback/reuse cannot silently change the meaning of these exact IDs.
    _terms: &'a TermStore,
    clause: Vec<TermId>,
    constraints: Vec<MultiConstraint>,
    variables: Vec<TermId>,
}

impl<'a> SosClauseSource<'a> {
    pub(crate) fn from_clause(
        terms: &'a TermStore,
        clause: &[TermId],
        budget: &mut SosPolynomialBudget<'_>,
    ) -> Option<Self> {
        let constraints = crate::NraSolver::sos_clause_constraints(terms, clause, budget)?;
        let slots = clause.len().checked_add(MAX_VARS)?;
        if !budget.charge(slots, slots.checked_mul(size_of::<TermId>())?) {
            return None;
        }
        let mut exact_clause = Vec::new();
        exact_clause.try_reserve_exact(clause.len()).ok()?;
        exact_clause.extend_from_slice(clause);
        let mut variables = Vec::new();
        variables.try_reserve_exact(MAX_VARS).ok()?;
        for &variable in constraints
            .iter()
            .flat_map(|source| &source.poly.terms)
            .flat_map(|(monomial, _)| monomial)
        {
            if !budget.charge(MAX_VARS, 0) {
                return None;
            }
            if !variables.contains(&variable) {
                if variables.len() == MAX_VARS {
                    return None;
                }
                variables.push(variable);
            }
        }
        variables.sort_unstable();
        budget.poll().then_some(Self {
            _terms: terms,
            clause: exact_clause,
            constraints,
            variables,
        })
    }

    pub(crate) fn constraints(&self) -> &[MultiConstraint] {
        &self.constraints
    }

    pub(crate) fn variables(&self) -> &[TermId] {
        &self.variables
    }

    /// A candidate still needs independent ay-proof authentication. Returning
    /// its exact conclusion along with the DTO prevents accidental attachment
    /// to a filtered or reordered caller clause during this conversion.
    pub(crate) fn convert_candidate(
        &self,
        candidate: &SosCertificate,
        progress: &mut SosProgress<'_>,
    ) -> Option<ProofStep> {
        if !progress.poll() || !candidate_dimensions_fit(candidate) {
            return None;
        }
        candidate
            .verify_with_progress(&self.constraints, progress)
            .ok()?;
        let n = candidate.basis.len();
        let cells = n.checked_mul(n)?;
        let bytes = self
            .clause
            .len()
            .checked_mul(size_of::<TermId>())?
            .checked_add(n.checked_mul(BASIS_ENTRY_BYTES)?)?
            .checked_add(n.checked_mul(size_of::<Vec<NraSosRational>>())?)?
            .checked_add(cells.checked_mul(size_of::<NraSosRational>())?)?
            .checked_add(candidate.terms.len().checked_mul(size_of::<NraSosTerm>())?)?;
        let units = self
            .clause
            .len()
            .checked_add(n)?
            .checked_add(cells)?
            .checked_add(candidate.terms.len())?;
        if !progress.charge(units, bytes) {
            return None;
        }
        let mut gram = Vec::new();
        gram.try_reserve_exact(n).ok()?;
        for row in &candidate.gram {
            let mut converted = Vec::new();
            converted.try_reserve_exact(n).ok()?;
            for coefficient in row {
                converted.push(convert_rational(coefficient, progress)?);
            }
            gram.push(converted);
        }
        let mut terms = Vec::new();
        terms.try_reserve_exact(candidate.terms.len()).ok()?;
        for term in &candidate.terms {
            let slot = |index: usize| {
                (index < self.clause.len())
                    .then(|| u32::try_from(index).ok())
                    .flatten()
            };
            let origin = match term.origin {
                CertOrigin::Constraint(index) => NraSosOrigin::ClauseLiteral {
                    position: slot(index)?,
                },
                CertOrigin::Product(left, right) => NraSosOrigin::Product {
                    left: slot(left)?,
                    right: slot(right)?,
                },
            };
            terms.push(NraSosTerm {
                origin,
                multiplier: convert_rational(&term.multiplier, progress)?,
            });
        }
        let certificate = NraSosCertificate {
            basis: candidate.basis.clone(),
            gram,
            terms,
            rhs: convert_rational(&candidate.rhs, progress)?,
        };
        certificate.validate_shape().ok()?;
        if !progress.poll() {
            return None;
        }
        let clause = self.clause.clone();
        progress.poll().then_some(ProofStep::NraSos {
            clause,
            certificate,
        })
    }
}

fn candidate_dimensions_fit(candidate: &SosCertificate) -> bool {
    let n = candidate.basis.len();
    n > 0
        && n <= NraSosCertificate::MAX_BASIS
        && candidate.gram.len() == n
        && candidate.gram.iter().all(|row| row.len() == n)
        && candidate.terms.len() <= NraSosCertificate::MAX_TERMS
        && candidate.basis.iter().all(|monomial| monomial.len() <= 2)
}

fn convert_rational(value: &BigRational, progress: &mut SosProgress<'_>) -> Option<NraSosRational> {
    if !rational_fits(value) {
        return None;
    }
    let bits = (value.numer().bits() + value.denom().bits()).max(1) as usize;
    // Both inputs fit 1024 bits; charge a conservative quadratic Euclidean
    // normalization bound and scratch BEFORE gcd or integer cloning.
    if !progress.charge(bits * bits, bits.div_ceil(8) * 32 + 512)
        || !value.numer().gcd(value.denom()).is_one()
    {
        return None;
    }
    Some(NraSosRational {
        numerator: value.numer().clone(),
        denominator: value.denom().clone(),
    })
}

#[cfg(test)]
mod tests;
