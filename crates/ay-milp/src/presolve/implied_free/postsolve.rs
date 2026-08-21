// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl AffineAggregationPostsolve {
    pub(crate) fn const_delta(&self) -> &BigRational {
        &self.const_delta
    }

    /// Recover the caller's literal column frame.  Reverse order is
    /// load-bearing: an earlier recovery may name a column eliminated later.
    pub(crate) fn widen(
        &self,
        reduced: &[BigRational],
        deadline: Option<Instant>,
        memory_budget: Option<usize>,
    ) -> Option<Vec<BigRational>> {
        if reduced.len() != self.n_reduced
            || self.recover.len() > MAX_ELIMINATIONS
            || self.recovery_terms > MAX_RECOVERY_TERMS
        {
            return None;
        }
        let planned = planned_widen_bytes(self.n_orig, self.recovery_terms)?;
        let guard = ResourceGuard::new(deadline, memory_budget, planned)?;
        let mut full = Vec::new();
        full.try_reserve_exact(self.n_orig).ok()?;
        full.resize_with(self.n_orig, BigRational::zero);
        for (original, mapped) in self.map.iter().enumerate() {
            if original.is_multiple_of(256) && guard.stopped() {
                return None;
            }
            if let Some(column) = mapped {
                full[original] = reduced[column.index()].clone();
            }
        }
        let mut terms_seen = 0usize;
        for (recovery_index, recovery) in self.recover.iter().rev().enumerate() {
            if recovery_index.is_multiple_of(64) && guard.stopped() {
                return None;
            }
            match recovery {
                AffineRecovery::Fixed { col, value } => {
                    if *col >= full.len() || !rational_fits(value) {
                        return None;
                    }
                    full[*col] = value.clone();
                }
                AffineRecovery::Equality {
                    row: _,
                    col,
                    constant,
                    terms,
                } => {
                    if *col >= full.len() {
                        return None;
                    }
                    let mut value = constant.clone();
                    for (term_index, (column, coefficient)) in terms.iter().enumerate() {
                        terms_seen = terms_seen.checked_add(1)?;
                        if term_index.is_multiple_of(256) && guard.stopped() {
                            return None;
                        }
                        if *column >= full.len() || !rational_fits(coefficient) {
                            return None;
                        }
                        value += coefficient * &full[*column];
                        if !rational_fits(&value) {
                            return None;
                        }
                    }
                    full[*col] = value;
                }
            }
        }
        (terms_seen == self.recovery_terms && !guard.stopped()).then_some(full)
    }

    /// Test-facing wrapper over [`Self::certificate_for_outcome_with_source_primal`]
    /// with no independently recovered source primal.
    #[cfg(test)]
    pub(crate) fn certificate_for_outcome(
        &self,
        outcome: &Outcome,
        reduced: &Model,
        source: &Model,
        deadline: Option<Instant>,
        memory_budget: Option<usize>,
    ) -> Option<AffineAggregationCertificate> {
        let source_primal = match outcome {
            Outcome::Optimal { model_values, .. } | Outcome::Feasible { model_values, .. } => {
                Some(self.widen(model_values, deadline, memory_budget)?)
            }
            _ => None,
        };
        self.certificate_for_outcome_with_source_primal(
            outcome,
            reduced,
            source,
            source_primal,
            deadline,
            memory_budget,
        )
    }

    pub(crate) fn certificate_for_outcome_with_source_primal(
        &self,
        outcome: &Outcome,
        reduced: &Model,
        source: &Model,
        source_primal: Option<Vec<BigRational>>,
        deadline: Option<Instant>,
        memory_budget: Option<usize>,
    ) -> Option<AffineAggregationCertificate> {
        if crate::cert_io::canonical_digest(reduced) != self.analysis.reduced_digest
            || crate::cert_io::canonical_digest(source) != self.analysis.source_digest
        {
            return None;
        }
        let planned = planned_certificate_bytes(outcome, self.n_orig, self.n_reduced)?;
        let guard = ResourceGuard::new(deadline, memory_budget, planned)?;
        let (claim, inner_proof, reduced_primal, source_primal) = match outcome {
            Outcome::Optimal {
                value,
                model_values,
                cert,
            } => {
                let source_values = source_primal?;
                source.check_point(&source_values).ok()?;
                let source_value = source.objective_value_at(&source_values);
                if source_value != value + &self.const_delta {
                    return None;
                }
                let claim = if source.has_objective() {
                    AffineAggregationClaim::Optimal {
                        value: source_value,
                    }
                } else {
                    AffineAggregationClaim::Feasible
                };
                let proof = if source.has_objective() {
                    cert.as_ref()
                        .map_or(AffineAggregationInnerProof::Unsupported, |certificate| {
                            AffineAggregationInnerProof::Optimality(certificate.clone())
                        })
                } else {
                    // A zero-objective LP certificate proves no source claim.
                    // Keep a feasibility artifact honest even if the reduced
                    // engine happened to attach that vacuous object.
                    AffineAggregationInnerProof::Unsupported
                };
                (
                    claim,
                    proof,
                    Some(model_values.clone()),
                    Some(source_values),
                )
            }
            Outcome::Feasible { model_values, .. } => {
                let source_values = source_primal?;
                source.check_point(&source_values).ok()?;
                (
                    AffineAggregationClaim::Feasible,
                    AffineAggregationInnerProof::Unsupported,
                    Some(model_values.clone()),
                    Some(source_values),
                )
            }
            Outcome::Infeasible { cert, tree_cert } => {
                let proof = cert.as_ref().map_or_else(
                    || {
                        tree_cert
                            .as_ref()
                            .map_or(AffineAggregationInnerProof::Unsupported, |tree| {
                                AffineAggregationInnerProof::InfeasibilityTree(tree.clone())
                            })
                    },
                    |certificate| AffineAggregationInnerProof::Farkas(certificate.clone()),
                );
                (AffineAggregationClaim::Infeasible, proof, None, None)
            }
            _ => return None,
        };
        if guard.stopped() {
            return None;
        }
        Some(AffineAggregationCertificate {
            analysis: self.analysis.clone(),
            claim,
            inner_proof,
            reduced_primal,
            source_primal,
        })
    }

    #[cfg(test)]
    pub(super) fn recoveries(&self) -> &[AffineRecovery] {
        self.recover.as_ref()
    }
}
