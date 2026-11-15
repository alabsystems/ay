// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-bound native checking without expanding LRAT into binary clauses.
//! This private object has no serialization interface. Its gate graph comes
//! from the live expression; exact CNF binding precedes independent LRAT replay.
//! Existing exported BvBlastProof certificates retain their binary format.

use super::cnf::BvExprCnf;
use super::*;
use crate::bv_blast_export::{BvBlastValidateError, BvBlastValidateLimits};

mod refusal_memo;
pub(crate) use refusal_memo::note_uncounted_failure;

pub(super) struct ExprRefutation {
    pub(super) graph: BvBlastProof,
    pub(super) dag: ResolutionDag,
}

pub(crate) fn validate_bv_expr_compact(
    lhs: &BvExpr,
    rhs: &BvExpr,
    limits: &BvExprProofLimits,
    replay: &BvBlastValidateLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<(), BvExprExportError> {
    cancellation::run(keep_going, |poll| {
        let preflight = preflight_bv_equality(lhs, rhs, limits, poll)?;
        let input = cnf::build(lhs, rhs, Some((limits, preflight)), poll)?;
        // An input this thread already saw the counted envelope refuse is
        // refused again without a search (`refusal_memo`).
        refusal_memo::deciding(input, limits, replay, poll, |input, poll| {
            refute_and_replay(input, limits, replay, poll)
        })
    })
}

/// Refute `input` and replay the refutation: the producer's work after the
/// CNF is built, as [`build_bv_expr_refutation`] does it and then
/// [`ExprRefutation::validate`]. A refusal of the search or of the replay
/// hands the input back, so that [`refusal_memo`] may remember it.
fn refute_and_replay(
    input: BvExprCnf,
    limits: &BvExprProofLimits,
    replay: &BvBlastValidateLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> (Result<(), BvExprExportError>, Option<BvExprCnf>) {
    #[cfg(test)]
    retained::producer_test_counter::record();
    let refuted =
        materialize_sat_clauses_with_cancellation(&input.clauses, &limits.resolution, keep_going)
            .and_then(|clauses| sweep::bounded_refutation(&input, &clauses, limits, keep_going));
    let dag = match refuted {
        Ok((dag, _)) => dag,
        Err(refusal) => return (Err(refusal), Some(input)),
    };
    if let Err(stopped) = finish_expr_export(Some(limits), keep_going) {
        return (Err(stopped), None);
    }
    let proof = ExprRefutation {
        graph: input.into_graph(),
        dag,
    };
    match proof.validate(limits, replay, keep_going) {
        Ok(()) => {
            drop(proof);
            (finish_expr_export(Some(limits), keep_going), None)
        }
        Err(refusal) => (Err(refusal), Some(BvExprCnf::from_graph(proof.graph))),
    }
}

impl ExprRefutation {
    pub(super) fn validate(
        &self,
        limits: &BvExprProofLimits,
        replay: &BvBlastValidateLimits,
        keep_going: &mut dyn FnMut() -> bool,
    ) -> Result<(), BvExprExportError> {
        self.bind(keep_going)?;
        self.graph
            .validate_cnf_with_limits_and_cancellation(replay, keep_going)
            .map_err(|error| match error {
                BvBlastValidateError::Cancelled => BvExprExportError::Cancelled,
                other => BvExprExportError::RefutationNotSurfaceable(format!(
                    "compact CNF replay: {other}"
                )),
            })?;
        let mut validation = limits.resolution.validation.clone();
        validation.deadline = match (validation.deadline, limits.resolution.deadline) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        };
        self.dag
            .validate_with_limits_and_cancellation(&validation, keep_going)
            .map_err(|error| {
                map_bounded_resolution_error(
                    ResolutionProofError::Validation(error),
                    &limits.resolution,
                )
            })?;
        finish_expr_export(Some(limits), keep_going)
    }

    pub(super) fn bind(
        &self,
        keep_going: &mut dyn FnMut() -> bool,
    ) -> Result<(), BvExprExportError> {
        poll_export(keep_going)?;
        if self.dag.num_vars != self.graph.vars.len()
            || self.dag.original_clauses.len() != self.graph.clauses.len()
        {
            return Err(BvExprExportError::Malformed(
                "compact refutation CNF shape differs".into(),
            ));
        }
        for (index, ((id, actual), expected)) in self
            .dag
            .original_clauses
            .iter()
            .zip(&self.graph.clauses)
            .enumerate()
        {
            poll_export(keep_going)?;
            if *id != index as u64 + 1 || actual.len() != expected.lits.len() {
                return Err(BvExprExportError::Malformed(
                    "compact refutation clause identity differs".into(),
                ));
            }
            for (actual, expected) in actual.iter().zip(&expected.lits) {
                poll_export(keep_going)?;
                if lit_from_sat(actual) != *expected {
                    return Err(BvExprExportError::Malformed(
                        "compact refutation original literal differs".into(),
                    ));
                }
            }
        }
        Ok(())
    }

    pub(super) fn expand(
        mut self,
        limits: Option<&BvExprProofLimits>,
        keep_going: &mut dyn FnMut() -> bool,
    ) -> Result<BvBlastProof, BvExprExportError> {
        let expansion_limits = limits
            .map(|limits| {
                let deadline = limits.resolution.deadline.ok_or_else(|| {
                    BvExprExportError::Malformed(
                        "bounded proof limits require an absolute deadline".into(),
                    )
                })?;
                Ok::<_, BvExprExportError>(RupExpansionLimits {
                    max_steps: limits.max_resolution_steps,
                    max_literals: limits.max_expanded_literals,
                    max_work: limits.max_expansion_work,
                    max_bytes: limits.max_expansion_bytes,
                    deadline,
                })
            })
            .transpose()?;
        let refutation = expand_dag_to_resolution_with_cancellation(
            &self.dag,
            &self.graph.clauses,
            expansion_limits,
            keep_going,
        )
        .map_err(|error| match error {
            BvSolvedExportError::Cancelled => BvExprExportError::Cancelled,
            BvSolvedExportError::ResourceLimit {
                resource,
                limit,
                actual,
            } => BvExprExportError::ResourceLimit {
                resource,
                limit,
                actual,
            },
            other => BvExprExportError::RefutationNotSurfaceable(other.to_string()),
        })?;
        if let Some(limits) = limits {
            if refutation.steps.len() > limits.max_resolution_steps {
                return Err(BvExprExportError::ResourceLimit {
                    resource: "expanded resolution steps",
                    limit: limits.max_resolution_steps,
                    actual: refutation.steps.len(),
                });
            }
        }

        self.graph.refutation = refutation;
        drop(self.dag);
        finish_expr_export(limits, keep_going)?;
        Ok(self.graph)
    }
}

#[cfg(test)]
mod tests;
