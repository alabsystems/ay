// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Source-bound authentication for Bool/BV and exact finite-array queries.

use ay_core::{time::Instant, TermId, TermStore};

use super::{
    array_congruence, balanced_bool_expr, proof_producing_limits, proof_replay_limits,
    AuthenticatedBoolBvUnsatQuery, BoolBvUnsatAuthenticationError, ProofProducingLowerer,
    MAX_PROOF_PRODUCING_TERM_NODES,
};
use crate::{bv_blast_solver::export_bv_blast_proof_expr_with_limits, BvExpr, BvExprExportError};

/// Authenticate that the conjunction of `roots` is UNSAT in the supported
/// quantifier-free Bool/BV fragment, exact recursively finite arrays, and the
/// separate same-array read-congruence reduction.
///
/// This is deliberately independent of the production solver's bit-blast CNF:
/// it lowers the exact source roots again, constructs provenance-bearing gate
/// clauses, obtains a pure-RUP refutation, and replays every gate and resolution
/// step before returning an opaque capability. Internal bit-vector terms may
/// be up to 128 bits subject to the finite proof-production envelope; the
/// serialized/top-level `BvBlastProof` width contract remains unchanged.
/// `caller_deadline`, when present, is clamped with this checker's fixed
/// three-second ceiling.
pub fn authenticate_bool_bv_unsat_query(
    terms: &TermStore,
    roots: &[TermId],
    caller_deadline: Option<Instant>,
) -> Result<AuthenticatedBoolBvUnsatQuery, BoolBvUnsatAuthenticationError> {
    if roots.is_empty() {
        return Err(BoolBvUnsatAuthenticationError::EmptyQuery);
    }
    if roots.len() > MAX_PROOF_PRODUCING_TERM_NODES {
        return Err(BoolBvUnsatAuthenticationError::ResourceLimit {
            reason: format!(
                "source query has {} roots, above the bounded proof-producing limit {}",
                roots.len(),
                MAX_PROOF_PRODUCING_TERM_NODES
            ),
        });
    }
    if let Some(&root) = roots.iter().find(|root| root.index() >= terms.len()) {
        return Err(BoolBvUnsatAuthenticationError::InvalidRoot { root });
    }

    let (limits, deadline) = proof_producing_limits(caller_deadline);
    let term_snapshot = terms.snapshot_stamp();
    let lowered = lower_authentication_roots(terms, roots, deadline)?;
    let conjunction = balanced_bool_expr(lowered.expressions, true, BvExpr::and)
        .map_err(|reason| BoolBvUnsatAuthenticationError::Refutation { reason })?;
    let false_expr = BvExpr::const_val(0, 1);
    let proof = export_bv_blast_proof_expr_with_limits(&conjunction, &false_expr, &limits)
        .map_err(|error| match error {
            BvExprExportError::NoRefutation if lowered.used_array_congruence => {
                BoolBvUnsatAuthenticationError::UnsupportedFragment {
                    reason: "same-array read-congruence reduction is satisfiable".to_string(),
                }
            }
            BvExprExportError::NoRefutation => BoolBvUnsatAuthenticationError::Satisfiable,
            // A bounded envelope that ran out says nothing about the claimed
            // refutation; decline so later certification routes still run.
            resource @ BvExprExportError::ResourceLimit { .. } => {
                BoolBvUnsatAuthenticationError::ResourceLimit {
                    reason: resource.to_string(),
                }
            }
            other => BoolBvUnsatAuthenticationError::Refutation {
                reason: other.to_string(),
            },
        })?;
    let replay_limits = proof_replay_limits(&limits);
    proof
        .validate_with_limits(&replay_limits)
        .map_err(|error| BoolBvUnsatAuthenticationError::Replay {
            reason: error.to_string(),
        })?;

    Ok(AuthenticatedBoolBvUnsatQuery {
        term_snapshot,
        roots: roots.into(),
        used_exact_finite_arrays: lowered.used_exact_finite_arrays,
        used_uninterpreted_leaves: false,
    })
}

/// Authenticate that the conjunction of `roots` is UNSAT in the
/// quantifier-free Bool/BV fragment EXTENDED by the congruence-free
/// uninterpreted-leaf abstraction (#bitblast-original-clause-authority).
///
/// Every ground application of a non-reserved function symbol is lowered to
/// one free leaf keyed by its canonical term identity. The abstraction
/// over-approximates the exact model class — any model of the exact query
/// induces a valuation of the leaves — so a refutation here IS a refutation
/// of the exact query, and every accepted query still carries an
/// independently re-lowered, provenance-bearing gate CNF whose pure-RUP
/// refutation is fully replayed, exactly like
/// [`authenticate_bool_bv_unsat_query`].
///
/// The converse direction deliberately fails closed: when the abstraction is
/// satisfiable and at least one leaf was minted, this returns
/// [`BoolBvUnsatAuthenticationError::UnsupportedFragment`] (a capability
/// DECLINE), never [`BoolBvUnsatAuthenticationError::Satisfiable`] — a
/// satisfiable congruence-free abstraction carries no evidence about the
/// exact query. The exact `Satisfiable` verdict is preserved only when the
/// lowering used no leaf at all (the query was pure Bool/BV, where the two
/// entry points coincide). The exact array-congruence fallback reduction is
/// deliberately NOT combined with this abstraction.
pub fn authenticate_uf_leaf_bool_bv_unsat_query(
    terms: &TermStore,
    roots: &[TermId],
    caller_deadline: Option<Instant>,
) -> Result<AuthenticatedBoolBvUnsatQuery, BoolBvUnsatAuthenticationError> {
    if roots.is_empty() {
        return Err(BoolBvUnsatAuthenticationError::EmptyQuery);
    }
    if roots.len() > MAX_PROOF_PRODUCING_TERM_NODES {
        return Err(BoolBvUnsatAuthenticationError::ResourceLimit {
            reason: format!(
                "source query has {} roots, above the bounded proof-producing limit {}",
                roots.len(),
                MAX_PROOF_PRODUCING_TERM_NODES
            ),
        });
    }
    if let Some(&root) = roots.iter().find(|root| root.index() >= terms.len()) {
        return Err(BoolBvUnsatAuthenticationError::InvalidRoot { root });
    }

    let (limits, deadline) = proof_producing_limits(caller_deadline);
    let term_snapshot = terms.snapshot_stamp();
    let mut lowerer = ProofProducingLowerer::new_with_uninterpreted_leaves(terms, deadline);
    let expressions = lowerer.lower_bool_terms(roots).map_err(|reason| {
        if lowerer.resource_exhausted {
            BoolBvUnsatAuthenticationError::ResourceLimit { reason }
        } else {
            BoolBvUnsatAuthenticationError::UnsupportedFragment { reason }
        }
    })?;
    let used_uninterpreted_leaves = lowerer.used_uninterpreted_leaves;
    let used_exact_finite_arrays = lowerer.used_exact_finite_arrays;
    let conjunction = balanced_bool_expr(expressions, true, BvExpr::and)
        .map_err(|reason| BoolBvUnsatAuthenticationError::Refutation { reason })?;
    let false_expr = BvExpr::const_val(0, 1);
    let proof = export_bv_blast_proof_expr_with_limits(&conjunction, &false_expr, &limits)
        .map_err(|error| match error {
            BvExprExportError::NoRefutation if used_uninterpreted_leaves => {
                BoolBvUnsatAuthenticationError::UnsupportedFragment {
                    reason: "the congruence-free uninterpreted-leaf abstraction is satisfiable, \
                             which is inconclusive for the exact query"
                        .to_string(),
                }
            }
            BvExprExportError::NoRefutation => BoolBvUnsatAuthenticationError::Satisfiable,
            resource @ BvExprExportError::ResourceLimit { .. } => {
                BoolBvUnsatAuthenticationError::ResourceLimit {
                    reason: resource.to_string(),
                }
            }
            other => BoolBvUnsatAuthenticationError::Refutation {
                reason: other.to_string(),
            },
        })?;
    let replay_limits = proof_replay_limits(&limits);
    proof
        .validate_with_limits(&replay_limits)
        .map_err(|error| BoolBvUnsatAuthenticationError::Replay {
            reason: error.to_string(),
        })?;

    Ok(AuthenticatedBoolBvUnsatQuery {
        term_snapshot,
        roots: roots.into(),
        used_exact_finite_arrays,
        used_uninterpreted_leaves,
    })
}

struct LoweredAuthenticationRoots {
    expressions: Vec<BvExpr>,
    used_array_congruence: bool,
    used_exact_finite_arrays: bool,
}

fn lower_authentication_roots(
    terms: &TermStore,
    roots: &[TermId],
    deadline: Instant,
) -> Result<LoweredAuthenticationRoots, BoolBvUnsatAuthenticationError> {
    let mut lowerer = ProofProducingLowerer::new(terms, deadline);
    let pure_reason = match lowerer.lower_bool_terms(roots) {
        Ok(expressions) => {
            return Ok(LoweredAuthenticationRoots {
                expressions,
                used_array_congruence: false,
                used_exact_finite_arrays: lowerer.used_exact_finite_arrays,
            });
        }
        Err(reason) if lowerer.resource_exhausted => {
            return Err(BoolBvUnsatAuthenticationError::ResourceLimit { reason });
        }
        Err(reason) => reason,
    };

    let mut reduction = ProofProducingLowerer::new(terms, deadline);
    match array_congruence::lower_same_array_read_disequalities(terms, roots, &mut reduction) {
        Ok(Some(expressions)) => Ok(LoweredAuthenticationRoots {
            expressions,
            used_array_congruence: true,
            used_exact_finite_arrays: reduction.used_exact_finite_arrays,
        }),
        Ok(None) => Err(BoolBvUnsatAuthenticationError::UnsupportedFragment {
            reason: pure_reason,
        }),
        Err(reason) if reduction.resource_exhausted => {
            Err(BoolBvUnsatAuthenticationError::ResourceLimit { reason })
        }
        Err(reason) => Err(BoolBvUnsatAuthenticationError::UnsupportedFragment {
            reason: format!("{pure_reason}; exact array-congruence reduction declined: {reason}"),
        }),
    }
}
