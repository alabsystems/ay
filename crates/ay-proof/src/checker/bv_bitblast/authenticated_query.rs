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
use crate::{
    bv_blast_export::{BvBlastProof, BvBlastValidateError},
    bv_blast_solver::{export_bv_blast_proof_expr_with_limits, BvExprProofLimits},
    BvExpr, BvExprExportError,
};

mod counted_declines;

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
/// The lane's budget is COUNTED (see `producer_limits.rs`); `caller_deadline`,
/// when present, and otherwise the producer's hang guard, only stop it. A
/// stop — like any exhausted cap — is a capability DECLINE, never a veto.
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
    let proof =
        export_refutation(&conjunction, &limits, deadline).map_err(|error| match error {
            BvExprExportError::NoRefutation
                if lowered.used_array_congruence || lowered.used_uninterpreted_leaves =>
            {
                BoolBvUnsatAuthenticationError::UnsupportedFragment {
                    reason:
                        "array read abstraction is satisfiable; the exact query is inconclusive"
                            .to_string(),
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
        .map_err(replay_failure)?;

    Ok(AuthenticatedBoolBvUnsatQuery {
        term_snapshot,
        roots: roots.into(),
        used_exact_finite_arrays: lowered.used_exact_finite_arrays,
        used_uninterpreted_leaves: lowered.used_uninterpreted_leaves,
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
    #[cfg(test)]
    lowerer.audit_census();
    let used_uninterpreted_leaves = lowerer.used_uninterpreted_leaves;
    let used_exact_finite_arrays = lowerer.used_exact_finite_arrays;
    let conjunction = balanced_bool_expr(expressions, true, BvExpr::and)
        .map_err(|reason| BoolBvUnsatAuthenticationError::Refutation { reason })?;
    let proof =
        export_refutation(&conjunction, &limits, deadline).map_err(|error| match error {
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
        .map_err(replay_failure)?;

    Ok(AuthenticatedBoolBvUnsatQuery {
        term_snapshot,
        roots: roots.into(),
        used_exact_finite_arrays,
        used_uninterpreted_leaves,
    })
}

/// Authenticate that the conjunction of `roots` is UNSAT in the
/// quantifier-free Bool/BV fragment extended by the congruence-free
/// uninterpreted-leaf abstraction AND by the Bool-ATOM abstraction over
/// operands whose sort lies outside the finite Bool/BitVec/array universe
/// (`Int`, `Char`, `Real`, …) (#bitblast-original-clause-authority).
///
/// This is a strictly separate entry point from
/// [`authenticate_uf_leaf_bool_bv_unsat_query`] so that the latter — and the
/// `CheckedQpfInstanceRefutation` lane that calls it — keeps a bit-identical
/// accept set. Widening an existing lane to admit queries it previously
/// refused is exactly what this split avoids.
///
/// # Why the abstraction is sound in the refutation direction
///
/// Write `Q` for the conjunction of the exact roots and `A` for its lowering.
/// For any structure `M` and assignment `nu` with `M, nu |= Q`, define a
/// Bool/BitVec valuation `beta` by `beta(proof_bool_t) :=` the truth value of
/// `t` under `(M, nu)` and `beta(proof_bv_t) :=` the width-`w` value of `t`.
/// Every leaf minted here is BOOLEAN and stands for a BOOL-SORTED term, so
/// that map is the IDENTITY on the two-element Boolean domain and is total.
/// Every non-leaf constructor the lowerer emits interprets its source operator
/// exactly (Bool `ite`, BV `ite`, the comparison lowerings, and the
/// same-width requirement all preserve meaning). By structural induction the
/// lowering evaluates under `beta` exactly as the source evaluates under
/// `(M, nu)`, so `SAT(Q)` implies `SAT(A)` and therefore `UNSAT(A)` implies
/// `UNSAT(Q)`.
///
/// No `Int`-specific reasoning is assumed anywhere: ordering (`<=`, `<`) and
/// arithmetic (`+`, `*`, `div`) are not reserved vocabulary and never reach an
/// interpreted arm, so `A` asserts nothing about transitivity, totality or
/// wraparound, and NO bit-vector adder is ever emitted for an integer term.
/// Congruence between distinct non-finitely-sorted subterms is likewise
/// forgotten: two syntactically distinct `Int` terms that happen to be
/// semantically equal sit in different atoms and become independent leaves.
/// That gives `A` strictly MORE models than `Q`, which in the refutation
/// direction can only turn a real refutation into a DECLINE — never a
/// satisfiable query into a refutation. The dangerous direction is MERGING
/// two terms that are not equal, and it cannot occur: leaves are keyed by
/// hash-consed `TermId`, so two leaves coincide only when the source terms are
/// syntactically identical and hence equal in every model. Reflexivity is
/// forgotten too — `(= i i)` over `Int` becomes a free leaf that `A` may set
/// false — which is again strictly more models.
///
/// Groundness is automatic: `Forall`, `Exists` and `Let` are rejected by the
/// lowerer's node classification, so `beta` is always well defined.
///
/// The converse direction fails closed exactly as in
/// [`authenticate_uf_leaf_bool_bv_unsat_query`]: a satisfiable abstraction
/// that minted at least one leaf returns
/// [`BoolBvUnsatAuthenticationError::UnsupportedFragment`] (a capability
/// DECLINE), never [`BoolBvUnsatAuthenticationError::Satisfiable`].
pub fn authenticate_atom_leaf_bool_bv_unsat_query(
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
    let mut lowerer = ProofProducingLowerer::new_with_non_finite_atom_leaves(terms, deadline);
    let expressions = lowerer.lower_bool_terms(roots).map_err(|reason| {
        if lowerer.resource_exhausted {
            BoolBvUnsatAuthenticationError::ResourceLimit { reason }
        } else {
            BoolBvUnsatAuthenticationError::UnsupportedFragment { reason }
        }
    })?;
    #[cfg(test)]
    lowerer.audit_census();
    let used_uninterpreted_leaves = lowerer.used_uninterpreted_leaves;
    let used_exact_finite_arrays = lowerer.used_exact_finite_arrays;
    let conjunction = balanced_bool_expr(expressions, true, BvExpr::and)
        .map_err(|reason| BoolBvUnsatAuthenticationError::Refutation { reason })?;
    let proof =
        export_refutation(&conjunction, &limits, deadline).map_err(|error| match error {
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
        .map_err(replay_failure)?;

    Ok(AuthenticatedBoolBvUnsatQuery {
        term_snapshot,
        roots: roots.into(),
        used_exact_finite_arrays,
        used_uninterpreted_leaves,
    })
}

/// Export the lane's refutation of `conjunction` — or repeat the counted
/// exhaustion this exact lowered query already reached under the same caps
/// (`counted_declines.rs`).
fn export_refutation(
    conjunction: &BvExpr,
    limits: &BvExprProofLimits,
    deadline: Instant,
) -> Result<BvBlastProof, BvExprExportError> {
    let key = counted_declines::key(conjunction);
    if let Some(exhausted) = counted_declines::remembered(key) {
        return Err(exhausted);
    }
    counted_declines::note_export();
    let exported =
        export_bv_blast_proof_expr_with_limits(conjunction, &BvExpr::const_val(0, 1), limits);
    // Every wall-clock check in the export compares the monotonic clock with
    // this one `deadline`: an exhaustion that ended before it was a counted
    // cap's, never the deadline's.
    if let Err(exhausted @ BvExprExportError::ResourceLimit { .. }) = &exported {
        if Instant::now() < deadline {
            counted_declines::remember(key, exhausted);
        }
    }
    exported
}

/// Classify a failed independent replay of the lane's OWN surfaced proof.
///
/// Only a replay that examined a step and rejected it is evidence that the
/// claimed refutation is wrong ([`BoolBvUnsatAuthenticationError::Replay`], a
/// veto). A replay that ran out of its counted caps, or was stopped by the
/// caller's deadline or the hang guard, examined nothing it could object to:
/// that is the lane running out of its own envelope, a DECLINE like every other
/// exhausted bound here. (A three-second wall used to end replay under load
/// and was read as a veto.)
fn replay_failure(error: BvBlastValidateError) -> BoolBvUnsatAuthenticationError {
    match error {
        BvBlastValidateError::DeadlineExceeded
        | BvBlastValidateError::Cancelled
        | BvBlastValidateError::WorkOverflow
        | BvBlastValidateError::ResourceLimit { .. } => {
            BoolBvUnsatAuthenticationError::ResourceLimit {
                reason: format!("replay: {error}"),
            }
        }
        other => BoolBvUnsatAuthenticationError::Replay {
            reason: other.to_string(),
        },
    }
}

struct LoweredAuthenticationRoots {
    expressions: Vec<BvExpr>,
    used_array_congruence: bool,
    used_uninterpreted_leaves: bool,
    used_exact_finite_arrays: bool,
}

fn lower_authentication_roots(
    terms: &TermStore,
    roots: &[TermId],
    deadline: Instant,
) -> Result<LoweredAuthenticationRoots, BoolBvUnsatAuthenticationError> {
    let mut lowerer = ProofProducingLowerer::new(terms, deadline);
    let pure_reason = match lowerer.lower_bool_terms(roots) {
        Ok(mut expressions) => {
            let consistency = lowerer.take_sparse_read_consistency().map_err(|reason| {
                if lowerer.resource_exhausted {
                    BoolBvUnsatAuthenticationError::ResourceLimit { reason }
                } else {
                    BoolBvUnsatAuthenticationError::UnsupportedFragment { reason }
                }
            })?;
            expressions.extend(consistency);
            #[cfg(test)]
            lowerer.audit_census();
            return Ok(LoweredAuthenticationRoots {
                expressions,
                used_array_congruence: false,
                used_uninterpreted_leaves: lowerer.used_uninterpreted_leaves,
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
        Ok(Some(expressions)) => {
            #[cfg(test)]
            reduction.audit_census();
            Ok(LoweredAuthenticationRoots {
                expressions,
                used_array_congruence: true,
                used_uninterpreted_leaves: reduction.used_uninterpreted_leaves,
                used_exact_finite_arrays: reduction.used_exact_finite_arrays,
            })
        }
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

#[cfg(test)]
#[path = "authenticated_query/budget_tests.rs"]
mod budget_tests;
