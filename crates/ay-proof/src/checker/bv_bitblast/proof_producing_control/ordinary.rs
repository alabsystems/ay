// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The ordinary route: refute the negated clause through its ordinary
//! lowering, retrying once with store-chain array reads after a counted
//! exhaustion of a complete-domain attempt that scalarized a read.

use super::*;

/// Refute the negated clause through its ordinary lowering.
///
/// Small-index array reads are first scalarized over their complete domain,
/// which is exact. When that attempt exhausts a COUNTED cap (in lowering, or
/// in the bit-blast/SAT/replay of the lowered query) and it scalarized at least
/// one read the store-chain lane can express, the same clause is lowered once
/// more with those reads taken through their store chains, as a wide index is
/// always read. Scalarizing a read-over-write costs a mux per index point for
/// every write where the store chain needs one comparison per write: measured,
/// `(= v (select (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) off
/// v) off))` overran the 4096-node expression bound, and at `idx7`/`elem32`
/// the lowered query overran the 700 000 bit-blast clause bound, so the strict
/// checker refused AY's own `BvBitBlast` lemma and a correct UNSAT became
/// `unknown (incomplete self-check-rejected)`.
///
/// The retry is sound for the same reason the wide-index lane is: constant
/// defaults and writes are exact, and a read of a declared base array becomes
/// an independent leaf, which only enlarges the model set. It is complete
/// where the first attempt was not: it runs only after that attempt stopped on
/// a COUNTED cap ([`counted_exhaustion`]), never after a satisfiable,
/// unsupported or cancelled one, nor after the hang guard, so it cannot change
/// an answer the complete-domain lane reached. Each attempt has its own
/// counted envelope; both share the one hang guard.
///
/// A pure bit-vector clause may instead be swept past a counted cap inside
/// its single attempt (`limits.sweep`; `bv_blast_solver/sweep.rs` says why
/// not a clause over an array), or lowered definitionally when its tree
/// lowering is too large (`lower_clause_with_reads`). Neither meets this
/// retry: a clause that scalarized an array read mentions an array, so it is
/// never swept or lowered definitionally, and a clause with no array has no
/// read to retry. `route` is the caller's choice of division lowering
/// (`super::division`) and of reading (`super::hypotheses`), and holds for
/// both attempts.
pub(super) fn refute_ordinary_clause(
    terms: &TermStore,
    clause: &[TermId],
    mut limits: BvExprProofLimits,
    deadline: Instant,
    poll: semantic_control::Poll<'_>,
    route: Route<'_>,
) -> Result<(), Failure> {
    limits.sweep = !mentions_array(terms, clause);
    let attempt = |reads, poll: semantic_control::Poll<'_>| {
        attempt_ordinary_refutation(terms, clause, &limits, deadline, poll, route, reads)
    };
    let exhausted = match attempt(array_finite::SmallIndexReads::CompleteDomain, poll) {
        Ok(()) => return admit_success(deadline, poll),
        Err(OrdinaryFailure::Exhausted {
            reason,
            scalarized_small_index_reads: true,
        }) => reason,
        Err(other) => return Err(other.into_failure()),
    };
    attempt(array_finite::SmallIndexReads::StoreChain, poll).map_err(|retry| {
        match retry.into_failure() {
            Failure::Rejected(reason) => Failure::Rejected(format!(
                "{exhausted}; retried with store-chain array reads: {reason}"
            )),
            other => other,
        }
    })?;
    admit_success(deadline, poll)
}

pub(super) fn attempt_ordinary_refutation(
    terms: &TermStore,
    clause: &[TermId],
    limits: &BvExprProofLimits,
    deadline: Instant,
    poll: semantic_control::Poll<'_>,
    route: Route<'_>,
    reads: array_finite::SmallIndexReads,
) -> Result<(), OrdinaryFailure> {
    let lowered = lower_clause_with_reads(
        terms,
        clause,
        deadline,
        route,
        &mut || poll().is_ok(),
        reads,
    )?;
    let scalarized_small_index_reads = lowered.scalarized_small_index_reads;
    replay_refutation(lowered.disjunction, limits, poll).map_err(|error| match error {
        BvExprExportError::Cancelled => OrdinaryFailure::Final(Failure::Cancelled),
        BvExprExportError::ResourceLimit { resource, .. } => OrdinaryFailure::exhausted(
            refutation_failure(&error),
            Some(resource),
            scalarized_small_index_reads,
            deadline,
        ),
        other => OrdinaryFailure::Final(Failure::Rejected(refutation_failure(&other))),
    })
}

/// Whether an attempt that ran out of `resource` (`None`: the lowering's own
/// bounds) stopped on a COUNTED cap, the only stop the store-chain retry
/// follows.
///
/// Every wall-clock bound on this route is the one hang guard `deadline`
/// (`strict_producer_limits`): the lowering's deadline check, the solver's
/// and the replay's. An attempt that ended while the clock was still before
/// it was not stopped by it; the producer's own deadline resources ("... proof
/// deadline", "absolute proof deadline", ...) never count either way. This is
/// the rule the sweep follows (`bv_blast_solver/sweep.rs`: never after a
/// cancellation or a deadline). Unlike the sweep, which re-solves the SAME
/// CNF, the retry lowers a smaller query, so a construction or input-size cap
/// (`preflight construction clauses`) is exactly what it is for. An
/// allocation the producer refused is reported under the resource it was
/// sizing and is followed like that resource's cap: the retry only ever asks
/// for less.
pub(super) fn counted_exhaustion(resource: Option<&str>, deadline: Instant) -> bool {
    Instant::now() < deadline && !resource.is_some_and(|name| name.contains("deadline"))
}

/// Why one ordinary lowering-and-refutation attempt did not accept.
#[derive(Debug)]
pub(super) enum OrdinaryFailure {
    /// A cancellation or a verdict-bearing rejection: never retried.
    Final(Failure),
    /// A counted cap ran out ([`counted_exhaustion`]). Retried with
    /// store-chain reads only when the attempt scalarized a read that lane can
    /// express.
    Exhausted {
        reason: String,
        scalarized_small_index_reads: bool,
    },
}

impl OrdinaryFailure {
    /// A resource refusal: [`Self::Exhausted`] when it was a counted cap,
    /// otherwise a final rejection (which the hang guard re-labels).
    pub(super) fn exhausted(
        reason: String,
        resource: Option<&str>,
        scalarized_small_index_reads: bool,
        deadline: Instant,
    ) -> Self {
        if counted_exhaustion(resource, deadline) {
            Self::Exhausted {
                reason,
                scalarized_small_index_reads,
            }
        } else {
            Self::Final(Failure::Rejected(reason))
        }
    }

    pub(super) fn into_failure(self) -> Failure {
        match self {
            Self::Final(failure) => failure,
            Self::Exhausted { reason, .. } => Failure::Rejected(reason),
        }
    }
}

pub(super) struct LoweredClause {
    pub(super) disjunction: BvExpr,
    pub(super) scalarized_small_index_reads: bool,
}
