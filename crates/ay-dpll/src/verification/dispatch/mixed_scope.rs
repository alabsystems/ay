// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scoped-first combined re-check of a mixed theory conflict
//! (#combiner-verify-scope).
//!
//! `verify_mixed_conflict_semantic` re-solves a conflict's literals (plus
//! their unconditional support) in a fresh Nelson-Oppen combiner. That
//! combiner's EUF registered congruence over every function application of
//! the whole term store, so every new conflict paid an O(|store|) e-graph
//! initialization and every merge walked parent lists of unrelated terms.
//!
//! The re-check now first runs with congruence registered only over the
//! subterm closure of the verification context, and that run's verdict is
//! used ONLY when it re-proves the conflict. Any other outcome (`Sat`, a
//! split or model-equality request, an undecided lemma batch, a budget stop)
//! is discarded and the full-store re-check decides, exactly as before:
//!
//! - Nothing the full-store check rejects is accepted on a weaker basis. The
//!   scoped run accepts only by deriving UNSAT, from the same literals with the
//!   same solvers and a SUBSET of the full check's congruence registrations
//!   (every scoped merge is a full-store merge). That is a genuine
//!   re-derivation for exactly this literal set, which is what the `Reproved`
//!   verdicts certify. The full-store check calling the same literal set `Sat`
//!   would make one of the two runs unsound; debug builds re-run the full
//!   check behind every scoped re-proof and assert it never does.
//! - Every outcome other than a scoped re-proof is the full-store verdict.
//!
//! The scoped run pays off only when it re-proves AND the store holds many
//! applications outside the conflict. Where most combined conflicts end
//! inconclusive (array lemma splits on the QF_AUFLIA swap family), the
//! full-store re-check runs anyway and the scoped run is pure overhead, so a
//! query attempts it only while its own record says it pays
//! ([`ScopedRecheckGate`]). Callers outside a query (no memo) keep the
//! full-store re-check alone.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{TermId, TermStore, TheoryLit, TheoryResult, TheorySolver};

use super::{
    classify_mixed_verifiability, close_valid_lemma_clauses, conflict_involves_int_real_mix,
    conflict_involves_nonlinear, make_verification_combiner, verification_combiner_kind,
    ConflictSemanticVerdict, LemmaTrailClosure, MixedVerifiability, VerificationCombinerKind,
};
use crate::combined_solvers::combiner::TheoryCombiner;
use crate::verification::VerificationError;

/// Which function applications the re-check's EUF registers for congruence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CongruenceScope {
    /// Every application in the term store: the reference re-check.
    FullStore,
    /// Only applications in the subterm closure of the verification context.
    Context,
}

/// Whether one query attempts the scoped re-check first
/// (#combiner-verify-scope).
///
/// A saturating credit over the query's scoped outcomes: a scoped re-proof
/// earns one credit, any other scoped outcome (which the full-store re-check
/// then repeats) costs [`Self::MISS_COST`], so the scoped run stays on while
/// more than three quarters of the query's scoped runs re-prove. A re-proof
/// saves at most the out-of-scope congruence registration, a fraction of a
/// full re-check (about 0.4 on deductive-checks's 7k-term stores, nearly nothing on
/// a few hundred terms), while a miss pays a whole scoped run on top of the
/// full one. Without credit the query re-checks on the full store alone,
/// except for one scoped probe every [`Self::PROBE_INTERVAL`] calls, so a
/// later run of re-provable conflicts wins the scoped path back.
///
/// The gate picks only WHICH re-checks run, never what one concludes: every
/// published verdict is a scoped re-proof or the unchanged full-store
/// verdict. Whether a conflict is accepted is therefore the full-store
/// decision either way, and a skipped scoped run at most leaves an accepted
/// conflict with the full-store label instead of a scoped re-proof. It counts
/// outcomes, never time, so a query's verdicts never depend on timing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ScopedRecheckGate {
    credit: u8,
    calls_without_scoped_run: u8,
}

impl ScopedRecheckGate {
    /// Credit of a fresh query: two misses in a row switch the scoped run off.
    const START_CREDIT: u8 = 4;
    const MAX_CREDIT: u8 = 8;
    const MISS_COST: u8 = 3;
    const PROBE_INTERVAL: u8 = 64;

    /// Whether this call runs the scoped re-check first.
    fn admits_scoped_run(&mut self) -> bool {
        if self.credit > 0 {
            return true;
        }
        self.calls_without_scoped_run += 1;
        self.calls_without_scoped_run >= Self::PROBE_INTERVAL
    }

    /// Book the outcome of a scoped run this gate admitted.
    fn record(&mut self, scoped_reproved: bool) {
        self.calls_without_scoped_run = 0;
        self.credit = if scoped_reproved {
            (self.credit + 1).min(Self::MAX_CREDIT)
        } else {
            self.credit.saturating_sub(Self::MISS_COST)
        };
    }
}

impl Default for ScopedRecheckGate {
    fn default() -> Self {
        Self {
            credit: Self::START_CREDIT,
            calls_without_scoped_run: 0,
        }
    }
}

/// Which verdict a definitive re-derivation under `kind` earns: the array
/// theory re-running its own inference is not an independent check.
pub(super) fn reproved_verdict(kind: VerificationCombinerKind) -> ConflictSemanticVerdict {
    if matches!(
        kind,
        VerificationCombinerKind::AufLia
            | VerificationCombinerKind::AufLra
            | VerificationCombinerKind::ArrayEuf
    ) {
        ConflictSemanticVerdict::ReprovedByArrayTheory
    } else {
        ConflictSemanticVerdict::Reproved
    }
}

/// Re-check the verification context: scoped first when the query's gate
/// admits it (the full store then decides unless the scoped run re-proved
/// it, see the module docs), otherwise on the full store alone.
pub(super) fn recheck_mixed_context(
    terms: &TermStore,
    verification_context: &[TheoryLit],
    trail: DetHashMap<TermId, bool>,
    selected_combiner_kind: VerificationCombinerKind,
    scoped_recheck: Option<&mut ScopedRecheckGate>,
) -> Result<ConflictSemanticVerdict, VerificationError> {
    let reproved = reproved_verdict(selected_combiner_kind);
    recheck_under_gate(reproved, trail, scoped_recheck, |scope, trail| {
        recheck_mixed_context_in(
            scope,
            terms,
            verification_context,
            trail,
            selected_combiner_kind,
            reproved,
        )
    })
}

/// The gate's choice between [`decide_scoped_first`] and the full-store
/// re-check alone; only an admitted scoped run is booked.
fn recheck_under_gate(
    reproved: ConflictSemanticVerdict,
    trail: DetHashMap<TermId, bool>,
    scoped_recheck: Option<&mut ScopedRecheckGate>,
    mut recheck: impl FnMut(
        CongruenceScope,
        DetHashMap<TermId, bool>,
    ) -> Result<ConflictSemanticVerdict, VerificationError>,
) -> Result<ConflictSemanticVerdict, VerificationError> {
    let Some(gate) = scoped_recheck else {
        return recheck(CongruenceScope::FullStore, trail);
    };
    if !gate.admits_scoped_run() {
        return recheck(CongruenceScope::FullStore, trail);
    }
    let (verdict, scoped_reproved) = decide_scoped_first(reproved, trail, recheck);
    gate.record(scoped_reproved);
    verdict
}

/// The decision rule: a scoped re-proof is published; any other scoped
/// outcome is discarded and the full-store re-check decides. Every run gets
/// its own copy of the fixed-context trail. Also reports whether the scoped
/// run re-proved.
fn decide_scoped_first(
    reproved: ConflictSemanticVerdict,
    trail: DetHashMap<TermId, bool>,
    mut recheck: impl FnMut(
        CongruenceScope,
        DetHashMap<TermId, bool>,
    ) -> Result<ConflictSemanticVerdict, VerificationError>,
) -> (Result<ConflictSemanticVerdict, VerificationError>, bool) {
    let scoped = recheck(CongruenceScope::Context, trail.clone());
    if matches!(scoped, Ok(verdict) if verdict == reproved) {
        #[cfg(debug_assertions)]
        {
            let full = recheck(CongruenceScope::FullStore, trail);
            debug_assert!(
                !matches!(full, Err(VerificationError::ConflictIsSat)),
                "the context-scoped re-check re-proved a literal set that the full-store \
                 re-check calls Sat"
            );
            if !matches!(full, Ok(verdict) if verdict == reproved) {
                // Not a defect: the scoped run is a genuine re-derivation, so
                // its label is earned. Traced so a suite can see where it
                // relabels an accepted conflict.
                tracing::debug!(
                    full = ?full,
                    "context-scoped re-check re-proved a conflict the full-store re-check left \
                     unproved (#combiner-verify-scope relabel)"
                );
            }
        }
        return (scoped, true);
    }
    (recheck(CongruenceScope::FullStore, trail), false)
}

/// One combined re-check of the verification context under `scope`.
pub(super) fn recheck_mixed_context_in(
    scope: CongruenceScope,
    terms: &TermStore,
    verification_context: &[TheoryLit],
    trail: DetHashMap<TermId, bool>,
    selected_combiner_kind: VerificationCombinerKind,
    reproved: ConflictSemanticVerdict,
) -> Result<ConflictSemanticVerdict, VerificationError> {
    let mut combiner =
        make_verification_combiner(terms, verification_context.iter().map(|lit| lit.term));
    if scope == CongruenceScope::Context {
        combiner.scope_congruence_to_roots(verification_context.iter().map(|lit| lit.term));
    }

    for lit in verification_context {
        combiner.register_atom(lit.term);
    }
    // Register and assert the support axioms (#8123 datatype tautologies AND
    // #AUFLIA-support ground instances of unconditionally-asserted Foralls) so
    // the combined solver can reprove a conflict the isolated combiner would
    // otherwise call spuriously-Sat. Every support literal is true in every
    // model of the problem, so it can only CONFIRM a genuine conflict, never
    // manufacture one.
    for lit in verification_context {
        combiner.assert_literal(lit.term, lit.value);
    }
    drive_lemma_batches(
        &mut combiner,
        terms,
        verification_context,
        trail,
        selected_combiner_kind,
        reproved,
    )
}

/// Check the asserted context, materializing the unit consequences of any
/// lemma batches the array and datatype solvers emit.
fn drive_lemma_batches(
    combiner: &mut TheoryCombiner<'_>,
    terms: &TermStore,
    verification_context: &[TheoryLit],
    mut trail: DetHashMap<TermId, bool>,
    selected_combiner_kind: VerificationCombinerKind,
    reproved: ConflictSemanticVerdict,
) -> Result<ConflictSemanticVerdict, VerificationError> {
    let mut verified_combiner_context = verification_context.to_vec();
    // Array and datatype solvers DRAIN a NeedLemmas batch after returning it:
    // the production DPLL(T) layer normally installs those clauses in SAT.
    // A bare second check therefore does not retain the emitted disjunction.
    // Materialize only consequences justified by this fixed trail:
    //   * zero live literals refutes the context immediately;
    //   * one live literal is unit-implied and may be asserted;
    //   * multiple live literals require a SAT split, so remain inconclusive.
    // Rechecking is sound only when every emitted clause is satisfied after
    // this closure. Speculative model equalities and arithmetic split requests
    // are never asserted here.
    const MAX_VERIFY_LEMMA_BATCHES: usize = 16;
    let mut remaining_batches = MAX_VERIFY_LEMMA_BATCHES;
    let mut seen_clauses: DetHashSet<Vec<TheoryLit>> = Default::default();
    let mut result = combiner.check();

    loop {
        match result {
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => return Ok(reproved),
            TheoryResult::Sat => return Err(VerificationError::ConflictIsSat),
            TheoryResult::NeedLemmas(lemmas) => {
                if remaining_batches == 0 || lemmas.is_empty() {
                    return Ok(ConflictSemanticVerdict::AcceptedUnchecked);
                }
                remaining_batches -= 1;

                let mut clauses = Vec::with_capacity(lemmas.len());
                let mut has_new_clause = false;
                for lemma in lemmas {
                    let mut clause = lemma.clause;
                    clause.sort_unstable();
                    clause.dedup();
                    has_new_clause |= seen_clauses.insert(clause.clone());
                    clauses.push(clause);
                }

                match close_valid_lemma_clauses(&clauses, &mut trail) {
                    LemmaTrailClosure::Contradiction => return Ok(reproved),
                    LemmaTrailClosure::Inconclusive => {
                        return Ok(ConflictSemanticVerdict::AcceptedUnchecked)
                    }
                    LemmaTrailClosure::Complete(units) => {
                        // A repeated, already-satisfied batch cannot change
                        // this single-path verifier. Stop instead of spinning.
                        if units.is_empty() && !has_new_clause {
                            return Ok(ConflictSemanticVerdict::AcceptedUnchecked);
                        }

                        verified_combiner_context.extend(units.iter().copied());
                        if units_leave_selected_fragment(
                            terms,
                            &verified_combiner_context,
                            selected_combiner_kind,
                        ) {
                            return Ok(ConflictSemanticVerdict::AcceptedUnchecked);
                        }

                        for unit in units {
                            combiner.register_atom(unit.term);
                            combiner.assert_literal(unit.term, unit.value);
                        }
                        result = combiner.check();
                    }
                }
            }
            // NeedModelEquality/NeedModelEqualities are retractable model
            // guidance, while NeedSplit/NeedDisequalitySplit/
            // NeedExpressionSplit(s) require genuine SAT case splits. An
            // immutable, single-path verifier cannot resolve them without
            // choosing an unjustified branch. Unknown and string requests are
            // likewise inconclusive. Preserve the existing optimistic policy.
            _ => return Ok(ConflictSemanticVerdict::AcceptedUnchecked),
        }
    }
}

/// Lemma atoms were not part of the original combiner selection. Before a
/// later `Sat` can reject the conflict, check that all materialized units
/// remain in the same supported fragment and require the same concrete
/// combiner. A support/lemma-only String, BitVec, nonlinear, or Int<->Real
/// bridge is therefore inconclusive rather than a false definitive `Sat`.
fn units_leave_selected_fragment(
    terms: &TermStore,
    verified_combiner_context: &[TheoryLit],
    selected_combiner_kind: VerificationCombinerKind,
) -> bool {
    let still_combined = matches!(
        classify_mixed_verifiability(terms, verified_combiner_context.iter().map(|lit| lit.term)),
        MixedVerifiability::Combined
    );
    let same_combiner =
        verification_combiner_kind(terms, verified_combiner_context.iter().map(|lit| lit.term))
            == selected_combiner_kind;
    !still_combined
        || !same_combiner
        || conflict_involves_int_real_mix(terms, verified_combiner_context)
        || conflict_involves_nonlinear(terms, verified_combiner_context)
}

#[cfg(test)]
#[path = "mixed_scope_gate_tests.rs"]
mod gate_tests;
#[cfg(test)]
#[path = "mixed_scope_tests.rs"]
mod tests;
