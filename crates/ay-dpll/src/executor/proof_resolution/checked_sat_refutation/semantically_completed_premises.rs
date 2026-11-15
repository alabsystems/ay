// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by executor::proof_resolution::checked_sat_refutation to preserve item paths.

/// Premise table whose only proof-kernel deferrals have all been discharged by
/// the semantic conflict verifier in this exact query.
///
/// The raw deferred table is intentionally private to this constructor.  A
/// caller cannot obtain a clause through this wrapper until every `Generic`
/// theory premise in the fragment has an exact
/// [`ConflictSemanticVerdict::Reproved`] memo entry: a fresh solve that did
/// not run the array theory re-derived UNSAT for exactly that literal set.
/// The memo is cleared at query entry and whenever quantified support axioms
/// change, so a match carries the same term/support state under which the
/// conflict was re-solved before it was learned.
///
/// Two acceptances the fail-closed search gate records are NOT authority
/// here. An optimistic acceptance (nonlinear or int/real-bridged fragment,
/// split request, budget trip, sampled-out EUF re-check, structural-only
/// domain) establishes nothing. A re-derivation by a combiner that carries
/// the array theory re-runs the very inference that produced the conflict:
/// on 2026-09-23 this lane admitted the wrong refutation of hunt file
/// `storeeq_41_0293` because the array solver's effective-store walker
/// dropped an index-distinctness reason, the premise
/// `(= S S') -> (not (= j 5))` was re-derived from the reduced literal set by
/// that same walker, and the memo's bare `true` read as an exact positive
/// verdict.
#[derive(Debug)]
struct SemanticallyCompletedPremiseClauses {
    premises: PremiseClausesWithDeferredGeneric,
}

impl SemanticallyCompletedPremiseClauses {
    fn complete(
        premises: PremiseClausesWithDeferredGeneric,
        semantic_memo: &ConflictSemanticVerifyMemo,
        terms: &TermStore,
        meter: &mut CheckedRefutationMeter,
    ) -> Result<Self, CheckedSatRefutationError> {
        for (step, clause) in premises.deferred_generic_clauses() {
            let bytes = checked_resource_mul(
                clause.len(),
                size_of::<TheoryLit>(),
                ResolutionValidationResource::Bytes,
            )?;
            let work = checked_resource_add(
                clause.len(),
                clause_sort_work(clause.len())?,
                ResolutionValidationResource::Work,
            )?;
            meter.charge(work, bytes)?;

            let mut key = Vec::new();
            key.try_reserve_exact(clause.len()).map_err(|_| {
                ResolutionValidationError::AllocationFailed {
                    resource: ResolutionValidationResource::Bytes,
                }
            })?;
            charge_capacity_excess::<TheoryLit>(key.capacity(), clause.len(), meter)?;
            for (index, &literal) in clause.iter().enumerate() {
                if literal.index() >= terms.len() {
                    return Err(CheckedSatRefutationError::StaleDeferredGenericTerm {
                        step,
                        term: literal,
                    });
                }
                key.push(match terms.get(literal) {
                    TermData::Not(inner) => TheoryLit::new(*inner, true),
                    _ => TheoryLit::new(literal, false),
                });
                if index % 1024 == 0 {
                    meter.charge(0, 0)?;
                }
            }
            key.sort_unstable();
            match semantic_memo.get(&key) {
                Some(ConflictSemanticVerdict::Reproved) => {}
                Some(ConflictSemanticVerdict::ReprovedByArrayTheory) => {
                    return Err(
                        CheckedSatRefutationError::DeferredGenericReprovedOnlyByArrayTheory {
                            step,
                        },
                    );
                }
                _ => {
                    return Err(
                        CheckedSatRefutationError::DeferredGenericNotSemanticallyVerified { step },
                    );
                }
            }
        }
        meter.charge(0, 0)?;
        Ok(Self { premises })
    }

    fn step_count(&self) -> usize {
        self.premises.step_count()
    }

    /// How many `Generic` theory premises rest on a `Reproved` re-derivation
    /// by AY's own semantic-conflict verifier rather than on the strict
    /// checker: evidence E1 for the refutation that uses them.
    fn re_derived_premise_count(&self) -> usize {
        self.premises.deferred_generic_clauses().count()
    }

    fn clause(&self, step: ProofId) -> Option<&[TermId]> {
        self.premises
            .strictly_authenticated_clause(step)
            .or_else(|| self.premises.deferred_generic_clause(step))
    }
}
