// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by executor::proof_resolution::checked_sat_refutation to preserve item paths.

/// Premise table whose only proof-kernel deferrals have all been discharged by
/// the semantic conflict verifier in this exact query.
///
/// The raw deferred table is intentionally private to this constructor.  A
/// caller cannot obtain a clause through this wrapper until every `Generic`
/// theory premise in the fragment has an exact `true` memo entry.  The memo is
/// cleared at query entry and whenever quantified support axioms change, so a
/// match carries the same term/support state under which the conflict was
/// independently re-solved before it was learned.
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
            if semantic_memo.get(&key) != Some(&true) {
                return Err(
                    CheckedSatRefutationError::DeferredGenericNotSemanticallyVerified { step },
                );
            }
        }
        meter.charge(0, 0)?;
        Ok(Self { premises })
    }

    fn step_count(&self) -> usize {
        self.premises.step_count()
    }

    fn clause(&self, step: ProofId) -> Option<&[TermId]> {
        self.premises
            .strictly_authenticated_clause(step)
            .or_else(|| self.premises.deferred_generic_clause(step))
    }
}
