// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::candidate::circuit;
use super::*;
use ay_sat::{CandidateSearchOutcome, Literal, SatUnknownReason};

impl Solver {
    pub(super) fn enumerate_bool_inner(
        &self,
        projection: &[Term],
        max_models: usize,
        kind: ProjectionKind,
        controls: NativePublicationControls,
        owner: &CountedAdmission,
        report: &mut EnumerationReport,
    ) -> Result<()> {
        owner.admit(1, 0)?;
        if controls
            .effective_term_memory_limit
            .is_some_and(|limit| self.terms().instance_memory_exceeded(limit))
        {
            return Err(Failure::Incomplete(UnknownReason::MemoryLimit));
        }
        let roots = &self.executor.ctx.assertions;
        let mut projection_ids = Vec::new();
        reserve(&mut projection_ids, projection.len(), owner)?;
        projection_ids.extend(projection.iter().map(|term| term.id()));
        let compiled = match kind {
            ProjectionKind::Bool => {
                finite_bool::compile(self.terms(), roots, &projection_ids, owner)
            }
            ProjectionKind::Finite => {
                finite_bool::compile_finite(self.terms(), roots, &projection_ids, owner)
            }
        }
        .map_err(|error| match error {
            finite_bool::Error::Stopped(error) => Failure::Stopped(error),
            finite_bool::Error::Unsupported => Failure::Api(invalid(
                "source is outside the finite Bool/Int enumeration fragment",
            )),
            finite_bool::Error::Invalid => Failure::Incomplete(UnknownReason::SelfCheckRejected),
        })?;
        if !compiled.matches_source(self.terms(), roots) {
            return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected));
        }
        self.check_enumeration_carriers(&compiled, owner)?;
        report.statistics.signed_integer_width = compiled.signed_width;
        let source_started = Instant::now();
        let source_before = owner.usage()?.work_admitted;
        let mut source = source::copy(self.terms(), roots, &compiled, owner)?;
        report.statistics.source_construction_work =
            owner.usage()?.work_admitted.saturating_sub(source_before);
        report.statistics.source_construction_micros =
            u64::try_from(source_started.elapsed().as_micros()).unwrap_or(u64::MAX);
        source.solver.interrupt = self.interrupt.clone();
        source
            .solver
            .executor
            .set_memory_limit(controls.effective_memory_limit);
        source
            .solver
            .executor
            .set_term_memory_limit(controls.effective_term_memory_limit);
        source
            .solver
            .executor
            .set_solve_controls(Some(self.interrupt.clone()), controls.deadline);
        source
            .solver
            .set_learned_clause_limit(self.learned_clause_limit);
        source
            .solver
            .set_clause_db_bytes_limit(self.clause_db_bytes_limit);
        source.solver.set_produce_proofs(true);
        // Demand strict semantic grant evidence and an independently strict
        // artifact below. The external Alethe wire-gap screen selected by
        // :check-proofs-strict is a separate presentation contract.
        source
            .solver
            .executor
            .set_strict_grant_evidence_required(true);
        source
            .solver
            .set_verification_level(if self.verification_level().has_debug_checks() {
                crate::api::VerificationLevel::FullyVerified
            } else {
                crate::api::VerificationLevel::ProofChecked
            });
        source
            .solver
            .executor
            .set_self_check(self.executor.self_check());
        source.solver.set_alethe_dialect(self.alethe_dialect());
        if self.executor.ctx.check_proofs_strict_requested() {
            source
                .solver
                .try_set_option(":check-proofs-strict", "true")?;
        }
        let (mut candidate, mapping) = circuit(&compiled, owner)?;
        candidate.set_interrupt(self.interrupt.clone());
        candidate.set_max_learned_clauses(self.learned_clause_limit);
        candidate.set_max_clause_db_bytes(self.clause_db_bytes_limit);
        let allowances = self.executor.bitblast_sat_allowances();
        let mut seen = HashSet::new();
        loop {
            owner.admit(1, 0)?;
            candidate.set_conflict_budget(
                allowances.conflicts.map(|limit| {
                    limit.saturating_sub(report.statistics.candidate_search.conflicts)
                }),
            );
            candidate.set_decision_budget(
                allowances.decisions.map(|limit| {
                    limit.saturating_sub(report.statistics.candidate_search.decisions)
                }),
            );
            report.statistics.candidate_solve_calls = report
                .statistics
                .candidate_solve_calls
                .checked_add(1)
                .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
            let answer = candidate.search();
            let candidate_work = candidate.last_work();
            let work = SearchWork {
                conflicts: candidate_work.conflicts,
                decisions: candidate_work.decisions,
                propagations: candidate_work.propagations,
            };
            report.statistics.candidate_materialization_work = report
                .statistics
                .candidate_materialization_work
                .checked_add(candidate_work.materialization)
                .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
            report.statistics.candidate_search.conflicts = report
                .statistics
                .candidate_search
                .conflicts
                .checked_add(work.conflicts)
                .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
            report.statistics.candidate_search.decisions = report
                .statistics
                .candidate_search
                .decisions
                .checked_add(work.decisions)
                .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
            report.statistics.candidate_search.propagations = report
                .statistics
                .candidate_search
                .propagations
                .checked_add(work.propagations)
                .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
            let answer = answer?;
            owner.check()?;
            match answer {
                CandidateSearchOutcome::Assignment(model) => {
                    let witness = mapping.validate(self, roots, projection, &model, owner)?;
                    let values = witness.values;
                    report.statistics.original_validation_work = report
                        .statistics
                        .original_validation_work
                        .checked_add(witness.validation_work)
                        .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
                    if seen.contains(&values) {
                        return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected));
                    }
                    if report.row_count() == max_models {
                        report.outcome = Outcome::Capped;
                        return Ok(());
                    }
                    owner.admit(values.len(), std::mem::size_of::<Vec<Scalar>>())?;
                    seen.try_reserve(1)
                        .map_err(|_| owner.refuse(CountedAdmissionError::StorageExhausted))?;
                    let mut key = Vec::new();
                    reserve(&mut key, values.len(), owner)?;
                    for value in &values {
                        key.push(candidate::copy_value(value, owner)?);
                    }
                    seen.insert(key);
                    // Both blockers are authored from the same independently
                    // evaluated values and exact source/projection mapping.
                    let mut blocker = Vec::new();
                    reserve(&mut blocker, values.len(), owner)?;
                    for (encoding, value) in mapping.projection.iter().zip(&values) {
                        encoding.block(value, &mut blocker, owner)?;
                    }
                    let source_started = Instant::now();
                    let source_before = owner.usage()?.work_admitted;
                    source.block(&projection_ids, &values, owner)?;
                    report.statistics.source_construction_work = report
                        .statistics
                        .source_construction_work
                        .checked_add(owner.usage()?.work_admitted.saturating_sub(source_before))
                        .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
                    report.statistics.source_construction_micros =
                        report.statistics.source_construction_micros.saturating_add(
                            u64::try_from(source_started.elapsed().as_micros()).unwrap_or(u64::MAX),
                        );
                    owner.admit(
                        blocker.len(),
                        blocker.len().saturating_mul(std::mem::size_of::<Literal>()),
                    )?;
                    candidate.add_clause(blocker)?;
                    report.push(
                        values,
                        witness.leaves,
                        work,
                        witness.validation_work,
                        candidate_work.materialization,
                        owner,
                    )?;
                }
                CandidateSearchOutcome::ExhaustionHint => {
                    // A candidate UNSAT is only a trigger. It cannot authorize
                    // completeness, irrespective of the compilation's tests.
                    source
                        .solver
                        .executor
                        .set_ground_budget_enabled(self.executor.ground_budget_enabled());
                    source
                        .solver
                        .executor
                        .set_resource_limit(allowances.conflicts.map(|limit| {
                            limit.saturating_sub(report.statistics.candidate_search.conflicts)
                        }));
                    source
                        .solver
                        .executor
                        .set_decision_limit(allowances.decisions.map(|limit| {
                            limit.saturating_sub(report.statistics.candidate_search.decisions)
                        }));
                    source.finish(owner, report)?;
                    return Ok(());
                }
                CandidateSearchOutcome::Unknown(reason) => {
                    let reason = match reason {
                        SatUnknownReason::ResourceBudget => UnknownReason::ResourceLimit,
                        SatUnknownReason::DeadlineExceeded => UnknownReason::Timeout,
                        SatUnknownReason::InvalidSatModel | SatUnknownReason::InvalidUnsatCore => {
                            UnknownReason::SelfCheckRejected
                        }
                        SatUnknownReason::Interrupted => UnknownReason::Interrupted,
                        _ => UnknownReason::Incomplete,
                    };
                    return Err(Failure::Incomplete(reason));
                }
                _ => return Err(Failure::Incomplete(UnknownReason::Incomplete)),
            }
        }
    }
}

impl Solver {
    /// Core Int lowering does not erase public Char/FiniteDomain identity at
    /// this primitive-scalar endpoint. Inspect live declaration metadata once,
    /// before any row can acquire original-witness meaning.
    fn check_enumeration_carriers(
        &self,
        compiled: &Compiled,
        owner: &CountedAdmission,
    ) -> Result<()> {
        let mut reached = Vec::new();
        reserve(&mut reached, self.terms().len(), owner)?;
        owner.admit(self.terms().len(), 0)?;
        reached.resize(self.terms().len(), false);
        for &(id, _) in &compiled.leaves {
            owner.admit(1, 0)?;
            let slot = reached
                .get_mut(id.index())
                .ok_or(Failure::Incomplete(UnknownReason::SelfCheckRejected))?;
            *slot = true;
            if self
                .var_sorts
                .get(&id)
                .is_some_and(|sort| !matches!(sort, Sort::Bool | Sort::Int))
            {
                return Err(Failure::Api(invalid(
                    "source uses an unsupported public scalar carrier",
                )));
            }
        }
        for (_, info) in self.executor.ctx.symbols_iter() {
            owner.admit(1, 0)?;
            if info
                .term
                .is_some_and(|id| reached.get(id.index()).copied().unwrap_or(false))
                && !matches!(
                    &info.public_sort,
                    ay_frontend::PublicSort::Core(Sort::Bool | Sort::Int)
                )
            {
                return Err(Failure::Api(invalid(
                    "source uses an unsupported public scalar carrier",
                )));
            }
        }
        owner.check()?;
        Ok(())
    }
}
