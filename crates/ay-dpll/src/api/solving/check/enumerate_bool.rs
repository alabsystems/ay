// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Persistent candidate search, original witness checking and source authority.

use std::collections::HashSet;
use std::sync::atomic::Ordering;
use std::sync::Arc;

use ay_core::original_query::{
    CountedAdmission, CountedAdmissionError, FiniteAdmissionGrant, OriginalAdmissionError,
    QueryError, StopReason,
};
use ay_core::resource::{
    current_check_stop, current_guard, enter_check_stop, CheckStop, ChildSpec, Exhausted, Guard,
    NodeLabel,
};
use ay_core::term::reserve_counted;
use ay_core::time::Instant;
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};

use super::{reject_bv_cnf_export_operation, NativePublicationControls};
use crate::api::types::EnumerationCommon;
use crate::api::FiniteEnumerationValue as Scalar;
use crate::api::{
    BoolEnumerationOutcome as Outcome, BoolEnumerationReport, BoolEnumerationRow,
    BoolEnumerationSearchWork as SearchWork, BoolEnumerationStatistics, FiniteEnumerationReport,
    FiniteEnumerationRow, Logic, ProofAcceptanceMode, Solver, SolverError, Term,
};
use crate::preprocess::finite_bool::{self, Compiled};
use crate::UnknownReason;

mod candidate;
mod engine;
#[cfg(test)]
mod finite_tests;
mod source;
#[cfg(test)]
mod tests;

const OPERATION: &str = "enumerate_projection";

#[derive(Clone, Copy)]
enum ProjectionKind {
    Bool,
    Finite,
}

#[derive(Debug, thiserror::Error)]
enum Failure {
    #[error(transparent)]
    Stopped(#[from] CountedAdmissionError),
    #[error(transparent)]
    Api(#[from] SolverError),
    #[error("enumeration cannot certify a complete result: {0}")]
    Incomplete(UnknownReason),
}
type Result<T> = std::result::Result<T, Failure>;

enum EnumerationReport {
    Bool(BoolEnumerationReport),
    Finite(FiniteEnumerationReport),
}

impl std::ops::Deref for EnumerationReport {
    type Target = EnumerationCommon;
    fn deref(&self) -> &Self::Target {
        match self {
            Self::Bool(report) => &report.common,
            Self::Finite(report) => &report.common,
        }
    }
}

impl std::ops::DerefMut for EnumerationReport {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Self::Bool(report) => &mut report.common,
            Self::Finite(report) => &mut report.common,
        }
    }
}

impl EnumerationReport {
    fn row_count(&self) -> usize {
        match self {
            Self::Bool(report) => report.rows.len(),
            Self::Finite(report) => report.rows.len(),
        }
    }

    fn push(
        &mut self,
        values: Vec<Scalar>,
        leaves: Vec<(Term, Scalar)>,
        search: SearchWork,
        validation_work: u64,
        materialization_work: u64,
        owner: &CountedAdmission,
    ) -> Result<()> {
        match self {
            Self::Bool(report) => {
                let mut booleans = Vec::new();
                reserve(&mut booleans, values.len(), owner)?;
                for value in values {
                    owner.admit(1, 0)?;
                    let Scalar::Bool(value) = value else {
                        return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected));
                    };
                    booleans.push(value);
                }
                let mut witness = Vec::new();
                reserve(&mut witness, leaves.len(), owner)?;
                for (term, value) in leaves {
                    owner.admit(1, 0)?;
                    let Scalar::Bool(value) = value else {
                        return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected));
                    };
                    witness.push((term, value));
                }
                reserve(&mut report.rows, 1, owner)?;
                report.rows.push(BoolEnumerationRow {
                    values: booleans,
                    witness,
                    search,
                    validation_work,
                    materialization_work,
                });
            }
            Self::Finite(report) => {
                reserve(&mut report.rows, 1, owner)?;
                report.rows.push(FiniteEnumerationRow {
                    values,
                    witness: leaves,
                    search,
                    validation_work,
                    materialization_work,
                });
            }
        }
        Ok(())
    }
}

fn invalid(message: impl Into<String>) -> SolverError {
    SolverError::InvalidArgument {
        operation: OPERATION,
        message: message.into(),
    }
}

fn binding_error(error: Failure) -> SolverError {
    match error {
        Failure::Api(error) => error,
        Failure::Stopped(error) => SolverError::BoolEnumerationStopped(stop_reason(error)),
        Failure::Incomplete(reason) => SolverError::BoolEnumerationStopped(reason),
    }
}

fn stop_reason(error: CountedAdmissionError) -> UnknownReason {
    match error {
        CountedAdmissionError::Guard(Exhausted::Deadline | Exhausted::Cpu) => {
            UnknownReason::Timeout
        }
        CountedAdmissionError::Original(OriginalAdmissionError::Query(
            QueryError::Interrupted(StopReason::Deadline),
        )) => UnknownReason::Timeout,
        CountedAdmissionError::Guard(Exhausted::Rlimit) | CountedAdmissionError::WorkExhausted => {
            UnknownReason::ResourceLimit
        }
        CountedAdmissionError::Original(OriginalAdmissionError::Query(QueryError::Exhausted)) => {
            UnknownReason::ResourceLimit
        }
        CountedAdmissionError::Original(OriginalAdmissionError::Query(QueryError::Invalid(_))) => {
            UnknownReason::Unsupported
        }
        CountedAdmissionError::Guard(Exhausted::Memory)
        | CountedAdmissionError::Memory
        | CountedAdmissionError::MemoryCapture
        | CountedAdmissionError::StorageExhausted => UnknownReason::MemoryLimit,
        _ => UnknownReason::Interrupted,
    }
}

fn reserve<T>(out: &mut Vec<T>, additional: usize, owner: &CountedAdmission) -> Result<()> {
    reserve_counted(out, additional, owner).map_err(|error| match error {
        ay_core::term::CountedTermError::Stopped(error) => Failure::Stopped(error),
        _ => Failure::Incomplete(UnknownReason::InternalError),
    })
}

impl Solver {
    /// Enumerate distinct Boolean projections with one persistent candidate
    /// circuit. All source integers must be finite expressions built from
    /// literals, Boolean-conditioned ITEs, addition, subtraction and
    /// multiplication and Euclidean div/mod with known nonzero divisors;
    /// ordinary Boolean connectives and signed comparisons
    /// are supported. Free Int variables and other theories are refused.
    ///
    /// Every row passes the independent original-model gate, including an
    /// independent evaluation of each projected expression. Candidate UNSAT
    /// triggers exactly one terminal ordinary source solve of the original
    /// assertions plus the authenticated projection blockers. `Exhaustive`
    /// additionally requires its strictly accepted native proof artifact.
    ///
    /// The absolute native deadline, inherited guard/callback, interrupt and
    /// memory controls cover preparation, every candidate, final certification
    /// and local cleanup. SAT conflict/decision allowances are shared across
    /// candidates and the terminal source solve. No allowance is renewed per
    /// model. An active counted `Run` is refused: the ordinary source proof
    /// funnel is not yet a fully counted SMT integration.
    ///
    /// `max_models` is a result cap. After reaching it, one more candidate is
    /// checked to distinguish `Capped` from certified `Exhaustive`. An empty
    /// projection has one empty row exactly when the source is satisfiable.
    /// Duplicate or foreign/stale projected handles are rejected. This method
    /// borrows the caller immutably and preserves all caller decision state.
    pub fn try_enumerate_bool(
        &self,
        projection: &[Term],
        max_models: usize,
    ) -> std::result::Result<BoolEnumerationReport, SolverError> {
        match self.enumerate_projection(projection, max_models, ProjectionKind::Bool)? {
            EnumerationReport::Bool(report) => Ok(report),
            EnumerationReport::Finite(_) => Err(invalid("unexpected projection report kind")),
        }
    }

    /// Enumerate original Boolean and finite integer scalar projections with
    /// one candidate circuit, independent original witness validation and one
    /// strict terminal source proof. Integer leaves require finite bounds from
    /// the original assertions. Missing bounds, unsupported theories or a
    /// refused terminal proof cannot establish completeness.
    /// Public Char/FiniteDomain carriers are refused even when lowered to Int.
    /// Div/mod require a source-derived nonzero divisor property; zero-divisor
    /// interpretations are outside this finite source fragment.
    ///
    /// All ownership, resource, cap and state guarantees of
    /// [`Self::try_enumerate_bool`] apply. Integers are mathematical `BigInt`
    /// values; rows are not ordinary solve profiles or synthesized `Model`s.
    pub fn try_enumerate_finite(
        &self,
        projection: &[Term],
        max_models: usize,
    ) -> std::result::Result<FiniteEnumerationReport, SolverError> {
        let result = self
            .enumerate_projection(projection, max_models, ProjectionKind::Finite)
            .map_err(|error| match error {
                SolverError::BoolEnumerationStopped(reason) => {
                    SolverError::FiniteEnumerationStopped(reason)
                }
                other => other,
            })?;
        match result {
            EnumerationReport::Finite(report) => Ok(report),
            EnumerationReport::Bool(_) => Err(invalid("unexpected projection report kind")),
        }
    }

    fn enumerate_projection(
        &self,
        projection: &[Term],
        max_models: usize,
        kind: ProjectionKind,
    ) -> std::result::Result<EnumerationReport, SolverError> {
        reject_bv_cnf_export_operation(OPERATION)?;
        if current_guard()
            .and_then(|guard| guard.nearest(NodeLabel::Run))
            .is_some_and(|run| run.remaining().is_some())
        {
            return Err(invalid(
                "ordinary projected enumeration is not a fully counted Run endpoint",
            ));
        }
        let controls = self.native_publication_controls();
        let spec = ChildSpec::new(NodeLabel::Check)
            .with_deadline(controls.deadline.into())
            .with_external(self.interrupt.clone())
            .with_lane_share();
        let guard = match current_guard() {
            Some(parent) => parent.child(spec),
            None => Guard::root_child(spec),
        };
        let _guard_scope = guard.enter();
        let original_stop = current_check_stop().map_err(|error| invalid(error.to_string()))?;
        let interrupt = self.interrupt.clone();
        let observer_guard = guard.clone();
        let memory_observed = Arc::new(std::sync::atomic::AtomicBool::new(false));
        let observer_memory = memory_observed.clone();
        let observer: CheckStop = Arc::new(move || {
            interrupt.load(Ordering::Relaxed)
                || observer_guard.poll().is_some()
                || {
                    let exceeded = crate::memory::memory_exceeded(controls.effective_memory_limit)
                        || ay_sys::process_memory_exceeded()
                        || ay_sys::current_memory_group_soft_tripped();
                    if exceeded {
                        observer_memory.store(true, Ordering::Relaxed);
                    }
                    exceeded
                }
                || original_stop.as_ref().is_some_and(|stop| stop())
        });
        let observed_reason = |reason| {
            if reason == UnknownReason::Interrupted && memory_observed.load(Ordering::Relaxed) {
                UnknownReason::MemoryLimit
            } else {
                reason
            }
        };
        // Enter the SAME observer before capturing it. The counted compiler's
        // owner consequently does not recursively call a wrapper of itself.
        let _stop_scope = enter_check_stop(observer.clone());
        let storage = controls
            .effective_term_memory_limit
            .map_or(usize::MAX, |limit| {
                limit.saturating_sub(self.terms().true_memory_bytes())
            });
        // This endpoint has the ordinary native envelope, not an invented
        // caller work grant. The compiler's bookkeeping is reused with an
        // unbounded logical credit; the original guard/deadline/memory remain
        // live, and a term ceiling conservatively caps cumulative scratch too.
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(u64::MAX, storage),
            controls.deadline,
            observer,
        )
        .map_err(|error| {
            SolverError::BoolEnumerationStopped(observed_reason(stop_reason(error)))
        })?;
        let common =
            self.enumeration_common(projection, kind, &owner)
                .map_err(|error| match error {
                    SolverError::BoolEnumerationStopped(reason) => {
                        SolverError::BoolEnumerationStopped(observed_reason(reason))
                    }
                    other => other,
                })?;
        let mut report = match kind {
            ProjectionKind::Bool => EnumerationReport::Bool(BoolEnumerationReport {
                common,
                rows: Vec::new(),
            }),
            ProjectionKind::Finite => EnumerationReport::Finite(FiniteEnumerationReport {
                common,
                rows: Vec::new(),
            }),
        };
        let result =
            self.enumerate_bool_inner(projection, max_models, kind, controls, &owner, &mut report);
        match result {
            Ok(()) => {}
            Err(Failure::Api(error)) => return Err(error),
            Err(Failure::Stopped(error)) => {
                report.outcome = Outcome::Incomplete(observed_reason(stop_reason(error)))
            }
            Err(Failure::Incomplete(reason)) => report.outcome = Outcome::Incomplete(reason),
        }
        if report.outcome != Outcome::Exhaustive {
            report.completeness_proof = None;
        }
        // The inner function has dropped the candidate engine, source solver,
        // compiler and scratch. Refusal after cleanup revokes completeness.
        if let Err(error) = owner.check() {
            report.completeness_proof = None;
            report.outcome = Outcome::Incomplete(observed_reason(stop_reason(error)));
        }
        if let Ok(usage) = owner.usage() {
            report.statistics.admitted_work = usage.work_admitted;
            report.statistics.admitted_storage = usage.storage_admitted;
        }
        Ok(report)
    }

    #[cfg(test)]
    fn enumeration_report(
        &self,
        projection: &[Term],
        owner: &CountedAdmission,
    ) -> std::result::Result<BoolEnumerationReport, SolverError> {
        Ok(BoolEnumerationReport {
            common: self.enumeration_common(projection, ProjectionKind::Bool, owner)?,
            rows: Vec::new(),
        })
    }

    fn enumeration_common(
        &self,
        projection: &[Term],
        kind: ProjectionKind,
        owner: &CountedAdmission,
    ) -> std::result::Result<EnumerationCommon, SolverError> {
        // Authentication precedes indexing or accepting any projection value.
        let mut seen = HashSet::new();
        owner
            .admit(
                projection.len(),
                projection
                    .len()
                    .checked_mul(std::mem::size_of::<TermId>() * 4)
                    .ok_or(SolverError::BoolEnumerationStopped(
                        UnknownReason::MemoryLimit,
                    ))?,
            )
            .map_err(|error| SolverError::BoolEnumerationStopped(stop_reason(error)))?;
        seen.try_reserve(projection.len()).map_err(|_| {
            SolverError::BoolEnumerationStopped(stop_reason(
                owner.refuse(CountedAdmissionError::StorageExhausted),
            ))
        })?;
        for &term in projection {
            let id = self.resolve_term(OPERATION, term)?;
            let supported = match kind {
                ProjectionKind::Bool => self.terms().sort(id) == &Sort::Bool,
                ProjectionKind::Finite => matches!(self.terms().sort(id), Sort::Bool | Sort::Int),
            };
            if !supported {
                return Err(invalid("projected term has an unsupported scalar sort"));
            }
            if !seen.insert(id) {
                return Err(invalid("projection contains a duplicate term"));
            }
        }
        // Output binding copies remain part of the invocation's logical store.
        let mut projected = Vec::new();
        let mut assertions = Vec::new();
        reserve(&mut projected, projection.len(), owner).map_err(binding_error)?;
        reserve(&mut assertions, self.executor.ctx.assertions.len(), owner)
            .map_err(binding_error)?;
        projected.extend_from_slice(projection);
        assertions.extend(
            self.executor
                .ctx
                .assertions
                .iter()
                .map(|&id| self.wrap_term(id)),
        );
        Ok(EnumerationCommon {
            outcome: Outcome::Incomplete(UnknownReason::Incomplete),
            projection: projected,
            statistics: BoolEnumerationStatistics {
                compilation_work_version: finite_bool::WORK_VERSION,
                ..BoolEnumerationStatistics::default()
            },
            completeness_proof: None,
            diagnostic: None,
            solver: self.cache_token.clone(),
            source_context: self.executor.ctx.source_context_stamp(),
            terms: self.terms().snapshot_stamp(),
            assertions,
        })
    }
}

impl BoolEnumerationReport {
    /// Whether the solver still has the exact source/declaration/term/assertion
    /// state this report describes. Any source mutation conservatively retires
    /// the binding; the retained rows still describe the original frozen query.
    #[must_use]
    pub fn is_current_for(&self, solver: &Solver) -> bool {
        self.common.is_current_for(solver)
    }
}

impl FiniteEnumerationReport {
    /// Whether this report still binds the caller's exact original source.
    #[must_use]
    pub fn is_current_for(&self, solver: &Solver) -> bool {
        self.common.is_current_for(solver)
    }
}

impl EnumerationCommon {
    fn is_current_for(&self, solver: &Solver) -> bool {
        self.solver.is_current()
            && self.solver == solver.cache_token
            && self.source_context == solver.executor.ctx.source_context_stamp()
            && self.terms == solver.terms().snapshot_stamp()
            && self.assertions.len() == solver.executor.ctx.assertions.len()
            && self
                .assertions
                .iter()
                .zip(&solver.executor.ctx.assertions)
                .all(|(&term, &id)| term == solver.wrap_term(id))
    }
}
