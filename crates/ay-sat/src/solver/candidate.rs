// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! An owning, non-authoritative incremental candidate producer. Its engine
//! never escapes as an ordinary Solver and no checked SAT/UNSAT wrapper is
//! returned. SMT consumers independently validate witnesses and completeness.

use super::*;
use crate::reconstruct::admitted::Counted;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, QueryError};
use std::cell::Cell;

#[cfg(test)]
mod tests;

type Result<T> = std::result::Result<T, CountedAdmissionError>;

/// Actual search counters and separately admitted materialization work.
/// These are diagnostics, not a complete work/CPU metric for ordinary CDCL.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct CandidateSearchWork {
    /// Conflicts in this incremental query.
    pub conflicts: u64,
    /// Decisions in this incremental query.
    pub decisions: u64,
    /// Propagations in this incremental query.
    pub propagations: u64,
    /// Logical work charged by mapping the assignment. This does not scan the
    /// original CNF ledger or arena and excludes search.
    pub materialization: u64,
}

/// Untrusted search DATA. No variant supplies a checked SAT result, refutation,
/// model-validation permit or completeness claim.
#[derive(Debug)]
#[non_exhaustive]
pub enum CandidateSearchOutcome {
    /// Assignment data in the original, fixed user-variable index space.
    /// The consumer must independently validate its intended source semantics.
    Assignment(Vec<bool>),
    /// The engine found no further assignment. This only triggers a consumer's
    /// independent completeness proof; it is not an accepted UNSAT verdict.
    ExhaustionHint,
    /// Search stopped or declined; there is no assignment or exhaustion fact.
    Unknown(SatUnknownReason),
}

/// One persistent pure incremental CDCL candidate engine.
///
/// Uses the existing IC3/MiniSat driver, retaining watches and learned clauses
/// without whole-formula startup or model-verdict scans per query. Only its
/// private per-call completion policy materializes untrusted assignment data;
/// every ordinary public Solver query retains its checked completion policy.
/// No global flag, mutable Solver escape or checked result conversion exists.
///
/// The same original owner covers construction, mapping, callbacks and cleanup.
/// Search uses ordinary conflict/decision limits and cooperative stop controls;
/// this is explicitly not a fully counted SAT solve integration.
pub struct CandidateSolver {
    solver: Solver,
    owner: CountedAdmission,
    last_work: CandidateSearchWork,
}

impl CandidateSolver {
    /// Construct a fixed variable namespace under the retained original owner.
    pub fn try_new(num_vars: usize, owner: CountedAdmission) -> Result<Self> {
        owner.admit(1, size_of::<Self>())?;
        let mut solver =
            Solver::build_with_hint(num_vars, None, None, &construction::Counted(&owner))?;
        owner.admit(num_vars.saturating_add(1), 0)?;
        solver.set_ic3_mode();
        owner.check()?;
        Ok(Self {
            solver,
            owner,
            last_work: CandidateSearchWork::default(),
        })
    }

    /// Add one candidate constraint in the fixed original namespace. Clauses
    /// requiring namespace growth or oversized-clause splitting are refused.
    /// Insertion supplies no formula/proof authority.
    pub fn add_clause(&mut self, clause: Vec<Literal>) -> Result<()> {
        self.owner.admit(
            clause.len().saturating_add(1),
            clause
                .len()
                .checked_mul(size_of::<Literal>())
                .ok_or_else(|| self.owner.refuse(CountedAdmissionError::StorageExhausted))?,
        )?;
        if clause.len() > clause_add::OVERSIZED_CLAUSE_SPLIT_THRESHOLD
            || clause
                .iter()
                .any(|literal| literal.variable().index() >= self.solver.user_num_vars)
        {
            return Err(invalid(
                &self.owner,
                "candidate clause exceeds its fixed namespace or clause bound",
            ));
        }
        self.solver.add_clause(clause);
        self.owner.check()
    }

    /// Retain a caller-observable variable identity through incremental search.
    pub fn freeze(&mut self, variable: Variable) -> Result<()> {
        self.owner.admit(1, 0)?;
        if variable.index() >= self.solver.user_num_vars {
            return Err(invalid(
                &self.owner,
                "candidate freeze names a foreign variable",
            ));
        }
        self.solver.freeze(variable);
        self.owner.check()
    }

    /// Install the original interrupt handle, without resetting it.
    pub fn set_interrupt(&mut self, interrupt: Arc<AtomicBool>) {
        self.solver.set_interrupt(interrupt);
    }

    /// Remaining conflicts for the next query; zero remains a real zero limit.
    pub fn set_conflict_budget(&mut self, remaining: Option<u64>) {
        self.solver.set_conflict_budget(remaining);
    }

    /// Remaining decisions for the next query; zero remains a real zero limit.
    pub fn set_decision_budget(&mut self, remaining: Option<u64>) {
        self.solver.set_decision_budget(remaining);
    }

    /// Preserve the ordinary learned-clause memory control.
    pub fn set_max_learned_clauses(&mut self, limit: Option<usize>) {
        self.solver.set_max_learned_clauses(limit);
    }

    /// Preserve the ordinary clause-arena memory control.
    pub fn set_max_clause_db_bytes(&mut self, limit: Option<usize>) {
        self.solver.set_max_clause_db_bytes(limit);
    }

    /// Counters for the last query, including one that stopped. Reading these
    /// neither polls nor supplies permission to continue after a refusal.
    #[must_use]
    pub fn last_work(&self) -> CandidateSearchWork {
        self.last_work
    }

    /// Produce only assignment data or an exhaustion hint. The original owner
    /// is retained across every call; no timer, grant or stop latch is renewed.
    pub fn search(&mut self) -> Result<CandidateSearchOutcome> {
        self.last_work = CandidateSearchWork::default();
        self.owner.admit(1, 0)?;
        let owner = self.owner.clone();
        let stop = || owner.check().is_err();
        let materialization = Cell::new(0);
        let before = (
            self.solver.total_num_conflicts(),
            self.solver.total_num_decisions(),
            self.solver.total_num_propagations(),
        );
        let mut result = self.solver.solve_incremental_ic3_raw(
            &[],
            &stop,
            IncrementalCompletion::UntrustedCandidate {
                owner: &owner,
                work: &materialization,
            },
        );
        // Same IC3 cleanup and memory controls, under the same late fence.
        if owner.check().is_ok() {
            if let Err(reason) = self.solver.backtrack_ic3_counted(0) {
                drop(result);
                result = self.solver.declare_assume_unknown_with_reason(reason);
            } else {
                self.solver.ic3_enforce_learned_cap();
                self.solver.ic3_memory_pressure_reduce();
            }
        }
        self.last_work = CandidateSearchWork {
            conflicts: self.solver.total_num_conflicts().saturating_sub(before.0),
            decisions: self.solver.total_num_decisions().saturating_sub(before.1),
            propagations: self
                .solver
                .total_num_propagations()
                .saturating_sub(before.2),
            materialization: materialization.get(),
        };
        owner.check()?;
        Ok(match result {
            AssumeResult::Sat(values) => CandidateSearchOutcome::Assignment(values),
            AssumeResult::Unsat(..) => CandidateSearchOutcome::ExhaustionHint,
            AssumeResult::Unknown => CandidateSearchOutcome::Unknown(
                self.solver
                    .last_unknown_reason()
                    .unwrap_or(SatUnknownReason::Unspecified),
            ),
        })
    }
}

/// Per-call completion, never an option on the reusable ordinary Solver.
#[derive(Clone, Copy)]
pub(in crate::solver) enum IncrementalCompletion<'a> {
    Checked,
    UntrustedCandidate {
        owner: &'a CountedAdmission,
        work: &'a Cell<u64>,
    },
}

impl IncrementalCompletion<'_> {
    pub(in crate::solver) fn is_candidate(self) -> bool {
        matches!(self, Self::UntrustedCandidate { .. })
    }

    pub(in crate::solver) fn resource_stop(self, solver: &Solver) -> Option<SatUnknownReason> {
        (self.is_candidate() && solver.resource_budget_exhausted())
            .then_some(SatUnknownReason::ResourceBudget)
    }

    pub(in crate::solver) fn current(self, solver: &mut Solver) -> AssumeResult {
        match self {
            Self::Checked => solver.declare_assume_sat_from_current_assignment(),
            Self::UntrustedCandidate { owner, work } => {
                let result = (|| {
                    let before = owner.usage()?.work_admitted;
                    let model = solver.current_model_admitted(&Counted(owner))?;
                    let mut external = solver.external_model_admitted(&model, &Counted(owner))?;
                    drop(model);
                    // CandidateSolver enables no scopes, preprocessing or BVE.
                    // No eliminated-variable reconstruction or CNF validation
                    // is needed to produce untrusted values in this namespace.
                    if solver.inproc.reconstruction.len() != 0
                        || solver.user_num_vars > external.len()
                    {
                        return Err(invalid(
                            owner,
                            "candidate engine changed its fixed variable mapping",
                        ));
                    }
                    external.truncate(solver.user_num_vars);
                    owner.check()?;
                    work.set(owner.usage()?.work_admitted.saturating_sub(before));
                    Ok(external)
                })();
                match result {
                    Ok(values) => AssumeResult::Sat(values),
                    Err(error) => {
                        solver.declare_assume_unknown_with_reason(counted_admission::reason(error))
                    }
                }
            }
        }
    }
}

fn invalid(owner: &CountedAdmission, reason: &'static str) -> CountedAdmissionError {
    owner.refuse(CountedAdmissionError::Original(
        QueryError::Invalid(reason).into(),
    ))
}
