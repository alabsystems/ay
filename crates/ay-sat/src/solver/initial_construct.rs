// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Same-owner construction of the real CDCL engine, including initial CNF.
//! No raw mutable solver escapes. This is not an all-operation solve meter:
//! ordinary reset/preprocessing, conflict analysis, later growth and proof
//! reconstruction still need admission before a solve entry can be exposed.

use super::*;
use crate::initial_cnf::CountedInitialCnf;
use ay_core::original_query::{
    AdmissionUsage, CountedAdmission, CountedAdmissionError, QueryError,
};

mod cleanup;
mod entry;
mod ingestion;
#[cfg(test)]
mod tests;
mod traced;
mod watches;

type Result<T> = std::result::Result<T, CountedAdmissionError>;

/// A real solver constructed and initially propagated under the input's owner.
///
/// The retained input preserves exact authored rows; the engine's original
/// ledger preserves the ordinary normalized clauses and issued proof IDs.
/// No owner replacement, mutable solver escape, or fresh grant is available.
/// Host process configuration caches must be captured before query admission;
/// their process-global lazy environment initialization is not query storage.
pub struct CountedInitialSolver {
    solver: Solver,
    input: CountedInitialCnf,
    initial_conflict: InitialConflict,
    source_ids: Vec<Option<u64>>,
    assumptions: Vec<Literal>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InitialConflict {
    None,
    OriginalEmpty { source_row: usize, clause_id: u64 },
    Clause(ClauseRef),
}

impl CountedInitialSolver {
    pub(crate) fn try_from_cnf(input: CountedInitialCnf) -> Result<Self> {
        entry::construct(input, None)
    }

    pub(crate) fn try_from_traced_cnf(
        input: CountedInitialCnf,
        assumptions: &[Literal],
    ) -> Result<Self> {
        entry::construct(input, Some(assumptions))
    }

    /// Initial root BCP found a conflict. This diagnostic is not a proof or a
    /// separately authorized UNSAT result. No production solve entry exists yet.
    pub fn initial_conflict(&self) -> Result<bool> {
        self.input.owner().admit(1, 0)?;
        Ok(self.initial_conflict != InitialConflict::None)
    }

    /// Exact allocated input-row ID. Traced tautologies retain their skipped
    /// original ID (without creating a ledger/trace clause); only untraced
    /// tautologies return `None`. This is provenance, not proof authority.
    pub fn source_clause_id(&self, index: usize) -> Result<Option<u64>> {
        self.input.owner().admit(1, 0)?;
        self.source_ids
            .get(index)
            .copied()
            .ok_or_else(|| invalid(self.input.owner(), "source row index out of range"))
    }

    /// Exact separately retained input premises, not asserted source clauses.
    /// Any later iteration/copy/search requires the original owner's admission.
    pub fn assumptions(&self) -> Result<&[Literal]> {
        self.input.owner().admit(1, 0)?;
        Ok(&self.assumptions)
    }

    /// Count of variables assigned by the actual initial two-watch engine.
    pub fn initial_assigned_variables(&self) -> Result<usize> {
        self.input.owner().admit(1, 0)?;
        Ok(self.solver.trail.len())
    }

    /// Diagnostic receipt shared with every other original-owner consumer.
    pub fn usage(&self) -> Result<AdmissionUsage> {
        self.input.usage()
    }

    /// Dispose both engine and input before polling the original owner again.
    pub fn dispose(self) -> Result<()> {
        let owner = self.input.owner().clone();
        let mut pending = Some(self);
        let admitted = cleanup::caught(&owner, || owner.admit(1, 0));
        let disposed = cleanup::caught(&owner, || {
            drop(pending.take());
            Ok(())
        });
        let checked = cleanup::caught(&owner, || owner.check());
        cleanup::release(owner, checked.and(admitted).and(disposed))
    }
}

fn preflight(input: &CountedInitialCnf, owner: &CountedAdmission) -> Result<()> {
    owner.admit(1, 0)?;
    let Some(flags) = ay_core::captured_misc_cli_flags() else {
        return Err(invalid(
            owner,
            "SAT process configuration must be captured before query admission",
        ));
    };
    if flags.ab_triage_var.is_some() {
        return Err(invalid(owner, "counted assignment diagnostic not admitted"));
    }
    #[cfg(ay_logging)]
    if ay_core::sat_debug_env_flags().log_enabled {
        return Err(invalid(owner, "counted solver logging not admitted"));
    }
    for index in 0..input.len() {
        let Some(clause) = input.clause(index)? else {
            return Err(invalid(owner, "missing prepared SAT row"));
        };
        if clause
            .normalized()
            .is_some_and(|lits| lits.len() > super::clause_add::OVERSIZED_CLAUSE_SPLIT_THRESHOLD)
        {
            // Do not truncate, poison, skip, or grow a new namespace for free.
            return Err(invalid(
                owner,
                "counted oversized-clause ladder not admitted",
            ));
        }
    }
    Ok(())
}

fn invalid(owner: &CountedAdmission, why: &'static str) -> CountedAdmissionError {
    owner.refuse(CountedAdmissionError::Original(
        QueryError::Invalid(why).into(),
    ))
}

struct Scratch(Option<Solver>);

impl Drop for Scratch {
    fn drop(&mut self) {
        drop(self.0.take());
        #[cfg(test)]
        AFTER_SCRATCH_DROP.with(|slot| {
            if let Some(hook) = slot.borrow_mut().take() {
                hook();
            }
        });
    }
}

#[cfg(test)]
thread_local! {
    static AFTER_SCRATCH_DROP: std::cell::RefCell<Option<Box<dyn FnOnce()>>> =
        const { std::cell::RefCell::new(None) };
}
