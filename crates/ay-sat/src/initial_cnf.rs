// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Paid input acquisition and normalization, before SAT state construction.
//!
//! Preparation does not authorize SAT/UNSAT. `construct` consumes this data
//! into an opaque real solver, admitting construction, original insertion and
//! initial BCP under the retained owner. Feeding borrowed views to ordinary
//! `Solver::new`/`add_clause` is NOT a counted ingestion path. Neither type
//! provides a raw mutable solver escape or an unmetered solve fallback.
//!
//! Every authored row (including duplicates, tautologies and empty clauses)
//! remains available in order. A separate normalized view deletes duplicate
//! literals and identifies tautologies, without inventing variables or IDs.
//! Later proof registration must use the existing original-ID protocol.
//!
//! Work version 1 charges bounded element/metadata transactions and explicit
//! comparisons/swaps. Storage charges logical allocations and literal copies;
//! growth also pays for relocation of existing elements. It is cumulative,
//! not live RSS, and cleanup never refunds it. Allocator internals remain under
//! the owner's memory controls. Caller input storage predates this operation.

use ay_core::original_query::{
    AdmissionUsage, CountedAdmission, CountedAdmissionError, QueryError,
};

use crate::Literal;

mod normalize;
mod storage;
#[cfg(test)]
mod tests;

type Result<T> = std::result::Result<T, CountedAdmissionError>;

/// Version of the preparation work metric, separate from the owner's receipt.
pub const INITIAL_CNF_WORK_VERSION: u32 = 1;

struct Row {
    original: std::ops::Range<usize>,
    normalized: std::ops::Range<usize>,
    tautology: bool,
}

/// Immutable input data retained with the same terminal invocation owner.
///
/// This has no `Clone`, mutation, owner replacement, or unchecked extraction.
pub struct CountedInitialCnf {
    owner: CountedAdmission,
    num_vars: usize,
    originals: Vec<Literal>,
    normalized: Vec<Literal>,
    rows: Vec<Row>,
}

/// One original row and its equivalent normalized disjunction.
pub struct InitialClause<'a> {
    original: &'a [Literal],
    normalized: Option<&'a [Literal]>,
}

impl InitialClause<'_> {
    /// Exact input order and multiplicity, including tautological rows.
    pub fn original(&self) -> &[Literal] {
        self.original
    }

    /// `None` means tautology; `Some(&[])` means the contradictory empty clause.
    pub fn normalized(&self) -> Option<&[Literal]> {
        self.normalized
    }
}

impl CountedInitialCnf {
    pub(crate) fn owner(&self) -> &CountedAdmission {
        &self.owner
    }

    /// Consume prepared input into the real solver, using this same owner.
    /// Construction, original ingestion and initial BCP are admitted. See
    /// [`crate::CountedInitialSolver`] for the remaining solve obligations.
    pub fn construct(self) -> Result<crate::CountedInitialSolver> {
        crate::CountedInitialSolver::try_from_cnf(self)
    }

    /// Construct the real fresh CHC-style traced solver with separate premises.
    ///
    /// The exact supplied literals are retained, ordered and namespace-checked,
    /// NEVER asserted as unit input rows or applied as decisions here. They are
    /// caller input, not evidence that a CHC source/encoding has been verified.
    /// A later source-bound integration must preserve its conjunct-to-literal
    /// mapping and admit the actual assumption loop before exposing a result.
    /// This uses the existing CHC selection: trace on, backward certificate and
    /// SAT preprocessing off; default retained-core policy is unchanged.
    pub fn construct_traced(self, assumptions: &[Literal]) -> Result<crate::CountedInitialSolver> {
        crate::CountedInitialSolver::try_from_traced_cnf(self, assumptions)
    }

    /// Acquire a fixed namespace and borrowed input under an existing owner.
    ///
    /// No fresh allowance or timer is created. Invalid literals and namespace
    /// sizes latch `QueryError::Invalid`; resource refusal remains distinct.
    /// All temporary normalization storage is destroyed before the final fence.
    pub fn try_new(
        num_vars: usize,
        clauses: &[&[Literal]],
        owner: CountedAdmission,
    ) -> Result<Self> {
        owner.with_work(|_| Ok(Self::prepare(num_vars, clauses, &owner)))?
    }

    fn prepare(num_vars: usize, clauses: &[&[Literal]], owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, std::mem::size_of::<Self>())?;
        if num_vars > i32::MAX as usize {
            return Err(invalid(
                owner,
                "SAT variable count exceeds the DIMACS namespace",
            ));
        }
        let mut prepared = Self {
            owner: owner.clone(),
            num_vars,
            originals: Vec::new(),
            normalized: Vec::new(),
            rows: Vec::new(),
        };
        owner.admit(1, std::mem::size_of::<normalize::Scratch>())?;
        let mut scratch = normalize::Scratch::new();
        for clause in clauses {
            owner.admit(1, 0)?;
            prepared.append(clause, &mut scratch)?;
        }
        // Flat Copy buffers have no element destructors. Their allocation and
        // disposal were admitted before creation; the outer owner fences AFTER
        // this local scratch is destroyed, including failed partial builds.
        drop(scratch);
        Ok(prepared)
    }

    fn append(&mut self, clause: &[Literal], scratch: &mut normalize::Scratch) -> Result<()> {
        let owner = &self.owner;
        let original_start = self.originals.len();
        storage::reserve_append(&mut self.originals, clause.len(), owner)?;
        for literal in clause {
            owner.admit(1, std::mem::size_of::<Literal>())?;
            let literal = *literal;
            if literal.variable().index() >= self.num_vars {
                return Err(invalid(
                    owner,
                    "initial SAT clause contains an out-of-range literal",
                ));
            }
            self.originals.push(literal);
        }
        let tautology = scratch.normalize(clause, owner)?;
        let normalized_start = self.normalized.len();
        if !tautology {
            storage::append_literals(&mut self.normalized, scratch.literals(), owner)?;
        }
        storage::reserve_append(&mut self.rows, 1, owner)?;
        owner.admit(1, std::mem::size_of::<Row>())?;
        self.rows.push(Row {
            original: original_start..self.originals.len(),
            normalized: normalized_start..self.normalized.len(),
            tautology,
        });
        Ok(())
    }

    /// Fixed original variable namespace; no allocation or result authority.
    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Number of input rows, including tautologies and empty clauses.
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    /// Whether there are no input rows; this is not a SAT verdict.
    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// A paid immutable row lookup. Later scans/copies of the borrowed view
    /// belong to the consumer and require that consumer's own admissions.
    pub fn clause(&self, index: usize) -> Result<Option<InitialClause<'_>>> {
        self.owner.admit(1, 0)?;
        let clause = self.rows.get(index).map(|row| InitialClause {
            original: &self.originals[row.original.clone()],
            normalized: (!row.tautology).then(|| &self.normalized[row.normalized.clone()]),
        });
        self.owner.check()?;
        Ok(clause)
    }

    /// Diagnostic receipt for the same owner, including its other consumers.
    pub fn usage(&self) -> Result<AdmissionUsage> {
        self.owner.usage()
    }

    /// Dispose retained data, then observe the same terminal owner again.
    pub fn dispose(self) -> Result<()> {
        let owner = self.owner.clone();
        let admission = owner.admit(1, 0);
        drop(self);
        owner.check()?;
        admission
    }
}

fn invalid(owner: &CountedAdmission, message: &'static str) -> CountedAdmissionError {
    owner.refuse(CountedAdmissionError::Original(
        QueryError::Invalid(message).into(),
    ))
}
