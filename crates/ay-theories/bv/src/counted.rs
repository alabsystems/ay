// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Paid eager encoding using the existing BV circuits, not a solver verdict.
//!
//! The restricted view intentionally has no mutable solver escape, delayed
//! mode, imported caches, model builder or unmetered flat-batch export. Those
//! APIs are not made accounted merely by attaching an owner. A typed unsupported
//! operation refuses the same owner before entering an uncovered helper.

use super::*;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};

mod array_reads;
mod bools;
mod cleanup;
mod materialize;
pub(crate) mod memory;
mod prepare;
mod primitives;
#[cfg(test)]
mod tests;
mod typing;

/// Version of logical BV work units, not CPU instructions or elapsed time.
/// Visits, gate attempts, copied elements, dictionary operations and collection
/// growth are charged before execution; cumulative storage is never refunded.
/// A gate-attempt unit includes its bounded scalar cache probes; collection
/// growth also prepays eventual bucket/element destruction. This is not a
/// worst-case hash-probe or CPU-instruction metric.
pub const COUNTED_BV_WORK_VERSION: u32 = 2;

/// A refused encoding is never a complete circuit or a solver answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum CountedBvError {
    /// The original invocation has stopped or exhausted its allowance.
    #[error(transparent)]
    Stopped(#[from] CountedAdmissionError),
    /// This encoder cannot yet account for the requested operation.
    #[error("unsupported counted BV encoding: {0}")]
    Unsupported(&'static str),
    /// The input is not a well-typed live Bool/BV term or CNF literal.
    #[error("invalid counted BV input")]
    Invalid,
}

type Result<T> = std::result::Result<T, CountedBvError>;

/// Original-owner, query-local eager BV circuit builder.
///
/// Multiple calls retain the same memo tables and allowance. Clauses and bits
/// are encoding data, NOT evidence that their source is satisfiable. Array
/// theory axioms, SAT, proof checking and model replay remain caller obligations.
/// The ordinary constructor accepts scalar Bool/BV DAGs only. The separate
/// authentic-array-closure constructor retains every read obligation; its
/// scalar read leaves are never a complete source circuit or model authority.
#[must_use = "finish the encoder under its original owner before publishing its output"]
pub struct CountedBvEncoder<'a> {
    solver: BvSolver<'a>,
    owner: CountedAdmission,
    prepared: HashSet<TermId>,
    array_reads: Option<&'a ay_arrays::counted_reads::CountedArrayReadClosure>,
}

impl<'a> CountedBvEncoder<'a> {
    /// Capture no new grant or timer; charge construction before allocation.
    pub fn new(terms: &'a TermStore, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(
            4,
            size_of::<Self>()
                + size_of::<encoding_control::EncodingControl>()
                + 2 * size_of::<usize>(),
        )?;
        let mut result = Self {
            solver: BvSolver::with_encoding(
                terms,
                encoding_control::EncodingControl::with_admission(owner),
            ),
            owner: owner.clone(),
            prepared: HashSet::default(),
            array_reads: None,
        };
        // The owned route retains the actual gate graph for later source-bound
        // proof construction. Recording is paid at each insertion, not enabled
        // retroactively after a clause has lost its origin.
        result.solver.capture_gate_provenance = true;
        if let Err(error) = cleanup::check(&result) {
            return Err(cleanup::finish(result).err().unwrap_or(error));
        }
        Ok(result)
    }

    /// Encode all reached scalar terms, including every dead Boolean/ITE arm.
    /// No root is asserted. Memoized continuations share the original ledger.
    pub fn encode_terms(&mut self, roots: &[TermId]) -> Result<()> {
        let owner = self.owner.clone();
        let result = owner.with_work(|_| Ok(prepare::encode(self, roots)))?;
        if let Err(error) = result {
            return Err(self.refuse(error));
        }
        self.check()
    }

    /// Encode and assert the exact ordered original Boolean roots.
    pub fn assert_roots(&mut self, roots: &[TermId]) -> Result<()> {
        self.encode_terms(roots)?;
        let owner = self.owner.clone();
        owner.with_work(|_| {
            let result = (|| {
                self.owner.admit(roots.len(), 0)?;
                for &root in roots {
                    if self.solver.terms.sort(root) != &Sort::Bool {
                        return Err(self.refuse(CountedBvError::Invalid));
                    }
                    let literal = self.literal(root)?;
                    self.solver.emit_clause(&[literal]);
                    self.check()?;
                }
                self.check()
            })();
            Ok(result)
        })?
    }

    /// Borrow an already encoded BV word. Copying it is the caller's work.
    pub fn bits(&self, term: TermId) -> Result<&[CnfLit]> {
        self.owner.admit(1, 0)?;
        self.check()?;
        self.solver
            .term_to_bits
            .get(&term)
            .map(Vec::as_slice)
            .ok_or_else(|| self.refuse(CountedBvError::Invalid))
    }

    /// Retrieve an already encoded Boolean source literal.
    pub fn literal(&self, term: TermId) -> Result<CnfLit> {
        self.owner.admit(1, 0)?;
        self.check()?;
        self.solver
            .bool_to_var
            .get(&term)
            .copied()
            .ok_or_else(|| self.refuse(CountedBvError::Invalid))
    }

    /// Borrow all current clauses without cloning them.
    pub fn clauses(&self) -> Result<&[CnfClause]> {
        self.check()?;
        Ok(&self.solver.clauses)
    }

    /// Transfer current clauses without a copy. Later disposal is caller-owned.
    pub fn take_clauses(&mut self) -> Result<Vec<CnfClause>> {
        self.owner.admit(1, 0)?;
        self.check()?;
        Ok(std::mem::take(&mut self.solver.clauses))
    }

    /// The variable range includes every successful previous encoding call.
    pub fn num_vars(&self) -> Result<u32> {
        self.check()?;
        Ok(self.solver.num_vars())
    }

    /// The original ledger for downstream SAT, theory and proof work.
    pub fn admission(&self) -> &CountedAdmission {
        &self.owner
    }

    /// Borrow exact AND input records; these are circuit data, not a proof.
    pub fn and_gates(&self) -> Result<&AndChildren> {
        self.check()?;
        Ok(&self.solver.and_children)
    }

    /// Borrow exact XOR input records, retained from the first emitted gate.
    pub fn xor_gates(&self) -> Result<&XorChildren> {
        self.check()?;
        Ok(&self.solver.xor_children)
    }

    /// Borrow exact selector/then/else records for every primitive MUX.
    pub fn mux_gates(&self) -> Result<&MuxChildren> {
        self.check()?;
        Ok(&self.solver.mux_children)
    }

    /// Poll retained controls, without granting work or certifying semantics.
    pub fn check(&self) -> Result<()> {
        self.owner.with_work(|_| {
            if !self.solver.encoding_complete() {
                return Ok(Err(
                    self.refuse(CountedBvError::Unsupported("encoding owner refused"))
                ));
            }
            Ok(Ok(()))
        })?
    }

    /// Dispose of private state before the original final resource fence.
    pub fn finish(self) -> Result<()> {
        cleanup::finish(self)
    }

    fn refuse(&self, error: CountedBvError) -> CountedBvError {
        match error {
            CountedBvError::Stopped(error) => {
                self.solver.encoding.counted_refuse(error);
            }
            CountedBvError::Unsupported(why) => self.solver.counted_unsupported(why),
            CountedBvError::Invalid => self.solver.counted_unsupported("invalid counted BV source"),
        }
        error
    }
}
