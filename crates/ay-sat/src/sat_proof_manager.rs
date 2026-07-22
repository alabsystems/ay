// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-level resolution proof metadata tracking.
//!
//! `SatProofManager` is intentionally narrower than the DRAT/LRAT
//! `crate::proof_manager::ProofManager`: it does not write proof files.
//! Instead it owns stable clause IDs and the in-memory derivation metadata
//! needed by later DRAT/LRAT/Alethe proof reconstruction.

use crate::kani_compat::DetHashMap;
use crate::Literal;

/// Stable SAT proof clause identifier.
pub type SatProofClauseId = u64;

/// A single resolution antecedent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ResolutionAntecedent {
    /// Antecedent clause ID.
    pub clause_id: SatProofClauseId,
    /// Resolution pivot used with this antecedent, when known.
    pub pivot: Option<Literal>,
}

impl ResolutionAntecedent {
    /// Create an antecedent without an explicit pivot.
    #[must_use]
    pub fn clause(clause_id: SatProofClauseId) -> Self {
        Self {
            clause_id,
            pivot: None,
        }
    }

    /// Create an antecedent with an explicit resolution pivot.
    #[must_use]
    pub fn with_pivot(clause_id: SatProofClauseId, pivot: Literal) -> Self {
        Self {
            clause_id,
            pivot: Some(pivot),
        }
    }
}

/// Clause derivation metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SatClauseDerivation {
    /// Input/original SAT clause.
    Original,
    /// Derived clause with ordered resolution antecedents.
    Resolution {
        /// Ordered resolution antecedents.
        antecedents: Vec<ResolutionAntecedent>,
    },
}

/// Recorded SAT clause proof metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SatClauseProof {
    id: SatProofClauseId,
    clause: Vec<Literal>,
    derivation: SatClauseDerivation,
    retained: bool,
}

impl SatClauseProof {
    /// Clause ID.
    #[must_use]
    pub fn id(&self) -> SatProofClauseId {
        self.id
    }

    /// Clause literals.
    #[must_use]
    pub fn clause(&self) -> &[Literal] {
        &self.clause
    }

    /// Derivation metadata.
    #[must_use]
    pub fn derivation(&self) -> &SatClauseDerivation {
        &self.derivation
    }

    /// True while the clause is retained and may be used as a future antecedent.
    #[must_use]
    pub fn is_retained(&self) -> bool {
        self.retained
    }
}

/// Errors returned by [`SatProofManager`].
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum SatProofError {
    /// Clause ID is already recorded.
    #[error("clause ID {0} is already recorded")]
    DuplicateClauseId(SatProofClauseId),
    /// Clause ID is unknown.
    #[error("unknown clause ID {0}")]
    UnknownClauseId(SatProofClauseId),
    /// Clause ID is known but has been deleted and cannot be used live.
    #[error("clause ID {0} has been deleted")]
    DeletedClauseId(SatProofClauseId),
    /// A derived clause needs at least one antecedent.
    #[error("derived clause needs at least one antecedent")]
    EmptyAntecedents,
}

/// SAT-level proof metadata manager.
#[derive(Debug, Clone)]
pub struct SatProofManager {
    next_clause_id: SatProofClauseId,
    clauses: DetHashMap<SatProofClauseId, SatClauseProof>,
}

impl Default for SatProofManager {
    fn default() -> Self {
        Self::new()
    }
}

impl SatProofManager {
    /// Create a manager whose first allocated clause ID is 1.
    #[must_use]
    pub fn new() -> Self {
        Self::with_first_clause_id(1)
    }

    /// Create a manager with a caller-selected first allocated clause ID.
    #[must_use]
    pub fn with_first_clause_id(first_clause_id: SatProofClauseId) -> Self {
        Self {
            next_clause_id: first_clause_id,
            clauses: Default::default(),
        }
    }

    /// Return the next clause ID that will be allocated.
    #[must_use]
    pub fn next_clause_id(&self) -> SatProofClauseId {
        self.next_clause_id
    }

    /// Allocate and reserve a fresh clause ID.
    pub fn allocate_clause_id(&mut self) -> SatProofClauseId {
        let id = self.next_clause_id;
        self.next_clause_id = self.next_clause_id.saturating_add(1);
        id
    }

    /// Record an original clause with a fresh clause ID.
    pub fn record_original_clause(&mut self, clause: Vec<Literal>) -> SatProofClauseId {
        let id = self.allocate_clause_id();
        self.record_original_clause_with_id(id, clause)
            .expect("fresh clause ID must be recordable");
        id
    }

    /// Record an original clause with an existing solver clause ID.
    pub fn record_original_clause_with_id(
        &mut self,
        id: SatProofClauseId,
        clause: Vec<Literal>,
    ) -> Result<(), SatProofError> {
        self.insert_clause(id, clause, SatClauseDerivation::Original)
    }

    /// Record a resolution-derived clause with a fresh clause ID.
    pub fn record_resolution_clause(
        &mut self,
        clause: Vec<Literal>,
        antecedents: Vec<ResolutionAntecedent>,
    ) -> Result<SatProofClauseId, SatProofError> {
        let id = self.allocate_clause_id();
        self.record_resolution_clause_with_id(id, clause, antecedents)?;
        Ok(id)
    }

    /// Record a resolution-derived clause with an existing solver clause ID.
    pub fn record_resolution_clause_with_id(
        &mut self,
        id: SatProofClauseId,
        clause: Vec<Literal>,
        antecedents: Vec<ResolutionAntecedent>,
    ) -> Result<(), SatProofError> {
        if antecedents.is_empty() {
            return Err(SatProofError::EmptyAntecedents);
        }
        for antecedent in &antecedents {
            self.require_retained(antecedent.clause_id)?;
        }
        self.insert_clause(id, clause, SatClauseDerivation::Resolution { antecedents })
    }

    /// Mark a retained clause as deleted.
    ///
    /// The record is preserved for audit/reconstruction, but the clause can no
    /// longer be used as a new derivation antecedent.
    pub fn delete_clause(&mut self, id: SatProofClauseId) -> Result<(), SatProofError> {
        let clause = self
            .clauses
            .get_mut(&id)
            .ok_or(SatProofError::UnknownClauseId(id))?;
        clause.retained = false;
        Ok(())
    }

    /// Return a recorded clause, including deleted records.
    #[must_use]
    pub fn clause(&self, id: SatProofClauseId) -> Option<&SatClauseProof> {
        self.clauses.get(&id)
    }

    /// Return a retained clause only.
    #[must_use]
    pub fn retained_clause(&self, id: SatProofClauseId) -> Option<&SatClauseProof> {
        self.clauses.get(&id).filter(|clause| clause.retained)
    }

    /// True if the clause is known and retained.
    #[must_use]
    pub fn is_retained(&self, id: SatProofClauseId) -> bool {
        self.retained_clause(id).is_some()
    }

    /// Number of recorded clauses, including deleted records.
    #[must_use]
    pub fn clause_count(&self) -> usize {
        self.clauses.len()
    }

    fn insert_clause(
        &mut self,
        id: SatProofClauseId,
        clause: Vec<Literal>,
        derivation: SatClauseDerivation,
    ) -> Result<(), SatProofError> {
        if self.clauses.contains_key(&id) {
            return Err(SatProofError::DuplicateClauseId(id));
        }
        self.next_clause_id = self.next_clause_id.max(id.saturating_add(1));
        self.clauses.insert(
            id,
            SatClauseProof {
                id,
                clause,
                derivation,
                retained: true,
            },
        );
        Ok(())
    }

    fn require_retained(&self, id: SatProofClauseId) -> Result<(), SatProofError> {
        match self.clauses.get(&id) {
            Some(clause) if clause.retained => Ok(()),
            Some(_) => Err(SatProofError::DeletedClauseId(id)),
            None => Err(SatProofError::UnknownClauseId(id)),
        }
    }
}

#[cfg(test)]
#[path = "sat_proof_manager_tests.rs"]
mod tests;
