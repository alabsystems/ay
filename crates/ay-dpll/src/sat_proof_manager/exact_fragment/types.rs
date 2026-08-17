// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Proof, ProofId, TermId};
use ay_sat::{Literal, ResolutionValidationError};

/// Exact proof candidate for one SAT original-clause ID.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExactOriginalClauseBinding {
    pub(in crate::sat_proof_manager) proof_id: ProofId,
    pub(in crate::sat_proof_manager) clause: Vec<TermId>,
    pub(in crate::sat_proof_manager) trace_id: u64,
    pub(in crate::sat_proof_manager) trace_index: usize,
    pub(in crate::sat_proof_manager) source_sat_clause: Vec<Literal>,
}

impl ExactOriginalClauseBinding {
    pub(crate) fn proof_id(&self) -> ProofId {
        self.proof_id
    }

    pub(crate) fn clause(&self) -> &[TermId] {
        &self.clause
    }

    pub(crate) fn trace_id(&self) -> u64 {
        self.trace_id
    }

    pub(crate) fn trace_index(&self) -> usize {
        self.trace_index
    }

    pub(crate) fn source_sat_clause(&self) -> &[Literal] {
        &self.source_sat_clause
    }
}

/// Candidate fragment for every original clause in one SAT trace.
#[derive(Debug, Clone)]
pub(crate) struct ExactOriginalProofFragment {
    pub(in crate::sat_proof_manager) proof: Proof,
    pub(in crate::sat_proof_manager) bindings: HashMap<u64, ExactOriginalClauseBinding>,
}

impl ExactOriginalProofFragment {
    pub(crate) fn proof(&self) -> &Proof {
        &self.proof
    }

    pub(crate) fn binding(&self, trace_id: u64) -> Option<&ExactOriginalClauseBinding> {
        self.bindings.get(&trace_id)
    }

    pub(crate) fn binding_count(&self) -> usize {
        self.bindings.len()
    }
}

/// Why an exact original-clause fragment could not be built.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum ExactOriginalProofError {
    #[error(transparent)]
    Resource(#[from] ResolutionValidationError),
    #[error("original clause uses reserved trace ID zero")]
    ZeroClauseId,
    #[error("duplicate original-clause trace ID {clause_id}")]
    DuplicateClauseId { clause_id: u64 },
    #[error("original clause {clause_id} is empty")]
    EmptyOriginalClause { clause_id: u64 },
    #[error("original clause {clause_id} references unmapped SAT variable {variable}")]
    UnmappedVariable { clause_id: u64, variable: u32 },
    #[error("scope premise for SAT variable {variable} must be negative")]
    PositiveScopeAssumption { variable: u32 },
    #[error("scope premise for SAT variable {variable} is duplicated")]
    DuplicateScopeAssumption { variable: u32 },
    #[error(
        "scope premise SAT variables must be strictly increasing, found {variable} after {previous}"
    )]
    UnorderedScopeAssumption { previous: u32, variable: u32 },
    #[error("scope premise for SAT variable {variable} overlaps the SMT-term map")]
    MappedScopeAssumption { variable: u32 },
    #[error("original clause {clause_id} contains satisfied negative scope selector {variable}")]
    SatisfiedScopeGuard { clause_id: u64, variable: u32 },
    #[error("original clause {clause_id} maps SAT variable {variable} to stale term {term:?}")]
    StaleMappedTerm {
        clause_id: u64,
        variable: u32,
        term: TermId,
    },
    #[error("original clause {clause_id} has two indexed proof annotations")]
    AmbiguousIndexedAnnotations { clause_id: u64 },
    #[error(
        "indexed clausification annotation does not prove original clause {clause_id}: {clause:?}"
    )]
    InvalidClausificationAnnotation { clause_id: u64, clause: Vec<TermId> },
    #[error("indexed theory annotation does not prove original clause {clause_id}: {clause:?}")]
    InvalidTheoryAnnotation { clause_id: u64, clause: Vec<TermId> },
    #[error("original clause {clause_id} has no exact proof authority: {clause:?}")]
    UnauthenticatedOriginalClause { clause_id: u64, clause: Vec<TermId> },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FragmentInstanceDerivation {
    pub(crate) quantifier: TermId,
    pub(crate) values: Vec<TermId>,
    /// Exact raw simultaneous substitution. Equal to the map key except for
    /// independently sealed fold-bridged records.
    pub(crate) instance: TermId,
}

/// Sealed `PropagateValues` licensing environment for the c7 unit channel
/// (#ppp-c7). Records and entries are HINTS: the fragment planner replays
/// every rewrite independently and each emitted step is re-derived by the
/// untouched strict checker; a wrong or missing map entry can only decline
/// a derivation, never mint one.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct FragmentPropagationEnvironment {
    /// after -> (before, stamp), first record wins.
    pub(crate) record_by_after: HashMap<TermId, (TermId, u32)>,
    /// expr -> (value, source assertion, stamp), first harvest wins.
    pub(crate) entry_by_expr: HashMap<TermId, (TermId, TermId, u32)>,
}

impl FragmentPropagationEnvironment {
    pub(crate) fn is_empty(&self) -> bool {
        self.record_by_after.is_empty()
    }
}

/// Sealed qpf premise-forced instance root for the c7 unit channel
/// (#ppp-c7): the raw exact instance of an authored quantifier, its unique
/// non-refuted disjunct survivor, and the closed disjuncts the seal replay
/// verified model-free `false`. Emission re-derives everything strictly:
/// `forall_inst` replays the exact substitution and every refuted disjunct
/// becomes a zero-variable exhaustively-evaluated `BvBitBlast` lemma.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FragmentInstanceRootDerivation {
    pub(crate) quantifier: TermId,
    pub(crate) values: Vec<TermId>,
    /// Exact raw simultaneous substitution of the quantifier body.
    pub(crate) instance: TermId,
    /// Unique non-refuted disjunct (equal to `instance` when no disjunct
    /// was refuted).
    pub(crate) survivor: TermId,
    /// Closed disjuncts sealed as model-free `false`.
    pub(crate) refuted_disjuncts: Vec<TermId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FragmentSkolemDerivation {
    pub(crate) source: TermId,
    pub(crate) quantified: TermId,
    pub(crate) witness: TermId,
    pub(crate) instance: TermId,
    pub(crate) positive: bool,
}

/// Authored `(or S false ... false)` fold plan for one solver-visible unit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::sat_proof_manager) struct OrFoldUnitPlan {
    pub(in crate::sat_proof_manager) or_root: TermId,
    pub(in crate::sat_proof_manager) disjuncts: Vec<TermId>,
    pub(in crate::sat_proof_manager) survivor: TermId,
    pub(in crate::sat_proof_manager) hops: Vec<(TermId, u32)>,
}
