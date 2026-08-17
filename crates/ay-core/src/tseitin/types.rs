// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tseitin transformation types: CNF clauses, results, and incremental state.

use crate::proof::AletheRule;
use crate::term::TermId;
use std::collections::BTreeMap;

/// A CNF literal (signed integer, DIMACS-style)
/// Positive values represent the variable being true,
/// negative values represent the variable being false.
/// Variable numbering starts at 1.
pub type CnfLit = i32;

/// A CNF clause (disjunction of literals)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CnfClause(pub Vec<CnfLit>);

impl CnfClause {
    /// Create a new clause from literals
    pub fn new(literals: Vec<CnfLit>) -> Self {
        Self(literals)
    }

    /// Create a unit clause
    pub fn unit(lit: CnfLit) -> Self {
        Self(vec![lit])
    }

    /// Create a binary clause
    pub fn binary(a: CnfLit, b: CnfLit) -> Self {
        Self(vec![a, b])
    }

    /// Create a ternary clause
    pub fn ternary(a: CnfLit, b: CnfLit, c: CnfLit) -> Self {
        Self(vec![a, b, c])
    }

    /// Check if the clause is empty (conflict)
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Get the literals
    pub fn literals(&self) -> &[CnfLit] {
        &self.0
    }
}

/// Proof annotation for a single Tseitin-generated clause.
///
/// Each annotation records the Alethe tautology rule that justifies the clause
/// and the source term it derives from. Tautology rules are premiseless — the
/// source term appears directly in the proof clause.
#[derive(Debug, Clone)]
pub struct ClausificationProof {
    /// The Alethe tautology rule justifying this clause (e.g., `and_pos(0)`)
    pub rule: AletheRule,
    /// The source term this clause derives from (e.g., the `(and a b)` TermId)
    pub source_term: TermId,
}

/// Result of Tseitin transformation
#[derive(Debug)]
#[non_exhaustive]
pub struct TseitinResult {
    /// The CNF clauses
    pub clauses: Vec<CnfClause>,
    /// Mapping from term IDs to CNF variables (1-indexed)
    pub term_to_var: BTreeMap<TermId, u32>,
    /// Mapping from CNF variables to term IDs
    pub var_to_term: BTreeMap<u32, TermId>,
    /// The root literal (represents the whole formula)
    pub root: CnfLit,
    /// Number of variables used (max variable index)
    pub num_vars: u32,
    /// Proof annotations for clausification (when proof tracking is enabled).
    /// Parallel to `clauses` — `proof_annotations[i]` justifies `clauses[i]`.
    /// `None` when proof tracking is disabled.
    pub proof_annotations: Option<Vec<Option<ClausificationProof>>>,
}

impl TseitinResult {
    /// Create a new Tseitin result
    #[must_use]
    pub fn new(
        clauses: Vec<CnfClause>,
        term_to_var: BTreeMap<TermId, u32>,
        var_to_term: BTreeMap<u32, TermId>,
        root: CnfLit,
        num_vars: u32,
    ) -> Self {
        Self {
            clauses,
            term_to_var,
            var_to_term,
            root,
            num_vars,
            proof_annotations: None,
        }
    }

    /// Attach a proof ledger only when it is exactly parallel to the clauses.
    ///
    /// A positional clausification annotation is authority for one original
    /// SAT-clause ID.  A short or long ledger therefore cannot be partially
    /// accepted: discard it wholesale and leave reconstruction proofless so
    /// the strict publication boundary fails closed.
    #[must_use]
    pub fn with_parallel_proof_annotations(
        mut self,
        proof_annotations: Option<Vec<Option<ClausificationProof>>>,
    ) -> Self {
        self.proof_annotations =
            proof_annotations.filter(|annotations| annotations.len() == self.clauses.len());
        self
    }

    /// Convert a CNF variable to a TermId if it exists
    pub fn term_for_var(&self, var: u32) -> Option<TermId> {
        self.var_to_term.get(&var).copied()
    }

    /// Convert a TermId to a CNF variable if it exists
    pub fn var_for_term(&self, term: TermId) -> Option<u32> {
        self.term_to_var.get(&term).copied()
    }
}

/// Result of encoding a single assertion for incremental solving.
///
/// This separates definitional clauses (which must remain globally active
/// when the term→var cache is reused across push/pop) from the root literal
/// (whose activation can be scoped).
///
/// **Incremental scoping invariant**: Definitional clauses define the meaning
/// of cached CNF variables and must be added with `SatSolver::add_clause_global()`
/// when reusing `TseitinState` across push/pop. Assertion activation (the unit
/// clause `[root_lit]`) should be added with `SatSolver::add_clause()` so it
/// follows SMT scoping.
///
/// See the development design notes for details.
#[derive(Debug, Clone)]
pub struct TseitinEncodedAssertion {
    /// The root literal representing this assertion.
    /// Add `CnfClause::unit(root_lit)` via scoped `add_clause()` to activate.
    pub root_lit: CnfLit,
    /// Definitional clauses for subterms introduced by this encoding.
    /// These may include unit clauses for Boolean constants and must be
    /// added via `add_clause_global()` to remain active across push/pop.
    pub def_clauses: Vec<CnfClause>,
    /// Proof annotations aligned with `def_clauses` when proof tracking is enabled.
    pub def_proof_annotations: Option<Vec<Option<ClausificationProof>>>,
}

/// Saved Tseitin state for incremental use
///
/// This stores the internal state of a Tseitin transformer, allowing
/// it to be saved and restored across multiple transformation calls
/// while sharing term-to-variable mappings.
#[derive(Debug, Clone)]
pub struct TseitinState {
    /// Mapping from term IDs to CNF variables
    pub term_to_var: BTreeMap<TermId, u32>,
    /// Mapping from CNF variables to term IDs
    pub var_to_term: BTreeMap<u32, TermId>,
    /// Next variable index (1-indexed, DIMACS style)
    pub next_var: u32,
    /// Cache for polarity-aware encoding
    pub encoded: BTreeMap<(TermId, bool), CnfLit>,
}

impl TseitinState {
    /// Create a new empty state
    pub fn new() -> Self {
        Self {
            term_to_var: BTreeMap::new(),
            var_to_term: BTreeMap::new(),
            next_var: 1, // DIMACS variables are 1-indexed
            encoded: BTreeMap::new(),
        }
    }
}

impl Default for TseitinState {
    fn default() -> Self {
        Self::new()
    }
}
