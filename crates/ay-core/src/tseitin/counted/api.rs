// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

impl CountedCnf<'_> {
    /// Immutable original store plus paid raw synthetic proof terms.
    /// Processing or copying this borrowed view must use `admission()`; this
    /// accessor itself does not debit the work of a consumer's traversal.
    pub fn terms(&self) -> &TermStore {
        self.terms
    }
    /// Clauses are not source SAT authority while theory atoms remain.
    pub fn rows(&self) -> &[Row] {
        &self.data.rows
    }
    /// Exact premise-bearing proof plan, not a successfully checked proof.
    pub fn steps(&self) -> &[Step] {
        &self.data.steps
    }
    /// Ordered input roots, preserving duplicates and original identities.
    pub fn roots(&self) -> &[TermId] {
        &self.data.roots
    }
    /// Every entry still requires the corresponding theory's real encoding.
    pub fn theory_atoms(&self) -> &[TermId] {
        &self.data.theory_atoms
    }
    /// Exact synthetic terms connecting original distinct nodes to equality.
    /// Their presence is a proof plan, not an independent replay result.
    pub fn bridges(&self) -> &[DistinctBridge] {
        &self.data.bridges
    }
    /// Number of allocated Boolean CNF variables, numbered from one.
    /// Theory-atom variables are included and remain unresolved obligations.
    pub fn num_vars(&self) -> u32 {
        self.data.num_vars
    }
    /// The same caller ledger, never a new grant or deadline.
    pub fn admission(&self) -> &CountedAdmission {
        &self.owner
    }

    /// Lookup of an admitted source Boolean term's signed CNF alias.
    /// Numeric TermIds must belong to `terms()`; this is not foreign-handle or
    /// authored-assertion authentication. Non-Boolean/unmapped terms refuse.
    pub fn literal_for_term(&self, term: TermId) -> Result<i32> {
        self.owner.admit(1, 0)?;
        self.data
            .term_literals
            .get(term.index())
            .copied()
            .flatten()
            .ok_or(Error::Invalid)
    }

    /// Exact, pre-materialized source literal, without Not normalization.
    /// Positive lookups require an admitted source/proof Boolean identity;
    /// negative lookups additionally require a prepared proof/SAT polarity.
    /// This maps an identity, not an assertion or a checked theorem. In
    /// particular a caller cannot use a successful lookup to add an assumption.
    pub fn source_literal_term(&self, literal: SourceLit) -> Result<TermId> {
        self.prepared.source_literal(literal, &self.owner)
    }

    /// Canonical source representative of a signed SAT literal. Both signs
    /// were materialized under the original owner before this immutable view.
    /// Zero, i32::MIN and out-of-range IDs are invalid, not new variables.
    pub fn sat_literal_term(&self, literal: i32) -> Result<TermId> {
        self.prepared.sat_literal(literal, &self.owner)
    }
}

impl Row {
    /// Signed, nonzero DIMACS literals in the original emitted row order.
    pub fn literals(&self) -> &[i32] {
        &self.literals
    }
    /// Input-root activation or proof-ledger index, never a checked-proof seal.
    pub fn justification(&self) -> Justification {
        self.justification
    }
}

impl Step {
    /// Native rule to replay against this step's exact source clause.
    pub fn rule(&self) -> &AletheRule {
        &self.rule
    }
    /// Original or synthetic typed source of the inference, not an assumption.
    pub fn source(&self) -> TermId {
        self.source
    }
    /// Exact source literals, before signed SAT aliases normalize raw Nots.
    pub fn clause(&self) -> &[SourceLit] {
        &self.clause
    }
    /// Backward proof-ledger indexes for binary resolution, or None for a
    /// premiseless native rule. These are not SAT row IDs or external ProofIds.
    pub fn premises(&self) -> Option<[usize; 2]> {
        self.premises
    }
    /// Exact source-term resolution pivot, present with `premises()`.
    pub fn pivot(&self) -> Option<TermId> {
        self.pivot
    }
}
