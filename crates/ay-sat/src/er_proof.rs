// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structured Extended Resolution proof logs for extension variables.
//!
//! This module records the proof-relevant artifacts created when SAT
//! inprocessing introduces fresh extension variables. The log intentionally
//! excludes heuristic selection data: downstream proof replay should trust only
//! the emitted definitions, source clause references, and soundness obligations.

use crate::literal::{Literal, Variable};

mod log;

/// SAT transformation that introduced an extension variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErProducer {
    /// Clause factorization introduced the variable.
    Factor,
    /// Structured bounded variable addition introduced the variable.
    Sbva,
}

impl ErProducer {
    fn lean_ctor(self) -> &'static str {
        match self {
            Self::Factor => "Producer.factor",
            Self::Sbva => "Producer.sbva",
        }
    }
}

/// Replay obligation emitted for an extension-variable definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErObligationKind {
    /// Definition clauses must be admitted by RAT on the fresh variable.
    FreshRatDefinition,
    /// Proof-only witness clauses must be admitted by RAT and then deleted.
    WitnessRat,
    /// Derived replacement clauses must be checked by RUP from sources plus definitions.
    DerivedClauseRup,
    /// Rewritten source clauses may be deleted after the replacement clauses are available.
    SourceDeletion,
    /// SAT models of the transformed formula must project back to the original clauses.
    OriginalModelProjection,
}

impl ErObligationKind {
    fn lean_ctor(self) -> &'static str {
        match self {
            Self::FreshRatDefinition => "Obligation.freshRatDefinition",
            Self::WitnessRat => "Obligation.witnessRat",
            Self::DerivedClauseRup => "Obligation.derivedClauseRup",
            Self::SourceDeletion => "Obligation.sourceDeletion",
            Self::OriginalModelProjection => "Obligation.originalModelProjection",
        }
    }
}

/// Definition and replay obligations for one extension variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ErDefinition {
    extension_var: Variable,
    producer: ErProducer,
    definition_clauses: Vec<Vec<Literal>>,
    proof_only_clauses: Vec<Vec<Literal>>,
    derived_clauses: Vec<Vec<Literal>>,
    source_clause_ids: Vec<u64>,
    obligations: Vec<ErObligationKind>,
}

impl ErDefinition {
    /// Create a factorization extension-variable definition record.
    #[must_use]
    pub fn factor(
        extension_var: Variable,
        divider_clauses: Vec<Vec<Literal>>,
        quotient_clauses: Vec<Vec<Literal>>,
        blocked_clause: Vec<Literal>,
        source_clause_ids: Vec<u64>,
    ) -> Self {
        Self::new(
            extension_var,
            ErProducer::Factor,
            divider_clauses,
            vec![blocked_clause],
            quotient_clauses,
            source_clause_ids,
        )
    }

    /// Create a factorization definition only when all replay/model obligations
    /// are explicit before the solver mutates proof state or the clause DB.
    pub(crate) fn factor_checked(
        extension_var: Variable,
        divider_clauses: Vec<Vec<Literal>>,
        quotient_clauses: Vec<Vec<Literal>>,
        blocked_clause: Vec<Literal>,
        source_clause_ids: Vec<u64>,
    ) -> Option<Self> {
        if !factor_definition_parts_complete(
            extension_var,
            &divider_clauses,
            &quotient_clauses,
            &blocked_clause,
            &source_clause_ids,
        ) {
            return None;
        }
        Some(Self::factor(
            extension_var,
            divider_clauses,
            quotient_clauses,
            blocked_clause,
            source_clause_ids,
        ))
    }

    /// Create an SBVA extension-variable definition record.
    #[must_use]
    pub fn sbva(
        extension_var: Variable,
        definition_clause: Vec<Literal>,
        tail_clauses: Vec<Vec<Literal>>,
        blocked_clause: Vec<Literal>,
        source_clause_ids: Vec<u64>,
    ) -> Self {
        Self::new(
            extension_var,
            ErProducer::Sbva,
            vec![definition_clause],
            vec![blocked_clause],
            tail_clauses,
            source_clause_ids,
        )
    }

    fn new(
        extension_var: Variable,
        producer: ErProducer,
        definition_clauses: Vec<Vec<Literal>>,
        proof_only_clauses: Vec<Vec<Literal>>,
        derived_clauses: Vec<Vec<Literal>>,
        mut source_clause_ids: Vec<u64>,
    ) -> Self {
        source_clause_ids.retain(|id| *id != 0);
        source_clause_ids.sort_unstable();
        source_clause_ids.dedup();

        let mut obligations = vec![
            ErObligationKind::FreshRatDefinition,
            ErObligationKind::DerivedClauseRup,
            ErObligationKind::SourceDeletion,
            ErObligationKind::OriginalModelProjection,
        ];
        if !proof_only_clauses.is_empty() {
            obligations.insert(1, ErObligationKind::WitnessRat);
        }

        Self {
            extension_var,
            producer,
            definition_clauses,
            proof_only_clauses,
            derived_clauses,
            source_clause_ids,
            obligations,
        }
    }

    /// Extension variable defined by this record.
    #[must_use]
    pub fn extension_var(&self) -> Variable {
        self.extension_var
    }

    /// Transformation that produced this definition.
    #[must_use]
    pub fn producer(&self) -> ErProducer {
        self.producer
    }

    /// Clauses that define the extension variable.
    #[must_use]
    pub fn definition_clauses(&self) -> &[Vec<Literal>] {
        &self.definition_clauses
    }

    /// Proof-only clauses used as RAT witnesses and then deleted.
    #[must_use]
    pub fn proof_only_clauses(&self) -> &[Vec<Literal>] {
        &self.proof_only_clauses
    }

    /// Replacement clauses derived from sources plus extension definitions.
    #[must_use]
    pub fn derived_clauses(&self) -> &[Vec<Literal>] {
        &self.derived_clauses
    }

    /// Source clause IDs consumed by the rewrite.
    #[must_use]
    pub fn source_clause_ids(&self) -> &[u64] {
        &self.source_clause_ids
    }

    /// Obligations that an external replay checker must discharge.
    #[must_use]
    pub fn obligations(&self) -> &[ErObligationKind] {
        &self.obligations
    }
}

fn factor_definition_parts_complete(
    extension_var: Variable,
    divider_clauses: &[Vec<Literal>],
    quotient_clauses: &[Vec<Literal>],
    blocked_clause: &[Literal],
    source_clause_ids: &[u64],
) -> bool {
    if divider_clauses.len() < 2 || quotient_clauses.is_empty() {
        return false;
    }
    let Some(expected_sources) = divider_clauses.len().checked_mul(quotient_clauses.len()) else {
        return false;
    };
    if source_clause_ids.len() != expected_sources || !all_nonzero_unique(source_clause_ids) {
        return false;
    }

    let fresh_pos = Literal::positive(extension_var);
    let fresh_neg = Literal::negative(extension_var);
    let mut factors = Vec::with_capacity(divider_clauses.len());
    for divider in divider_clauses {
        if divider.len() != 2
            || divider[0] != fresh_pos
            || divider[1].variable() == extension_var
            || !clause_well_formed(divider)
        {
            return false;
        }
        factors.push(divider[1]);
    }
    if !all_literals_unique(&factors) {
        return false;
    }

    if blocked_clause.len() != factors.len() + 1
        || blocked_clause.first().copied() != Some(fresh_neg)
        || !clause_well_formed(blocked_clause)
    {
        return false;
    }
    for (&factor, &blocked_lit) in factors.iter().zip(&blocked_clause[1..]) {
        if blocked_lit != factor.negated() {
            return false;
        }
    }

    for quotient in quotient_clauses {
        if quotient.len() < 2
            || quotient.first().copied() != Some(fresh_neg)
            || !clause_well_formed(quotient)
        {
            return false;
        }
    }

    true
}

fn all_nonzero_unique(ids: &[u64]) -> bool {
    if ids.contains(&0) {
        return false;
    }
    let mut sorted = ids.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    sorted.len() == ids.len()
}

fn all_literals_unique(lits: &[Literal]) -> bool {
    let mut sorted = lits.iter().map(|lit| lit.to_dimacs()).collect::<Vec<_>>();
    sorted.sort_unstable();
    sorted.dedup();
    sorted.len() == lits.len()
}

fn clause_well_formed(clause: &[Literal]) -> bool {
    if clause.is_empty() {
        return false;
    }
    for (idx, &lit) in clause.iter().enumerate() {
        for &prev in &clause[..idx] {
            if prev == lit || prev == lit.negated() {
                return false;
            }
        }
    }
    true
}

/// Structured log of all extension-variable definitions emitted by a solver.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ErProofLog {
    definitions: Vec<ErDefinition>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_replay_export_records_definition_obligations_without_heuristics() {
        let x = Variable::new(2);
        let a = Literal::positive(Variable::new(0));
        let b = Literal::positive(Variable::new(1));
        let xpos = Literal::positive(x);
        let xneg = Literal::negative(x);

        let mut log = ErProofLog::new();
        log.push(ErDefinition::factor(
            x,
            vec![vec![xpos, a], vec![xpos, b]],
            vec![vec![xneg, a, b]],
            vec![xneg, a.negated(), b.negated()],
            vec![2, 1, 2],
        ));

        let mut buf = Vec::new();
        log.write_proof_replay(&mut buf).expect("write ER log");
        let source = String::from_utf8(buf).expect("utf8");

        assert!(source.contains("extensionDefinitions"));
        assert!(source.contains("extensionVar := 3"));
        assert!(source.contains("Obligation.freshRatDefinition"));
        assert!(source.contains("Obligation.derivedClauseRup"));
        assert!(source.contains("Obligation.originalModelProjection"));
        assert!(source.contains("theorem er_extension_log_structural_ok"));
        assert!(
            !source.contains("heuristicScore") && !source.contains("candidate"),
            "heuristic choices must stay outside the replay artifact"
        );
    }
}
