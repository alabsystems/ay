// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A counterexample found on a case split of a problem, restated over that
//! problem.
//!
//! `ChcProblem::try_split_ites_in_clauses_recorded` (and the OR variant)
//! return the source clause of every split clause. A case is an instance of
//! its source clause (the same predicates and variables under a stronger
//! constraint), so a fact one case derives is derived by its source clause
//! from the same premises: the witness's and the steps' clause indices map one
//! for one. The ground derivation is mapped too, and kept only when it then
//! validates on the unsplit problem.

use super::{Counterexample, DerivationWitness};
use crate::ground_derivation::{validate_ground_derivation, GroundDerivation};
use crate::ChcProblem;

impl Counterexample {
    /// This counterexample, found on a case split of `unsplit` whose clause
    /// `i` came from clause `origins[i]`, restated over `unsplit`. A witness
    /// naming a clause outside `origins` is dropped.
    pub(crate) fn restated_over_unsplit(mut self, origins: &[usize], unsplit: &ChcProblem) -> Self {
        self.witness = self
            .witness
            .take()
            .and_then(|witness| unsplit_witness(witness, origins));
        for step in &mut self.steps {
            step.clause_index = step
                .clause_index
                .and_then(|index| origins.get(index).copied());
        }
        self.ground_derivation = self
            .ground_derivation
            .take()
            .and_then(|derivation| unsplit_derivation(derivation, origins, unsplit));
        self
    }
}

fn unsplit_witness(mut witness: DerivationWitness, origins: &[usize]) -> Option<DerivationWitness> {
    for entry in &mut witness.entries {
        if let Some(index) = entry.incoming_clause {
            entry.incoming_clause = Some(*origins.get(index)?);
        }
    }
    if let Some(index) = witness.query_clause {
        witness.query_clause = Some(*origins.get(index)?);
    }
    Some(witness)
}

fn unsplit_derivation(
    mut derivation: GroundDerivation,
    origins: &[usize],
    unsplit: &ChcProblem,
) -> Option<GroundDerivation> {
    for step in &mut derivation.steps {
        step.clause_index = *origins.get(step.clause_index)?;
    }
    validate_ground_derivation(unsplit, &derivation)
        .ok()
        .map(|()| derivation)
}
