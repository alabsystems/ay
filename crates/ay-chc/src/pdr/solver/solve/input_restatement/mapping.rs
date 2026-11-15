// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Recorded split/nullary maps preserve original-clause names. Mapping is not
//! proof authority: ground evidence is replayed on the original input. The
//! caller distinguishes ordinary rejection from the same owner's sticky stop.
//! Existing environment copies and evaluator work remain opaque, as on the
//! nullary translation path; these polls do not claim whole-operation metering.

use super::{Counterexample, InputRestatementControl, InputRestatementInterrupted, PdrSolver};
use crate::ground_derivation::{
    validate_ground_derivation_with_progress, GroundDerivation, GroundDerivationError,
};
use crate::pdr::counterexample::{DerivationWitness, DerivationWitnessEntry};
use crate::problem::ExpandedClauseOrigin;
use crate::{ChcExpr, ClauseHead};
use ay_core::kani_compat::DetHashMap as FxHashMap;

enum InputClause {
    Clause(usize),
    ExpandedQuery { into_fail: usize, fail_query: usize },
}

impl PdrSolver {
    /// Compose recorded case-split maps; an identity needs no stored map.
    pub(in crate::pdr::solver) fn compose_case_split_origins(
        inner: Option<Vec<usize>>,
        outer: Vec<usize>,
    ) -> Option<Vec<usize>> {
        let composed: Vec<usize> = match inner {
            None => outer,
            Some(inner) => outer.into_iter().map(|source| inner[source]).collect(),
        };
        let identity = composed
            .iter()
            .enumerate()
            .all(|(index, &source)| index == source);
        (!identity).then_some(composed)
    }

    fn input_clause(&self, index: usize) -> Option<InputClause> {
        let unsplit = match &self.case_split_origins {
            Some(origins) => *origins.get(index)?,
            None if index < self.problem.clauses().len() => index,
            None => return None,
        };
        match &self.nullary_expansion {
            None => Some(InputClause::Clause(unsplit)),
            Some(expansion) => Some(match expansion.origin(unsplit)? {
                ExpandedClauseOrigin::Kept(input) => InputClause::Clause(input),
                ExpandedClauseOrigin::Expanded {
                    into_fail,
                    fail_query,
                } => InputClause::ExpandedQuery {
                    into_fail,
                    fail_query,
                },
            }),
        }
    }

    pub(super) fn restate_step_indices(
        &self,
        cex: &mut Counterexample,
        owner: &InputRestatementControl<'_>,
    ) {
        for step in &mut cex.steps {
            if !owner.open() {
                return;
            }
            step.clause_index =
                step.clause_index
                    .and_then(|index| match self.input_clause(index) {
                        Some(InputClause::Clause(input)) => Some(input),
                        Some(InputClause::ExpandedQuery { .. }) | None => None,
                    });
        }
    }

    pub(super) fn derivation_through_clause_maps(
        &self,
        derivation: &GroundDerivation,
        owner: &InputRestatementControl<'_>,
    ) -> Result<Option<GroundDerivation>, InputRestatementInterrupted> {
        if !owner.open() {
            return Err(InputRestatementInterrupted);
        }
        let mut unsplit = GroundDerivation {
            steps: Vec::with_capacity(derivation.steps.len()),
            query_step: derivation.query_step,
        };
        for step in &derivation.steps {
            if !owner.open() {
                return Err(InputRestatementInterrupted);
            }
            let mut mapped = step.clone();
            if let Some(origins) = &self.case_split_origins {
                let Some(&source) = origins.get(mapped.clause_index) else {
                    return Ok(None);
                };
                mapped.clause_index = source;
            }
            unsplit.steps.push(mapped);
            if !owner.open() {
                return Err(InputRestatementInterrupted);
            }
        }
        match &self.nullary_expansion {
            Some(expansion) => expansion
                .translate_derivation_with_progress(
                    &unsplit,
                    expansion.expanded_clause_count(),
                    &mut || owner.open(),
                )
                .map_err(|_| InputRestatementInterrupted),
            None => match validate_ground_derivation_with_progress(
                &self.input_problem,
                &unsplit,
                &mut || owner.open(),
            ) {
                Ok(()) => Ok(Some(unsplit)),
                Err(GroundDerivationError::Interrupted) => Err(InputRestatementInterrupted),
                Err(_) => Ok(None),
            },
        }
    }

    pub(super) fn restate_witness(
        &self,
        mut witness: DerivationWitness,
        owner: &InputRestatementControl<'_>,
    ) -> Option<DerivationWitness> {
        // Scalarization changes state argument positions, not just indices.
        if !owner.open() || !self.array_scalarization_maps.is_empty() {
            return None;
        }
        let root = witness.root;
        for (position, entry) in witness.entries.iter_mut().enumerate() {
            if !owner.open() {
                return None;
            }
            if let Some(index) = entry.incoming_clause {
                match self.input_clause(index)? {
                    InputClause::Clause(input) => entry.incoming_clause = Some(input),
                    InputClause::ExpandedQuery { .. } if position != root => return None,
                    InputClause::ExpandedQuery { into_fail, .. } => {
                        entry.predicate = self.fail_predicate(into_fail)?;
                        entry.state = ChcExpr::Bool(true);
                        entry.incoming_clause = Some(into_fail);
                    }
                }
            }
        }
        if !owner.open() {
            return None;
        }
        if let Some(index) = witness.query_clause {
            match self.input_clause(index)? {
                InputClause::Clause(input) => witness.query_clause = Some(input),
                InputClause::ExpandedQuery {
                    into_fail,
                    fail_query,
                } => {
                    let root = witness.entries.get(witness.root)?;
                    if root.incoming_clause == Some(into_fail) {
                        witness.query_clause = Some(fail_query);
                    } else {
                        self.route_root_through_fail(&mut witness, into_fail, fail_query, owner)?;
                    }
                }
            }
        }
        Some(witness)
    }

    fn fail_predicate(&self, into_fail: usize) -> Option<crate::PredicateId> {
        match &self.input_problem.clauses().get(into_fail)?.head {
            ClauseHead::Predicate(fail, args) if args.is_empty() => Some(*fail),
            _ => None,
        }
    }

    fn route_root_through_fail(
        &self,
        witness: &mut DerivationWitness,
        into_fail: usize,
        fail_query: usize,
        owner: &InputRestatementControl<'_>,
    ) -> Option<()> {
        if !owner.open() {
            return None;
        }
        let clauses = self.input_problem.clauses();
        let into = clauses.get(into_fail)?;
        clauses.get(fail_query)?;
        let fail = self.fail_predicate(into_fail)?;
        let [(premise, _)] = into.body.predicates.as_slice() else {
            return None;
        };
        let root = witness.entries.get(witness.root)?;
        if root.predicate != *premise {
            return None;
        }
        let fail_fact = DerivationWitnessEntry {
            predicate: fail,
            level: root.level.checked_add(1)?,
            state: ChcExpr::Bool(true),
            incoming_clause: Some(into_fail),
            premises: vec![witness.root],
            instances: FxHashMap::default(),
        };
        witness.entries.push(fail_fact);
        witness.root = witness.entries.len() - 1;
        witness.query_clause = Some(fail_query);
        owner.open().then_some(())
    }
}
