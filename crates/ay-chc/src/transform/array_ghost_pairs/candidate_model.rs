// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete raw-ghost model construction after Houdini reaches a fixpoint.

use ay_core::kani_compat::DetHashMap as FxHashMap;

use crate::pdr::{InvariantModel, PredicateInterpretation};
use crate::{ChcExpr, ChcProblem, ChcVar, PredicateId};

use super::candidate::scalar_candidate_node_count;

#[derive(Clone)]
pub(super) struct CandidateAtom {
    pub(super) formula: ChcExpr,
}

pub(super) fn complete_model(
    problem: &ChcProblem,
    canonical: &FxHashMap<PredicateId, Vec<ChcVar>>,
    pools: &FxHashMap<PredicateId, Vec<CandidateAtom>>,
    mut should_stop: impl FnMut() -> bool,
) -> Option<InvariantModel> {
    let mut model = InvariantModel::new();
    for predicate in problem.predicates() {
        if should_stop() {
            return None;
        }
        let vars = canonical.get(&predicate.id)?.clone();
        let formulas = pools
            .get(&predicate.id)
            .into_iter()
            .flat_map(|candidates| candidates.iter().map(|candidate| candidate.formula.clone()));
        let formula = ChcExpr::and_all_checked(formulas, &mut should_stop)?;
        scalar_candidate_node_count(problem, &vars, &formula)?;
        model.set(predicate.id, PredicateInterpretation::new(vars, formula));
    }
    Some(model)
}
