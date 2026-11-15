// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Precharge legacy scalar validation's datatype/signature reconstruction.
//! SAT-context and solver internals retain their separate memory envelope;
//! this ledger covers the new datatype-bearing model-validation call sites.

use super::super::candidate_model::CandidateAtom;
use super::*;
use crate::quantified::records::{registry_bytes, sort_bytes, MAX_FIELDS};
use crate::{ChcProblem, PredicateId};
use ay_core::kani_compat::DetHashMap;

pub(super) fn scalar_validation(problem: &ChcProblem, control: &SourceControl<'_>) -> Option<()> {
    // collect_datatype_sorts plus constructor/selector signatures can copy an
    // owner descriptor at every field. Expanded registry bytes overcount Arc
    // sharing; the field multiplier also covers those separate signature maps.
    let copies = MAX_FIELDS.checked_add(4)?;
    control.bytes(registry_bytes(problem)?.checked_mul(copies)?)?;
    for predicate in problem.predicates() {
        control.charge(predicate.arg_sorts.len())?;
        control.bytes(predicate.name.len())?;
        for sort in &predicate.arg_sorts {
            control.bytes(sort_bytes(sort)?.checked_mul(2)?)?;
        }
    }
    // replay_function_signatures also walks all original applications, even
    // though this candidate's own grammar is strictly scalar and function-free.
    for clause in problem.clauses() {
        source_premises::preflight_clause(clause, control)?;
    }
    control.poll()
}

pub(super) fn final_model(
    raw: &ChcProblem,
    layout: &Layout,
    pools: &DetHashMap<PredicateId, Vec<CandidateAtom>>,
    control: &SourceControl<'_>,
) -> Option<()> {
    for predicate in raw.predicates() {
        // complete_model performs one scalar validator call per predicate,
        // including predicates whose surviving conjunction is simply true.
        scalar_validation(raw, control)?;
        for var in layout.canonical(predicate.id)? {
            control.charge(1)?;
            control.bytes(var.name.len().checked_add(sort_bytes(&var.sort)?)?)?;
        }
        if let Some(candidates) = pools.get(&predicate.id) {
            control.charge(candidates.len())?;
            for candidate in candidates {
                source_premises::preflight(&candidate.formula, control, &mut 0)?;
            }
        }
    }
    control.poll()
}
