// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::identity::{self, Comparison};
use super::*;
use ay_chc::{ChcProblem, ClauseBody, HornClause, InvariantModel};

mod facts;
#[cfg(test)]
mod tests;

pub(super) fn reconstruct(
    archive: &R34Archive,
    witness: &capture::Witness,
    source: &capture::Source,
    binding: &mut R34WitnessBinding,
    progress: &mut dyn FnMut() -> bool,
) -> Result<()> {
    if !progress() {
        return Ok(());
    }
    // The complete source bytes are authenticated before parsing. Neither a
    // replacement SMT script nor a hash-to-hash alias supplies the formula.
    let mut problem = capture::parse_source(archive, source)?;
    let recipe = &source.aggregate_problem["passes"];
    if recipe["expand_nullary_fail_queries"] != true
        || recipe["transforms"]["enabled"] != false
        || recipe["transforms"]["selected"] != serde_json::json!([])
    {
        binding
            .blockers
            .push(R34WitnessBlocker::MissingAggregatePreparation);
        return Ok(());
    }
    problem.expand_nullary_fail_queries(false);
    let index = usize::try_from(binding.clause_index)
        .map_err(|_| BenchError::msg("R34 witness clause index overflow"))?;
    let (formula, predecessors) = match facts::reconstruct(&problem, index, progress)? {
        facts::Recipe::Ready {
            formula,
            predecessors,
        } => (formula, predecessors),
        facts::Recipe::Missing => {
            binding
                .blockers
                .push(R34WitnessBlocker::MissingPredecessorFactRecipe);
            return Ok(());
        }
        facts::Recipe::Stopped => return Ok(()),
    };
    let mut query = ChcProblem::new();
    for (name, constructors) in problem.datatype_defs() {
        if !progress() {
            return Ok(());
        }
        query.add_datatype_def(name.clone(), constructors.clone());
    }
    // This is the consumer's actual constraint_query_problem construction.
    // add_clause performs the same ordinary reflexive-equality simplification.
    query.add_clause(HornClause::query(ClauseBody::constraint(formula.clone())));
    let normalized = query.normalized_input();
    let path = format!(
        "{}/{}",
        source.base,
        capture::string(&witness.record["constraint_query"], "file")?
    );
    let captured = archive.text(&path)?;
    if !authenticate(&query, &normalized, captured, binding, progress)? {
        return Ok(());
    }
    let debug_identity = capture::digest(format!("{formula:?}").as_bytes());
    let original_debug = capture::string(&witness.record, "formula_debug_sha256")?;
    if debug_identity != original_debug {
        binding
            .blockers
            .push(R34WitnessBlocker::FormulaDebugIdentity {
                captured: original_debug.to_owned(),
                current: debug_identity,
            });
    }
    if !progress() {
        return Ok(());
    }
    binding.current_query_schema = normalized.lines().next().map(str::to_owned);
    binding.current_query_sha256 = Some(capture::digest(normalized.as_bytes()));
    binding.datatype_definitions = query.datatype_defs().len();
    binding.predecessor_fact_indices = predecessors;
    binding.historical_query_authenticated = true;
    binding.qualified_expression = Some(InvariantModel::expr_to_smtlib(&formula));
    // Actual scratch and its datatype registry retire inside with_resources;
    // the original owner performs the post-operation/retirement fences.
    drop(query);
    drop(formula);
    drop(problem);
    Ok(())
}

fn authenticate(
    query: &ChcProblem,
    normalized: &str,
    captured: &str,
    binding: &mut R34WitnessBinding,
    progress: &mut dyn FnMut() -> bool,
) -> Result<bool> {
    match identity::compare(
        query,
        normalized,
        &binding.original_query_sha256,
        Some(captured),
        progress,
    )? {
        Some(Comparison::Exact) => {}
        Some(Comparison::Historical { captured, current }) => {
            // The schema difference remains visible; it supplies neither an
            // invocation grant nor a source-level verdict.
            binding
                .blockers
                .push(R34WitnessBlocker::IdentityMigration { captured, current });
        }
        Some(Comparison::Refused(reason)) => return Err(BenchError::msg(reason)),
        None => return Ok(false),
    }
    Ok(true)
}
