// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Restrict the authenticated DAG to its active solver scope before RUP expansion.

use super::*;

/// The caller has authenticated each original binding after this same scope
/// projection. User assumptions are mapped SMT terms and cannot enter this
/// domain: every fixed premise must be an ordered, negative, unmapped selector.
/// Positive selector occurrences are false in the active scope. Satisfied
/// negative occurrences need a different proof representation and are refused.
pub(super) fn project(
    validated: &ValidatedPremisedClauseTraceResolution,
    needed: &[bool],
    var_to_term: &HashMap<u32, TermId>,
    meter: &mut CheckedRefutationMeter,
) -> Option<Vec<Vec<Literal>>> {
    let dag = validated.dag();
    validate_scope_assumptions(validated.unit_premises(), var_to_term, dag.num_vars, meter).ok()?;
    let mut guards = reserve(dag.num_vars, meter)?;
    guards.resize(dag.num_vars, false);
    for premise in validated.unit_premises() {
        meter.charge(1, 0).ok()?;
        *guards.get_mut(premise.variable().index())? = true;
    }
    let mut clauses = reserve(needed.len(), meter)?;
    clauses.push(Vec::new());
    let source = dag
        .original_clauses
        .iter()
        .map(|(_, clause)| clause)
        .chain(dag.derived.iter().map(|row| &row.clause));
    for (index, source_clause) in source.enumerate() {
        meter.charge(1, 0).ok()?;
        let mut clause = Vec::new();
        if *needed.get(index + 1)? {
            clause = reserve(source_clause.len(), meter)?;
            for &literal in source_clause {
                meter.charge(1, 0).ok()?;
                if *guards.get(literal.variable().index())? {
                    if !literal.is_positive() {
                        return None;
                    }
                } else {
                    clause.push(literal);
                }
            }
        }
        clauses.push(clause);
    }
    Some(clauses)
}
