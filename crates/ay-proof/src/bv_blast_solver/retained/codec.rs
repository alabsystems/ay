// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Positional plain-data copying, not an alternative proof checker.
use super::*;
use accounting::{add, cap, product};

pub(super) fn encode(
    dag: &ResolutionDag,
    shape: Shape,
    control: &mut Control<'_>,
    poll: &mut dyn FnMut() -> bool,
) -> Result<RetainedBvRefutation, BvExprExportError> {
    control.retain(size_of::<RetainedBvRefutation>())?;
    let mut rows = control.reserve(shape.rows, poll)?;
    for row in &dag.derived {
        control.charge(1, poll)?;
        let mut literals = control.reserve(row.clause.len(), poll)?;
        let mut hints = control.reserve(row.rup_hints.len(), poll)?;
        for literal in &row.clause {
            control.charge(1, poll)?;
            literals.push(literal.raw());
        }
        for hint in &row.rup_hints {
            control.charge(1, poll)?;
            hints.push(*hint);
        }
        rows.push(RetainedRupRow {
            id: row.id,
            literals,
            hints,
        });
    }
    Ok(RetainedBvRefutation {
        version: VERSION,
        rows,
        empty_clause_id: dag.empty_clause_id,
    })
}

pub(super) fn decode(
    payload: &RetainedBvRefutation,
    shape: Shape,
    graph: &BvBlastProof,
    control: &mut Control<'_>,
    poll: &mut dyn FnMut() -> bool,
) -> Result<ResolutionDag, BvExprExportError> {
    control.retain(size_of::<ResolutionDag>())?;
    let original_clauses = originals(graph, control, poll)?;
    let mut previous =
        u64::try_from(original_clauses.len()).map_err(|_| malformed("original ID overflow"))?;
    let mut derived = control.reserve(shape.rows, poll)?;
    for row in &payload.rows {
        control.charge(1, poll)?;
        if row.id <= previous {
            return Err(malformed("retained row aliases an original or prior row"));
        }
        previous = row.id;
        let mut clause = control.reserve(row.literals.len(), poll)?;
        let mut rup_hints = control.reserve(row.hints.len(), poll)?;
        for &literal in &row.literals {
            control.charge(1, poll)?;
            if (literal >> 1) as usize >= graph.vars.len() {
                return Err(malformed(
                    "retained literal outside reconstructed namespace",
                ));
            }
            clause.push(Literal::from_index(literal as usize));
        }
        for &hint in &row.hints {
            control.charge(1, poll)?;
            if hint == 0 || hint >= row.id {
                return Err(malformed("retained hint is zero or forward"));
            }
            rup_hints.push(hint);
        }
        derived.push(RupStep {
            id: row.id,
            clause,
            rup_hints,
        });
    }
    Ok(ResolutionDag {
        num_vars: graph.vars.len(),
        original_clauses,
        derived,
        empty_clause_id: payload.empty_clause_id,
    })
}

fn original_shape(
    graph: &BvBlastProof,
    control: &mut Control<'_>,
    poll: &mut dyn FnMut() -> bool,
) -> Result<(), BvExprExportError> {
    control.charge(1, poll)?;
    let limits = &control.limits.resolution;
    cap(
        "retained original clauses",
        graph.clauses.len(),
        limits
            .max_input_clauses
            .min(limits.validation.max_original_clauses),
    )?;
    let mut literals = 0;
    for clause in &graph.clauses {
        control.charge(1, poll)?;
        cap(
            "retained original clause literals",
            clause.lits.len(),
            control.limits.resolution.max_input_clause_literals,
        )?;
        literals = add(literals, clause.lits.len())?;
    }
    let limits = &control.limits.resolution;
    cap(
        "retained original literals",
        literals,
        limits
            .max_input_literals
            .min(limits.validation.max_original_literals),
    )?;
    let bytes = add(
        product(graph.clauses.len(), size_of::<(u64, Vec<Literal>)>())?,
        product(literals, size_of::<Literal>())?,
    )?;
    cap("retained original bytes", bytes, limits.max_input_bytes)
}

fn originals(
    graph: &BvBlastProof,
    control: &mut Control<'_>,
    poll: &mut dyn FnMut() -> bool,
) -> Result<Vec<(u64, Vec<Literal>)>, BvExprExportError> {
    original_shape(graph, control, poll)?;
    let mut originals = control.reserve::<(u64, Vec<Literal>)>(graph.clauses.len(), poll)?;
    let mut bytes = product(originals.capacity(), size_of::<(u64, Vec<Literal>)>())?;
    for (position, clause) in graph.clauses.iter().enumerate() {
        control.charge(1, poll)?;
        let id = u64::try_from(position)
            .ok()
            .and_then(|position| position.checked_add(1))
            .ok_or_else(|| malformed("original ID overflow"))?;
        let mut literals = control.reserve(clause.lits.len(), poll)?;
        bytes = add(bytes, product(literals.capacity(), size_of::<Literal>())?)?;
        cap(
            "retained original bytes",
            bytes,
            control.limits.resolution.max_input_bytes,
        )?;
        for literal in &clause.lits {
            control.charge(1, poll)?;
            if literal.var as usize >= graph.vars.len() || literal.var > i32::MAX as u32 {
                return Err(malformed("reconstructed literal outside SAT namespace"));
            }
            literals.push(lit_to_sat(literal));
        }
        originals.push((id, literals));
    }
    Ok(originals)
}
