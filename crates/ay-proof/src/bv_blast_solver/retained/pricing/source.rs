// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual source topology, never wire-supplied CNF dimensions or a theorem.

use super::*;

pub(super) struct SourceBound {
    pub(super) gates: usize,
    pub(super) clauses: usize,
    pub(super) literals: usize,
    pub(super) width: usize,
    pub(super) construction_work: usize,
    pub(super) construction_bytes: usize,
}

pub(super) fn source_bound(
    lhs: &BvExpr,
    rhs: &BvExpr,
    proof: &BvExprProofLimits,
    poll: &mut dyn FnMut() -> bool,
) -> Result<SourceBound, PriceError> {
    let preflight = preflight_bv_equality(lhs, rhs, proof, poll)?;
    // topology_bound includes leaf variables and gate outputs, the final
    // equality outputs, and every distinct source node. Sharing can reduce
    // actual variables/gates, never increase them above this bound.
    let gates = preflight.estimated_gate_work;
    let clauses = add(mul(gates, 8)?, 1)?;
    let literals = add(mul(gates, 32)?, preflight.top_width)?;
    // Every repeated occurrence can copy a complete width's output vector
    // from the memo; distinct-node output_bits alone would underprice it.
    let occurrence_work = mul(
        preflight.occurrences,
        add(1, mul(proof.max_internal_width as usize, 2)?)?,
    )?;
    let name_work = mul(preflight.leaf_name_bytes, 16)?;
    let gate_work = mul(gates, 512)?;
    let construction_work = add(
        add(occurrence_work, name_work)?,
        add(preflight.output_bits, gate_work)?,
    )?;
    // Primary stores: G roles/gates, (8G+1) clauses, 32G+W literals,
    // <=6G gate-input u32s, cache/leaf tables and distinct-node output memo.
    // The separate occurrence/name terms cover zero-gate rewiring nodes.
    // Actual allocation/capacity and physical RSS are not inferred from this
    // formula; existing construction, codec and validator caps still enforce.
    let gate_bytes = mul(gates, 2048)?;
    let occurrence_bytes = mul(preflight.occurrences, 256)?;
    let output_bytes = mul(preflight.output_bits, 16)?;
    let name_bytes = mul(preflight.leaf_name_bytes, 4)?;
    let construction_bytes = add(
        64 * 1024,
        add(
            add(gate_bytes, occurrence_bytes)?,
            add(output_bytes, name_bytes)?,
        )?,
    )?;
    let result = SourceBound {
        gates,
        clauses: clauses
            .min(proof.resolution.max_input_clauses)
            .min(proof.resolution.validation.max_original_clauses),
        literals: literals
            .min(proof.resolution.max_input_literals)
            .min(proof.resolution.validation.max_original_literals),
        width: preflight.top_width,
        construction_work,
        construction_bytes,
    };
    drop(preflight);
    finish_expr_export(Some(proof), poll)?;
    Ok(result)
}
