// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The encoder blasts each DISTINCT expression node once.
//!
//! The preflight interned every source occurrence of the borrowed trees
//! (`preflight_sharing`), so the encoder knows, per occurrence, which node it
//! is. The first occurrence of a node is blasted; every later one reuses its
//! output bits without descending. That is what makes the preflight's
//! distinct-node count, not its occurrence count, the measure of encoding
//! work (`BvExprProofLimits::max_expr_nodes`).

use super::*;

impl ExprBlaster<'_> {
    /// Bit-blast `expr` into its output bit vars (LSB-first). Gates flow through the
    /// shared cache, so structurally-identical sub-terms (even across the two sides
    /// of the equality) reuse one set of output vars.
    ///
    /// A preflighted occurrence whose interned node was already blasted returns
    /// that node's bits without descending. Re-blasting it would rebuild the
    /// same gates through `cache` and allocate nothing, so the encoding is
    /// unchanged; what changes is that the work is paid once per DISTINCT node,
    /// which is what `max_expr_nodes` counts.
    pub(super) fn blast(
        &mut self,
        expr: &BvExpr,
        vars: &mut VarTable,
        bit_lemmas: &mut Vec<BitLemma>,
        clauses: &mut Vec<Clause>,
    ) -> Result<Vec<u32>, BvExprExportError> {
        self.check_deadline()?;
        let node = self
            .shared
            .get(&(std::ptr::from_ref(expr) as usize))
            .copied();
        if let Some(bits) = node.and_then(|node| self.blasted.get(&node)) {
            return copy_blasted_bits(bits);
        }
        let bits = self.blast_node(expr, vars, bit_lemmas, clauses)?;
        if let Some(node) = node {
            let stored = copy_blasted_bits(&bits)?;
            self.blasted
                .try_reserve(1)
                .map_err(|_| blasted_bits_refused(bits.len()))?;
            self.blasted.insert(node, stored);
        }
        Ok(bits)
    }
}

/// Bytes the memo may hold: one entry per distinct node, and its output bits
/// (`output_bits`, the preflight's sum of distinct-node widths). A rewiring
/// node allocates no gate yet stores its bits, so the gate estimate does not
/// bound them.
pub(super) fn reserved_bytes(nodes: usize, output_bits: usize) -> Option<usize> {
    let entries = nodes.checked_mul(2 * size_of::<(u32, Vec<u32>)>())?;
    let bits = output_bits.checked_mul(size_of::<u32>())?;
    entries.checked_add(bits)
}

fn blasted_bits_refused(len: usize) -> BvExprExportError {
    BvExprExportError::ResourceLimit {
        resource: "expression memo allocation",
        limit: len,
        actual: len.saturating_add(1),
    }
}

fn copy_blasted_bits(bits: &[u32]) -> Result<Vec<u32>, BvExprExportError> {
    let mut copy = Vec::new();
    copy.try_reserve_exact(bits.len())
        .map_err(|_| blasted_bits_refused(bits.len()))?;
    copy.extend_from_slice(bits);
    Ok(copy)
}
