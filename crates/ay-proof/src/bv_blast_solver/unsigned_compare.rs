// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Unsigned comparison through existing independently checked Boolean gates.
//! At each bit, unequal operands decide the result; equal bits retain the
//! comparison of the less significant prefix. No adder sums are constructed.

use super::*;

impl ExprBlaster<'_> {
    pub(super) fn blast_unsigned_compare(
        &mut self,
        left: &BvExpr,
        right: &BvExpr,
        vars: &mut VarTable,
        lemmas: &mut Vec<BitLemma>,
        clauses: &mut Vec<Clause>,
    ) -> Result<Vec<u32>, BvExprExportError> {
        let a = self.blast(left, vars, lemmas, clauses)?;
        let b = self.blast(right, vars, lemmas, clauses)?;
        if a.len() != b.len() {
            return Err(BvExprExportError::WidthMismatch {
                lhs: a.len() as u32,
                rhs: b.len() as u32,
            });
        }
        if a.is_empty() {
            return Err(BvExprExportError::Malformed(
                "unsigned comparison of zero-width operands".into(),
            ));
        }
        let mut result = None;
        for (bit, (&x, &y)) in a.iter().zip(&b).enumerate() {
            self.check_deadline()?;
            let mut gate = |kind, inputs| {
                build_gate(
                    kind,
                    inputs,
                    VarRole::Aux { bit: bit as u32 },
                    vars,
                    lemmas,
                    clauses,
                    &mut self.cache,
                )
            };
            let not_x = gate(BitLemmaKind::Not, vec![x]);
            let less = gate(BitLemmaKind::And2, vec![not_x, y]);
            result = Some(if let Some(previous) = result {
                let equal = gate(BitLemmaKind::XnorEq, vec![x, y]);
                let same = gate(BitLemmaKind::And2, vec![equal, previous]);
                gate(BitLemmaKind::Or2, vec![same, less])
            } else {
                less
            });
        }
        Ok(vec![result.ok_or_else(|| {
            BvExprExportError::Malformed("missing unsigned comparison result".into())
        })?])
    }
}

#[cfg(test)]
mod tests;
