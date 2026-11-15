// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Prove the exact printed BV variable-plus-zero fold before congruence.

use super::*;
use crate::alethe_printer::{parse_printed_bitvec_literal, split_application};

impl AlethePrinter<'_> {
    pub(in crate::alethe_printer) fn format_bv_add_zero_surface_equivalence(
        &self,
        id: &str,
        left: &str,
        right: &str,
        canonical: TermId,
    ) -> Option<Vec<String>> {
        if self.work_budget_exhausted() {
            return None;
        }
        self.terms.entry_stamp(canonical)?;
        let TermData::Var(name, _) = self.terms.get(canonical) else {
            return None;
        };
        let Sort::BitVec(sort) = self.terms.sort(canonical) else {
            return None;
        };
        let width = sort.width as usize;
        if !(1..=MAX_WIDTH).contains(&width) || left.len() > 8192 || right.len() > 8192 {
            return None;
        }
        let variable = ay_core::quote_symbol(name);
        let (sum, reversed) = if right == variable {
            (left, false)
        } else if left == variable {
            (right, true)
        } else {
            return None;
        };
        let args: [String; 2] = split_application(sum, "bvadd")?.try_into().ok()?;
        let zero_index = if args[0] == variable {
            1
        } else if args[1] == variable {
            0
        } else {
            return None;
        };
        let (value, literal_width) = parse_printed_bitvec_literal(&args[zero_index])?;
        if value != num_bigint::BigUint::from(0u8) || literal_width != sort.width {
            return None;
        }
        let mut proof =
            PackedProof::with_prefix(self, format!("{id}.bvzero"), &format!("__ay_bvzero_{id}_"))?;
        let bits = (0..width)
            .map(|i| format!("((_ @bit_of {i}) {variable})"))
            .collect();
        let variable = proof.blast(&variable, bits, "bitblast_var")?;
        let zero = proof.blast(
            &args[zero_index],
            vec!["false".into(); width],
            "bitblast_const",
        )?;
        let result = if zero_index == 0 {
            proof.addition_values(zero, variable.clone(), width)?
        } else {
            proof.addition_values(variable.clone(), zero, width)?
        };
        if result.bits != variable.bits || result.equality.left != sum {
            return None;
        }
        let backwards = proof.equality(
            &variable.equality.right,
            &variable.equality.left,
            "symm",
            &[&variable.equality.step],
        )?;
        let conclusion = format!("(= {left} {right})");
        if reversed {
            let forward = proof.chain(result.equality, backwards)?;
            proof.named_step(id, &conclusion, "symm", &[&forward.step], "")?;
        } else {
            proof.named_step(
                id,
                &conclusion,
                "trans",
                &[&result.equality.step, &backwards.step],
                "",
            )?;
        }
        proof.definitions.push_str(&proof.out);
        Some(proof.definitions.lines().map(str::to_owned).collect())
    }
}

#[cfg(test)]
mod tests;
