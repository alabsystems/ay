// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Prove the free-offset theorem, then discharge the actual outside assumption
//! after checked read-over-write steps. Recognition contributes no premise.

use super::*;
use crate::checker::bv_bitblast::proof_producing_control::OutsideFrameShape;

mod instantiate;
mod lemma;
mod source;

pub(super) struct Outside {
    pub(super) shape: OutsideFrameShape,
    universal: String,
    unit: String,
    guard_unit: String,
}

impl Circuit<'_, '_, '_> {
    pub(super) fn prove_local_property(
        &mut self,
        root: TermId,
        root_unit: &str,
        shape: OutsideFrameShape,
    ) -> Option<()> {
        let guard_unit = project_guard(self.proof, root, root_unit, shape.guard, &mut 0)?;
        let (mut info, deadline) = lemma::prove(self.proof, shape)?;
        info.guard_unit = guard_unit;
        self.deadline = Some(deadline);
        self.refutation_parts = 2;
        let equality = self.outside_property(&info)?;
        let value = self.atom(if info.shape.property_value {
            "true"
        } else {
            "false"
        })?;
        self.booleans.insert(info.shape.property, (value, equality));
        Some(())
    }
}

fn project_guard(
    proof: &mut PackedProof<'_, '_>,
    root: TermId,
    root_unit: &str,
    guard: TermId,
    visited: &mut usize,
) -> Option<String> {
    *visited = visited.checked_add(1)?;
    if *visited > 64 {
        return None;
    }
    if root == guard {
        return Some(root_unit.into());
    }
    let TermData::App(Symbol::Named(op), args) = proof.printer.terms.get(root) else {
        return None;
    };
    if op != "and" || args.is_empty() || args.len() > 128 {
        return None;
    }
    let text = proof.printer.format_term(root);
    for (i, &child) in args.iter().enumerate() {
        let child_text = proof.printer.format_term(child);
        let child_unit = proof.project_conjunct(&text, root_unit, &child_text, i)?;
        if let Some(unit) = project_guard(proof, child, &child_unit, guard, visited) {
            return Some(unit);
        }
    }
    None
}

#[cfg(test)]
mod tests;
