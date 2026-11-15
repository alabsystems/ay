// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked interval partition via complete unsigned bit sums and four cases.

use super::*;
use crate::checker::bv_affine::{
    context_conditional, partition_identity, IntervalLeaf, PartitionIdentity,
};

mod cases;
mod order;
mod rewrite;

struct PartitionProof<'proof, 'printer, 'terms, 'identity> {
    proof: &'proof mut PackedProof<'printer, 'terms>,
    identity: &'identity PartitionIdentity,
    units: DetHashMap<TermId, String>,
    visited: usize,
}

impl AlethePrinter<'_> {
    pub(super) fn format_bv_partition_identity(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let identity = partition_identity(self.terms, clause, &mut |work, _| {
            self.charge(work as u64);
            !self.work_budget_exhausted()
        })
        .ok()??;
        let budget = self.work_budget.map_or(MAX_TEXT as u64, |limit| {
            limit.saturating_sub(self.work_used()).min(MAX_TEXT as u64)
        });
        let raw = AlethePrinter::new_with_overrides_and_budget(self.terms, None, Some(budget));
        let root = raw.format_term(identity.root);
        let eq = raw.format_term(identity.equality);
        let goal = format!("(not {root})");
        self.charge(raw.work_used());
        if raw.work_budget_exhausted()
            || self.work_budget_exhausted()
            || self.format_term(clause[0]) != goal
        {
            return None;
        }
        let mut proof = PackedProof::new(self, id)?;
        let end = proof.fresh();
        let assumption = proof.fresh();
        proof.append(&format!(
            "(anchor :step {end})\n(assume {assumption} {root})\n"
        ))?;
        let mut partition = PartitionProof {
            proof: &mut proof,
            identity: &identity,
            units: DetHashMap::default(),
            visited: 0,
        };
        partition.collect(identity.root, &assumption, 0)?;
        let negative = partition.units.get(&identity.negated_equality)?.clone();
        let ordered = partition.ordered()?;
        let mut leaf_units = DetHashMap::default();
        for leaf in &identity.leaves {
            leaf_units.insert(leaf.equality, partition.leaf(leaf, &ordered)?);
        }
        let unit = partition.conjunction(identity.body, &leaf_units, 0)?;
        let body = self.format_term(identity.body);
        if self.format_term(identity.equality) != eq {
            return None;
        }
        let simple = proof.equality(&eq, &body, "equiv_simplify", &[])?;
        let reverse = proof.equality(&body, &eq, "symm", &[&simple.step])?;
        let unit = proof.transport_unit(&reverse, &unit)?;
        proof.step("", "resolution", &[&unit, &negative])?;
        proof.named_step(
            &end,
            &format!("{goal} false"),
            "subproof",
            &[],
            &format!(" :discharge ({assumption})"),
        )?;
        let not_false = proof.step("(not false)", "false", &[])?;
        proof.named_step(
            &id.to_string(),
            &goal,
            "resolution",
            &[&end, &not_false],
            "",
        )?;
        proof.definitions.push_str(&proof.out);
        Some(proof.definitions)
    }
}

impl PartitionProof<'_, '_, '_, '_> {
    // At most 32 validated leaves, four cases each, and 64 levels of source.
    // Keep this cumulative across all cases; never reset a branch's charges.
    fn enter(&mut self, depth: usize) -> Option<()> {
        self.visited = self.visited.checked_add(1)?;
        (self.visited <= 8192 && depth <= MAX_DEPTH && !self.proof.printer.work_budget_exhausted())
            .then_some(())
    }

    fn collect(&mut self, term: TermId, unit: &str, depth: usize) -> Option<()> {
        self.enter(depth)?;
        self.units.insert(term, unit.into());
        if let TermData::App(Symbol::Named(op), args) = self.proof.printer.terms.get(term) {
            if op == "and" {
                let root = self.proof.printer.format_term(term);
                for (i, &child) in args.iter().enumerate() {
                    let text = self.proof.printer.format_term(child);
                    let derived = self.proof.project_conjunct(&root, unit, &text, i)?;
                    self.collect(child, &derived, depth + 1)?;
                }
            }
        }
        Some(())
    }

    fn conjunction(
        &mut self,
        term: TermId,
        units: &DetHashMap<TermId, String>,
        depth: usize,
    ) -> Option<String> {
        self.enter(depth)?;
        if let Some(unit) = units.get(&term) {
            return Some(unit.clone());
        }
        let TermData::App(Symbol::Named(op), args) = self.proof.printer.terms.get(term) else {
            return None;
        };
        if op != "and" || args.len() != 2 {
            return None;
        }
        let left = self.conjunction(args[0], units, depth + 1)?;
        let right = self.conjunction(args[1], units, depth + 1)?;
        self.proof.step(
            &self.proof.printer.format_term(term),
            "and_intro",
            &[&left, &right],
        )
    }
}

#[cfg(test)]
mod tests;
