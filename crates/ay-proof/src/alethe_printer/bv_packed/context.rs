// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked conditional rewrites using only the original conjunction's facts.

use super::*;
use crate::checker::bv_affine::{context_conditional, context_identity};

mod lower;
mod reflexive;

struct ContextProof<'proof, 'printer, 'terms> {
    proof: &'proof mut PackedProof<'printer, 'terms>,
    width: u32,
    facts: DetHashMap<TermId, String>,
    words: DetHashMap<TermId, Equality>,
    booleans: DetHashMap<TermId, Equality>,
}

impl AlethePrinter<'_> {
    pub(super) fn format_bv_context_identity(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let identity = context_identity(self.terms, clause, &mut |work, _| {
            self.charge(work as u64);
            !self.work_budget_exhausted()
        })
        .ok()??;
        let budget = self.work_budget.map_or(MAX_TEXT as u64, |limit| {
            limit.saturating_sub(self.work_used()).min(MAX_TEXT as u64)
        });
        let raw = AlethePrinter::new_with_overrides_and_budget(self.terms, None, Some(budget));
        let root = raw.format_term(identity.root);
        let equality = raw.format_term(identity.equality);
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
        let mut context = ContextProof {
            proof: &mut proof,
            width: identity.width,
            facts: DetHashMap::default(),
            words: DetHashMap::default(),
            booleans: DetHashMap::default(),
        };
        context.collect(identity.root, &assumption, 0)?;
        let negative = context.facts.get(&identity.negated_equality)?.clone();
        let left = context.word(identity.left, 0)?;
        let right = context.word(identity.right, 0)?;
        if left.right != right.right || format!("(= {} {})", left.left, right.left) != equality {
            return None;
        }
        let reverse = proof.equality(&right.right, &right.left, "symm", &[&right.step])?;
        let equality = proof.chain(left, reverse)?;
        proof.step("", "resolution", &[&equality.step, &negative])?;
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

impl ContextProof<'_, '_, '_> {
    fn collect(&mut self, term: TermId, unit: &str, depth: usize) -> Option<()> {
        self.proof.enter(depth)?;
        self.facts.insert(term, unit.into());
        let TermData::App(Symbol::Named(op), args) = self.proof.printer.terms.get(term) else {
            return Some(());
        };
        if op == "and" {
            let root = self.proof.printer.format_term(term);
            for (i, &arg) in args.iter().enumerate() {
                let child = self.proof.printer.format_term(arg);
                let derived = self.proof.project_conjunct(&root, unit, &child, i)?;
                self.collect(arg, &derived, depth + 1)?;
            }
        }
        Some(())
    }

    fn positive_fact(&mut self, term: TermId, unit: &str) -> Option<Equality> {
        let source = self.proof.printer.format_term(term);
        let equation = format!("(= {source} true)");
        let simple = self
            .proof
            .equality(&equation, &source, "equiv_simplify", &[])?;
        let implication = self.proof.step(
            &format!("{equation} (not {source})"),
            "equiv2",
            &[&simple.step],
        )?;
        let step = self
            .proof
            .step(&equation, "resolution", &[unit, &implication])?;
        Some(Equality {
            left: source,
            right: "true".into(),
            step,
        })
    }

    fn unchanged(&mut self, term: TermId) -> Option<Equality> {
        let text = self.proof.printer.format_term(term);
        self.proof.equality(&text, &text, "refl", &[])
    }
}

#[cfg(test)]
mod tests;
