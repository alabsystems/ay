// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::alethe_printer::parse_printed_bitvec_literal;
use num_traits::ToPrimitive;

impl PartitionProof<'_, '_, '_, '_> {
    fn constant(&self, value: u128) -> String {
        format!("#b{:0width$b}", value, width = self.identity.width as usize)
    }

    fn literal(&self, text: &str) -> Option<u128> {
        let (value, width) = parse_printed_bitvec_literal(text)?;
        (width == self.identity.width).then_some(value.to_u128()?)
    }

    pub(super) fn rewrite(
        &mut self,
        term: TermId,
        leaf: &IntervalLeaf,
        facts: &DetHashMap<String, Equality>,
        depth: usize,
    ) -> Option<Equality> {
        self.enter(depth)?;
        let source = self.proof.printer.format_term(term);
        if let Some(eq) = facts.get(&source) {
            return Some(eq.clone());
        }
        if term == leaf.upper {
            return self.proof.equality(
                &source,
                &self.constant(leaf.upper_value),
                "poly_simp",
                &[],
            );
        }
        if let Some((c, y, n)) = context_conditional(self.proof.printer.terms, term) {
            let c = self.rewrite(c, leaf, facts, depth + 1)?;
            let y = self.rewrite(y, leaf, facts, depth + 1)?;
            let n = self.rewrite(n, leaf, facts, depth + 1)?;
            let changed = self
                .proof
                .congruence("ite", &[c.clone(), y.clone(), n.clone()])?;
            let reduced = self.proof.simplify_ite(&c.right, &y.right, &n.right)?;
            return self.proof.chain(changed, reduced);
        }
        let TermData::App(Symbol::Named(op), args) = self.proof.printer.terms.get(term) else {
            return self.proof.equality(&source, &source, "refl", &[]);
        };
        if !matches!(op.as_str(), "bvadd" | "bvule" | "bvult" | "and") || args.len() != 2 {
            return None;
        }
        let a = self.rewrite(args[0], leaf, facts, depth + 1)?;
        let b = self.rewrite(args[1], leaf, facts, depth + 1)?;
        let changed = self.proof.congruence(op, &[a.clone(), b.clone()])?;
        let (target, rule) = match op.as_str() {
            "and" => {
                let value = match (a.right.as_str(), b.right.as_str()) {
                    ("false", _) | (_, "false") => "false",
                    ("true", "true") => "true",
                    _ => return None,
                };
                (value.into(), "and_simplify")
            }
            "bvadd" => {
                let value = self
                    .literal(&a.right)?
                    .wrapping_add(self.literal(&b.right)?)
                    & (u128::MAX >> (128 - self.identity.width));
                (self.constant(value), "poly_simp")
            }
            _ => {
                let a = self.literal(&a.right)?;
                let b = self.literal(&b.right)?;
                let value = if op == "bvule" { a <= b } else { a < b };
                ((if value { "true" } else { "false" }).into(), "evaluate")
            }
        };
        let reduced = self.proof.equality(&changed.right, &target, rule, &[])?;
        self.proof.chain(changed, reduced)
    }
}
