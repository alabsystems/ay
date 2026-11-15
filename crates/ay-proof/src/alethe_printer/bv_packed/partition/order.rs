// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn negate(text: &str) -> String {
    if let Some(inner) = text.strip_prefix("(not ").and_then(|s| s.strip_suffix(')')) {
        inner.into()
    } else {
        format!("(not {text})")
    }
}

impl PartitionProof<'_, '_, '_, '_> {
    fn sum(&mut self, word: &str) -> Option<String> {
        let terms = (0..self.identity.width)
            .map(|i| {
                let bit = format!("((_ @int_of {i}) {word})");
                if i == 0 {
                    bit
                } else {
                    format!("(* {} {bit})", 1u128 << i)
                }
            })
            .collect::<Vec<_>>();
        let sum = if terms.len() == 1 {
            terms[0].clone()
        } else {
            application("+", terms.iter().map(String::as_str))
        };
        self.proof.define_term(&sum, "Int")
    }

    pub(super) fn order(&mut self, op: &str, left: &str, right: &str) -> Option<Equality> {
        let a = self.sum(left)?;
        let b = self.sum(right)?;
        let (a, b) = if matches!(op, "bvule" | "bvult") {
            (b, a)
        } else {
            (a, b)
        };
        let bound = usize::from(matches!(op, "bvult" | "bvugt"));
        self.proof.equality(
            &format!("({op} {left} {right})"),
            &format!("(>= (- {a} {b}) {bound})"),
            &format!("pbblast_{op}"),
            &[],
        )
    }

    pub(super) fn ordered(&mut self) -> Option<(String, String)> {
        let TermData::App(Symbol::Named(op), args) =
            self.proof.printer.terms.get(self.identity.ordered)
        else {
            return None;
        };
        let unit = self.units.get(&self.identity.ordered)?.clone();
        let left = self.proof.printer.format_term(args[0]);
        let right = self.proof.printer.format_term(args[1]);
        let eq = self.order(op, &left, &right)?;
        let unit = self.proof.transport_unit(&eq, &unit)?;
        Some((eq.right, unit))
    }

    pub(super) fn literal_order(
        &mut self,
        left: &str,
        right: &str,
        value: bool,
        unit: &str,
    ) -> Option<(String, String)> {
        let mut eq = self.order("bvult", left, right)?;
        if !value {
            eq = self.proof.congruence("not", &[eq])?;
        }
        let unit = self.proof.transport_unit(&eq, unit)?;
        Some((eq.right, unit))
    }

    pub(super) fn complement(
        &mut self,
        left: &str,
        right: &str,
        source: &(String, String),
        value: bool,
    ) -> Option<String> {
        let mut eq = self.order("bvule", left, right)?;
        if !value {
            eq = self.proof.congruence("not", &[eq])?;
        }
        let lemma = self.proof.fresh();
        self.proof.named_step(
            &lemma,
            &format!("{} {}", negate(&source.0), eq.right),
            "la_generic",
            &[],
            " :args (1 1)",
        )?;
        let unit = self
            .proof
            .step(&eq.right, "resolution", &[&lemma, &source.1])?;
        let reverse = self
            .proof
            .equality(&eq.right, &eq.left, "symm", &[&eq.step])?;
        self.proof.transport_unit(&reverse, &unit)
    }

    pub(super) fn fact(&mut self, term: &str, value: bool, unit: &str) -> Option<Equality> {
        let literal = if value {
            term.into()
        } else {
            format!("(not {term})")
        };
        let value = if value { "true" } else { "false" };
        let formula = format!("(= {term} {value})");
        let simple = self
            .proof
            .equality(&formula, &literal, "equiv_simplify", &[])?;
        let implication = self.proof.step(
            &format!("{formula} (not {literal})"),
            "equiv2",
            &[&simple.step],
        )?;
        let step = self
            .proof
            .step(&formula, "resolution", &[&implication, unit])?;
        Some(Equality {
            left: term.into(),
            right: value.into(),
            step,
        })
    }
}
