// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::alethe_printer::parse_printed_bitvec_literal;
use num_traits::ToPrimitive;

impl ContextProof<'_, '_, '_> {
    pub(super) fn boolean(&mut self, term: TermId, depth: usize) -> Option<Equality> {
        if let Some(proof) = self.booleans.get(&term) {
            return Some(proof.clone());
        }
        self.proof.enter(depth)?;
        let result = if let Some(unit) = self.facts.get(&term).cloned() {
            self.positive_fact(term, &unit)?
        } else {
            match self.proof.printer.terms.get(term) {
                TermData::App(Symbol::Named(op), args) if matches!(op.as_str(), "and" | "or") => {
                    let children = args
                        .iter()
                        .map(|&arg| self.boolean(arg, depth + 1))
                        .collect::<Option<Vec<_>>>()?;
                    let changed = self.proof.congruence(op, &children)?;
                    let skip = if op == "and" { "true" } else { "false" };
                    let short = if op == "and" { "false" } else { "true" };
                    let mut unique = Vec::new();
                    for child in &children {
                        if child.right != skip && !unique.contains(&child.right.as_str()) {
                            unique.push(child.right.as_str());
                        }
                    }
                    let rule = format!("{op}_simplify");
                    let reduced = if unique.contains(&short) {
                        self.proof.equality(&changed.right, short, &rule, &[])?
                    } else {
                        match unique.as_slice() {
                            [] => self.proof.equality(&changed.right, skip, &rule, &[])?,
                            // One argument survives, and it may itself be an
                            // `and`/`or` application (see `simplify_to_survivor`).
                            [one] => {
                                let one = (*one).to_string();
                                self.proof
                                    .simplify_to_survivor(&changed.right, &one, op, &rule)?
                            }
                            _ => {
                                let target = application(op, unique);
                                self.proof.equality(&changed.right, &target, &rule, &[])?
                            }
                        }
                    };
                    self.proof.chain(changed, reduced)?
                }
                TermData::App(Symbol::Named(op), args)
                    if op == "bvult" && args.len() == 2 && args[0] == args[1] =>
                {
                    self.reflexive_ult(args[0])?
                }
                TermData::Not(inner) => {
                    let inner = self.boolean(*inner, depth + 1)?;
                    let changed = self.proof.congruence("not", std::slice::from_ref(&inner))?;
                    let target = match inner.right.as_str() {
                        "true" => "false",
                        "false" => "true",
                        _ => &changed.right,
                    };
                    let simple = self.proof.equality(
                        &changed.right,
                        target,
                        if target == changed.right {
                            "refl"
                        } else {
                            "not_simplify"
                        },
                        &[],
                    )?;
                    self.proof.chain(changed, simple)?
                }
                _ => self.unchanged(term)?,
            }
        };
        if self.proof.printer.format_term(term) != result.left {
            return None;
        }
        self.booleans.insert(term, result.clone());
        Some(result)
    }

    pub(super) fn word(&mut self, term: TermId, depth: usize) -> Option<Equality> {
        if let Some(proof) = self.words.get(&term) {
            return Some(proof.clone());
        }
        self.proof.enter(depth)?;
        let result = if let Some((condition, yes, no)) =
            context_conditional(self.proof.printer.terms, term)
        {
            let condition = self.boolean(condition, depth + 1)?;
            let yes = self.word(yes, depth + 1)?;
            let no = self.word(no, depth + 1)?;
            let changed = self
                .proof
                .congruence("ite", &[condition.clone(), yes.clone(), no.clone()])?;
            let reduced = self
                .proof
                .simplify_ite(&condition.right, &yes.right, &no.right)?;
            self.proof.chain(changed, reduced)?
        } else {
            match self.proof.printer.terms.get(term) {
                TermData::App(Symbol::Named(op), args) if op == "bvadd" => {
                    let [a, b] = args.as_slice() else {
                        return None;
                    };
                    let a = self.word(*a, depth + 1)?;
                    let b = self.word(*b, depth + 1)?;
                    let changed = self.proof.congruence("bvadd", &[a.clone(), b.clone()])?;
                    let literal = |text: &str| {
                        let (value, width) = parse_printed_bitvec_literal(text)?;
                        (width == self.width).then_some(value.to_u128()?)
                    };
                    let target = match (literal(&a.right), literal(&b.right)) {
                        (Some(0), _) => b.right,
                        (_, Some(0)) => a.right,
                        (Some(a), Some(b)) => format!(
                            "#b{:0width$b}",
                            a.wrapping_add(b) & (u128::MAX >> (128 - self.width)),
                            width = self.width as usize
                        ),
                        _ => changed.right.clone(),
                    };
                    let reduced = self
                        .proof
                        .equality(&changed.right, &target, "poly_simp", &[])?;
                    self.proof.chain(changed, reduced)?
                }
                _ => self.unchanged(term)?,
            }
        };
        if self.proof.printer.format_term(term) != result.left {
            return None;
        }
        self.words.insert(term, result.clone());
        Some(result)
    }
}
