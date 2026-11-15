// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::literal_spelling::prints_alike;
use super::*;
use ay_core::Constant;

impl Circuit<'_, '_, '_> {
    pub(super) fn word(&mut self, term: TermId, depth: usize) -> Option<Word> {
        self.proof.printer.terms.entry_stamp(term)?;
        if let Some(word) = self.words.get(&term) {
            return Some(word.clone());
        }
        self.proof.enter(depth)?;
        let Sort::BitVec(sort) = self.proof.printer.terms.sort(term) else {
            return None;
        };
        let width = sort.width as usize;
        if width == 0 || width > MAX_WIDTH {
            return None;
        }
        let data = self.proof.printer.terms.get(term).clone();
        let word = match data {
            TermData::Var(_, _) | TermData::Const(Constant::BitVec { .. }) => {
                let value = self.proof.vector(term, depth)?;
                let bits = value
                    .bits
                    .iter()
                    .map(|text| self.atom(text))
                    .collect::<Option<Vec<_>>>()?;
                Word {
                    bits,
                    equality: value.equality,
                }
            }
            TermData::App(Symbol::Named(op), _) if op == "bvadd" => {
                self.addition(term, width, depth)?
            }
            other => self.operation(term, other, width, depth)?,
        };
        // Up to literal spelling: the exporter keeps an authored `(_ bvN W)`
        // where this lane builds binary (`literal_spelling`).
        if word.bits.len() != width
            || !prints_alike(&self.proof.printer.format_term(term), &word.equality.left)
        {
            return None;
        }
        self.words.insert(term, word.clone());
        Some(word)
    }

    pub(super) fn bit_text(&self, bits: &[i32]) -> Option<Vec<String>> {
        bits.iter().map(|&bit| self.text(bit)).collect()
    }

    pub(super) fn boolean(&mut self, term: TermId, depth: usize) -> Option<(i32, Equality)> {
        self.proof.printer.terms.entry_stamp(term)?;
        self.proof.enter(depth)?;
        if self.proof.printer.terms.sort(term) != &Sort::Bool {
            return None;
        }
        if let Some(value) = self.booleans.get(&term) {
            return Some(value.clone());
        }
        let data = self.proof.printer.terms.get(term).clone();
        let value = match data {
            TermData::Var(_, _) | TermData::Const(Constant::Bool(_)) => {
                let eq = self.proof.boolean(term, depth)?;
                (self.atom(&eq.right)?, eq)
            }
            TermData::Not(child) => {
                let (bit, eq) = self.boolean(child, depth + 1)?;
                self.negate(bit, eq)?
            }
            TermData::Ite(c, y, n) => self.boolean_conditional(&[c, y, n], depth)?,
            TermData::App(Symbol::Named(op), args) if op == "ite" => {
                self.boolean_conditional(&args, depth)?
            }
            TermData::App(Symbol::Named(op), args) => self.application(&op, &args, depth)?,
            _ => return None,
        };
        if !prints_alike(&self.proof.printer.format_term(term), &value.1.left) {
            return None;
        }
        self.booleans.insert(term, value.clone());
        Some(value)
    }

    fn application(&mut self, op: &str, args: &[TermId], depth: usize) -> Option<(i32, Equality)> {
        if op == "distinct" {
            let [a, b] = args else { return None };
            let (bit, equality) = self.application("=", args, depth + 1)?;
            let (bit, negated) = self.negate(bit, equality)?;
            let source = format!(
                "(distinct {} {})",
                self.proof.printer.format_term(*a),
                self.proof.printer.format_term(*b)
            );
            let bridge = self
                .proof
                .equality(&source, &negated.left, "distinct_elim", &[])?;
            return Some((bit, self.proof.chain(bridge, negated)?));
        }
        if op == "not" {
            let [child] = args else { return None };
            let (bit, eq) = self.boolean(*child, depth + 1)?;
            return self.negate(bit, eq);
        }
        if matches!(op, "and" | "or" | "xor") {
            if args.len() < 2 || args.len() > 128 || op == "xor" && args.len() != 2 {
                return None;
            }
            let values = args
                .iter()
                .map(|&arg| self.boolean(arg, depth + 1))
                .collect::<Option<Vec<_>>>()?;
            let bits = values.iter().map(|value| value.0).collect::<Vec<_>>();
            let equations = values.into_iter().map(|value| value.1).collect::<Vec<_>>();
            let bit = self.gate(op, &bits)?;
            let mut changed = self.proof.congruence(op, &equations)?;
            changed.right = self.text(bit)?;
            return Some((bit, changed));
        }
        let [a, b] = args else { return None };
        if op == "=" && self.proof.printer.terms.sort(*a) == &Sort::Bool {
            let (x, a) = self.boolean(*a, depth + 1)?;
            let (y, b) = self.boolean(*b, depth + 1)?;
            let bit = self.gate("=", &[x, y])?;
            let mut changed = self.proof.congruence("=", &[a, b])?;
            changed.right = self.text(bit)?;
            return Some((bit, changed));
        }
        if !matches!(
            op,
            "=" | "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
        ) {
            return None;
        }
        if let Some(bridged) = self.offset_equality(op, *a, *b, depth) {
            return Some(bridged);
        }
        let a = self.word(*a, depth + 1)?;
        let b = self.word(*b, depth + 1)?;
        if a.bits.len() != b.bits.len() {
            return None;
        }
        let swapped = matches!(op, "bvule" | "bvugt" | "bvsle" | "bvsgt");
        let (left, right) = if swapped {
            (b.clone(), a.clone())
        } else {
            (a.clone(), b.clone())
        };
        let primitive = if op == "=" {
            "="
        } else if matches!(op, "bvslt" | "bvsle" | "bvsgt" | "bvsge") {
            "bvslt"
        } else {
            "bvult"
        };
        let changed = self
            .proof
            .congruence(primitive, &[left.equality.clone(), right.equality.clone()])?;
        let bit = self.comparison(primitive, &left.bits, &right.bits)?;
        let blasted = self.proof.equality(
            &changed.right,
            &self.text(bit)?,
            if op == "=" {
                "bitblast_equal"
            } else if primitive == "bvslt" {
                "bitblast_slt"
            } else {
                "bitblast_ult"
            },
            &[],
        )?;
        let eq = self.proof.chain(changed, blasted)?;
        if matches!(op, "=" | "bvult" | "bvslt") {
            return Some((bit, eq));
        }
        let dual = self.order_duality(op, &a.equality.left, &b.equality.left, a.bits.len())?;
        let (bit, eq) = if matches!(op, "bvule" | "bvuge" | "bvsle" | "bvsge") {
            self.negate(bit, eq)?
        } else {
            (bit, eq)
        };
        Some((bit, self.proof.chain(dual, eq)?))
    }

    pub(super) fn comparison(&mut self, op: &str, a: &[i32], b: &[i32]) -> Option<i32> {
        if a.is_empty() || a.len() != b.len() {
            return None;
        }
        if op == "=" {
            let equal = a
                .iter()
                .zip(b)
                .map(|(&x, &y)| self.gate("=", &[x, y]))
                .collect::<Option<Vec<_>>>()?;
            // Carcara omits the conjunction wrapper at width one.
            return if equal.len() == 1 {
                Some(equal[0])
            } else {
                self.gate("and", &equal)
            };
        }
        let signed = op == "bvslt";
        if signed && a.len() == 1 {
            return self.gate("and", &[a[0], -b[0]]);
        }
        let mut result = self.gate("and", &[-a[0], b[0]])?;
        for (i, (&x, &y)) in a[1..].iter().zip(&b[1..]).enumerate() {
            let equal = self.gate("=", &[x, y])?;
            let same = self.gate("and", &[equal, result])?;
            let less = if signed && i + 2 == a.len() {
                self.gate("and", &[x, -y])?
            } else {
                self.gate("and", &[-x, y])?
            };
            result = self.gate("or", &[same, less])?;
        }
        Some(result)
    }

    fn negate(&mut self, bit: i32, equality: Equality) -> Option<(i32, Equality)> {
        let changed = self.proof.congruence("not", &[equality])?;
        let target = self.text(-bit)?;
        if changed.right == target {
            return Some((-bit, changed));
        }
        let reduced = self
            .proof
            .equality(&changed.right, &target, "not_simplify", &[])?;
        Some((-bit, self.proof.chain(changed, reduced)?))
    }
}
