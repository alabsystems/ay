// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::Constant;
use num_traits::ToPrimitive;

impl Circuit<'_, '_, '_> {
    pub(super) fn value(&self, word: Word) -> Option<Value> {
        Some(Value {
            bits: self.bit_text(&word.bits)?,
            equality: word.equality,
        })
    }

    pub(super) fn from_value(&mut self, value: Value) -> Option<Word> {
        let bits = value
            .bits
            .iter()
            .map(|text| self.atom(text))
            .collect::<Option<Vec<_>>>()?;
        Some(Word {
            bits,
            equality: value.equality,
        })
    }

    pub(super) fn operation(
        &mut self,
        term: TermId,
        data: TermData,
        width: usize,
        depth: usize,
    ) -> Option<Word> {
        match data {
            TermData::App(Symbol::Named(op), args) if op == "select" => {
                self.select(term, &args, width, depth)
            }
            TermData::App(Symbol::Named(op), _) if op == "bvmul" => {
                let value = self.proof.vector(term, depth)?;
                self.from_value(value)
            }
            TermData::App(Symbol::Named(op), args) if op == "concat" => {
                let [a, b] = args.as_slice() else { return None };
                let a = self.word(*a, depth + 1)?;
                let b = self.word(*b, depth + 1)?;
                let bits = b.bits.iter().chain(&a.bits).copied().collect::<Vec<_>>();
                self.wired("concat", &[a.equality, b.equality], bits, "bitblast_concat")
            }
            TermData::App(Symbol::Indexed(op, indices), args) => {
                self.indexed(&op, &indices, &args, width, depth)
            }
            TermData::Ite(c, y, n) => self.word_conditional(&[c, y, n], width, depth),
            TermData::App(Symbol::Named(op), args) if op == "ite" => {
                self.word_conditional(&args, width, depth)
            }
            TermData::App(Symbol::Named(op), args)
                if matches!(op.as_str(), "bvsub" | "bvneg" | "bvnot") =>
            {
                self.arithmetic(&op, &args, depth)
            }
            TermData::App(Symbol::Named(op), args) if matches!(op.as_str(), "bvor" | "bvand") => {
                self.bitwise(&op, &args, width, depth)
            }
            TermData::App(Symbol::Named(op), args) if op == "bvxor" => {
                let [a, b] = args.as_slice() else { return None };
                let a = self.word(*a, depth + 1)?;
                let b = self.word(*b, depth + 1)?;
                if a.bits.len() != width || b.bits.len() != width {
                    return None;
                }
                let boolean = &op[2..];
                let bits = a
                    .bits
                    .iter()
                    .zip(&b.bits)
                    .map(|(&x, &y)| self.gate(boolean, &[x, y]))
                    .collect::<Option<Vec<_>>>()?;
                self.wired(
                    &op,
                    &[a.equality, b.equality],
                    bits,
                    &format!("bitblast_{boolean}"),
                )
            }
            TermData::App(Symbol::Named(op), args)
                if matches!(op.as_str(), "bvshl" | "bvlshr" | "bvashr") =>
            {
                let [_, amount] = args.as_slice() else {
                    return None;
                };
                if !matches!(self.proof.printer.terms.get(*amount), TermData::Const(_)) {
                    let value = self.proof.vector(term, depth)?;
                    return self.from_value(value);
                }
                self.shift(&op, &args, width, depth)
            }
            _ => None,
        }
    }

    fn bitwise(&mut self, op: &str, args: &[TermId], width: usize, depth: usize) -> Option<Word> {
        let [a, b] = args else { return None };
        let a = self.word(*a, depth + 1)?;
        let b = self.word(*b, depth + 1)?;
        if a.bits.len() != width || b.bits.len() != width {
            return None;
        }
        for (&x, &y) in a.bits.iter().zip(&b.bits) {
            // Unknown relations still need their original checked CNF gate.
            // Constants and repeated bits are reduced by the separate Alethe
            // derivation, never by substituting an unproved bitblast result.
            if x != y
                && !matches!(self.text(x)?.as_str(), "true" | "false")
                && !matches!(self.text(y)?.as_str(), "true" | "false")
            {
                self.gate(&op[2..], &[x, y])?;
            }
        }
        let a = self.value(a)?;
        let b = self.value(b)?;
        let value = self.proof.bitwise_values(op, a, b)?;
        self.from_value(value)
    }

    pub(super) fn wired(
        &mut self,
        op: &str,
        args: &[Equality],
        bits: Vec<i32>,
        rule: &str,
    ) -> Option<Word> {
        let changed = self.proof.congruence(op, args)?;
        let text = self.bit_text(&bits)?;
        let blasted = self
            .proof
            .equality(&changed.right, &bbterm(&text), rule, &[])?;
        Some(Word {
            bits,
            equality: self.proof.chain(changed, blasted)?,
        })
    }

    fn shift(&mut self, op: &str, args: &[TermId], width: usize, depth: usize) -> Option<Word> {
        let [a, b] = args else { return None };
        let a = self.word(*a, depth + 1)?;
        let literal = self.word(*b, depth + 1)?;
        if a.bits.len() != width || literal.bits.len() != width {
            return None;
        }
        let TermData::Const(Constant::BitVec { value, .. }) = self.proof.printer.terms.get(*b)
        else {
            return None;
        };
        let amount = value.to_usize()?;
        if amount > MAX_WIDTH || op == "bvashr" && amount >= width {
            return None;
        }
        let a = self.value(a)?;
        let literal = self.value(literal)?;
        let value = self.proof.bitblast_literal_shift(op, a, literal, amount)?;
        self.from_value(value)
    }
}
