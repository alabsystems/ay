// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact ripple-carry terms consumed by the independent bitblast rules.

use super::*;

impl Circuit<'_, '_, '_> {
    fn ripple(&mut self, a: &[i32], b: &[i32], mut carry: i32) -> Option<Vec<i32>> {
        if a.is_empty() || a.len() != b.len() || a.len() > MAX_WIDTH {
            return None;
        }
        let mut bits = Vec::with_capacity(a.len());
        for (&x, &y) in a.iter().zip(b) {
            let parity = self.gate("xor", &[x, y])?;
            bits.push(self.gate("xor", &[parity, carry])?);
            let generated = self.gate("and", &[x, y])?;
            let propagated = self.gate("and", &[parity, carry])?;
            carry = self.gate("or", &[generated, propagated])?;
        }
        Some(bits)
    }

    pub(super) fn add(&mut self, a: Word, b: Word) -> Option<Word> {
        let carry = self.atom("false")?;
        let bits = self.ripple(&a.bits, &b.bits, carry)?;
        self.wired("bvadd", &[a.equality, b.equality], bits, "bitblast_add")
    }

    fn negate_word(&mut self, a: Word) -> Option<Word> {
        let zero = self.atom("false")?;
        let carry = self.atom("true")?;
        let inverse = a
            .bits
            .iter()
            .map(|&bit| self.gate("not", &[bit]))
            .collect::<Option<Vec<_>>>()?;
        let zeros = vec![zero; inverse.len()];
        let bits = self.ripple(&inverse, &zeros, carry)?;
        self.wired("bvneg", &[a.equality], bits, "bitblast_neg")
    }

    pub(super) fn arithmetic(&mut self, op: &str, args: &[TermId], depth: usize) -> Option<Word> {
        match (op, args) {
            ("bvneg", [a]) => {
                let a = self.word(*a, depth + 1)?;
                self.negate_word(a)
            }
            ("bvnot", [a]) => {
                let a = self.word(*a, depth + 1)?;
                let bits = a
                    .bits
                    .iter()
                    .map(|&bit| self.gate("not", &[bit]))
                    .collect::<Option<Vec<_>>>()?;
                self.wired("bvnot", &[a.equality], bits, "bitblast_not")
            }
            ("bvsub", [a, b]) => {
                let a = self.word(*a, depth + 1)?;
                let b = self.word(*b, depth + 1)?;
                self.subtract(a, b)
            }
            _ => None,
        }
    }

    /// `(bvsub a b)`, re-spelled `(bvadd a (bvneg b))` by `poly_simp`.
    pub(super) fn subtract(&mut self, a: Word, b: Word) -> Option<Word> {
        let left = &a.equality.left;
        let right = &b.equality.left;
        let expanded = self.proof.equality(
            &format!("(bvsub {left} {right})"),
            &format!("(bvadd {left} (bvneg {right}))"),
            "poly_simp",
            &[],
        )?;
        let b = self.negate_word(b)?;
        let mut sum = self.add(a, b)?;
        sum.equality = self.proof.chain(expanded, sum.equality)?;
        Some(sum)
    }
}
