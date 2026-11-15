// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Circuit<'_, '_, '_> {
    pub(super) fn boolean_conditional(
        &mut self,
        args: &[TermId],
        depth: usize,
    ) -> Option<(i32, Equality)> {
        let [c, y, n] = args else { return None };
        let (c, condition) = self.boolean(*c, depth + 1)?;
        let (y, yes) = self.boolean(*y, depth + 1)?;
        let (n, no) = self.boolean(*n, depth + 1)?;
        let mut equality = self.proof.congruence("ite", &[condition, yes, no])?;
        let bit = self.gate("ite", &[c, y, n])?;
        equality.right = self.text(bit)?;
        Some((bit, equality))
    }

    pub(super) fn word_conditional(
        &mut self,
        args: &[TermId],
        width: usize,
        depth: usize,
    ) -> Option<Word> {
        let [c, y, n] = args else { return None };
        let (bit, condition) = self.boolean(*c, depth + 1)?;
        let yes = self.word(*y, depth + 1)?;
        let no = self.word(*n, depth + 1)?;
        if yes.bits.len() != width || no.bits.len() != width {
            return None;
        }
        let changed = self
            .proof
            .congruence("ite", &[condition, yes.equality, no.equality])?;
        let condition_text = self.text(bit)?;
        let yes_text = self.bit_text(&yes.bits)?;
        let no_text = self.bit_text(&no.bits)?;
        let distributed = self
            .proof
            .distribute(&condition_text, &yes_text, &no_text)?;
        let bits = yes
            .bits
            .iter()
            .zip(&no.bits)
            .map(|(&y, &n)| self.gate("ite", &[bit, y, n]))
            .collect::<Option<Vec<_>>>()?;
        let mut equality = self.proof.chain(changed, distributed)?;
        equality.right = bbterm(&self.bit_text(&bits)?);
        Some(Word { bits, equality })
    }
}
