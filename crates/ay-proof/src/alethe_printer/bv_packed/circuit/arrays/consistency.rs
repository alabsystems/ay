// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Finite read functionality, derived from source array/index terms. No
//! consistency clause enters the SAT circuit without an Alethe derivation.

use super::*;

impl Circuit<'_, '_, '_> {
    pub(super) fn remember_base_read(
        &mut self,
        array: TermId,
        key: TermId,
        index: Address,
        word: Word,
    ) -> Option<()> {
        if self.base_read_slots.contains_key(&(array, key)) {
            return Some(());
        }
        if !self.proof.printer.admit_emission_work(1) {
            return None;
        }
        self.base_reads.try_reserve(1).ok()?;
        self.base_read_slots.try_reserve(1).ok()?;
        self.base_read_slots
            .insert((array, key), self.base_reads.len());
        self.base_reads.push(BaseRead {
            array,
            key,
            index,
            word,
        });
        Some(())
    }

    pub(in crate::alethe_printer::bv_packed::circuit) fn assert_read_consistency(
        &mut self,
    ) -> Option<()> {
        for (position, left) in self.base_reads.iter().enumerate() {
            for right in &self.base_reads[..position] {
                if !self.proof.printer.admit_emission_work(1) {
                    return None;
                }
                if left.array == right.array {
                    self.offset_shares
                        .count(self.proof.printer.terms, left.key, right.key);
                }
            }
        }
        // Lowering an index can discover another source read. Retain the
        // ledger and visit any such read too, under the same printer budget.
        let mut position = 0;
        while position < self.base_reads.len() {
            let left = self.base_reads[position].clone();
            for previous in 0..position {
                if !self.proof.printer.admit_emission_work(1) {
                    return None;
                }
                let right = self.base_reads[previous].clone();
                if left.array != right.array || left.index.relation(&right.index) == Some(false) {
                    continue;
                }
                self.read_consistency(&left, &right)?;
            }
            position += 1;
        }
        Some(())
    }

    fn read_consistency(&mut self, left: &BaseRead, right: &BaseRead) -> Option<()> {
        let index_equality = format!("(= {} {})", left.index.text, right.index.text);
        let value_equality = format!(
            "(= {} {})",
            left.word.equality.left, right.word.equality.left
        );
        let (value_bit, value_bridge) = self.read_word_equality(&left.word, &right.word)?;
        if left.index.relation(&right.index) == Some(true) {
            let indices =
                self.proof
                    .equality(&left.index.text, &right.index.text, "poly_simp", &[])?;
            let values = self.proof.equality(
                &left.word.equality.left,
                &right.word.equality.left,
                "cong",
                &[&indices.step],
            )?;
            let unit = self.proof.transport_unit(&value_bridge, &values.step)?;
            return self.input(vec![value_bit], unit);
        }
        let (index_bit, index_bridge) = match self.offset_equality("=", left.key, right.key, 0) {
            Some(compared) => compared,
            None => {
                let a = self.word(left.key, 0)?;
                let b = self.word(right.key, 0)?;
                self.read_word_equality(&a, &b)?
            }
        };
        if index_bridge.left != index_equality || value_bridge.left != value_equality {
            return None;
        }
        let end = self.proof.fresh();
        let assume = self.proof.fresh();
        self.proof.append(&format!(
            "(anchor :step {end})\n(assume {assume} {index_equality})\n"
        ))?;
        self.proof.equality(
            &left.word.equality.left,
            &right.word.equality.left,
            "cong",
            &[&assume],
        )?;
        self.proof.named_step(
            &end,
            &format!("(not {index_equality}) {value_equality}"),
            "subproof",
            &[],
            &format!(" :discharge ({assume})"),
        )?;
        let index_reverse = self.proof.step(
            &format!("{} (not {})", index_bridge.left, index_bridge.right),
            "equiv2",
            &[&index_bridge.step],
        )?;
        let value_forward = self.proof.step(
            &format!("(not {}) {}", value_bridge.left, value_bridge.right),
            "equiv1",
            &[&value_bridge.step],
        )?;
        let clause = self.proof.step(
            &format!("(not {}) {}", index_bridge.right, value_bridge.right),
            "resolution",
            &[&end, &index_reverse, &value_forward],
        )?;
        self.input(vec![-index_bit, value_bit], clause)
    }

    fn read_word_equality(&mut self, left: &Word, right: &Word) -> Option<(i32, Equality)> {
        if left.bits.len() != right.bits.len() {
            return None;
        }
        let changed = self
            .proof
            .congruence("=", &[left.equality.clone(), right.equality.clone()])?;
        let bit = self.comparison("=", &left.bits, &right.bits)?;
        let blasted =
            self.proof
                .equality(&changed.right, &self.text(bit)?, "bitblast_equal", &[])?;
        Some((bit, self.proof.chain(changed, blasted)?))
    }
}
