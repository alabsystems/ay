// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded store chains over validated constant or arbitrary array bases.
//! Every discarded write is validated. Known affine index relations produce
//! checked polynomial proofs; unknown relations become conditional reads.

use super::address::Address;
use super::*;

mod consistency;
mod outside;
mod row;

#[derive(Clone)]
pub(super) struct BaseRead {
    array: TermId,
    key: TermId,
    index: Address,
    word: Word,
}

#[derive(Clone)]
pub(super) struct Write {
    outer: String,
    inner: String,
    inner_term: TermId,
    key: TermId,
    index: Address,
    value: Word,
}

impl Circuit<'_, '_, '_> {
    pub(super) fn select(
        &mut self,
        _term: TermId,
        args: &[TermId],
        width: usize,
        depth: usize,
    ) -> Option<Word> {
        let [array, key] = args else { return None };
        let index = self.address(*key, depth + 1)?;
        let writes = self.writes(*array, depth + 1)?;
        let matched = writes
            .iter()
            .position(|write| write.key == *key || write.index.relation(&index) == Some(true));
        let (mut value, pending) = if let Some(matched) = matched {
            (self.matched_read(&writes[matched], &index, width)?, matched)
        } else {
            let base = writes.last().map_or_else(
                || self.proof.printer.format_term(*array),
                |write| write.inner.clone(),
            );
            let read = format!("(select {base} {})", index.text);
            let bits = (0..width)
                .map(|i| format!("((_ @bit_of {i}) {read})"))
                .collect();
            let value = self.proof.blast(&read, bits, "bitblast_var")?;
            let value = self.from_value(value)?;
            let base_term = writes.last().map_or(*array, |write| write.inner_term);
            if matches!(self.proof.printer.terms.get(base_term), TermData::Var(..)) {
                self.remember_base_read(base_term, *key, index.clone(), value.clone())?;
            }
            (value, writes.len())
        };
        for write in writes[..pending].iter().rev() {
            let different = if write.index.relation(&index) == Some(false) {
                Some(self.different_addresses(&write.index, &index)?)
            } else if let Some(info) = self.disjoint.as_ref().filter(|info| {
                info.shape
                    .separates(self.proof.printer.terms, write.key, *key)
            }) {
                Some(info.different(self.proof, write.key, *key)?)
            } else {
                None
            };
            if let Some(unit) = different {
                let read = format!("(select {} {})", write.outer, index.text);
                let next = format!("(select {} {})", write.inner, index.text);
                let sort = format!("(_ BitVec {width})");
                self.proof.define_term(&read, &sort)?;
                self.proof.define_term(&next, &sort)?;
                let row = self.proof.equality(&read, &next, "arrays_row", &[&unit])?;
                value.equality = self.proof.chain(row, value.equality)?;
            } else {
                value = self.conditional_read(write, *key, value, depth + 1)?;
            }
        }
        Some(value)
    }

    fn matched_read(&mut self, write: &Write, index: &Address, width: usize) -> Option<Word> {
        if write.value.bits.len() != width {
            return None;
        }
        let read = format!("(select {} {})", write.outer, index.text);
        let at = format!("(select {} {})", write.outer, write.index.text);
        let sort = format!("(_ BitVec {width})");
        self.proof.define_term(&read, &sort)?;
        self.proof.define_term(&at, &sort)?;
        let rule = if index.text == write.index.text {
            "refl"
        } else {
            "poly_simp"
        };
        let key = self
            .proof
            .equality(&index.text, &write.index.text, rule, &[])?;
        let moved = self.proof.equality(&read, &at, "cong", &[&key.step])?;
        let found = self
            .proof
            .equality(&at, &write.value.equality.left, "arrays_idx", &[])?;
        let eq = self.proof.chain(moved, found)?;
        Some(Word {
            bits: write.value.bits.clone(),
            equality: self.proof.chain(eq, write.value.equality.clone())?,
        })
    }

    fn conditional_read(
        &mut self,
        write: &Write,
        key: TermId,
        value: Word,
        depth: usize,
    ) -> Option<Word> {
        let index = self.word(key, depth)?;
        let written = self.word(write.key, depth)?;
        let row = self.read_over_write(write, &index.equality.left)?;
        let changed = self
            .proof
            .congruence("=", &[written.equality, index.equality])?;
        let bit = self.comparison("=", &written.bits, &index.bits)?;
        let blasted =
            self.proof
                .equality(&changed.right, &self.text(bit)?, "bitblast_equal", &[])?;
        let guard = self.proof.chain(changed, blasted)?;
        let changed = self.proof.congruence(
            "ite",
            &[guard, write.value.equality.clone(), value.equality],
        )?;
        let yes = self.bit_text(&write.value.bits)?;
        let no = self.bit_text(&value.bits)?;
        let distributed = self.proof.distribute(&self.text(bit)?, &yes, &no)?;
        let bits = write
            .value
            .bits
            .iter()
            .zip(&value.bits)
            .map(|(&y, &n)| self.gate("ite", &[bit, y, n]))
            .collect::<Option<Vec<_>>>()?;
        let equation = self.proof.chain(row, changed)?;
        let mut equality = self.proof.chain(equation, distributed)?;
        equality.right = bbterm(&self.bit_text(&bits)?);
        Some(Word { bits, equality })
    }

    fn writes(&mut self, array: TermId, depth: usize) -> Option<Vec<Write>> {
        if let Some(writes) = self.arrays.get(&array) {
            return Some(writes.clone());
        }
        let sort = self.proof.printer.terms.sort(array).clone();
        let Sort::Array(shape) = &sort else {
            return None;
        };
        let mut cursor = array;
        let mut writes = Vec::new();
        loop {
            self.proof.enter(depth)?;
            self.proof.printer.terms.entry_stamp(cursor)?;
            if self.proof.printer.terms.sort(cursor) != &sort {
                return None;
            }
            if matches!(self.proof.printer.terms.get(cursor), TermData::Var(..)) {
                break;
            }
            let TermData::App(Symbol::Named(op), args) =
                self.proof.printer.terms.get(cursor).clone()
            else {
                return None;
            };
            match (op.as_str(), args.as_slice()) {
                ("const-array", [fill]) => {
                    let fill = self.word(*fill, depth + 1)?;
                    if shape.element_sort != Sort::bitvec(fill.bits.len() as u32) {
                        return None;
                    }
                    let expected = format!(
                        "((as const {}) {})",
                        crate::alethe_printer::format_sort_alethe(&sort),
                        fill.equality.left
                    );
                    if self.proof.printer.format_term(cursor) != expected {
                        return None;
                    }
                    break;
                }
                ("store", [inner, key, value]) if writes.len() < 64 => {
                    let index = self.address(*key, depth + 1)?;
                    let value = self.word(*value, depth + 1)?;
                    if shape.index_sort != Sort::bitvec(index.width as u32)
                        || shape.element_sort != Sort::bitvec(value.bits.len() as u32)
                    {
                        return None;
                    }
                    let outer = self.proof.printer.format_term(cursor);
                    let base = self.proof.printer.format_term(*inner);
                    if outer != format!("(store {base} {} {})", index.text, value.equality.left) {
                        return None;
                    }
                    writes.push(Write {
                        outer,
                        inner: base,
                        inner_term: *inner,
                        key: *key,
                        index,
                        value,
                    });
                    cursor = *inner;
                }
                _ => return None,
            }
        }
        self.arrays.insert(array, writes.clone());
        Some(writes)
    }
}
