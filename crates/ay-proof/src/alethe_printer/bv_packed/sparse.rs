// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Scalar store-chain reads with independently checked modular index guards.

use super::*;
use crate::alethe_printer::format_sort_alethe;

const MAX_STORES: usize = 32;

#[derive(Clone)]
pub(super) struct Write {
    outer: String,
    inner: String,
    index: Value,
    value: Value,
}

impl PackedProof<'_, '_> {
    pub(super) fn sparse_select(
        &mut self,
        args: &[TermId],
        width: usize,
        depth: usize,
    ) -> Option<Value> {
        let [array, index] = args else { return None };
        self.printer.terms.entry_stamp(*array)?;
        self.printer.terms.entry_stamp(*index)?;
        let Sort::Array(sort) = self.printer.terms.sort(*array) else {
            return None;
        };
        if sort.element_sort != Sort::bitvec(width as u32)
            || self.printer.terms.sort(*index) != &sort.index_sort
        {
            return None;
        }
        let index = self.vector(*index, depth + 1)?;
        let writes = self.sparse_writes(*array, depth)?;
        let source = format!(
            "(select {} {})",
            self.printer.format_term(*array),
            index.equality.left
        );
        let mut path = self.equality(&source, &source, "refl", &[])?;
        for write in writes {
            let read = format!("(select {} {})", write.outer, index.equality.left);
            if write.index.bits == index.bits {
                let reverse = self.equality(
                    &index.equality.right,
                    &index.equality.left,
                    "symm",
                    &[&index.equality.step],
                )?;
                let equal = self.chain(write.index.equality.clone(), reverse)?;
                let equal = self.equality(&equal.right, &equal.left, "symm", &[&equal.step])?;
                let at_store = format!("(select {} {})", write.outer, write.index.equality.left);
                let moved = self.equality(&read, &at_store, "cong", &[&equal.step])?;
                let value =
                    self.equality(&at_store, &write.value.equality.left, "arrays_idx", &[])?;
                path = self.chain(path, moved)?;
                path = self.chain(path, value)?;
                return Some(Value {
                    equality: self.chain(path, write.value.equality)?,
                    bits: write.value.bits,
                });
            }
            let equality = self.vector_equality(write.index.clone(), index.clone())?;
            if equality.right != "false" {
                return None;
            }
            let simplified = self.simplify_equal(&equality.left, "false")?;
            let implication = self.step(
                &format!("(not {}) {}", simplified.left, simplified.right),
                "equiv1",
                &[&simplified.step],
            )?;
            let guard = self.step(
                &simplified.right,
                "resolution",
                &[&equality.step, &implication],
            )?;
            let next = format!("(select {} {})", write.inner, index.equality.left);
            let row = self.equality(&read, &next, "arrays_row", &[&guard])?;
            path = self.chain(path, row)?;
        }
        // The pinned checker has no const-array read axiom. An unmatched read
        // stays unsupported even though the producer knows its default value.
        None
    }

    fn sparse_writes(&mut self, array: TermId, depth: usize) -> Option<Vec<Write>> {
        if let Some(writes) = self.arrays.get(&array) {
            return Some(writes.clone());
        }
        let array_sort = self.printer.terms.sort(array).clone();
        let Sort::Array(sort) = &array_sort else {
            return None;
        };
        let mut writes = Vec::new();
        let mut cursor = array;
        loop {
            self.enter(depth + 1)?;
            self.printer.terms.entry_stamp(cursor)?;
            if self.printer.terms.sort(cursor) != &array_sort {
                return None;
            }
            let TermData::App(Symbol::Named(op), args) = self.printer.terms.get(cursor).clone()
            else {
                return None;
            };
            match (op.as_str(), args.as_slice()) {
                ("const-array", [fill]) => {
                    self.printer.terms.entry_stamp(*fill)?;
                    if self.printer.terms.sort(*fill) != &sort.element_sort {
                        return None;
                    }
                    let fill = self.vector(*fill, depth + 1)?;
                    let expected = format!(
                        "((as const {}) {})",
                        format_sort_alethe(&array_sort),
                        fill.equality.left
                    );
                    if self.printer.format_term(cursor) != expected {
                        return None;
                    }
                    break;
                }
                ("store", [inner, index, value]) if writes.len() < MAX_STORES => {
                    for child in [inner, index, value] {
                        self.printer.terms.entry_stamp(*child)?;
                    }
                    if self.printer.terms.sort(*inner) != &array_sort {
                        return None;
                    }
                    if self.printer.terms.sort(*index) != &sort.index_sort
                        || self.printer.terms.sort(*value) != &sort.element_sort
                    {
                        return None;
                    }
                    let index = self.vector(*index, depth + 1)?;
                    let value = self.vector(*value, depth + 1)?;
                    let outer = self.printer.format_term(cursor);
                    let printed_inner = self.printer.format_term(*inner);
                    if outer
                        != format!(
                            "(store {printed_inner} {} {})",
                            index.equality.left, value.equality.left
                        )
                    {
                        return None;
                    }
                    writes.push(Write {
                        outer,
                        inner: printed_inner,
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
