// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::outside_frame::Outside;
use super::*;

mod common;
mod discharge;

fn binary(terms: &ay_core::TermStore, term: TermId, op: &str) -> Option<[TermId; 2]> {
    terms.entry_stamp(term)?;
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    let [a, b] = args.as_slice() else { return None };
    (name == op).then_some([*a, *b])
}

impl Circuit<'_, '_, '_> {
    pub(in crate::alethe_printer::bv_packed::circuit) fn outside_property(
        &mut self,
        info: &Outside,
    ) -> Option<Equality> {
        let terms = self.proof.printer.terms;
        let equal = info.shape.equality;
        if [info.shape.property, info.shape.outside, equal]
            .iter()
            .any(|&term| terms.sort(term) != &Sort::Bool)
        {
            return None;
        }
        self.validate_outside_siblings(info)?;
        let [left, right] = binary(terms, equal, "=")?;
        let [a, i] = binary(terms, left, "select")?;
        let [b, j] = binary(terms, right, "select")?;
        if i != info.shape.observe || j != i || terms.sort(left) != terms.sort(right) {
            return None;
        }
        let Sort::BitVec(width) = terms.sort(left) else {
            return None;
        };
        let width = width.width;
        let index = self.address(i, 0)?;
        if terms.sort(a) != terms.sort(b)
            || terms.sort(a) != &Sort::array(Sort::bitvec(index.width as u32), Sort::bitvec(width))
        {
            return None;
        }
        // Validate ALL writes before entering the conditional scope, including
        // values overwritten later. Their unconditional gate facts stay outer.
        let a_writes = self.writes(a, 0)?;
        let b_writes = self.writes(b, 0)?;
        let shared = a_writes
            .iter()
            .zip(&b_writes)
            .take_while(|(a, b)| a.key == b.key && a.value.equality.left == b.value.equality.left)
            .count();
        let a_tail = &a_writes[shared..];
        let b_tail = &b_writes[shared..];
        let base_text = |term, writes: &[Write]| {
            if shared == 0 {
                self.proof.printer.format_term(term)
            } else {
                writes[shared - 1].inner.clone()
            }
        };
        let (writes, base, swapped) = match (a_tail.is_empty(), b_tail.is_empty()) {
            (false, true) => (a_tail, base_text(b, &b_writes), false),
            (true, false) => (b_tail, base_text(a, &a_writes), true),
            _ => return None,
        };
        if writes.last()?.inner != base
            || writes.iter().any(|w| w.value.bits.len() != width as usize)
        {
            return None;
        }
        let read_base = format!("(select {base} {})", index.text);
        let outside = self.proof.printer.format_term(info.shape.outside);
        let end = self.proof.fresh();
        let assumption = self.proof.fresh();
        self.proof.append(&format!(
            "(anchor :step {end})\n(assume {assumption} {outside})\n"
        ))?;
        let mut equality = self.proof.equality(&read_base, &read_base, "refl", &[])?;
        for write in writes.iter().rev() {
            let different = info.different(self.proof, write.key, &assumption)?;
            let read = format!("(select {} {})", write.outer, index.text);
            let next = format!("(select {} {})", write.inner, index.text);
            let sort = format!("(_ BitVec {width})");
            self.proof.define_term(&read, &sort)?;
            self.proof.define_term(&next, &sort)?;
            let row = self
                .proof
                .equality(&read, &next, "arrays_row", &[&different])?;
            equality = self.proof.chain(row, equality)?;
        }
        if swapped {
            equality =
                self.proof
                    .equality(&equality.right, &equality.left, "symm", &[&equality.step])?;
        }
        for (a, b) in a_writes[..shared].iter().zip(&b_writes[..shared]).rev() {
            equality = self.common_write(a, b, &index.text, equality)?;
        }
        discharge::finish(self.proof, info, equality, &end, &assumption)
    }

    fn validate_outside_siblings(&mut self, info: &Outside) -> Option<()> {
        if info.shape.property_value {
            return Some(());
        }
        let terms = self.proof.printer.terms;
        let TermData::App(Symbol::Named(op), args) = terms.get(info.shape.property) else {
            return None;
        };
        if op != "and" || args.len() > 128 {
            return None;
        }
        // Only the two proved counterexample operands may be bypassed. Full
        // lowering still validates every other sibling before the AND is
        // cached as false, including malformed or mistyped discarded terms.
        for &child in args {
            if child != info.shape.outside
                && !matches!(terms.get(child), TermData::Not(inner) if *inner == info.shape.equality)
            {
                self.boolean(child, 0)?;
            }
        }
        Some(())
    }
}
