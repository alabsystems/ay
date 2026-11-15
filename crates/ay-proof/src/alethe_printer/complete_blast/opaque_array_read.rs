// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! An array-variable read is one opaque BV word, proved with the existing
//! bitblast_var rule. This grants no read-over-write or equal-index axiom.

use super::*;

pub(super) enum ReadChildren {
    Ordinary,
    Index(TermId),
    Refused,
}

impl Blaster<'_, '_> {
    pub(super) fn opaque_array_variable_read(&mut self, term: TermId) -> ReadChildren {
        let TermData::App(Symbol::Named(head), args) = self.printer.terms.get(term) else {
            return ReadChildren::Ordinary;
        };
        let [array, index] = args.as_slice() else {
            return ReadChildren::Ordinary;
        };
        if head != "select" {
            return ReadChildren::Ordinary;
        }
        let (array, index) = (*array, *index);
        if self.printer.terms.entry_stamp(array).is_none()
            || self.printer.terms.entry_stamp(index).is_none()
        {
            return ReadChildren::Refused;
        }
        if !matches!(self.printer.terms.get(array), TermData::Var(..)) {
            return ReadChildren::Ordinary;
        }
        let Sort::Array(shape) = self.printer.terms.sort(array) else {
            return ReadChildren::Ordinary;
        };
        if !self.printer.anchor_binder_names.borrow().is_empty() {
            return ReadChildren::Refused;
        }
        if self.printer.terms.sort(index) != &shape.index_sort
            || self.printer.terms.sort(term) != &shape.element_sort
            || !matches!(&shape.index_sort, Sort::BitVec(width) if (1..=MAX_WIDTH).contains(&width.width))
            || !matches!(&shape.element_sort, Sort::BitVec(width) if (1..=MAX_WIDTH).contains(&width.width))
        {
            return ReadChildren::Refused;
        }
        if self.printer.complete_blast_progress().is_none()
            || self.printer.complete_blast_surface_agrees(array).is_none()
        {
            return ReadChildren::Refused;
        }
        if !self.opaque_array_variables.contains(&array) {
            // No array descendants are skipped: this is a checked Var leaf.
            // Reserve it before insertion, sharing the existing node limit
            // with every ordinary Bool/BV source node in this same blaster.
            let Some(next) = self.walked.checked_add(1).filter(|n| *n <= MAX_TERM_NODES) else {
                return ReadChildren::Refused;
            };
            self.walked = next;
            self.opaque_array_variables.insert(array);
        }
        // build_word_app cannot interpret the Array operand and therefore
        // takes its existing WordOp::Leaf/bitblast_var branch. The index is
        // still traversed in full, with its usual width/surface/work checks.
        ReadChildren::Index(index)
    }
}
