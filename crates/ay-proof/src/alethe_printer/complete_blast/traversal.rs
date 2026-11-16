// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bottom-up traversal of the source term DAG into words and gates.

use super::*;

impl Blaster<'_, '_> {
    /// Reduce the whole assertion, bottom-up, and return the Boolean
    /// reference that stands for it.
    pub(super) fn prepare(&mut self, root: TermId) -> Option<SRef> {
        self.emit_constant_steps()?;
        self.prepare_more(root)
    }

    /// [`Self::prepare`] for a further root of the SAME document, sharing
    /// every node already built (the constant steps are emitted once).
    pub(super) fn prepare_more(&mut self, root: TermId) -> Option<SRef> {
        self.printer.complete_blast_progress()?;
        // Count the root's equalities before any is built: only a reading
        // that cancels, or whose pair two of them read, is bridged to its
        // difference (`offset.rs`).
        let mut room = MAX_TERM_NODES.saturating_sub(self.offset_shares.walked());
        self.offset_shares
            .count_reachable(self.printer.terms, [root], false, &mut || {
                room = room.saturating_sub(1);
                room > 0 && self.printer.complete_blast_progress().is_some()
            });
        self.printer.complete_blast_progress()?;
        let mut stack = vec![(root, false)];
        let mut expanded = DetHashSet::default();
        while let Some((term, ready)) = stack.pop() {
            self.printer.complete_blast_progress()?;
            if self.built(term) {
                continue;
            }
            if ready {
                self.walked += 1;
                if self.walked > MAX_TERM_NODES || self.circuit.len() > MAX_GATES {
                    return None;
                }
                self.build(term)?;
                continue;
            }
            if !expanded.insert(term) {
                continue;
            }
            stack.push((term, true));
            for child in self.children(term)? {
                if !self.built(child) {
                    stack.push((child, false));
                }
            }
        }
        self.bool_of.get(&root).copied()
    }

    fn built(&self, term: TermId) -> bool {
        self.word_of.contains_key(&term) || self.bool_of.contains_key(&term)
    }

    fn children(&mut self, term: TermId) -> Option<Vec<TermId>> {
        match self.opaque_array_variable_read(term) {
            opaque_array_read::ReadChildren::Index(index) => return Some(vec![index]),
            opaque_array_read::ReadChildren::Refused => return None,
            opaque_array_read::ReadChildren::Ordinary => (),
        }
        // A bridged offset equality is built from its two words, never from
        // its authored operands (`offset.rs`).
        if let Some(bridge) = self.offset_bridge(term) {
            return Some(bridge.words());
        }
        Some(match self.printer.terms.get(term) {
            TermData::Const(_) | TermData::Var(..) => Vec::new(),
            TermData::Not(inner) => vec![*inner],
            TermData::Ite(c, t, e) => vec![*c, *t, *e],
            TermData::App(_, args) => args.clone(),
            // `let`, quantifiers and anything else added later are outside the
            // measured fragment; refuse rather than guess.
            _ => return None,
        })
    }

    fn build(&mut self, term: TermId) -> Option<()> {
        if self.printer.complete_blast_surface_agrees(term).is_none() {
            self.prepare_note("its printed surface disagrees", term);
            return None;
        }
        match self.printer.terms.sort(term).clone() {
            Sort::Bool => {
                let Some(reference) = self.build_bool(term) else {
                    self.prepare_note("no Boolean lowering", term);
                    return None;
                };
                self.bool_of.insert(term, reference);
            }
            Sort::BitVec(bv) => {
                if bv.width == 0 || bv.width > MAX_WIDTH {
                    self.prepare_note("width outside the lowering", term);
                    return None;
                }
                let Some(word) = self.build_word(term, bv.width) else {
                    self.prepare_note("no word lowering", term);
                    return None;
                };
                self.word_of.insert(term, word);
            }
            _ => {
                self.prepare_note("a sort outside the lowering", term);
                return None;
            }
        }
        Some(())
    }

    /// `--debug-cert` detail for a refused node. Keep only its identity:
    /// rendering through this printer would spend the document's work and
    /// populate its format cache solely because diagnostics were enabled.
    fn prepare_note(&self, why: &str, term: TermId) {
        if ay_core::misc_cli_flags().debug_cert {
            ay_core::safe_eprintln!("c !! complete-blast prepare declined: {why}: term_id={term}");
        }
    }
}

#[cfg(test)]
#[path = "traversal_tests.rs"]
mod tests;
