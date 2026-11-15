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
            super::opaque_array_read::ReadChildren::Index(index) => return Some(vec![index]),
            super::opaque_array_read::ReadChildren::Refused => return None,
            super::opaque_array_read::ReadChildren::Ordinary => (),
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
mod tests {
    use super::*;
    use ay_core::{Proof, TermStore, TheoryLemmaKind};

    /// Refusal logging must not spend/cache through the live printer: the
    /// same finite allowance still has to emit and replay the next theorem.
    #[test]
    fn debug_rejection_preserves_same_printer_budget_cache_and_next_certificate() {
        fn run(debug_cert: bool, probe_cert_reject: bool) -> (String, u64, (u64, usize)) {
            let _flags = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
                debug_cert,
                probe_cert_reject,
                ..Default::default()
            });
            let mut terms = TermStore::new();
            // The old logger rendered and cached this long identifier after
            // the lowering had already refused its unsupported integer sort.
            let unsupported = terms.mk_var("unprintable_".repeat(512), Sort::Int);
            let x = terms.mk_var("x", Sort::bitvec(3));
            let y = terms.mk_var("y", Sort::bitvec(3));
            let left = terms.mk_app(Symbol::named("bvadd"), [x, y], Sort::bitvec(3));
            let right = terms.mk_app(Symbol::named("bvadd"), [y, x], Sort::bitvec(3));
            let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
            let assertion = terms.mk_not_raw(equality);
            let literal = terms.mk_not_raw(assertion);
            let polls = std::cell::Cell::new(0usize);
            let mut progress = || {
                polls.set(polls.get() + 1);
                true
            };
            let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(100_000))
                .with_emission_progress(&mut progress);
            let cache_before = printer.format_cache.borrow().clone();
            let mut blaster = Blaster::new(&printer, ProofId(9), "@diagnostic_reject".into());
            let before_rejection = (printer.work_used(), polls.get());
            assert!(blaster.build(unsupported).is_none());
            drop(blaster);
            let rejection_observations = (
                printer.work_used() - before_rejection.0,
                polls.get() - before_rejection.1,
            );
            assert_eq!(*printer.format_cache.borrow(), cache_before);
            assert_eq!(printer.work_budget, Some(100_000));
            let document = printer
                .format_bv_complete_blast_refutation(ProofId(10), &[literal])
                .expect("the next real theorem uses the same unreset ledger");
            assert!(!document.contains(":rule hole"));
            assert!(!document.contains(":rule trust"));
            assert!(document.contains(":rule resolution"));
            // Separately validate the native authored-scope refutation. A
            // syntactically complete document is not itself proof authority.
            let mut proof = Proof::new();
            let assume = proof.add_assume(assertion, None);
            let lemma =
                proof.add_theory_lemma_with_kind("bv", vec![literal], TheoryLemmaKind::BvBitBlast);
            proof.add_resolution(Vec::new(), assertion, assume, lemma);
            crate::check_proof_strict_with_context(&proof, &terms, None, None, Some(&[assertion]))
                .expect("the native refutation remains strictly checked");
            // Later proof emission can reuse the thread's exact-CNF refutation
            // memo. Compare its document and charged work; progress equality
            // belongs to the rejection phase observed above.
            (document, printer.work_used(), rejection_observations)
        }
        let ordinary = run(false, false);
        for (debug, probe) in [(true, false), (false, true), (true, true)] {
            assert_eq!(run(debug, probe), ordinary);
        }
    }
}
