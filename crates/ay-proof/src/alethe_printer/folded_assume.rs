// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The FOLDED-CONJUNCTION `assume` bridge.
//!
//! # The false claim this exists to remove
//!
//! Elaboration FOLDS. `(assert (and (not p) (= x1 x1)))` simplifies the
//! reflexive equality to `true` and drops it, so the assertion interns as the
//! bare `(not p)` and the proof's `assume` leaf carries THAT `TermId`.
//!
//! The root surface override (`collect_root_surface_term_override`) then
//! records the AUTHORED spelling against that folded id, because the `assume`
//! must reproduce the problem file byte-for-byte or an external checker refuses
//! the document at its first premise. But the override table is keyed by
//! `TermId` and is consulted at EVERY print site, so the whole authored
//! conjunction was also substituted for `(not p)` in every derived step. The
//! resolution that consumes the assume then had no eliminable pivot.
//!
//! Measured on main before this bridge (two-line QF_DT input, `(assert (and
//! (not p) (= x1 x1)))` + `(assert p)`): AY published
//!
//! ```text
//! (assume t0 (and (not p) (= x1 x1)))
//! (assume t1 p)
//! (step t2 (cl) :rule resolution :premises (t1 t0))
//! ```
//!
//! `unsat`, stamped `trust_free=yes ay_self_checkable=yes`, and carcara 1.1.0
//! answered **invalid** — "pivot was not eliminated: '(and (not p) (= x1
//! x1))'". The identical input with a conjunct that does NOT fold (`(and (not
//! p) q)`) emits the `and_pos` projection and is `valid`. The defect is
//! specific to fold-then-print-the-unfolded-surface.
//!
//! # The repair
//!
//! Print the projection the non-folding path already prints, and confine the
//! authored spelling to the one place it belongs:
//!
//! ```text
//! (assume t0.a (and (not p) (= x1 x1)))
//! (step t0.p (cl (not (and (not p) (= x1 x1))) (not p)) :rule and_pos :args (0))
//! (step t0 (cl (not p)) :rule resolution :premises (t0.a t0.p))
//! ```
//!
//! `t0` still names the clause every later premise expects, the `assume` still
//! matches the problem, and `(not p)` prints as itself everywhere else because
//! the folded rendering is installed in the document-wide bridge channel BEFORE
//! any step is emitted.
//!
//! When the folded term is not a printed conjunct of the authored spelling at
//! all — the surviving conjunct is itself re-spelled by canonicalization, e.g.
//! `(and (=> p q) (= x x))` folding to `(or (not p) q)` — no `and_pos` index
//! exists and the bridge falls back to ONE visible, countable `hole` for that
//! single equivalence. That is the repo's honest escape hatch: carcara reports
//! the document *holey* instead of *invalid*, `printed_unproved_steps` counts
//! the hole, and the certificate stamp reads `trust_free=no`. A claim AY cannot
//! discharge is never published as one it can.

use super::{AlethePrinter, PrintedNesting, PRINTED_NESTING_NODE_BUDGET};
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Proof, ProofId, ProofStep, Symbol, TermData, TermId};

/// Cap the planning scan. Override tables are already bounded by the collector
/// (`surface_override_map_is_bounded`); this is the printer's own belt.
const MAX_PLANNED_FOLDED_ASSUMES: usize = 8_192;

impl AlethePrinter<'_> {
    /// Decide, before any step is printed, which authored conjunctions folded.
    ///
    /// Runs from `prepare_proof` so the document-wide rendering switch is
    /// atomic: a step that mentions the folded term BEFORE its `assume` is
    /// reached must not see the authored conjunction either.
    ///
    /// Three outcomes per folded root:
    ///
    /// * the term is assumed and that `assume` is a PREMISE of some step — the
    ///   authored spelling moves to the assume-scoped channel and the bridge
    ///   below derives the folded clause the premise users expect;
    /// * the term is assumed but nothing consumes it — the authored spelling
    ///   still has to print (it is what the checker matches against the
    ///   problem) but no derivation is owed, so the `assume` is emitted
    ///   unchanged and NO bridge, and in particular no `hole`, is introduced
    ///   into a document that did not need one;
    /// * the term is NOT assumed — the authored spelling is simply dropped in
    ///   favour of the canonical rendering. Dropping an override can only make
    ///   a term print as what it denotes; it is the substitution that was the
    ///   claim, and with no `assume` to match there is nothing the authored
    ///   spelling could be preserving.
    ///
    /// Deliberately narrow. A surface `and` whose term IS still an `and`
    /// application (operand reordering, flattening, a re-spelled operand) is
    /// left exactly as it was: those are re-spellings of the same connective
    /// and every existing bridge continues to handle them.
    pub(super) fn plan_folded_and_assumes(&self, proof: &Proof) {
        let Some(overrides) = self.term_overrides else {
            return;
        };
        if overrides.is_empty() {
            return;
        }
        let mut consumed: HashSet<ProofId> = HashSet::default();
        for step in &proof.steps {
            match step {
                ProofStep::Step { premises, .. } => consumed.extend(premises.iter().copied()),
                ProofStep::Resolution {
                    clause1, clause2, ..
                } => {
                    consumed.insert(*clause1);
                    consumed.insert(*clause2);
                }
                ProofStep::Anchor { end_step, .. } => {
                    consumed.insert(*end_step);
                }
                // Leaves: neither carries premises, so neither consumes an
                // assume. `Assume` in particular is the thing being classified
                // — it is present in every proof, so it must be named here and
                // not left to the wildcard below.
                ProofStep::Assume(_) => {}
                ProofStep::TheoryLemma { .. } => {}
                // `ProofStep` is #[non_exhaustive], so this crate CANNOT match it
                // exhaustively — the compiler requires a wildcard. That makes the
                // wildcard's polarity load-bearing: treating an unknown variant as
                // consuming NOTHING would let a future premise-carrying variant
                // leave a consumed assume looking unconsumed, and the unconsumed
                // arm below then prints the AUTHORED conjunction as the assume
                // while the rest of the document uses the folded rendering. That
                // is precisely the "pivot was not eliminated" document carcara
                // rejects — re-opened, and stamped `trust_free=yes`.
                //
                // So fail CLOSED: an unrecognised variant abandons the whole plan
                // rather than emitting a document we cannot justify. Losing the
                // folded-assume bridge costs an honest `hole`; guessing costs a
                // lie.
                _ => return,
            }
        }
        let mut assumed: HashSet<TermId> = HashSet::default();
        let mut consumed_assumes: HashSet<TermId> = HashSet::default();
        for (index, step) in proof.steps.iter().enumerate() {
            let ProofStep::Assume(term) = step else {
                continue;
            };
            assumed.insert(*term);
            if consumed.contains(&ProofId(index as u32)) {
                consumed_assumes.insert(*term);
            }
        }

        // Collect first, mutate after: `format_term_data` reads the very
        // channels this pass writes, and a folded rendering must be computed
        // against the untouched state.
        let mut planned: Vec<(TermId, String, String, bool, bool)> = Vec::new();
        for (&term, surface) in overrides.iter() {
            if planned.len() >= MAX_PLANNED_FOLDED_ASSUMES {
                break;
            }
            if !surface.starts_with("(and") {
                continue;
            }
            // The authored conjunction SURVIVED elaboration: not a fold.
            if matches!(
                self.terms.get(term),
                TermData::App(Symbol::Named(head), _) if head == "and"
            ) {
                continue;
            }
            self.charge(surface.len() as u64);
            if self.work_budget_exhausted() {
                return;
            }
            let Some(nesting) = PrintedNesting::build(surface, "and", PRINTED_NESTING_NODE_BUDGET)
            else {
                continue;
            };
            if nesting.operands.first().map_or(0, Vec::len) < 2 {
                continue;
            }
            let folded = self.format_term_data(self.terms.get(term));
            if folded == *surface {
                continue;
            }
            let is_assumed = assumed.contains(&term);
            // A term nobody assumes keeps its authored spelling unless that
            // spelling is provably the fold's own operand — outside the
            // `assume` there is no premise-matching obligation to preserve,
            // and an unrecognized divergence is not this pass's business.
            if !is_assumed && nesting.find_operand(&folded).is_none() {
                continue;
            }
            planned.push((
                term,
                surface.clone(),
                folded,
                is_assumed,
                consumed_assumes.contains(&term),
            ));
        }

        let mut renderings = self.let_bridge_renderings.borrow_mut();
        let mut surfaces = self.folded_assume_surfaces.borrow_mut();
        let mut bridged = self.folded_assume_bridged.borrow_mut();
        for (term, surface, folded, is_assumed, is_consumed) in planned {
            if is_assumed {
                surfaces.insert(term, surface);
                if is_consumed {
                    bridged.insert(term);
                }
            }
            renderings.insert(term, folded);
        }
    }

    /// Emit the bridge for an `assume` whose authored conjunction folded.
    ///
    /// `None` when this term was not planned, which is every ordinary assume.
    pub(super) fn format_folded_and_assume_bridge(
        &self,
        id: ProofId,
        term: TermId,
    ) -> Option<String> {
        let surface = self.folded_assume_surfaces.borrow().get(&term).cloned()?;
        if !self.folded_assume_bridged.borrow().contains(&term) {
            // Nothing consumes this premise. Print exactly what the problem
            // asserts and owe nothing.
            return Some(format!("(assume {id} {surface})"));
        }
        let folded = self.let_bridge_renderings.borrow().get(&term).cloned()?;
        let premise_id = format!("{id}.a");
        let gate_id = format!("{id}.p");
        if let Some(projection) = self
            .flat_folded_and_projection(&gate_id, &surface, &folded)
            .or_else(|| self.navigate_and_pos_gate(&gate_id, &surface, &folded))
        {
            return Some(format!(
                "(assume {premise_id} {surface})\n\
                 {projection}\n\
                 (step {id} (cl {folded}) :rule resolution :premises ({premise_id} {gate_id}))"
            ));
        }
        // No `and_pos` index exists over the PRINTED conjunction. Say so: one
        // hole, countable by `printed_unproved_steps`, rather than a step that
        // claims a derivation the document does not contain.
        Some(format!(
            "(assume {premise_id} {surface})\n\
             (step {id} (cl {folded}) :rule hole :premises ({premise_id}))"
        ))
    }

    /// `and_pos` off a FLAT printed conjunction, first matching operand wins.
    ///
    /// The shared printed-nesting navigator refuses a duplicated spelling
    /// because in its caller the index it repairs is load-bearing. Here it is
    /// not: the clause emitted is `(cl (not SOURCE) FOLDED)` whatever index is
    /// chosen, and byte-identical operands make every choice the same step —
    /// `(and (not p) (not p))`, the authored duplicate that elaboration
    /// deduplicates, is otherwise pushed into the `hole` arm for no reason.
    /// This mirrors `format_flat_surface_and_pos`, which already takes the
    /// first identical surface operand.
    fn flat_folded_and_projection(
        &self,
        gate_id: &str,
        surface: &str,
        folded: &str,
    ) -> Option<String> {
        let operands =
            super::split_alethe_application_bounded(surface, "and", surface.len(), surface.len())
                .ok()?;
        let index = operands.iter().position(|operand| *operand == folded)?;
        Some(format!(
            "(step {gate_id} (cl (not {surface}) {folded}) :rule and_pos :args ({index}))"
        ))
    }
}
