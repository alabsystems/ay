// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One solve's declines of the bit-vector support questions its wire-gap
//! screen asks the complete bit-blast.
//!
//! # The repetition this removes
//!
//! One publication screens the same document many times
//! (`proof_has_known_wire_gap` in `ay-dpll` lists the asks), and each screen
//! asks every bit-vector lemma's support question again. A refutation is
//! solved once per CNF (`resolution_dag_memo.rs`) and a `true` answer is
//! rendered once per lemma (the parent module), but a decline is kept by
//! neither, and the complete bit-blast's declines are its most expensive
//! answers: the sweep's refusal is its 120 s wall (`sat_sweep.rs`
//! `SWEEP_WALL`), which no memo may retain across solves, because a wall
//! clock may decline at one ask what a later ask refutes.
//!
//! Measured on `bv_affine_source`'s elaborated 64-bit affine identity under
//! `(set-option :check-proofs-strict true)` with no timeout, its one positive
//! unit `ArithClauseTautology` (5,079 gates, 16,511 clauses blasted) was asked
//! 14 times in one solve, each ask paying the sweep's 120 s wall again before
//! the monolithic refutation's retained refusal, and the solve answered
//! `unknown` after about 29 minutes. The asks came from eleven call sites:
//! `retry_native_strict_wire_gap`'s guard and its four re-asks, the repair's
//! presentation check, the exact authored repair's candidate screen (twice),
//! the post-fallback ask, a conjunct-refutation guard, the checked SAT
//! retention, the guarded collapse at the final boundary, and `unsat_cert`'s
//! two policy entries.
//!
//! # Why a remembered decline is this solve's answer
//!
//! * The record is the asking solve's own ([`BvSupportDeclines`]): the
//!   caller keeps one per solve and empties it when the next begins. A
//!   wall-clock decline therefore never reaches another solve's screen.
//! * The key is the parent module's: the lemma's kind and clause, the
//!   dialect, and the override spelling of every term below the clause, the
//!   whole of what the question reads of the lemma, from a store that is
//!   still the store it was asked from or only extends it.
//! * A decline is kept only when the solve's stop never fired while it was
//!   asked. A stopped question says nothing about the lemma; the stop is
//!   latched for the ask, so one that fired and relented is still a stop.
//! * Only a decline is kept, and a decline only declines: the lemma stays a
//!   wire gap, the screen stays conservative, and the exporter's own render
//!   (which never reads this record) still prints or refuses the document as
//!   before. Nothing it keeps can admit a step or publish a document.
//! * Within the solve, the first answer becomes every later ask's: the
//!   screens of one publication can no longer disagree about a lemma because
//!   a wall clock ran out at one ask and not at another.
//!
//! # The solve's renders read it too
//!
//! A render asked from inside the solve (`clean_render_len` and
//! `renders_wire_clean` in `ay-dpll`) lowers each bit-vector lemma through
//! the very dispatch a question asks, until the same stop
//! (`AlethePrinter::support_declined`). Where the record holds the lemma
//! under the spelling the render gives every term below its clause, the
//! render does not lower it again: it keeps the unproved step those
//! lowerings leave on a decline, which makes the render not clean, as the
//! declined question already made the screen report a gap. A render only
//! reads the record. It has a work budget the question does not, so its own
//! decline may be the budget's and is never kept.

use super::{remember_supported, supported_already, Key};
use crate::alethe_printer::{dialect, AlethePrinter, CompleteBlastAsk};
use crate::resolution_dag_memo::memo_disabled;
use crate::ArithPolySimpPromotionBudget;
use ay_core::kani_compat::DetHashMap;
use ay_core::term::TermStoreSnapshotStamp;
use ay_core::{ProofId, TermId, TermStore, TheoryLemmaKind};
use std::cell::{Cell, RefCell};

type HashMap<K, V> = DetHashMap<K, V>;

#[cfg(test)]
#[path = "within_solve_tests.rs"]
mod tests;

/// Declines one record keeps before it is emptied wholesale.
const MAX_DECLINES: usize = 4_096;
/// Key bytes one record keeps before it is emptied wholesale.
const MAX_DECLINE_BYTES: usize = 32 * 1024 * 1024;

/// The declines of one solve's support questions.
///
/// The solve that asks owns it, and empties it ([`Self::clear`]) before
/// another solve asks through it: what it keeps is only ever true of the
/// solve that kept it.
#[derive(Default)]
pub struct BvSupportDeclines {
    table: RefCell<Declines>,
}

#[derive(Default)]
struct Declines {
    /// Each lemma declined unstopped, and the store it was asked from.
    entries: DetHashMap<Key, TermStoreSnapshotStamp>,
    bytes: usize,
    /// Asks answered from `entries`, for tests and measurement.
    served: u64,
}

impl BvSupportDeclines {
    /// Forget every decline: a new solve begins.
    pub fn clear(&self) {
        *self.table.borrow_mut() = Declines::default();
    }

    /// Asks this record answered without asking again since it was last
    /// emptied.
    #[must_use]
    pub fn served(&self) -> u64 {
        self.table.borrow().served
    }

    /// Whether this solve already declined the lemma `key` names, counting
    /// the ask as served when it did.
    fn serves(&self, key: &Key, terms: &TermStore) -> bool {
        let mut table = self.table.borrow_mut();
        let declined = table
            .entries
            .get(key)
            .is_some_and(|stamp| stamp.is_append_only_prefix_of(terms));
        table.served += u64::from(declined);
        declined
    }

    fn remember(&self, key: Key, stamp: TermStoreSnapshotStamp, bytes: usize) {
        let mut table = self.table.borrow_mut();
        if table.entries.len() >= MAX_DECLINES || table.bytes + bytes > MAX_DECLINE_BYTES {
            let served = table.served;
            *table = Declines {
                served,
                ..Declines::default()
            };
        }
        if table.entries.insert(key, stamp).is_none() {
            table.bytes += bytes;
        }
    }
}

/// [`crate::checked_bv_bitblast_lowering_supported_asking`] for the screen of
/// a solve: the complete bit-blast is asked until `stop`, the solve's own
/// stop, and an unstopped decline is kept in `declines`, the solve's record,
/// which answers every later ask of the same lemma in the solve.
#[must_use]
pub fn checked_bv_bitblast_lowering_supported_within_solve(
    terms: &TermStore,
    kind: &TheoryLemmaKind,
    clause: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    stop: &dyn Fn() -> bool,
    declines: &BvSupportDeclines,
) -> bool {
    if !matches!(
        kind,
        TheoryLemmaKind::BvBitBlast | TheoryLemmaKind::BvBitBlastGate { .. }
    ) {
        return false;
    }
    let question = Question {
        terms,
        kind: *kind,
        clause,
        term_overrides,
        remembers_support: true,
    };
    question.answered(stop, declines, |ask| {
        super::super::bv_bitblast_support_rendered(terms, kind, clause, term_overrides, ask)
    })
}

/// [`crate::theory_lemma_bv_arithmetic_lowering_supported_asking`] for the
/// screen of a solve, as
/// [`checked_bv_bitblast_lowering_supported_within_solve`] is the bit-blast
/// question's.
///
/// The attempt is spent from `budget` before the record is read, so a kept
/// decline costs the proof's promotion cap exactly what asking again would,
/// and a decline the cap gave (no attempt left) is never kept: it is the
/// budget's answer, not the lemma's.
#[must_use]
pub fn theory_lemma_bv_arithmetic_lowering_supported_within_solve(
    terms: &TermStore,
    kind: &TheoryLemmaKind,
    clause: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    budget: &mut ArithPolySimpPromotionBudget,
    stop: &dyn Fn() -> bool,
    declines: &BvSupportDeclines,
) -> bool {
    if !matches!(kind, TheoryLemmaKind::ArithClauseTautology) || !budget.spend_attempt() {
        return false;
    }
    let question = Question {
        terms,
        kind: *kind,
        clause,
        term_overrides,
        remembers_support: false,
    };
    question.answered(stop, declines, |ask| {
        let printer =
            AlethePrinter::new_with_overrides(terms, term_overrides).asking_complete_blast(ask);
        // A question, not a render: nothing it spells reaches a document.
        dialect::discarding_notes(|| {
            printer
                .format_bv_structural_arithmetic_attempt(ProofId(0), clause)
                .is_some()
        })
    })
}

impl<'a> AlethePrinter<'a> {
    /// Read `declines`, the record of the solve this render is asked from
    /// inside, at each lemma its screen asked about
    /// ([`Self::support_declined`]).
    #[must_use]
    pub(crate) fn reading_support_declines(mut self, declines: &'a BvSupportDeclines) -> Self {
        self.support_declines = Some(declines);
        self
    }

    /// Whether the solve this render is asked from inside already declined,
    /// unstopped, the support question of the lemma `(kind, clause)` as this
    /// render spells it: the key is the question's, over the spelling this
    /// printer gives every term below the clause. A render outside a solve
    /// reads no record.
    pub(in crate::alethe_printer) fn support_declined(
        &self,
        kind: &TheoryLemmaKind,
        clause: &[TermId],
    ) -> bool {
        let Some(declines) = self.support_declines else {
            return false;
        };
        if memo_disabled()
            || !matches!(
                kind,
                TheoryLemmaKind::BvBitBlast
                    | TheoryLemmaKind::BvBitBlastGate { .. }
                    | TheoryLemmaKind::ArithClauseTautology
            )
        {
            return false;
        }
        let spelled = |term: TermId| self.channel_spelling(term);
        let spelling: &dyn Fn(TermId) -> Option<String> = &spelled;
        let walked = !self.skolem_overrides.borrow().is_empty()
            || !self.let_bridge_renderings.borrow().is_empty()
            || self
                .term_overrides
                .is_some_and(|overrides| !overrides.is_empty());
        Key::spelled(self.terms, *kind, clause, walked.then_some(spelling))
            .is_some_and(|(key, _)| declines.serves(&key, self.terms))
    }

    /// The spelling `write_term_into` gives `term` from a channel, if one has
    /// it: a Skolem's, a `let` bridge's, then the producer's override unless
    /// that override belongs to `assume` leaves alone.
    fn channel_spelling(&self, term: TermId) -> Option<String> {
        if let Some(text) = self.skolem_overrides.borrow().get(&term) {
            return Some(text.clone());
        }
        if let Some(text) = self.let_bridge_renderings.borrow().get(&term) {
            return Some(text.clone());
        }
        if self.assume_only_override_terms.borrow().contains(&term) {
            return None;
        }
        self.term_overrides
            .and_then(|overrides| overrides.get(&term))
            .cloned()
    }
}

/// One support question about one lemma.
struct Question<'q> {
    terms: &'q TermStore,
    kind: TheoryLemmaKind,
    clause: &'q [TermId],
    term_overrides: Option<&'q HashMap<TermId, String>>,
    /// Whether a `true` answer joins the thread's support memo (the parent
    /// module), as the bit-blast question's always has.
    remembers_support: bool,
}

impl Question<'_> {
    /// `render`'s answer, asked until `stop`; `false` without asking when
    /// `declines` holds this solve's unstopped decline of the lemma, and
    /// `true` without asking when the support memo holds the lemma.
    fn answered(
        &self,
        stop: &dyn Fn() -> bool,
        declines: &BvSupportDeclines,
        render: impl FnOnce(CompleteBlastAsk<'_>) -> bool,
    ) -> bool {
        // Latched: once a poll has seen the stop, every later poll of this
        // ask sees it too, and the decline it caused is never kept.
        let stopped = Cell::new(false);
        let latched = || {
            if stopped.replace(true) {
                return true;
            }
            let refused = stop();
            stopped.set(refused);
            refused
        };
        if latched() {
            return false;
        }
        let ask = CompleteBlastAsk::AskedUntil(&latched);
        if memo_disabled() {
            return render(ask) && !latched();
        }
        let Some((key, bytes)) = Key::of(self.terms, self.kind, self.clause, self.term_overrides)
        else {
            return render(ask) && !latched();
        };
        if latched() {
            return false;
        }
        if self.remembers_support && supported_already(&key, self.terms) {
            return !latched();
        }
        if declines.serves(&key, self.terms) {
            return false;
        }
        let stamp = self.terms.snapshot_stamp();
        let answer = render(ask);
        if latched() {
            return false;
        }
        if answer {
            if self.remembers_support {
                remember_supported(key, stamp, bytes);
            }
        } else {
            declines.remember(key, stamp, bytes);
        }
        answer
    }
}
