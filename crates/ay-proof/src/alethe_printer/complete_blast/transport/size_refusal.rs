// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A swept refutation refused only by its document's size ends the lemma's
//! plan.
//!
//! `Blaster::finish_planned` tries a large circuit's lanes in order (the
//! direct refutation, the case split, the sweep). After a sweep that does
//! not print, three more attempts follow: the case split over every leaf
//! (which 5b5c1f454 deferred behind the sweep, so that "every lane is still
//! tried, only their order changes"), the monolithic search, and, for a
//! lazily planned lemma, a second plan with every division exact
//! (`lazy.rs`). Each exists for a plan the lanes before it did not REFUTE:
//! the split and the monolithic search for a CNF the sweep could not close
//! (1cc8cfe30 measured the monolithic search carrying a render whose sweep
//! spent its wall), the exact plan for an abstraction whose opaque divisions
//! leave it satisfiable (`r2_sdiv32_or3` below). When the sweep has refuted
//! the plan and only the size of its document refused it, the lemma is true
//! over that plan, and the one question left is whether some other
//! refutation prints within the same lines. Those lines are counts: the
//! counted text bound [`MAX_COUNTED_TEXT_BYTES`], checked after every
//! transported step, and the consumer's budget ([`consumer_accepts`]: the
//! 76 MiB byte line, then the normalizer's own work count).
//!
//! Measured at 85f8d30d3 on model-checker-consumer's `sdiv64_or2` (two definitional 64-bit
//! `bvsdiv x -1` in one disjunction, the 2026-10-14 ask), default posture, no
//! timeout, release build on a loaded host: the solve takes 0.01 s, and the
//! wire-gap screen's one support question took 221 to 268 s of runs of 273
//! to over 290 s (316 s in the ask). Its lazy plan (275,856 gates, 960,664
//! clauses) swept to a refutation of 314,810 derived clauses, whose transport
//! passed the counted bound at 134,218,923 bytes. The split over every leaf
//! then declined, and the monolithic search spent its whole envelope
//! (`monolithic.rs`, 100,000 conflicts) on that CNF without refuting it: 95
//! to 128 s for the two. The exact plan (528,675 gates, 1,843,220 clauses)
//! swept to a refutation of 314,808 derived clauses, passed the bound at
//! 134,217,789 bytes, and its split and monolithic search spent 85 to 86 s
//! more. The export then repeated that ladder for 51 s, and the published
//! document printed the lemma as the same `hole`. The consumer's budget ends
//! the same ladder on variants of that shape, whose swept documents are under
//! the counted bound but outside that budget: two 56-bit copies (120,444,321
//! bytes) ran past 280 s, and six 32-bit copies (129,846,797 bytes) took
//! 153 s.
//!
//! So such a sweep ends the plan with a decline, which deliberately departs
//! from 5b5c1f454's "every lane is still tried": neither the split over
//! every leaf nor the monolithic search runs after it, and `lemma_document`
//! does not plan the lemma again with every division exact. The support
//! question, the in-solve renders and the export all reach that decline
//! alike: the sweep's refutation is retained (`resolution_dag_memo.rs`), so
//! a later render of the plan goes straight to it, transports it again under
//! its own step names and is refused by the same counts. The decision reads
//! only those counts, never a clock, and it is the same for a small circuit,
//! whose sweep is not expected to reach either line. A refusal for any other
//! reason (a failed replay, or more chain steps than `MAX_CHAIN_STEPS`)
//! keeps the whole ladder.
//!
//! The calibration is an observation, not a proof that the skipped lanes are
//! useless. Over the review's 154-case corpus (a lane census of chunks c00 to
//! c10 at 120 s per case, the cases undecided there at 270 s, and chunks c11
//! and c12, under `--debug-cert`), no render printed through any of the
//! three after a sweep that refuted its plan, the only refuting sweeps
//! refused by size were `r2_sdiv64_or2`'s and `r2_sdiv64_or3`'s (both past
//! the counted bound), and an exact plan printed only after an abstraction
//! the direct lane found satisfiable (`r2_sdiv32_or3`, 64 MB), which this
//! leaves untouched. No decided corpus document lies between the consumer's
//! 76 MiB line and the counted bound, so what the skipped lanes are worth
//! there is uncalibrated: a lemma one of them could have printed now keeps
//! its `hole`, a possible admission loss and never an unsound one. A decline
//! leaves the honest `hole`, and the screen's answer to a declined lemma is
//! a wire gap, its conservative answer: neither admits anything, and every
//! document that does print is replayed before it is. With it, the
//! `sdiv64_or2` run above takes 23 to 25 s and publishes the same 3,568-byte
//! document, the two variants take 18 s (the six copies publish the base's
//! 7,424-byte document), and every document the corpus decided at 120 s is
//! byte-identical. The cost left is one ladder up to the sweep's transport,
//! which grows with the width; bounding it relative to the solve needs an
//! exact early size predictor, which does not exist.

use super::super::{consumer_accepts, Blaster, MAX_COUNTED_TEXT_BYTES};
use super::{debug_note, Target};
use ay_sat::ResolutionDag;

#[cfg(test)]
#[path = "size_refusal_tests.rs"]
mod tests;

impl Blaster<'_, '_> {
    /// `dag`, the sweep's refutation of the planned CNF, printed within the
    /// counted text bound and the consumer's budget; when only its size
    /// refuses it, the plan is settled as declined (`swept_refused_by_size`).
    pub(super) fn print_swept(
        &mut self,
        dag: &ResolutionDag,
        target: &Target<'_>,
    ) -> Option<String> {
        self.refused_by_size.set(false);
        let document = self.transport_document(
            dag,
            target.cnf,
            target.root_clause_id,
            target.root,
            target.unit,
            target.final_clause,
            swept_text_bound(),
        );
        self.swept_refused_by_size = document.is_none() && self.refused_by_size.take();
        if self.swept_refused_by_size {
            debug_note(|| {
                "the swept refutation's document is refused by its size (the counted text \
                 bound or the consumer's budget): no split over every leaf, monolithic search \
                 or exact plan follows it"
                    .to_string()
            });
        }
        document
    }

    /// A transport's refusal by the size of its document: past the bound it
    /// was given, or outside the consumer's budget.
    pub(super) fn refuse_by_size<T>(&self) -> Option<T> {
        self.refused_by_size.set(true);
        None
    }
}

/// The bound a swept refutation is printed within: [`MAX_COUNTED_TEXT_BYTES`],
/// which a test lowers so that a lemma small enough to test runs past it.
fn swept_text_bound() -> usize {
    #[cfg(test)]
    if let Some(bound) = tests::SWEPT_TEXT_BOUND.with(std::cell::Cell::get) {
        return bound;
    }
    MAX_COUNTED_TEXT_BYTES
}

/// Whether the consumer takes `document` ([`consumer_accepts`]); a test
/// lowers the line so that a document small enough to test is refused.
pub(super) fn consumer_takes(document: &str) -> bool {
    #[cfg(test)]
    if let Some(line) = tests::CONSUMER_LINE.with(std::cell::Cell::get) {
        return document.len() <= line;
    }
    consumer_accepts(document)
}
