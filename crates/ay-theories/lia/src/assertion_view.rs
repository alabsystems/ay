// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cached asserted-literal classification for LIA (#4742).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Symbol, TermData, TermId, TermStore};
use ay_core::TheoryLit;
use num_bigint::BigInt;
use num_traits::One;

/// Integer bounds and source literals for a single term.
#[derive(Clone, Debug, Default)]
pub(crate) struct TermBounds {
    /// Tightest asserted lower bound (integer-adjusted for strict atoms).
    pub(crate) lower: Option<BigInt>,
    /// Tightest asserted upper bound (integer-adjusted for strict atoms).
    pub(crate) upper: Option<BigInt>,
    /// Positive asserted inequality literals that produced bounds.
    pub(crate) reason_lits: Vec<TheoryLit>,
}

/// Pre-classified asserted literals shared by LIA submodules.
#[derive(Clone, Debug, Default)]
pub(crate) struct AssertionView {
    /// Positive equality literals (`(= lhs rhs)` asserted true).
    pub(crate) positive_equalities: Vec<TermId>,
    /// Negative equality literals (`(= lhs rhs)` asserted false / disequalities).
    pub(crate) negative_equalities: Vec<TermId>,
    /// Inequality literals (`>=`, `<=`, `>`, `<`) with asserted polarity.
    pub(crate) inequalities: Vec<(TermId, bool)>,
    /// Stable, deduplicated key for positive equalities.
    pub(crate) equality_key: Vec<TermId>,
    /// Integer bounds derived from positive asserted inequalities.
    pub(crate) bounds_by_term: HashMap<TermId, TermBounds>,
}

impl AssertionView {
    /// Build a new view from asserted literals.
    // From-scratch reference path: production folds literals incrementally via
    // `AssertionViewCache::on_assert`; tests build this to validate the cache.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn build(terms: &TermStore, asserted: &[(TermId, bool)]) -> Self {
        let mut view = Self::default();
        for &(literal, value) in asserted {
            view.classify_and_record(terms, literal, value, None);
        }
        view.equality_key = view.positive_equalities.clone();
        view.equality_key.sort_by_key(|term| term.0);
        view.equality_key.dedup();
        view
    }

    /// Classify one asserted literal and fold it into the view lists/bounds.
    ///
    /// Shared by the from-scratch `build` path and the incremental
    /// `AssertionViewCache::on_assert` path so both produce *identical*
    /// content for the same `asserted` prefix (the undo-trail validity of
    /// the incremental cache depends on this, see `AssertionViewCache`).
    ///
    /// When `bounds_undo` is `Some`, every `bounds_by_term` mutation records
    /// `(target, previous_entry)` before it is applied. NOTE: this method
    /// intentionally does NOT maintain `equality_key`; `build` recomputes it
    /// and `on_assert` maintains it incrementally via refcounts.
    fn classify_and_record(
        &mut self,
        terms: &TermStore,
        literal: TermId,
        value: bool,
        bounds_undo: Option<&mut Vec<(TermId, Option<TermBounds>)>>,
    ) {
        let TermData::App(Symbol::Named(name), args) = terms.get(literal) else {
            return;
        };
        if args.len() != 2 {
            return;
        }

        match name.as_str() {
            "=" => {
                if value {
                    self.positive_equalities.push(literal);
                } else {
                    self.negative_equalities.push(literal);
                }
            }
            ">=" | "<=" | ">" | "<" => {
                self.inequalities.push((literal, value));
                if value {
                    Self::record_integer_bound(
                        &mut self.bounds_by_term,
                        bounds_undo,
                        terms,
                        literal,
                        name.as_str(),
                        args[0],
                        args[1],
                    );
                }
            }
            _ => {}
        }
    }

    fn record_integer_bound(
        bounds_by_term: &mut HashMap<TermId, TermBounds>,
        mut bounds_undo: Option<&mut Vec<(TermId, Option<TermBounds>)>>,
        terms: &TermStore,
        literal: TermId,
        op: &str,
        lhs: TermId,
        rhs: TermId,
    ) {
        let lhs_const = terms.extract_integer_constant(lhs);
        let rhs_const = terms.extract_integer_constant(rhs);
        match (lhs_const, rhs_const) {
            (None, Some(c)) => Self::record_one_integer_bound(
                bounds_by_term,
                bounds_undo,
                literal,
                op,
                lhs,
                c,
                true,
            ),
            (Some(c), None) => Self::record_one_integer_bound(
                bounds_by_term,
                bounds_undo,
                literal,
                op,
                rhs,
                c,
                false,
            ),
            (Some(cl), Some(cr)) => {
                // Both sides constant (e.g. `(>= 5 3)`): the historical
                // `get_integer_bounds_for_term` trail scan derived a bound
                // for whichever side was queried, so record both directions
                // for exact #C6 parity. When both sides are the SAME term
                // the scan's `args[0] == tid` branch won, so only the
                // left-target direction is recorded.
                Self::record_one_integer_bound(
                    bounds_by_term,
                    bounds_undo.as_deref_mut(),
                    literal,
                    op,
                    lhs,
                    cr,
                    true,
                );
                if lhs != rhs {
                    Self::record_one_integer_bound(
                        bounds_by_term,
                        bounds_undo,
                        literal,
                        op,
                        rhs,
                        cl,
                        false,
                    );
                }
            }
            (None, None) => {}
        }
    }

    /// Fold one `target OP constant` (or `constant OP target`) bound into
    /// `bounds_by_term`, with integer adjustment for strict atoms.
    fn record_one_integer_bound(
        bounds_by_term: &mut HashMap<TermId, TermBounds>,
        bounds_undo: Option<&mut Vec<(TermId, Option<TermBounds>)>>,
        literal: TermId,
        op: &str,
        target: TermId,
        constant: BigInt,
        target_on_left: bool,
    ) {
        let mut lower: Option<BigInt> = None;
        let mut upper: Option<BigInt> = None;
        match (op, target_on_left) {
            (">=", true) | ("<=", false) => lower = Some(constant),
            (">", true) | ("<", false) => lower = Some(&constant + BigInt::one()),
            ("<=", true) | (">=", false) => upper = Some(constant),
            ("<", true) | (">", false) => upper = Some(&constant - BigInt::one()),
            _ => {}
        }

        // Snapshot the previous entry for the incremental undo trail (#C1)
        // BEFORE any mutation, so `AssertionViewCache::on_pop` can restore
        // the exact pre-assert state (including `reason_lits` union content).
        if let Some(undo) = bounds_undo {
            undo.push((target, bounds_by_term.get(&target).cloned()));
        }

        let bounds = bounds_by_term.entry(target).or_default();
        if let Some(candidate) = lower {
            bounds.lower = Some(
                bounds
                    .lower
                    .as_ref()
                    .map_or(candidate.clone(), |current| current.max(&candidate).clone()),
            );
        }
        if let Some(candidate) = upper {
            bounds.upper = Some(
                bounds
                    .upper
                    .as_ref()
                    .map_or(candidate.clone(), |current| current.min(&candidate).clone()),
            );
        }

        // Union semantics: keep EVERY contributing positive inequality literal
        // for the target (dedup only). Soundness: `complete_reason_pairs`
        // provenance (#8151) requires reason completeness even when a tighter
        // bound supersedes an older one.
        let reason = TheoryLit::new(literal, true);
        if !bounds.reason_lits.contains(&reason) {
            bounds.reason_lits.push(reason);
        }
    }
}

/// Per-scope marks for truncating the incremental view on `pop()` (#C1).
#[derive(Clone, Copy, Debug)]
struct ViewScopeMark {
    pos_eq: usize,
    neg_eq: usize,
    ineq: usize,
    bounds_undo: usize,
}

/// Always-valid incremental [`AssertionView`] (#C1, lia-hot-loop-plan §C1).
///
/// Invariant: `self.view` content is exactly `AssertionView::build(terms,
/// &solver.asserted)` at all times. Maintained by:
/// - `on_assert` after every `asserted.push(..)` (classifies the one new
///   literal in O(1) amortized instead of an O(asserted) rebuild per access),
/// - `on_push`/`on_pop` bracketing the solver's scope stack, with an undo
///   trail for `bounds_by_term` and refcounts for the sorted/deduped
///   `equality_key`,
/// - `rebuild` for the defensive shared-equality invalidation paths and
/// - `clear` for `reset`/`clear_assertions`.
///
/// SOUNDNESS (#8784 / plan §3.4): `on_pop` must run in the same transaction
/// as `asserted.truncate(mark)` so `conflict_reasons_all_live` never sees
/// view-derived reason literals that are no longer on the trail.
///
/// `rebuild` keeps the undo trail and scope marks: rebuilding from the same
/// `asserted` produces byte-identical content (classification is a pure
/// function of `(terms, asserted)` and `TermStore` is append-only), so undo
/// entries recorded before a rebuild still describe the correct restore
/// targets afterwards.
#[derive(Clone, Debug, Default)]
pub(crate) struct AssertionViewCache {
    view: AssertionView,
    /// Occurrence count per positive-equality literal; `equality_key`
    /// contains exactly the terms with count > 0 (sorted by raw id).
    eq_counts: HashMap<TermId, u32>,
    /// Undo trail for `bounds_by_term`: `(target, entry before mutation)`.
    bounds_undo: Vec<(TermId, Option<TermBounds>)>,
    /// Marks pushed by `on_push`, popped by `on_pop`.
    scope_marks: Vec<ViewScopeMark>,
    /// Monotone revision counter for the VIEW CONTENT: bumped by every
    /// mutation that can change what a reader observes (`on_assert`,
    /// `on_pop`, `rebuild`, `clear`; `on_push` records marks only and does
    /// not bump). Stamped by the `detect_algebraic_equalities` memo, which
    /// reads `positive_equalities` — an equal epoch guarantees the view is
    /// byte-identical to when the stamp was taken. Kept monotone across
    /// `clear` so a cleared-and-refilled cache can never alias an old stamp.
    epoch: u64,
}

impl AssertionViewCache {
    /// The always-valid view.
    pub(crate) fn view(&self) -> &AssertionView {
        &self.view
    }

    /// Revision counter for the view content (see field doc).
    pub(crate) fn epoch(&self) -> u64 {
        self.epoch
    }

    /// Reset everything (solver `reset` / `clear_assertions`).
    pub(crate) fn clear(&mut self) {
        // Preserve epoch monotonicity across the reset (see `epoch` doc).
        let epoch = self.epoch;
        *self = Self::default();
        self.epoch = epoch + 1;
    }

    /// Bump the view-content epoch WITHOUT rebuilding (#certora-diseq-epoch).
    ///
    /// For callers whose trigger cannot change the view content — the view is
    /// a pure function of `(terms, asserted)`, and e.g. a shared DISequality
    /// touches neither — a full `rebuild` reconstructs byte-identical content
    /// and its only observable effect is the epoch bump that invalidates the
    /// epoch-stamped memos. Bumping directly is behaviour-identical at O(1):
    /// a spurious memo miss is safe, a stale hit is not, and this preserves
    /// exactly the misses the rebuild produced. (`rebuild` of the same
    /// `asserted` was measured at ~35% of on-CPU time on the Certora
    /// QF_UFLIA VC family, 2026-07-14 sample profile: the Nelson-Oppen loop
    /// asserts shared disequalities every round against a ~1.2k-assertion
    /// trail full of 2^256 EVM constants.)
    pub(crate) fn bump_epoch(&mut self) {
        self.epoch += 1;
    }

    /// Rebuild the view content from scratch, preserving the undo trail and
    /// scope marks (see type-level docs for why that is sound).
    // From-scratch reference path: production folds literals incrementally via
    // `on_assert`; tests rebuild to validate the incremental content.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn rebuild(&mut self, terms: &TermStore, asserted: &[(TermId, bool)]) {
        // Rebuilding from the same `asserted` produces identical content, but
        // bump anyway: a spurious memo miss is safe, a stale hit is not.
        self.epoch += 1;
        self.view = AssertionView::build(terms, asserted);
        self.eq_counts.clear();
        for &literal in &self.view.positive_equalities {
            *self.eq_counts.entry(literal).or_insert(0) += 1;
        }
    }

    /// Incrementally fold one newly asserted literal into the view.
    /// `(term, value)` must be the already-NOT-unwrapped pair that was just
    /// pushed onto `solver.asserted`.
    pub(crate) fn on_assert(&mut self, terms: &TermStore, term: TermId, value: bool) {
        self.epoch += 1;
        let pos_eq_before = self.view.positive_equalities.len();
        self.view
            .classify_and_record(terms, term, value, Some(&mut self.bounds_undo));
        if self.view.positive_equalities.len() > pos_eq_before {
            let count = self.eq_counts.entry(term).or_insert(0);
            *count += 1;
            if *count == 1 {
                match self
                    .view
                    .equality_key
                    .binary_search_by_key(&term.0, |t| t.0)
                {
                    Err(pos) => self.view.equality_key.insert(pos, term),
                    Ok(_) => debug_assert!(
                        false,
                        "BUG: equality_key already contains term {} with refcount 0",
                        term.0
                    ),
                }
            }
        }
    }

    /// Record scope marks (call from `TheorySolver::push`).
    pub(crate) fn on_push(&mut self) {
        self.scope_marks.push(ViewScopeMark {
            pos_eq: self.view.positive_equalities.len(),
            neg_eq: self.view.negative_equalities.len(),
            ineq: self.view.inequalities.len(),
            bounds_undo: self.bounds_undo.len(),
        });
    }

    /// Truncate the view to the innermost scope mark (call from
    /// `TheorySolver::pop`, in the same transaction as
    /// `asserted.truncate(mark)`).
    pub(crate) fn on_pop(&mut self) {
        let Some(mark) = self.scope_marks.pop() else {
            debug_assert!(false, "BUG: AssertionViewCache::on_pop without on_push");
            return;
        };
        // Truncation below changes view content (even a no-op truncation is
        // only a spurious memo miss; see `epoch` doc).
        self.epoch += 1;
        while self.view.positive_equalities.len() > mark.pos_eq {
            let literal = self
                .view
                .positive_equalities
                .pop()
                .expect("len > mark >= 0");
            match self.eq_counts.get_mut(&literal) {
                Some(count) => {
                    *count -= 1;
                    if *count == 0 {
                        self.eq_counts.remove(&literal);
                        match self
                            .view
                            .equality_key
                            .binary_search_by_key(&literal.0, |t| t.0)
                        {
                            Ok(pos) => {
                                let _ = self.view.equality_key.remove(pos);
                            }
                            Err(_) => debug_assert!(
                                false,
                                "BUG: equality_key missing popped term {}",
                                literal.0
                            ),
                        }
                    }
                }
                None => debug_assert!(
                    false,
                    "BUG: eq_counts missing popped positive equality {}",
                    literal.0
                ),
            }
        }
        self.view.negative_equalities.truncate(mark.neg_eq);
        self.view.inequalities.truncate(mark.ineq);
        while self.bounds_undo.len() > mark.bounds_undo {
            let (target, previous) = self.bounds_undo.pop().expect("len > mark >= 0");
            match previous {
                Some(bounds) => {
                    self.view.bounds_by_term.insert(target, bounds);
                }
                None => {
                    self.view.bounds_by_term.remove(&target);
                }
            }
        }
    }
}

#[cfg(test)]
#[path = "assertion_view_tests.rs"]
mod tests;
