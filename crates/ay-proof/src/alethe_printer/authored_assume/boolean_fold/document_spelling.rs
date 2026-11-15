// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whether confining a bridge root through the Boolean fold is coherent with
//! the spellings the rest of the document prints.
//!
//! A fold bridge concludes the OVERRIDE-FREE rendering of its root
//! (`render_term_canonical`), and the planner then prints exactly that text at
//! every occurrence but the `assume` (`commit_authored_assume_plan`). That is
//! coherent only when no OTHER producer override re-spells a term inside or
//! around the root, the invariant `strict_descendants_of_overridden_terms`
//! states for every confining channel:
//!
//! * a re-spelled strict DESCENDANT keeps its authored text in every step, so
//!   the confined root beside it ships one internal term two ways in steps
//!   that meet. MEASURED on `(assert (and p (not (not (< x 3)))))` +
//!   `(assert (>= x 5))`: the root collector records `(not (not (< x 3)))` on
//!   the descendant `(< x 3)`. At the base the root kept its authored spelling
//!   document-wide and the document was carcara `valid`; once the fold leaf
//!   planned the root (`not_simplify` under the conjunction's `cong`), the root
//!   printed `(and p (< x 3))` while its `and_pos` conjunct printed
//!   `(not (not (< x 3)))`, and the printer refused the publication ("and_pos
//!   indexed conjunct is absent from its effective source"). Every fold under
//!   a compound root with a re-spelled descendant (`(or r (not (not A)))`,
//!   `(= p (not (not A)))`, `(and p (= A true))`, ...) lost its answer or its
//!   checked document the same way;
//! * a re-spelled strict ANCESTOR keeps embedding the root's authored text.
//!   MEASURED on `(assert (= (< x 3) true))` +
//!   `(assert (=> (= (< x 3) true) (>= (+ y 1) 7)))` + `(assert (< y 6))` +
//!   `(assert (or (< x 3) (> y 100)))`: the implication's `assume` is bridged
//!   onto the document's rendering of its canonical term, which reads the
//!   first row's spelling `(= (< x 3) true)` on the folded root `(< x 3)`; with
//!   the fold leaf confining that root the planned rendering went stale and
//!   the printer refused the document the base published carcara `valid`
//!   ("planned authored assume equivalence no longer has a checked
//!   derivation").
//!
//! So the fold leaf, and the folded linear implication, decline under a
//! bridge ROOT (not only the operand being folded: a sibling operand's
//! re-spelling breaks the root's clauses just the same) with a strict
//! descendant or a strict ancestor whose override differs from its canonical
//! rendering. An override that IS the canonical rendering (the identity seal
//! of `seal_authored_identity_surfaces`) re-spells nothing. Declining leaves
//! the root exactly where it was before the fold leaf existed.
//!
//! The two directions differ on an override that is one term with the
//! canonical rendering to carcara's `alpha_equiv` (equality operand order,
//! bit-vector literal notation):
//!
//! * ABOVE the root it re-spells nothing the root's steps read: the ancestor
//!   meets the confined root only at literals, where the resolution
//!   orientation repair (`symm`) already bridges the two spellings.
//!   MEASURED on `(assert (or (= (f a) c) false))` +
//!   `(assert (not (= (f a) c)))`: AY stores `(= c (f a))`, so the second row
//!   spells the ancestor `(not (= c (f a)))` as `(not (= (f a) c))`; counted
//!   as a re-spelling, it withheld the fold and the document assumed the
//!   foreign `(= (f a) c)`, while confined beside it the document is carcara
//!   `valid`;
//! * BELOW the root it does re-spell: an `and_pos` conjunct must occur in the
//!   printed conjunction verbatim, and no repair re-orients it. MEASURED on
//!   `(assert (and p (not (not (= (f x) c)))))` + `(assert (not (= (f x)
//!   c)))`: exempting the descendant's `(= (f x) c)` let the fold confine the
//!   root to `(and p (= c (f x)))`, and the printer refused the document the
//!   base published carcara `valid` ("and_pos indexed conjunct is absent from
//!   its effective source").

use super::super::super::quantifier_surface::printed_terms_alpha_equivalent;
use super::*;

/// Node cap on the walk below one bridge root; over it, the root counts as
/// re-spelled and the fold declines.
const MAX_DOCUMENT_SPELLING_NODES: usize = 4_096;

/// Node cap on the walk below every re-spelled term, and work cap on judging
/// every override; over either, every root counts as re-spelled and the fold
/// declines.
const MAX_RESPELLED_DESCENDANT_NODES: usize = 1 << 16;
const MAX_RESPELLED_SCAN_WORK: u64 = 1 << 22;

/// The stack is bounded by edges, not just distinct nodes: one application
/// can repeat a shared child arbitrarily many times.
struct SpellingWalk<'p, 't> {
    printer: &'p AlethePrinter<'t>,
    stack: Vec<TermId>,
    edges: usize,
    max_edges: usize,
    work: u64,
}

impl<'p, 't> SpellingWalk<'p, 't> {
    fn new(printer: &'p AlethePrinter<'t>, max_edges: usize) -> Self {
        Self {
            printer,
            stack: Vec::new(),
            edges: 0,
            max_edges,
            work: 0,
        }
    }

    fn spend(&mut self, amount: u64) -> bool {
        let Some(next) = self.work.checked_add(amount) else {
            return false;
        };
        if next > MAX_RESPELLED_SCAN_WORK || !self.printer.admit_emission_work(amount) {
            return false;
        }
        self.work = next;
        true
    }

    fn push_slice(&mut self, children: &[TermId]) -> bool {
        let Some(edges) = self.edges.checked_add(children.len()) else {
            return false;
        };
        if edges > self.max_edges
            || self
                .stack
                .len()
                .checked_add(children.len())
                .is_none_or(|len| len > self.max_edges)
            || !self.spend(children.len() as u64)
            || self.stack.try_reserve(children.len()).is_err()
        {
            return false;
        }
        self.edges = edges;
        self.stack.extend(children.iter().copied());
        true
    }

    fn push_children(&mut self, term: TermId) -> bool {
        let terms = self.printer.terms;
        match terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => true,
            TermData::App(_, children) => self.push_slice(children),
            TermData::Not(child) => self.push_slice(std::slice::from_ref(child)),
            TermData::Ite(condition, yes, no) => self.push_slice(&[*condition, *yes, *no]),
            TermData::Let(bindings, body) => {
                if bindings
                    .len()
                    .checked_add(1)
                    .is_none_or(|len| len > self.max_edges.saturating_sub(self.edges))
                {
                    return false;
                }
                for (_, child) in bindings {
                    if !self.push_slice(std::slice::from_ref(child)) {
                        return false;
                    }
                }
                self.push_slice(std::slice::from_ref(body))
            }
            // Match TermStore::children: triggers are not document children.
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                self.push_slice(std::slice::from_ref(body))
            }
            _ => false,
        }
    }
}

/// The Boolean-fold leaf's view of the document.
#[derive(Default)]
pub(in crate::alethe_printer) struct BooleanFoldScope {
    /// The root of the depth-0 equivalence attempt in progress, with its
    /// memoized coherence.
    root: Option<(TermId, Option<bool>)>,
    /// Every strict descendant of a re-spelled term (`None`: over its cap),
    /// computed on first use.
    below_respelled: std::cell::OnceCell<Option<HashSet<TermId>>>,
}

impl AlethePrinter<'_> {
    /// Open the Boolean-fold scope of a depth-0 equivalence attempt on
    /// `root`. Every nested attempt runs inside the depth-0 call that opened
    /// its scope (child bridges are always `depth + 1`), so the leaf reads
    /// the root of the bridge it is part of.
    pub(in crate::alethe_printer::authored_assume) fn open_boolean_fold_scope(&self, root: TermId) {
        self.boolean_fold_scope.borrow_mut().root = Some((root, None));
    }

    /// Whether the current bridge root admits the fold leaf. Memoized per
    /// scope; `false` outside a scope.
    pub(super) fn boolean_fold_scope_is_coherent(&self) -> bool {
        let Some((root, known)) = self.boolean_fold_scope.borrow().root else {
            return false;
        };
        if let Some(coherent) = known {
            return coherent;
        }
        let coherent = self.fold_root_is_coherent(root);
        self.boolean_fold_scope.borrow_mut().root = Some((root, Some(coherent)));
        coherent
    }

    /// Whether confining `root` through a fold is coherent: no strict
    /// descendant and no strict ancestor carries a re-spelling override.
    pub(super) fn fold_root_is_coherent(&self, root: TermId) -> bool {
        let Some(overrides) = self.term_overrides else {
            return true;
        };
        if overrides.is_empty() {
            return true;
        }
        if self.descendant_is_respelled(overrides, root) {
            return false;
        }
        let scope = self.boolean_fold_scope.borrow();
        let below = scope
            .below_respelled
            .get_or_init(|| self.descendants_of_respelled_terms(overrides));
        below.as_ref().is_some_and(|below| !below.contains(&root))
    }

    /// Whether `term`'s override (if any) re-spells it, charging the work:
    /// its text is not the canonical rendering (nor, `modulo_alpha`, one term
    /// with it to carcara). A term whose canonical rendering is over its bound
    /// counts as re-spelled.
    fn override_respells(
        &self,
        overrides: &HashMap<TermId, String>,
        term: TermId,
        modulo_alpha: bool,
        walk: &mut SpellingWalk<'_, '_>,
    ) -> Option<bool> {
        let Some(text) = overrides.get(&term) else {
            return Some(false);
        };
        if text.len() > MAX_EQUIVALENCE_BYTES {
            return Some(true);
        }
        let Some(bound) =
            super::super::bounds::canonical_rendering_work_upper_bound(self.terms, term)
        else {
            return Some(true);
        };
        let charge = bound.checked_add(u64::try_from(text.len()).ok()?)?;
        // Pay for the canonical allocation and comparison before rendering.
        if !walk.spend(charge) {
            return None;
        }
        let canonical = crate::render_term_canonical(self.terms, term);
        if *text == canonical {
            return Some(false);
        }
        if modulo_alpha {
            // This existing matcher has a one-million-node bound, including
            // equality reordering. Admit that bound before its speculative walk.
            if !walk.spend(super::super::super::quantifier_surface::MAX_SURFACE_NODES as u64) {
                return None;
            }
            return Some(!printed_terms_alpha_equivalent(text, &canonical));
        }
        Some(true)
    }

    /// Whether some strict descendant of `root` is re-spelled (or the walk is
    /// over its cap).
    fn descendant_is_respelled(&self, overrides: &HashMap<TermId, String>, root: TermId) -> bool {
        let mut walk = SpellingWalk::new(self, MAX_DOCUMENT_SPELLING_NODES);
        if !walk.push_children(root) {
            return true;
        }
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(term) = walk.stack.pop() {
            if !walk.spend(1) {
                return true;
            }
            if seen.contains(&term) {
                continue;
            }
            if seen.len() >= MAX_DOCUMENT_SPELLING_NODES || seen.try_reserve(1).is_err() {
                return true;
            }
            seen.insert(term);
            if self.override_respells(overrides, term, false, &mut walk) != Some(false)
                || !walk.push_children(term)
            {
                return true;
            }
        }
        false
    }

    /// Every strict descendant of a term re-spelled modulo `alpha_equiv`, or
    /// `None` over the cap.
    fn descendants_of_respelled_terms(
        &self,
        overrides: &HashMap<TermId, String>,
    ) -> Option<HashSet<TermId>> {
        let mut below: HashSet<TermId> = HashSet::default();
        let mut walk = SpellingWalk::new(self, MAX_RESPELLED_DESCENDANT_NODES);
        for &term in overrides.keys() {
            if !walk.spend(1) {
                return None;
            }
            if self.override_respells(overrides, term, true, &mut walk)?
                && !walk.push_children(term)
            {
                return None;
            }
        }
        while let Some(term) = walk.stack.pop() {
            if !walk.spend(1) {
                return None;
            }
            if below.contains(&term) {
                continue;
            }
            if below.len() >= MAX_RESPELLED_DESCENDANT_NODES || below.try_reserve(1).is_err() {
                return None;
            }
            below.insert(term);
            if !walk.push_children(term) {
                return None;
            }
        }
        Some(below)
    }
}

#[cfg(test)]
#[path = "document_spelling_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "document_spelling_resource_tests.rs"]
mod resource_tests;
