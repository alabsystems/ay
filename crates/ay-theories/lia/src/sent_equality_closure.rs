// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The classes LIA's sent Nelson-Oppen equalities already join
//! (#tight-bound-star-dedup).
//!
//! `propagated_equality_pairs` is the "already sent" set of
//! `propagate_equalities`. A pair enters it when LIA hands it to EUF (the
//! tight-bound phase, Phase 3) or queues it to be handed (Case-2 algebraic
//! equalities), when a fresh instance is seeded with a replayed pair the
//! combiner has just asserted into EUF, or when a fresh instance imports a
//! predecessor's set with its `DiophState`. A non-tentative pop clears it.
//! Phase 3 (implied difference equalities) skips a pair that is already in
//! the set.
//!
//! Before f7f0d7ad8 the tight-bound phase emitted ALL pairs of a same-value
//! group, so every pair inside a group was in the set and Phase 3 never
//! re-sent one. The anchor star (DR-AY-TIGHT-BOUND-STAR-20261104) sends only
//! `n - 1` edges per group and relies on EUF's transitivity. A literal set
//! lookup has none, so Phase 3 began re-sending every spoke pair the star
//! had joined, in imported sets too. On the QF_ALIA store-chain witnesses of
//! `array_repair_completeness_2026_09_24` (`d4b_free_bases`,
//! `storeeq_2809_0181`, `finstore_2809_0048`) those redundant equalities
//! became cross-theory replays and new Nelson-Oppen work, and the search
//! settled on a first model the gates could not confirm, so the checks
//! answered `unknown`.
//!
//! [`SentEqualityClosure`] reads the set the way the star assumes: a pair is
//! already sent when the sent pairs connect it.
//!
//! * Within one instance, EUF holds every pair LIA handed it or was seeded
//!   with, so it already holds the joined class and skipping loses nothing.
//!   (A Case-0 conflict that drops queued Case-2 pairs is returned before
//!   Phase 3 runs, and the backtrack that follows clears the set.)
//! * An imported pair may be missing from the fresh instance's EUF. The
//!   literal lookup already treated imported pairs as sent, and all-pairs
//!   emission put every pair inside an imported group in the set. The
//!   closure reproduces that. It has to: built without the imported pairs,
//!   it leaves `d4b_free_bases` `unknown`.
//! * The closure also joins pairs across groups and rounds, which all-pairs
//!   emission did not. Where EUF lacks an imported link, a skipped pair can
//!   be missing from EUF as well. That costs completeness only: skipping adds
//!   no constraint, and every `sat` still passes the model gates.
//!
//! The closure is linear in the set; no quadratic pair set is rebuilt.

use super::{HashMap, TermId};

/// Union-find over the sent pairs, flattened to term -> class root.
pub(crate) struct SentEqualityClosure {
    root: HashMap<TermId, TermId>,
}

impl SentEqualityClosure {
    /// Join every sent pair.
    pub(crate) fn new<'p>(sent: impl IntoIterator<Item = &'p (TermId, TermId)>) -> Self {
        let mut parent: HashMap<TermId, TermId> = HashMap::default();
        for &(lhs, rhs) in sent {
            let lhs_root = find(&mut parent, lhs);
            let rhs_root = find(&mut parent, rhs);
            if lhs_root != rhs_root {
                parent.insert(lhs_root, rhs_root);
            }
        }
        let members: Vec<TermId> = parent.keys().copied().collect();
        let mut root = HashMap::default();
        for member in members {
            let member_root = find(&mut parent, member);
            root.insert(member, member_root);
        }
        Self { root }
    }

    /// Whether the sent pairs already connect `lhs` and `rhs`.
    pub(crate) fn connected(&self, lhs: TermId, rhs: TermId) -> bool {
        lhs != rhs && self.root_of(lhs) == self.root_of(rhs)
    }

    fn root_of(&self, term: TermId) -> TermId {
        self.root.get(&term).copied().unwrap_or(term)
    }
}

/// Root of `term`, halving the path on the way up.
fn find(parent: &mut HashMap<TermId, TermId>, term: TermId) -> TermId {
    let mut current = term;
    while let Some(&next) = parent.get(&current) {
        if let Some(&grand) = parent.get(&next) {
            parent.insert(current, grand);
        }
        current = next;
    }
    current
}
