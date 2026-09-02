// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{TermEntryStamp, TermStore};
use ay_core::TermId;

/// One exact current-solve extensionality emission.
#[derive(Debug, Clone)]
pub(crate) struct ArrayExtShadowEntry {
    pub(crate) ext_clause: TermId,
    pub(crate) eq_term: TermId,
    pub(crate) lhs: TermId,
    pub(crate) rhs: TermId,
    pub(crate) not_sel_eq: TermId,
    stamps: [TermEntryStamp; 5],
}

impl ArrayExtShadowEntry {
    /// Numeric term slots can be reused after a speculative rollback. Require
    /// every recorded root to retain the exact birth identity it had at the
    /// generation site before treating this solve-local log as provenance.
    pub(crate) fn is_current(&self, terms: &TermStore) -> bool {
        [
            self.ext_clause,
            self.eq_term,
            self.lhs,
            self.rhs,
            self.not_sel_eq,
        ]
        .into_iter()
        .zip(self.stamps)
        .all(|(term, stamp)| terms.entry_stamp(term) == Some(stamp))
    }
}

/// Current-solve array-extensionality emission log.
///
/// The eager path (`add_array_extensionality_axioms_up_to`) emits one
/// `__ay_ext_diff(a,b)` witness clause per SYNTACTIC array-equality atom whose
/// negation appears anywhere in the term store — an over-approximation that
/// balloons on qlock-style AUFLIA (many witnesses vs z3's few demand-driven).
/// This struct records, per solve, the EAGER set of pairs actually emitted so
/// the finalizer can correlate it against the DEMANDED set (pairs whose
/// equality atom the search forced false) and surface the dead mass on `-st`.
///
/// The eager path remains the logical authority. Telemetry reads every entry;
/// model completion may consume only the strictly stamped, shape-checked,
/// active-witness subset and still submits its candidate to every final gate.
/// Kept always-on (not `cfg(debug_assertions)`) so both consumers see the same
/// current-solve provenance.
#[derive(Debug, Clone, Default)]
pub(crate) struct ArrayExtShadow {
    /// Per emitted witness: `(eq_term, lhs, rhs, not_sel_eq_atom)`.
    ///
    /// `eq_term` is the `(= a b)` atom the extensionality clause guards;
    /// `not_sel_eq` is the `¬((select a k) = (select b k))` witness literal.
    /// Deduplicated by the ordered `(lhs, rhs)` pair at record time.
    pub(crate) emitted: Vec<ArrayExtShadowEntry>,
    /// Ordered `(lhs, rhs)` pairs already recorded, to dedup emissions.
    pub(crate) seen_pairs: HashSet<(TermId, TermId)>,
}

impl ArrayExtShadow {
    pub(crate) fn clear(&mut self) {
        self.emitted.clear();
        self.seen_pairs.clear();
    }

    /// Record one emitted extensionality witness. Returns false if the ordered
    /// pair was already recorded this solve (caller may ignore).
    pub(crate) fn record(
        &mut self,
        terms: &TermStore,
        ext_clause: TermId,
        eq_term: TermId,
        lhs: TermId,
        rhs: TermId,
        not_sel_eq: TermId,
    ) -> bool {
        let (
            Some(ext_clause_stamp),
            Some(eq_stamp),
            Some(lhs_stamp),
            Some(rhs_stamp),
            Some(not_sel_eq_stamp),
        ) = (
            terms.entry_stamp(ext_clause),
            terms.entry_stamp(eq_term),
            terms.entry_stamp(lhs),
            terms.entry_stamp(rhs),
            terms.entry_stamp(not_sel_eq),
        )
        else {
            return false;
        };
        let stamps = [
            ext_clause_stamp,
            eq_stamp,
            lhs_stamp,
            rhs_stamp,
            not_sel_eq_stamp,
        ];
        let pair = if lhs.0 <= rhs.0 {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        };
        if !self.seen_pairs.insert(pair) {
            return false;
        }
        self.emitted.push(ArrayExtShadowEntry {
            ext_clause,
            eq_term,
            lhs,
            rhs,
            not_sel_eq,
            stamps,
        });
        true
    }
}
