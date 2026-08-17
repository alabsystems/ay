// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::TermId;

/// D1 shadow instrumentation for the on-assert lazy-extensionality campaign.
///
/// The eager path (`add_array_extensionality_axioms_up_to`) emits one
/// `__ay_ext_diff(a,b)` witness clause per SYNTACTIC array-equality atom whose
/// negation appears anywhere in the term store — an over-approximation that
/// balloons on qlock-style AUFLIA (many witnesses vs z3's few demand-driven).
/// This struct records, per solve, the EAGER set of pairs actually emitted so
/// the finalizer can correlate it against the DEMANDED set (pairs whose
/// equality atom the search forced false) and surface the dead mass on `-st`.
///
/// Measurement only: the eager path stays authoritative and is never gated on
/// this data. Kept always-on (not `cfg(debug_assertions)`) so the counters are
/// visible on release `-st` runs; the sets are tiny (bounded by the number of
/// array-equality atoms) so the overhead is negligible.
#[derive(Debug, Clone, Default)]
pub(crate) struct ArrayExtShadow {
    /// Per emitted witness: `(eq_term, lhs, rhs, not_sel_eq_atom)`.
    ///
    /// `eq_term` is the `(= a b)` atom the extensionality clause guards;
    /// `not_sel_eq` is the `¬((select a k) = (select b k))` witness literal.
    /// Deduplicated by the ordered `(lhs, rhs)` pair at record time.
    pub(crate) emitted: Vec<(TermId, TermId, TermId, TermId)>,
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
        eq_term: TermId,
        lhs: TermId,
        rhs: TermId,
        not_sel_eq: TermId,
    ) -> bool {
        let pair = if lhs.0 <= rhs.0 {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        };
        if !self.seen_pairs.insert(pair) {
            return false;
        }
        self.emitted.push((eq_term, lhs, rhs, not_sel_eq));
        true
    }
}
