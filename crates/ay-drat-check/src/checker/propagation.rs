// Copyright 2026 Andrew Yates
// Two-watched-literal BCP propagation engine for the DRAT proof checker.
// Includes standard single-pass BCP and two-pass core-first BCP
// (drat-trim.c:194-230 parity).

use crate::literal::Literal;

use super::{DratChecker, Visit, Watch};

impl DratChecker {
    // -- Propagation (2WL BCP) --

    /// Run BCP. Returns `true` if no conflict, `false` on conflict.
    ///
    /// When `core_first` is enabled, uses a two-pass scheme matching
    /// drat-trim.c:194-230: ACTIVE-watched clauses are propagated before
    /// non-ACTIVE ones. If a unit propagation is found in the non-ACTIVE
    /// pass, the core pass is re-entered for any new assignments (the
    /// "flip_check" jump in drat-trim).
    pub(super) fn propagate(&mut self) -> bool {
        if !self.core_first {
            return self.propagate_simple();
        }
        self.propagate_core_first()
    }

    /// Standard single-pass BCP (used when core_first is off).
    fn propagate_simple(&mut self) -> bool {
        while let Some(&lit) = self.trail.get(self.propagate_cursor) {
            // `get` succeeded, so the cursor is below `trail.len()` and the
            // increment is exact.
            self.propagate_cursor = self.propagate_cursor.saturating_add(1);
            self.stats.propagations = self.stats.propagations.saturating_add(1);
            if !self.propagate_watches(lit, None) {
                return false;
            }
        }
        true
    }

    /// Two-pass core-first BCP (drat-trim.c:194-230).
    ///
    /// Uses two trail cursors. Pass 1 (core=true) processes only
    /// ACTIVE-watched clauses. Pass 2 (core=false) processes only
    /// non-ACTIVE-watched clauses. When a unit is found in pass 2,
    /// control returns to pass 1 for any new assignments.
    fn propagate_core_first(&mut self) -> bool {
        let mut cursor_core = self.propagate_cursor;
        let mut cursor_noncore = self.propagate_cursor;

        loop {
            // Pass 1: process ACTIVE-watched clauses
            while let Some(&lit) = self.trail.get(cursor_core) {
                // In bounds, so the increment is exact.
                cursor_core = cursor_core.saturating_add(1);
                self.stats.propagations = self.stats.propagations.saturating_add(1);
                if !self.propagate_watches(lit, Some(true)) {
                    self.propagate_cursor = self.trail.len();
                    return false;
                }
            }

            // Pass 2: process non-ACTIVE-watched clauses
            let mut found_unit = false;
            while let Some(&lit) = self.trail.get(cursor_noncore) {
                // In bounds, so the increment is exact.
                cursor_noncore = cursor_noncore.saturating_add(1);
                self.stats.propagations = self.stats.propagations.saturating_add(1);
                let trail_before = self.trail.len();
                if !self.propagate_watches(lit, Some(false)) {
                    self.propagate_cursor = self.trail.len();
                    return false;
                }
                // If new units were found, jump back to core pass
                // (drat-trim.c:225 goto flip_check)
                if self.trail.len() > trail_before {
                    found_unit = true;
                    break;
                }
            }

            if !found_unit {
                break;
            }
        }

        self.propagate_cursor = self.trail.len();
        true
    }

    /// Propagate watches for a single literal.
    ///
    /// `core_filter`: `None` = process all watches (standard mode),
    /// `Some(true)` = process only core watches, `Some(false)` = only non-core.
    fn propagate_watches(&mut self, lit: Literal, core_filter: Option<bool>) -> bool {
        let neg_code = lit.negated().index();
        let mut ws = std::mem::take(&mut self.watches[neg_code]);
        let mut conflict = false;
        // In-order compaction: each watch is visited once and kept (possibly
        // with a new blocking literal) unless its clause moved the watch or
        // was skipped.
        ws.retain_mut(|w| {
            // Core-first filter: keep watches that don't match the current pass.
            if let Some(want_core) = core_filter {
                if w.core != want_core {
                    return true;
                }
            }
            if conflict || self.value(w.blocking) == Some(true) {
                return true;
            }
            let cidx = w.clause_idx;
            match self.visit_clause(cidx, w.blocking, lit.negated(), neg_code, w.core) {
                Visit::KeepUpdate(b) => {
                    w.blocking = b;
                    true
                }
                Visit::Propagate(u, reason) => {
                    self.assign_with_reason(u, reason);
                    true
                }
                Visit::Conflict(conflict_cidx) => {
                    conflict = true;
                    self.bcp_conflict_cidx = Some(conflict_cidx);
                    true
                }
                Visit::Moved | Visit::Skip => false,
            }
        });
        self.watches[neg_code] = ws;
        !conflict
    }

    fn visit_clause(
        &mut self,
        cidx: usize,
        blit: Literal,
        neg_lit: Literal,
        neg_code: usize,
        watch_core: bool,
    ) -> Visit {
        let clause = match &self.clauses[cidx] {
            Some(c) => c,
            None => return Visit::Skip,
        };
        if clause.len() == 2 {
            return match self.value(blit) {
                Some(false) => Visit::Conflict(cidx),
                None => {
                    // Ensure propagated literal is at clause[0] (drat-trim.c:212).
                    // This is needed so is_reason_for_first_lit() correctly
                    // identifies the clause as a pseudo-unit reason.
                    if let Some(Some(c)) = self.clauses.get_mut(cidx) {
                        if let [first, second, ..] = c.as_mut_slice() {
                            if *first != blit {
                                std::mem::swap(first, second);
                            }
                        }
                    }
                    Visit::Propagate(blit, cidx)
                }
                Some(true) => Visit::Skip,
            };
        }
        self.visit_long(cidx, neg_lit, neg_code, watch_core)
    }

    fn visit_long(
        &mut self,
        cidx: usize,
        neg_lit: Literal,
        neg_code: usize,
        watch_core: bool,
    ) -> Visit {
        let clause = match self.clauses[cidx].as_ref() {
            Some(c) => c,
            None => return Visit::Skip, // Deleted clause — skip (robustness).
        };
        // Only clauses of length >= 2 are watched, and binary clauses are
        // handled by `visit_clause`; a shorter clause cannot propagate here.
        let [first, second, rest @ ..] = clause.as_slice() else {
            return Visit::Skip;
        };
        let other = if *first == neg_lit { *second } else { *first };
        if self.value(other) == Some(true) {
            return Visit::KeepUpdate(other);
        }
        let mut replacement = None;
        for &rep in rest {
            if self.value(rep) != Some(false) {
                replacement = Some(rep);
                break;
            }
        }
        if let Some(rep) = replacement {
            self.reorder_watched(cidx, other, rep);
            if rep.index() == neg_code {
                return Visit::KeepUpdate(other);
            }
            self.watches[rep.index()].push(Watch {
                blocking: other,
                clause_idx: cidx,
                core: watch_core,
            });
            return Visit::Moved;
        }
        match self.value(other) {
            None => {
                // Ensure propagated literal is at clause[0] (drat-trim.c:212,220).
                // The falsified literal (neg_lit) goes to clause[1]. This is
                // needed so is_reason_for_first_lit() correctly identifies the
                // clause as a pseudo-unit reason during deletion.
                if let Some(Some(c)) = self.clauses.get_mut(cidx) {
                    if let [first, second, ..] = c.as_mut_slice() {
                        if *first != other {
                            std::mem::swap(first, second);
                        }
                    }
                }
                Visit::Propagate(other, cidx)
            }
            Some(false) => Visit::Conflict(cidx),
            Some(true) => Visit::KeepUpdate(other),
        }
    }

    fn reorder_watched(&mut self, cidx: usize, w0: Literal, w1: Literal) {
        let Some(Some(c)) = self.clauses.get_mut(cidx) else {
            return;
        };
        reorder_watched_lits(c, w0, w1);
    }

    /// Mark the watch entries for clause `cidx` as core/ACTIVE.
    /// Called from `BackwardChecker::mark_active` to set the low-bit
    /// equivalent of drat-trim's `markWatch` (drat-trim.c:131-135).
    pub(super) fn mark_watches_core(&mut self, cidx: usize) {
        let (w0, w1) = match &self.clauses[cidx] {
            Some(c) if c.len() >= 2 => (c[0], c[1]),
            _ => return,
        };
        Self::set_core_on_watches(&mut self.watches[w0.index()], cidx);
        Self::set_core_on_watches(&mut self.watches[w1.index()], cidx);
    }

    fn set_core_on_watches(watches: &mut [Watch], cidx: usize) {
        for w in watches.iter_mut() {
            if w.clause_idx == cidx {
                w.core = true;
                break; // Each clause has at most one watch entry per literal list.
            }
        }
    }
}

/// Move the first occurrence of `w0` to slot 0, then the first occurrence of
/// `w1` after slot 0 to slot 1 (`swap(0, position(w0))` followed by
/// `swap(1, 1 + position_in_tail(w1))`). Written with slice splits rather
/// than computed indices, so no position can be out of bounds.
fn reorder_watched_lits(c: &mut [Literal], w0: Literal, w1: Literal) {
    let Some((first, tail)) = c.split_first_mut() else {
        return;
    };
    bring_to_front(first, tail, w0);
    if let Some((second, rest)) = tail.split_first_mut() {
        bring_to_front(second, rest, w1);
    }
}

/// If `*slot != lit`, swap `*slot` with the first occurrence of `lit` in
/// `rest` (if any).
fn bring_to_front(slot: &mut Literal, rest: &mut [Literal], lit: Literal) {
    if *slot == lit {
        return;
    }
    if let Some(found) = rest.iter_mut().find(|l| **l == lit) {
        std::mem::swap(slot, found);
    }
}

#[cfg(test)]
mod reorder_tests {
    use super::reorder_watched_lits;
    use crate::literal::Literal;

    /// The index-based reordering `reorder_watched_lits` replaced.
    fn reference(c: &mut [Literal], w0: Literal, w1: Literal) {
        if let Some(p) = c.iter().position(|&l| l == w0) {
            c.swap(0, p);
        }
        let tail_pos = c.get(1..).and_then(|t| t.iter().position(|&l| l == w1));
        if let Some(q) = tail_pos {
            c.swap(1, q + 1);
        }
    }

    /// Exhaustive over clauses of length 0..=4 drawn from four literals
    /// (duplicates included) and every watched pair: identical results.
    #[test]
    fn reorder_matches_index_based_reference() {
        let pool = [
            Literal::from_raw(2),
            Literal::from_raw(3),
            Literal::from_raw(4),
            Literal::from_raw(7),
        ];
        let mut clauses: Vec<Vec<Literal>> = vec![Vec::new()];
        for _ in 0..4 {
            let next: Vec<Vec<Literal>> = clauses
                .iter()
                .filter(|c| c.len() < 4)
                .flat_map(|c| {
                    pool.iter().map(move |&l| {
                        let mut d = c.clone();
                        d.push(l);
                        d
                    })
                })
                .collect();
            clauses.extend(next);
            clauses.sort();
            clauses.dedup();
        }
        for clause in &clauses {
            for &w0 in &pool {
                for &w1 in &pool {
                    let mut got = clause.clone();
                    let mut want = clause.clone();
                    reorder_watched_lits(&mut got, w0, w1);
                    reference(&mut want, w0, w1);
                    assert_eq!(got, want, "clause {clause:?} w0 {w0:?} w1 {w1:?}");
                }
            }
        }
    }
}
