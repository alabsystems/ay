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
        while self.propagate_cursor < self.trail.len() {
            let lit = self.trail[self.propagate_cursor];
            self.propagate_cursor += 1;
            self.stats.propagations += 1;
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
            while cursor_core < self.trail.len() {
                let lit = self.trail[cursor_core];
                cursor_core += 1;
                self.stats.propagations += 1;
                if !self.propagate_watches(lit, Some(true)) {
                    self.propagate_cursor = self.trail.len();
                    return false;
                }
            }

            // Pass 2: process non-ACTIVE-watched clauses
            let mut found_unit = false;
            while cursor_noncore < self.trail.len() {
                let lit = self.trail[cursor_noncore];
                cursor_noncore += 1;
                self.stats.propagations += 1;
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
        let mut j = 0;
        let mut conflict = false;
        for i in 0..ws.len() {
            // Core-first filter: skip watches that don't match the current pass.
            if let Some(want_core) = core_filter {
                if ws[i].core != want_core {
                    ws[j] = ws[i];
                    j += 1;
                    continue;
                }
            }
            if conflict {
                ws[j] = ws[i];
                j += 1;
                continue;
            }
            if self.value(ws[i].blocking) == Some(true) {
                ws[j] = ws[i];
                j += 1;
                continue;
            }
            let cidx = ws[i].clause_idx;
            match self.visit_clause(cidx, ws[i].blocking, lit.negated(), neg_code, ws[i].core) {
                Visit::KeepUpdate(b) => {
                    ws[j] = Watch {
                        blocking: b,
                        clause_idx: cidx,
                        core: ws[i].core,
                    };
                    j += 1;
                }
                Visit::Propagate(u, reason) => {
                    self.assign_with_reason(u, reason);
                    ws[j] = ws[i];
                    j += 1;
                }
                Visit::Conflict(conflict_cidx) => {
                    conflict = true;
                    self.bcp_conflict_cidx = Some(conflict_cidx);
                    ws[j] = ws[i];
                    j += 1;
                }
                Visit::Moved | Visit::Skip => {}
            }
        }
        ws.truncate(j);
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
                    if let Some(ref mut c) = self.clauses[cidx] {
                        if c[0] != blit {
                            c.swap(0, 1);
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
        let other = if clause[0] == neg_lit {
            clause[1]
        } else {
            clause[0]
        };
        if self.value(other) == Some(true) {
            return Visit::KeepUpdate(other);
        }
        let mut replacement = None;
        for &rep in &clause[2..] {
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
                if let Some(ref mut c) = self.clauses[cidx] {
                    if c[0] != other {
                        c.swap(0, 1);
                    }
                }
                Visit::Propagate(other, cidx)
            }
            Some(false) => Visit::Conflict(cidx),
            Some(true) => Visit::KeepUpdate(other),
        }
    }

    fn reorder_watched(&mut self, cidx: usize, w0: Literal, w1: Literal) {
        if let Some(ref mut c) = self.clauses[cidx] {
            if let Some(p) = c.iter().position(|&l| l == w0) {
                c.swap(0, p);
            }
            if let Some(p) = c[1..].iter().position(|&l| l == w1) {
                c.swap(1, p + 1);
            }
        }
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
