// Copyright 2026 Andrew Yates
// Resolution check for the LRAT checker.
//
// Verifies that the symbolic resolution of the hint chain produces exactly the
// derived clause. Called after successful RUP check as an extra safety net.
//
// Reference: CaDiCaL lratchecker.cpp:233-294 (check_resolution).

use crate::dimacs::Literal;

use super::LratChecker;

impl LratChecker {
    /// Verify that symbolic resolution of the hint chain produces exactly
    /// the derived clause.
    ///
    /// Algorithm (CaDiCaL lratchecker.cpp:233-294):
    /// 1. Start with the last hint clause. Mark all its literals in `checked_lits`.
    /// 2. Walk hints backward (second-to-last to first). For each hint clause:
    ///    - If `~lit` is marked: cancel both (resolution step).
    ///    - Else: mark `lit` (add to resolvent).
    /// 3. Compare resolvent to imported clause: for each variable, both polarities
    ///    must be marked (present in both) or neither (absent from both). Any
    ///    mismatch means the resolution chain doesn't produce the claimed clause.
    ///
    /// Uses `checked_stack` for O(touched) cleanup instead of O(num_vars) scan.
    /// Without this, resolution checking degrades to O(n × num_vars) on long
    /// proof chains (100K+ steps). Fix for #5263.
    ///
    /// Only takes positive (RUP) hints. RAT witnesses are verified separately.
    pub(super) fn check_resolution(&mut self, clause: &[Literal], hints: &[i64]) -> bool {
        if hints.is_empty() {
            // Tautological clause — no chain needed.
            return true;
        }

        // Last hint must be positive (a clause ID, not an ER marker).
        let last_hint = *hints
            .last()
            .expect("invariant: non-empty hints checked above");
        if last_hint < 0 {
            return false;
        }

        // Defensive: clear any leaked state from a prior call.
        // Converted from debug_assert to runtime guard for release safety.
        if !self.checked_stack.is_empty() {
            self.clear_checked_stack();
        }

        // Phase 1: Initialize resolvent from last hint clause.
        // Copy the ClauseEntry (16 bytes) to release the borrow on clause_index.
        // No heap allocation — replaces the previous Vec::clone(). (#5267)
        let last_entry = match self.clause_index.get(&(last_hint as u64)) {
            Some(&e) => e,
            None => return false,
        };
        // Iterate by arena index: `clause_arena[i]` copies the Literal (u32),
        // releasing the borrow before `ensure_mark_capacity` mutates self.
        let start = last_entry.start as usize;
        let end = start + last_entry.len as usize;
        for i in start..end {
            let lit = self.clause_arena[i];
            self.ensure_mark_capacity(lit);
            self.ensure_mark_capacity(lit.negated());
            // Tautological last hint clause: ~lit already marked → reject.
            // Converted from debug_assert to runtime guard for release safety.
            if self.checked_lits[lit.negated().index()] {
                self.clear_checked_stack();
                return false;
            }
            self.set_checked(lit.index());
        }

        // Phase 2: Walk hints from second-to-last backward to first.
        // For each literal: if ~lit is in resolvent, cancel both; else add lit.
        for &hint_id in hints[..hints.len() - 1].iter().rev() {
            if hint_id < 0 {
                self.clear_checked_stack();
                return false;
            }
            // Copy ClauseEntry to avoid borrow conflict with self.checked_lits.
            let entry = match self.clause_index.get(&(hint_id as u64)) {
                Some(&e) => e,
                None => {
                    self.clear_checked_stack();
                    return false;
                }
            };
            let start = entry.start as usize;
            let end = start + entry.len as usize;
            for i in start..end {
                let lit = self.clause_arena[i];
                self.ensure_mark_capacity(lit);
                self.ensure_mark_capacity(lit.negated());
                let neg_idx = lit.negated().index();
                if self.checked_lits[neg_idx] {
                    self.checked_lits[neg_idx] = false; // Cancel: resolution step
                                                        // Note: neg_idx stays on the stack but is now false.
                                                        // Phase 4 handles this correctly by checking actual values.
                } else {
                    self.set_checked(lit.index());
                }
            }
        }

        // Phase 3: Compare resolvent to imported clause.
        // For each literal in the imported clause, mark both polarities as
        // "accounted for." If ~lit is in the resolvent, that's a contradiction.
        for &lit in clause {
            self.ensure_mark_capacity(lit);
            self.ensure_mark_capacity(lit.negated());
            let neg_idx = lit.negated().index();
            if self.checked_lits[neg_idx] {
                // ~lit is in resolvent but lit is in the derived clause — mismatch.
                self.clear_checked_stack();
                return false;
            }
            if !self.checked_lits[lit.index()] {
                // Derived clause literal not in resolvent — subsumption is OK.
                self.set_checked(lit.index());
            }
            // Mark the negative polarity to indicate "accounted for."
            self.set_checked(neg_idx);
        }

        // Phase 4: Final check — every touched variable must have both or
        // neither polarity marked. Only checks variables referenced by the
        // resolution chain, not all variables (O(touched) vs O(num_vars)).
        let mut failed = false;
        for &idx in &self.checked_stack {
            // Derive the variable index and both polarity indices.
            let var_idx = idx / 2;
            let pos_idx = var_idx * 2;
            let neg_idx = var_idx * 2 + 1;
            let pos = pos_idx < self.checked_lits.len() && self.checked_lits[pos_idx];
            let neg = neg_idx < self.checked_lits.len() && self.checked_lits[neg_idx];
            if pos != neg {
                failed = true;
                break; // Will clear below.
            }
        }

        self.clear_checked_stack();
        !failed
    }

    /// Record a `checked_lits` index as set, with stack tracking.
    #[inline]
    pub(super) fn set_checked(&mut self, idx: usize) {
        if !self.checked_lits[idx] {
            self.checked_lits[idx] = true;
            self.checked_stack.push(idx);
        }
    }

    /// Clear `checked_lits` via the stack (O(touched) instead of O(num_vars)).
    pub(super) fn clear_checked_stack(&mut self) {
        for &idx in &self.checked_stack {
            self.checked_lits[idx] = false;
        }
        self.checked_stack.clear();
    }
}
