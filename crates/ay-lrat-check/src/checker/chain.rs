// Copyright 2026 Andrew Yates
// LRAT chain verification for the checker.
//
// Dispatches derived clauses through RUP, RAT, and blocked-clause checks.

use crate::dimacs::Literal;

use super::LratChecker;

impl LratChecker {
    /// Verify that `clause` is derivable using the `hints`.
    ///
    /// Dispatch: **(RUP ∧ Resolution) ∨ RAT ∨ Blocked**
    /// Reference: CaDiCaL lratchecker.cpp:503-508, drat-trim lrat-check.c:135-191.
    pub(super) fn verify_chain(&mut self, clause: &[Literal], hints: &[i64]) -> bool {
        // Split at the first negative hint: RUP hints before it, RAT witness
        // groups from it on. `position` returns an index inside `hints`, so
        // both halves exist; the `None` arm is unreachable and fails closed.
        let first_neg = hints.iter().position(|&h| h < 0);
        let (rup_hints, rat_hints) = match first_neg {
            Some(pos) => match (hints.get(..pos), hints.get(pos..)) {
                (Some(rup), Some(rat)) => (rup, Some(rat)),
                _ => return false,
            },
            None => (hints, None),
        };

        let saved = self.trail.len();

        // Step 1: Assume negation of each literal in the clause.
        for &lit in clause {
            let neg = lit.negated();
            match self.value(neg) {
                Some(true) => {}
                Some(false) => {
                    self.backtrack(saved);
                    return true;
                }
                None => {
                    if !self.assign(neg) {
                        self.backtrack(saved);
                        return false;
                    }
                }
            }
        }

        // Step 2: Walk positive (RUP) hints and propagate.
        let rup_ok = self.propagate_rup_hints(rup_hints);
        if rup_ok {
            self.stats.rup_ok = self.stats.rup_ok.saturating_add(1);
            // Resolution check is advisory: tracks whether the hint chain
            // forms a valid syntactic resolution proof. RUP alone is
            // sufficient per the LRAT specification — a clause verified by
            // RUP is accepted regardless of resolution check outcome.
            if self.check_resolution(clause, rup_hints) {
                self.stats.resolution_ok = self.stats.resolution_ok.saturating_add(1);
            } else {
                self.stats.resolution_mismatch = self.stats.resolution_mismatch.saturating_add(1);
            }
            self.backtrack(saved);
            return true;
        }

        // Step 3: Try RAT if negative hints are present.
        if let Some(rat_hints) = rat_hints {
            if let Some(&pivot) = clause.first() {
                let after_rup = self.trail.len();
                let rat_ok = self.verify_rat_witnesses(pivot, rat_hints, after_rup);
                if rat_ok {
                    self.stats.rat_ok = self.stats.rat_ok.saturating_add(1);
                    self.backtrack(saved);
                    return true;
                }
            }
        }

        // Step 4: Try blocked clause check (ER proofs).
        self.backtrack(saved);
        if first_neg.is_some() || hints.is_empty() {
            let blocked = self.check_blocked(clause, hints);
            if blocked {
                self.stats.blocked_ok = self.stats.blocked_ok.saturating_add(1);
            }
            return blocked;
        }

        false
    }
}
