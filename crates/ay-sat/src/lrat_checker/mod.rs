// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Online LRAT chain verifier.
//!
//! Verifies that each derived clause can be obtained by RUP (Reverse Unit
//! Propagation) using *only* the specified hint clauses. This is strictly
//! stronger than DRUP checking: DRUP allows any clause in the database as a
//! reason, whereas LRAT requires an explicit certificate.
//!
//! ## Algorithm
//!
//! For `add_derived(id, clause, hints)`:
//! 1. Assume the negation of every literal in `clause`.
//! 2. Walk the hint list in order. For each hint clause, count non-falsified
//!    literals (both satisfied and unassigned):
//!    - 0 non-falsified → conflict → clause verified.
//!    - 1 non-falsified, unassigned → propagate (unit).
//!    - 1 non-falsified, satisfied → no-op (continue).
//!    - 2+ non-falsified → reject (non-unit hint, CaDiCaL parity).
//! 3. If the hints are exhausted without conflict, the LRAT proof is invalid.
//!
//! Reference: CaDiCaL `lratchecker.cpp` (Biere 2021), `--checkproof=2` mode.

#[cfg(any(debug_assertions, test))]
use crate::kani_compat::DetHashMap;
#[cfg(any(debug_assertions, test))]
use crate::Literal;

/// Result of scanning a single hint clause during RUP propagation.
///
/// Matches the standalone ay-lrat-check `HintAction` and CaDiCaL's
/// `lratchecker.cpp` hint classification logic (#5233).
#[cfg(test)]
enum HintAction {
    /// All literals falsified — conflict found.
    Conflict,
    /// Exactly one non-falsified literal (unassigned) — propagate it.
    Propagate(Literal),
    /// Exactly one non-falsified literal (already true) — no-op.
    SatisfiedUnit,
    /// Two or more non-falsified literals — hint is not unit, reject.
    NonUnit,
}

/// Online LRAT chain verifier with clause-ID-indexed database.
#[cfg(any(debug_assertions, test))]
pub(crate) struct LratChecker {
    /// Clause database: maps clause ID to literal vector.
    clauses: DetHashMap<u64, Vec<Literal>>,
    /// Assignment array: `assigns[var_index] = Some(polarity)`.
    assigns: Vec<Option<bool>>,
    /// Trail of assigned variables for backtracking (test-only verification).
    #[cfg(test)]
    trail: Vec<usize>,
    /// Running statistics.
    stats: LratCheckerStats,
}

#[cfg(any(debug_assertions, test))]
#[derive(Default)]
struct LratCheckerStats {
    originals: u64,
    #[cfg(test)]
    derived: u64,
    deleted: u64,
    failures: u64,
}

/// Production API: clause tracking without chain verification.
/// ProofManager uses `add_original`, `delete`, and `failures`.
#[cfg(any(debug_assertions, test))]
impl LratChecker {
    /// Create a new LRAT checker sized for `num_vars` variables.
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            clauses: DetHashMap::default(),
            assigns: vec![None; num_vars],
            #[cfg(test)]
            trail: Vec::new(),
            stats: LratCheckerStats::default(),
        }
    }

    /// Add an original (input) clause. No chain check.
    pub(crate) fn add_original(&mut self, clause_id: u64, clause: &[Literal]) {
        for &lit in clause {
            self.ensure_var(lit);
        }
        self.clauses.insert(clause_id, clause.to_vec());
        self.stats.originals += 1;
    }

    /// Delete a clause from the checker database.
    pub(crate) fn delete(&mut self, clause_id: u64) {
        if self.clauses.remove(&clause_id).is_some() {
            self.stats.deleted += 1;
        }
    }

    /// Number of verification failures detected.
    pub(crate) fn failures(&self) -> u64 {
        self.stats.failures
    }

    fn ensure_var(&mut self, lit: Literal) {
        let idx = lit.variable().index();
        if idx >= self.assigns.len() {
            self.assigns.resize(idx + 1, None);
        }
    }
}

/// Test-only API: full LRAT chain verification via RUP propagation.
#[cfg(test)]
impl LratChecker {
    /// Add a derived clause and verify its LRAT chain.
    ///
    /// Panics if the hint chain does not produce a RUP conflict.
    /// Test-only: direct callers want a hard failure on bad chains (#5003).
    pub(crate) fn add_derived(&mut self, clause_id: u64, clause: &[Literal], hints: &[u64]) {
        assert!(
            self.try_add_derived(clause_id, clause, hints),
            "LRAT chain verification failed for clause {clause_id}"
        );
    }

    /// Add a derived clause and verify its LRAT chain.
    ///
    /// Returns `true` if the chain verifies, `false` if it fails.
    /// Failures are logged via `eprintln!` but do NOT panic — the caller
    /// (ProofManager) falls back to `add_original` (#7108 Fix E).
    pub(crate) fn try_add_derived(
        &mut self,
        clause_id: u64,
        clause: &[Literal],
        hints: &[u64],
    ) -> bool {
        for &lit in clause {
            self.ensure_var(lit);
        }
        self.stats.derived += 1;

        let ok = self.verify_chain(clause, hints);
        if !ok {
            self.stats.failures += 1;
            let missing: Vec<u64> = hints
                .iter()
                .filter(|&&h| h != 0 && !self.clauses.contains_key(&h))
                .copied()
                .collect();
            let clause_dimacs: Vec<i32> = clause.iter().map(|l| l.to_dimacs()).collect();
            eprintln!(
                "BUG: LRAT chain verification failed for clause {clause_id}: \
                 clause={clause_dimacs:?} hints={hints:?} missing_hints={missing:?} \
                 (failure #{}) db_size={}",
                self.stats.failures,
                self.clauses.len(),
            );
            // Replay trace on first failure for debugging
            if self.stats.failures == 1 {
                let saved = self.trail.len();
                for &lit in clause {
                    let neg = lit.negated();
                    match self.value(neg) {
                        Some(true) => {}
                        Some(false) => {
                            self.backtrack(saved);
                            break;
                        }
                        None => self.assign(neg),
                    }
                }
                for &h in hints {
                    if let Some(c) = self.clauses.get(&h) {
                        let d: Vec<i32> = c.iter().map(|l| l.to_dimacs()).collect();
                        let mut nf = 0u32;
                        for &l in c.iter() {
                            if self.value(l) != Some(false) {
                                nf += 1;
                            }
                        }
                        let act = if nf == 0 {
                            "CONFLICT"
                        } else if nf == 1 {
                            "unit"
                        } else {
                            "NON-UNIT"
                        };
                        eprintln!("  h{h}: {d:?} nf={nf} → {act}");
                        if nf == 1 {
                            if let Some(&l) = c.iter().find(|&&l| {
                                self.value(l) != Some(false) && self.value(l) != Some(true)
                            }) {
                                self.assign(l);
                            }
                        }
                    } else {
                        eprintln!("  h{h}: MISSING");
                    }
                }
                self.backtrack(saved);
            }
        }

        // Only insert on success. Inserting unverified clauses lets
        // subsequent steps use them as hints, accepting invalid proofs.
        // CaDiCaL lratchecker.cpp:525 skips insertion on failure.
        if ok {
            self.clauses.insert(clause_id, clause.to_vec());
        }
        ok
    }

    // ── Core verification ──────────────────────────────────────────

    /// Verify that `clause` is RUP-derivable using only the `hints` clauses.
    ///
    /// Returns `true` if a conflict is found (clause is valid).
    ///
    /// Strict mode: empty clause with empty hints is rejected, matching the
    /// standalone ay-lrat-check and CaDiCaL lratchecker behavior. Callers
    /// that lack a resolution chain must use `add_original()` instead of
    /// `try_add_derived()` (#5236 Gap 1).
    fn verify_chain(&mut self, clause: &[Literal], hints: &[u64]) -> bool {
        let saved = self.trail.len();

        // Step 1: Assume negation of each literal in the clause.
        for &lit in clause {
            let neg = lit.negated();
            match self.value(neg) {
                Some(true) => {} // Already assigned this way, fine.
                Some(false) => {
                    // The literal itself is already true → clause trivially satisfied.
                    self.backtrack(saved);
                    return true;
                }
                None => self.assign(neg),
            }
        }

        // Step 2: Walk hints and propagate.
        let conflict = self.propagate_hints(hints);
        self.backtrack(saved);
        conflict
    }

    /// Process hint clauses in order, propagating units and detecting conflicts.
    ///
    /// Counts both satisfied (`Some(true)`) and unassigned (`None`) literals as
    /// "non-falsified." A hint clause with 2+ non-falsified literals is rejected
    /// as `NonUnit`, matching CaDiCaL's `lratchecker.cpp:348-370` and the
    /// standalone ay-lrat-check checker (#5233, #5236 Gap 3).
    fn propagate_hints(&mut self, hints: &[u64]) -> bool {
        for &hint_id in hints {
            // Determine action under immutable borrow of self.clauses.
            let action = {
                let hint_clause = match self.clauses.get(&hint_id) {
                    Some(c) => c,
                    None => return false, // Unknown hint ID — strict mode (#5236).
                };

                let mut non_falsified_count = 0u32;
                let mut candidate_lit = None;

                for &lit in hint_clause {
                    match self.value(lit) {
                        Some(false) => {} // falsified — skip
                        _ => {
                            // Not falsified: either true (satisfied) or unassigned.
                            // CaDiCaL counts both as non-falsified (#5233).
                            non_falsified_count += 1;
                            if non_falsified_count >= 2 {
                                break; // early exit: already non-unit
                            }
                            candidate_lit = Some(lit);
                        }
                    }
                }

                if non_falsified_count == 0 {
                    HintAction::Conflict
                } else if non_falsified_count == 1 {
                    let lit = candidate_lit.expect("invariant: one non-falsified");
                    if self.value(lit) == Some(true) {
                        HintAction::SatisfiedUnit // already true — no-op
                    } else {
                        HintAction::Propagate(lit) // unassigned — propagate
                    }
                } else {
                    HintAction::NonUnit // 2+ non-falsified — CaDiCaL parity rejection
                }
            }; // immutable borrow ends here

            match action {
                HintAction::Conflict => return true,
                HintAction::Propagate(unit) => self.assign(unit),
                HintAction::SatisfiedUnit => {} // no-op: continue to next hint
                HintAction::NonUnit => return false, // CaDiCaL parity: non-unit = failure
            }
        }
        false
    }

    // ── Assignment management ──────────────────────────────────────

    #[inline]
    fn value(&self, lit: Literal) -> Option<bool> {
        let var_idx = lit.variable().index();
        if var_idx >= self.assigns.len() {
            return None;
        }
        self.assigns[var_idx].map(|v| v == lit.is_positive())
    }

    #[inline]
    fn assign(&mut self, lit: Literal) {
        let var_idx = lit.variable().index();
        self.ensure_var(lit);
        assert!(
            self.assigns[var_idx].is_none(),
            "BUG: LRAT checker double-assign var {var_idx}"
        );
        self.assigns[var_idx] = Some(lit.is_positive());
        self.trail.push(var_idx);
    }

    fn backtrack(&mut self, saved_trail_len: usize) {
        while self.trail.len() > saved_trail_len {
            let var_idx = self.trail.pop().expect("invariant: trail non-empty");
            self.assigns[var_idx] = None;
        }
    }
}

#[cfg(test)]
mod tests;
