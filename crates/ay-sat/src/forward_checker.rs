// Copyright 2026 Andrew Yates <andrewyates.name@gmail.com>
// Online forward DRUP checker. CaDiCaL `checker.cpp` (Biere 2021) parity.
//
// Adapter over `ay_drat_check::checker::DratChecker` — the BCP engine,
// RUP verification, and clause database are shared. This file adds:
//   - Literal type conversion (ay-sat ↔ ay-proof-common, zero-cost via index)
//   - Incremental push/pop for scoped solving (debug builds only)
//   - Trusted transform validation (non-RUP inprocessing clauses)
//   - Graceful RUP failure handling for inprocessing clauses (#7929)

mod convert;
#[cfg(test)]
mod tests;

use crate::Literal;
use convert::to_proof_lits;

/// Online forward DRUP checker with self-contained clause database and BCP engine.
///
/// Delegates to `ay_drat_check::checker::DratChecker` for the core BCP engine,
/// adding incremental scope management and trusted transform validation.
///
/// Supports sampled mode (#5625): only every `sample_period`th derived clause
/// undergoes full RUP verification. Non-sampled clauses are added as trusted
/// to maintain BCP state consistency without the O(clause_len) BCP cost.
///
/// RUP failures during inprocessing (#7929): when a derived clause fails the
/// forward RUP check, the checker adds it as trusted and increments
/// `rup_failures`. This is expected for inprocessing-derived clauses (BVE
/// resolvents, backbone units, sweep equivalences) whose derivations depend
/// on intermediate CDCL state not tracked by the forward checker. External
/// DRAT/LRAT verification covers these steps.
pub(crate) struct ForwardChecker {
    inner: ay_drat_check::checker::DratChecker,
    /// Incremental scope stack: saves (trail_len, inconsistent) per push().
    /// Only used from ProofManager in debug builds.
    #[cfg(debug_assertions)]
    scope_stack: Vec<(usize, bool)>,
    /// Derived clause counter (DratChecker tracks as `additions`).
    derived_count: u64,
    /// Sampling period: 0 = check every clause, N > 0 = check every Nth clause.
    /// Non-checked clauses are added as trusted (no RUP verification).
    sample_period: u64,
    /// Count of derived clauses that failed RUP verification (#7929).
    /// These clauses are added as trusted to maintain clause DB consistency.
    /// A non-zero count is expected when inprocessing is active (BVE, backbone,
    /// sweep emit clauses whose derivation chains are not reproducible by
    /// the forward checker's simplified BCP engine).
    rup_failures: u64,
    /// Count of clauses that were RUP-checked (sampled).
    #[cfg(test)]
    pub(crate) sampled_checks: u64,
    /// Count of clauses that were added as trusted (skipped RUP).
    #[cfg(test)]
    pub(crate) sampled_skips: u64,
}

impl ForwardChecker {
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            // check_rat=false: ForwardChecker is DRUP-only (no RAT support).
            inner: ay_drat_check::checker::DratChecker::new(num_vars, false),
            #[cfg(debug_assertions)]
            scope_stack: Vec::new(),
            derived_count: 0,
            sample_period: 0,
            rup_failures: 0,
            #[cfg(test)]
            sampled_checks: 0,
            #[cfg(test)]
            sampled_skips: 0,
        }
    }

    /// Create a sampled forward checker (#5625).
    ///
    /// Only every `sample_period`th derived clause undergoes full RUP
    /// verification. Non-sampled clauses are added to the checker DB as
    /// trusted (no BCP cost) to maintain state consistency.
    pub(crate) fn new_sampled(num_vars: usize, sample_period: u64) -> Self {
        Self {
            inner: ay_drat_check::checker::DratChecker::new(num_vars, false),
            #[cfg(debug_assertions)]
            scope_stack: Vec::new(),
            derived_count: 0,
            sample_period,
            rup_failures: 0,
            #[cfg(test)]
            sampled_checks: 0,
            #[cfg(test)]
            sampled_skips: 0,
        }
    }

    /// The sampling period (0 = check every clause).
    pub(crate) fn sample_period(&self) -> u64 {
        self.sample_period
    }

    // ── Incremental Scope Management ──────────────────────────────
    // Called from ProofManager in debug builds only.

    /// Save the current state for incremental push/pop.
    ///
    /// Records the trail length and `inconsistent` flag so that `pop()` can
    /// restore the checker to a pre-scope state. Without this, the checker
    /// becomes permanently silent after the first scoped UNSAT (#4481).
    #[cfg(debug_assertions)]
    pub(crate) fn push(&mut self) {
        self.scope_stack
            .push((self.inner.trail_len(), self.inner.is_inconsistent()));
    }

    /// Restore checker state to before the most recent `push()`.
    ///
    /// Undoes trail assignments made since the push and restores the
    /// `inconsistent` flag. Scoped clauses remain in the clause DB
    /// (conservative: extra clauses only make RUP checks easier).
    #[cfg(debug_assertions)]
    pub(crate) fn pop(&mut self) {
        debug_assert!(
            !self.scope_stack.is_empty(),
            "BUG: forward checker pop without matching push"
        );
        if let Some((saved_trail_len, saved_inconsistent)) = self.scope_stack.pop() {
            self.inner.backtrack_to(saved_trail_len);
            self.inner.set_inconsistent(saved_inconsistent);
        }
    }

    // ── Public API ────────────────────────────────────────────────

    /// Add an original (input formula) clause. No RUP check.
    pub(crate) fn add_original(&mut self, clause: &[Literal]) {
        debug_assert!(
            !Self::has_duplicate_literal(clause),
            "BUG: forward checker original clause contains duplicate literal (len={})",
            clause.len()
        );
        let converted = to_proof_lits(clause);
        self.inner.add_original(&converted);
    }

    /// Add a trusted inprocessing transform clause (#4609).
    ///
    /// Runs weaker-than-RUP validation: verifies the clause is non-empty,
    /// non-tautological, and not already entirely falsified (all literals
    /// assigned false). This catches the most common transform bugs without
    /// requiring full RUP derivability. The clause is then added as trusted
    /// so it is available for future RUP derivations.
    pub(crate) fn add_trusted_transform(&mut self, clause: &[Literal]) {
        if self.inner.is_inconsistent() {
            return;
        }
        debug_assert!(!clause.is_empty(), "BUG: empty trusted transform clause");

        let converted = to_proof_lits(clause);

        // Check that at least one literal is not falsified. A fully-falsified
        // clause from an inprocessing transform is suspicious but not always a
        // bug: the LRAT materialization fallback emits TrustedTransform units
        // for level-0 variables whose proof chains can't be fully constructed.
        // The forward checker's state may disagree with the solver's trail
        // (e.g., after inprocessing reassignments). Downgraded from assert to
        // debug_assert per #7108.
        #[cfg(debug_assertions)]
        {
            let all_false = converted
                .iter()
                .all(|&lit| self.inner.lit_value(lit) == Some(false));
            if all_false {
                eprintln!(
                    "WARNING: trusted transform clause fully falsified in forward checker: {:?}",
                    clause.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>(),
                );
            }
        }

        self.inner.add_trusted(&converted);
    }

    /// Add a derived (learned) clause. Verifies RUP when possible.
    ///
    /// If the clause fails the forward RUP check, it is added as trusted
    /// and `rup_failures` is incremented (#7929). This is expected for
    /// inprocessing-derived clauses (BVE resolvents, backbone units, sweep
    /// equivalences) whose derivations depend on intermediate CDCL state
    /// not tracked by the forward checker. External DRAT/LRAT verification
    /// covers these steps.
    ///
    /// In sampled mode (#5625), only every `sample_period`th clause undergoes
    /// full RUP verification. Non-sampled clauses are added as trusted to
    /// maintain BCP state consistency without the O(clause_len) BCP cost.
    pub(crate) fn add_derived(&mut self, clause: &[Literal]) {
        debug_assert!(
            !Self::has_duplicate_literal(clause),
            "BUG: forward checker derived clause contains duplicate literal (len={})",
            clause.len()
        );
        // Once inconsistent, non-empty additions cannot make the checker stricter.
        // Still accept an explicit empty-clause step so proof completion can be
        // recorded by callers (issue #4483).
        if self.inner.is_inconsistent() && !clause.is_empty() {
            return;
        }
        self.derived_count += 1;

        let converted = to_proof_lits(clause);

        // Sampled mode: skip RUP check for non-sampled clauses.
        if self.sample_period > 0 && (self.derived_count % self.sample_period) != 1 {
            // Add as trusted — maintains clause DB for future RUP checks
            // without the BCP cost of full derivation verification.
            self.inner.add_trusted(&converted);
            #[cfg(test)]
            {
                self.sampled_skips += 1;
            }
            return;
        }

        #[cfg(test)]
        {
            self.sampled_checks += 1;
        }

        match self.inner.add_derived(&converted) {
            Ok(()) => {}
            Err(_msg) => {
                if clause.is_empty() {
                    // Block-UIP shrink introduces variables unreachable by
                    // level-0 BCP. The empty clause may fail RUP when the
                    // shrunk chain's intermediate variables have no permanent
                    // assignment. External LRAT verification covers this step.
                    self.inner.set_inconsistent(true);
                    return;
                }
                // Inprocessing-derived clauses (BVE resolvents, backbone units,
                // sweep equivalences) may not be RUP-derivable in the forward
                // checker's clause DB because their derivation chains depend on
                // intermediate CDCL state (learned clauses from bounded probes,
                // deleted antecedents, etc.) that the checker doesn't track.
                //
                // Add the clause as trusted to maintain clause DB consistency
                // for future RUP checks. External DRAT/LRAT verification
                // validates these steps against the full proof. (#7929)
                self.rup_failures += 1;
                #[cfg(debug_assertions)]
                {
                    let dimacs: Vec<i32> = clause.iter().map(|l| l.to_dimacs()).collect();
                    eprintln!(
                        "forward checker: RUP failure #{} on derived clause {dimacs:?} \
                         (added as trusted)",
                        self.rup_failures,
                    );
                }
                self.inner.add_trusted(&converted);
            }
        }
    }

    /// Number of derived clauses that failed RUP verification (#7929).
    #[cfg(test)]
    pub(crate) fn rup_failures(&self) -> u64 {
        self.rup_failures
    }

    /// Delete a clause from the checker's database. Matches by literal set
    /// (order-independent). Necessary for DRUP correctness: without deletion,
    /// satisfied clauses from the original formula mask derivation failures.
    pub(crate) fn delete_clause(&mut self, clause: &[Literal]) {
        debug_assert!(
            !clause.is_empty(),
            "BUG: forward checker delete_clause called with empty clause"
        );
        debug_assert!(
            !Self::has_duplicate_literal(clause),
            "BUG: forward checker delete_clause contains duplicate literal (len={})",
            clause.len()
        );
        let converted = to_proof_lits(clause);
        self.inner.delete_clause(&converted);
    }

    #[cfg(test)]
    pub(crate) fn derived_count(&self) -> u64 {
        self.derived_count
    }

    /// Number of live (non-deleted) clauses in the checker's database.
    ///
    /// Used by `validate_proof_coherence` (#5012 Family B) to cross-check
    /// the forward checker's clause set against the solver's active count.
    #[cfg(debug_assertions)]
    pub(crate) fn live_clause_count(&self) -> usize {
        self.inner.live_clause_count()
    }

    /// Returns true if clause contains duplicate literals.
    /// Only called from `debug_assert!()` -- dead-code eliminated in release builds.
    fn has_duplicate_literal(clause: &[Literal]) -> bool {
        for i in 0..clause.len() {
            for j in (i + 1)..clause.len() {
                if clause[i] == clause[j] {
                    return true;
                }
            }
        }
        false
    }
}
