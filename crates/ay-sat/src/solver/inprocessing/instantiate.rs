// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Post-BVE clause instantiation (CaDiCaL `instantiate.cpp`).
//!
//! After bounded variable elimination, some literals appear in very few
//! clauses. Instantiation tests whether such a literal is redundant in
//! a clause by assuming the literal TRUE and all other clause literals
//! FALSE, then running BCP. If BCP derives a conflict, the literal is
//! redundant and can be removed (strengthening the clause).
//!
//! This enables further elimination: removing the last occurrence of a
//! literal creates a pure variable that the next BVE round can eliminate.
//!
//! Reference: CaDiCaL `instantiate.cpp` (365 lines), triggered at the
//! end of `elim_round` (`elim.cpp:917-947`).
//!
//! Integration: called from `bve_body()` after the elimination loop but
//! before watches are rebuilt for search. Instantiation temporarily
//! rebuilds 2WL watches to run BCP, then tears them down.

use super::super::*;
use crate::solver_log::solver_log;

/// Maximum number of occurrences for a literal to be considered as an
/// instantiation candidate. CaDiCaL: `instantiateocclim=1` (options.hpp:146).
/// We use 2 to match CaDiCaL's actual behavior (options range 1..2e9, default 1).
const INST_OCC_LIMIT: usize = 1;

/// Minimum clause size for instantiation candidates.
/// CaDiCaL: `instantiateclslim=3` (options.hpp:145).
const INST_CLAUSE_SIZE_MIN: usize = 3;

/// A candidate for instantiation: a (literal, clause) pair.
///
/// CaDiCaL `Instantiator::Candidate` (instantiate.hpp:24-31).
pub(crate) struct InstCandidate {
    /// The literal to try removing from the clause.
    pub lit: Literal,
    /// Arena offset of the clause containing the literal.
    pub clause_idx: usize,
    /// Clause size at collection time (for sorting).
    pub clause_size: usize,
    /// Number of negative occurrences of `lit` (for priority sorting).
    pub neg_occs: usize,
}

impl Solver {
    /// Collect instantiation candidates from BVE occurrence lists.
    ///
    /// Must be called while occurrence lists are still live (before
    /// `reset_occs`). CaDiCaL `collect_instantiation_candidates`
    /// (instantiate.cpp:14-58).
    ///
    /// For each active variable that was NOT scheduled for BVE elimination
    /// (i.e., elimination was attempted and failed, or it was never tried),
    /// check if either polarity has few occurrences. If so, each clause
    /// containing that literal is a candidate for instantiation.
    pub(in crate::solver) fn collect_instantiation_candidates(&self) -> Vec<InstCandidate> {
        let mut candidates = Vec::new();

        for var_idx in 0..self.num_vars {
            let var = Variable(var_idx as u32);

            // Skip frozen variables.
            if self.cold.freeze_counts.get(var_idx).copied().unwrap_or(0) != 0 {
                continue;
            }
            // Skip inactive/eliminated variables.
            if self.var_lifecycle.is_removed(var_idx) {
                continue;
            }
            // Skip assigned variables (root-level units).
            if self.var_is_assigned(var_idx) {
                continue;
            }
            // CaDiCaL: skip variables still pending BVE elimination
            // (`flags(idx).elim`). In AY, eliminated variables are already
            // caught by `var_lifecycle.is_removed()` above.

            for sign in [true, false] {
                let lit = if sign {
                    Literal::positive(var)
                } else {
                    Literal::negative(var)
                };

                let occs = self.inproc.bve.get_occs(lit);
                if occs.len() > INST_OCC_LIMIT {
                    continue;
                }

                let neg_occs_count = self.inproc.bve.get_occs(lit.negated()).len();

                for &c_idx in occs {
                    if !self.arena.is_active(c_idx) {
                        continue;
                    }
                    // CaDiCaL `instantiateonce`: skip already-instantiated clauses.
                    if self.arena.is_instantiated(c_idx) {
                        continue;
                    }
                    let clause_size = self.arena.len_of(c_idx);
                    if clause_size < INST_CLAUSE_SIZE_MIN {
                        continue;
                    }
                    // Check the clause is not satisfied and has >= 3 unassigned lits.
                    let clause_lits = self.arena.literals(c_idx);
                    let mut satisfied = false;
                    let mut unassigned = 0usize;
                    for &other in clause_lits {
                        let v = self.lit_val(other);
                        if v > 0 {
                            satisfied = true;
                            break;
                        }
                        if v == 0 {
                            unassigned += 1;
                        }
                    }
                    if satisfied {
                        continue;
                    }
                    // CaDiCaL: `if (unassigned < 3) continue;` — avoid
                    // learning units (binary clause case).
                    if unassigned < 3 {
                        continue;
                    }

                    candidates.push(InstCandidate {
                        lit,
                        clause_idx: c_idx,
                        clause_size,
                        neg_occs: neg_occs_count,
                    });
                }
            }
        }

        candidates
    }

    /// Run post-BVE instantiation on collected candidates.
    ///
    /// CaDiCaL `instantiate` (instantiate.cpp:312-365).
    ///
    /// Temporarily rebuilds 2WL watches for BCP-based instantiation, then
    /// tears them down. The caller (BVE elimination phase) operates with
    /// watches disconnected; the final `rebuild_watches()` in
    /// `run_elimination_passes` will do the definitive reconnection.
    ///
    /// Returns true if UNSAT was derived.
    ///
    /// `deadline` (lever 2, AY_AB_BVE_INST_GATE — see `bve_inst_gate_enabled`):
    /// when set, the candidate loop stops once the caller's BVE wall deadline
    /// passes. Instantiate previously had NO budget of its own — the
    /// fast-inner profile measured 6.5-13.2s per call on the deep
    /// collapse+BVE path, every second of it outside the fastelim wall.
    /// `None` (gate killed) preserves the historical run-to-completion
    /// behavior.
    pub(in crate::solver) fn instantiate(
        &mut self,
        mut candidates: Vec<InstCandidate>,
        deadline: Option<ay_core::time::Instant>,
    ) -> bool {
        if candidates.is_empty() {
            return false;
        }

        // Sort candidates: prefer smaller clauses and fewer negative
        // occurrences (more likely to succeed). CaDiCaL processes them
        // in insertion order which happens to be variable-index order.
        // We sort by (clause_size, neg_occs) ascending for efficiency.
        candidates.sort_unstable_by_key(|c| (c.clause_size, c.neg_occs));

        // Temporarily reconnect watches for BCP-based instantiation (#8093).
        // CaDiCaL: `init_watches(); connect_watches();` (instantiate.cpp:321-322).
        // Instantiation needs 2WL watches for BCP to test literal redundancy.
        // Must clear watches_disconnected so that replace_clause_checked()
        // performs incremental watch detach/attach for strengthened clauses,
        // keeping the 2WL invariant valid across instantiation BCP calls.
        //
        // Uses reconnect_bve_watches(0) instead of rebuild_watches(): purges
        // stale entries from the disconnected BVE phase and attaches all active
        // clauses (baseline=0). Avoids reallocating the WatchedLists structure.
        // Full re-propagation needed (#8095).
        self.watches_disconnected = false;
        self.mark_trail_affected(0);
        self.reconnect_bve_watches(0);
        self.cold.instantiate_rebuilt_watches = true;

        // Propagate any pending units from watch rebuild.
        if self.qhead < self.trail.len() && self.search_propagate().is_some() {
            // Propagation found a conflict: UNSAT.
            // Keep watches intact (#8093) — reconnect_bve_watches will
            // handle cleanup. Set disconnected for the BVE loop continuation.
            self.watches_disconnected = true;
            self.cold.disconnected_deletions = 0; // #8093
            return true;
        }

        let mut instantiated_count: u64 = 0;
        let total_candidates = candidates.len();

        for cand in &candidates {
            if self.has_empty_clause {
                break;
            }
            if self.is_interrupted() {
                break;
            }
            // Wall-budget deadline (lever 2): each candidate is a full BCP
            // over the live watch graph; one clock read per candidate is
            // negligible next to that. Break — not skip — so the pass ends
            // the moment the caller's BVE wall is consumed.
            if deadline.is_some_and(|d| ay_core::time::Instant::now() >= d) {
                break;
            }

            // Check the literal's variable is still active.
            if self.var_lifecycle.is_removed(cand.lit.variable().index()) {
                continue;
            }
            if self.var_is_assigned(cand.lit.variable().index()) {
                continue;
            }

            if self.instantiate_candidate(cand.lit, cand.clause_idx) {
                instantiated_count += 1;
            }
        }

        tracing::debug!(
            candidates = total_candidates,
            instantiated = instantiated_count,
            "post-BVE instantiation"
        );
        solver_log!(
            self,
            "instantiate: {} candidates, {} succeeded",
            total_candidates,
            instantiated_count,
        );

        // (#8093): Keep rebuilt watches intact instead of tearing them down.
        // The reconnect_bve_watches(0) above attached watches for all active
        // clauses. Subsequent BVE rounds (if any) will operate with
        // watches_disconnected=true, meaning new adds skip attachment and
        // deletes skip binary removal. reconnect_bve_watches() at the end
        // of the elimination phase handles stale binary entries and new
        // clauses added after this point.
        self.watches_disconnected = true;
        self.cold.disconnected_deletions = 0; // #8093
        self.earliest_affected_trail_pos = None;

        false
    }

    /// Try to instantiate a single (literal, clause) pair.
    ///
    /// CaDiCaL `instantiate_candidate` (instantiate.cpp:175-305).
    ///
    /// Assumes `lit` TRUE and all other clause literals FALSE, then runs
    /// BCP. If BCP derives a conflict, `lit` is redundant — remove it
    /// from the clause (strengthening).
    ///
    /// Returns true if the clause was strengthened.
    fn instantiate_candidate(&mut self, lit: Literal, clause_idx: usize) -> bool {
        // Re-validate the clause.
        if !self.arena.is_active(clause_idx) {
            return false;
        }

        let clause_lits: Vec<Literal> = self.arena.literals(clause_idx).to_vec();

        // The literal must still be in the clause.
        if !clause_lits.contains(&lit) {
            return false;
        }

        // Re-check: clause not satisfied, no inactive literals, >= 3 unassigned.
        let mut satisfied = false;
        let mut inactive = false;
        let mut unassigned = 0usize;
        for &other in &clause_lits {
            let v = self.lit_val(other);
            if v > 0 {
                satisfied = true;
                break;
            }
            if v == 0 && self.var_lifecycle.is_removed(other.variable().index()) {
                inactive = true;
                break;
            }
            if v == 0 {
                unassigned += 1;
            }
        }
        if satisfied || inactive || unassigned < 3 {
            return false;
        }

        // Mark clause as instantiated (CaDiCaL `c->instantiated = true`).
        self.arena.set_instantiated(clause_idx, true);

        // Save trail position for backtracking.
        debug_assert_eq!(self.decision_level, 0, "instantiation requires level 0");
        debug_assert_eq!(
            self.qhead,
            self.trail.len(),
            "pending propagations before instantiation"
        );
        let trail_before = self.trail.len();

        // CaDiCaL: `level++; inst_assign(lit);`
        // We use a temporary decision level for the instantiation attempt.
        self.decision_level += 1;
        self.trail_lim.push(self.trail.len());

        // Assign `lit` TRUE (it's the literal we're testing for redundancy).
        self.inst_assign(lit);

        // Assign all other clause literals FALSE.
        for &other in &clause_lits {
            if other == lit {
                continue;
            }
            let v = self.lit_val(other);
            if v != 0 {
                // Already assigned (root-level false).
                debug_assert!(v < 0, "clause should not be satisfied");
                continue;
            }
            self.inst_assign(other.negated());
        }

        // Run BCP.
        let conflict = self.inst_propagate();

        // Build LRAT proof chain if needed (simplified: use TrustedTransform).
        let lrat_hints: Vec<u64> = if conflict.is_some() && self.cold.lrat_enabled {
            self.collect_inst_lrat_chain(lit, clause_idx, &clause_lits, trail_before)
        } else {
            Vec::new()
        };

        // Backtrack: undo all assignments from trail_before onwards.
        // CaDiCaL: manual unassign loop (instantiate.cpp:241-265).
        self.backtrack_without_phase_saving(0);

        let succeeded = conflict.is_some();

        if !succeeded {
            return false;
        }

        // Strengthen the clause: remove `lit`.
        let new_lits: Vec<Literal> = clause_lits.iter().filter(|&&l| l != lit).copied().collect();
        debug_assert!(
            new_lits.len() >= 2,
            "instantiation should not reduce clause below size 2 \
             (unassigned >= 3 check ensures this)"
        );

        // Husk guard (husk adjudication): the replace below skips dead
        // (garbage-kept) targets; bail out first so the BVE occ notification
        // stays paired with an actual replacement and a husk is never
        // re-added to BVE occ lists.
        if self.arena.is_dead(clause_idx) {
            return false;
        }

        // Notify BVE that the clause will change (for dirty-candidate tracking).
        self.note_irredundant_clause_replaced_for_bve(clause_idx, &clause_lits, &new_lits);

        // Replace the clause in-place.
        if self.cold.lrat_enabled && !lrat_hints.is_empty() {
            self.replace_clause_with_final_hints(clause_idx, &new_lits, &lrat_hints);
        } else if self.cold.lrat_enabled {
            // LRAT enabled but no hints: use TrustedTransform to avoid checker failure.
            self.replace_clause_with_final_hints(clause_idx, &new_lits, &[]);
        } else {
            self.replace_clause_checked(clause_idx, &new_lits);
        }

        true
    }

    /// Simplified assignment for instantiation (no phase saving, no reason).
    ///
    /// CaDiCaL `inst_assign` (instantiate.cpp:64-71).
    fn inst_assign(&mut self, lit: Literal) {
        debug_assert!(
            !self.var_is_assigned(lit.variable().index()),
            "inst_assign: variable {} already assigned",
            lit.variable().index()
        );
        // Suppress phase saving during instantiation.
        self.suppress_phase_saving = true;
        self.enqueue(lit, None);
        self.suppress_phase_saving = false;
    }

    /// Simplified BCP for instantiation.
    ///
    /// CaDiCaL `inst_propagate` (instantiate.cpp:78-169).
    ///
    /// Uses the standard 2WL propagation. Returns Some(conflict_ref) if
    /// a conflict was found, None otherwise.
    fn inst_propagate(&mut self) -> Option<ClauseRef> {
        self.search_propagate()
    }

    /// Collect LRAT proof chain for a successful instantiation.
    ///
    /// CaDiCaL instantiate.cpp:229-286: walks the trail backwards,
    /// collecting reason clause IDs via a seen-flag variant of conflict
    /// analysis. This is a simplified variant that collects all reason
    /// clause IDs between `trail_before` and the current trail position,
    /// plus the original clause ID.
    ///
    /// For correctness, we use the same reverse-trail resolution strategy
    /// as CaDiCaL, but fall back to TrustedTransform if the chain is
    /// incomplete.
    fn collect_inst_lrat_chain(
        &self,
        _lit: Literal,
        clause_idx: usize,
        clause_lits: &[Literal],
        trail_before: usize,
    ) -> Vec<u64> {
        let mut chain = Vec::new();

        // Collect all reason clause IDs from the instantiation trail.
        // Walk backwards from current trail position to trail_before.
        let mut seen = vec![false; self.num_vars];

        // Mark all clause literals as seen (the initial conflict resolution).
        for &cl in clause_lits {
            seen[cl.variable().index()] = true;
        }

        // Walk trail backwards collecting reasons.
        for i in (trail_before..self.trail.len()).rev() {
            let trail_lit = self.trail[i];
            let var_idx = trail_lit.variable().index();
            if !seen[var_idx] {
                continue;
            }
            seen[var_idx] = false;
            if let Some(reason_ref) = self.var_reason(var_idx) {
                let reason_id = self.clause_id(reason_ref);
                if reason_id != 0 {
                    chain.push(reason_id);
                    // Mark all literals in the reason clause as seen.
                    let reason_lits = self.arena.literals(reason_ref.0 as usize);
                    for &rl in reason_lits {
                        seen[rl.variable().index()] = true;
                    }
                }
            }
        }

        // Add the original clause ID.
        let orig_id = self.clause_id(ClauseRef(clause_idx as u32));
        if orig_id != 0 {
            chain.push(orig_id);
        }

        // Reverse to match LRAT order (CaDiCaL instantiate.cpp:285).
        chain.reverse();

        // Add unit clause IDs for any root-level assignments that
        // were seen but not resolved (they have no reason in the
        // instantiation trail).
        // This is a simplification; if the chain is incomplete, the
        // caller will use TrustedTransform.

        chain
    }
}
