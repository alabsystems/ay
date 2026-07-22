// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model shrinking: retract don't-care assignments from a satisfying state.
//!
//! After a SAT answer, IC3/PDR-style consumers want the *smallest* partial
//! assignment (cube) that still forces the query's outcome. Rather than paying
//! for a fresh SAT call per literal, they ask this module a cheaper question,
//! variable by variable: "is this assignment a don't-care — can it be withdrawn
//! while every clause keeps a reason to be satisfiable?" [`Solver::flip_to_none`]
//! answers for one variable; [`Solver::minimize_model`] bulk-retracts every
//! assignment it soundly can and returns the surviving literals as a cube.
//! A generalized (smaller) cube lets the induction engine block a whole family
//! of states per query instead of one, which is where the primitive earns its
//! keep: each answer is bounded local work on solver state, never a search.
//!
//! A clause counts as *supported* by the current partial assignment when
//! either (S1) one of its literals is true, or (S2) — only under an active
//! IC3 domain restriction — one of its literals is unassigned on a variable
//! outside the (BCP-cone-expanded) domain, i.e. a variable the current query
//! does not range over and which can be freely satisfied later. Without a
//! domain restriction an unassigned literal is *not* support: the remaining
//! assignment must itself satisfy every clause.
//!
//! The delicate part is the two-watched-literal invariant (Een & Sorensson,
//! "An Extensible SAT-solver", SAT 2003 — the MiniSat design): every clause of
//! length >= 2 watches two distinct literals, and a clause that is not
//! satisfied must keep both watched literals non-false, because propagation
//! only re-examines a clause when one of its watches becomes false. Retracting
//! a *true* literal can silently break this: a clause that was satisfied by
//! the retracted literal is allowed to be watching false literals (the blocker
//! fast path parks watches on falsified literals of satisfied clauses), and
//! once its last true literal is withdrawn those parked false watches would
//! let future BCP miss units or conflicts. So every successful retraction
//! re-establishes the invariant for the clauses it touched, moving parked
//! false watches onto non-false literals.
//!
//! Both operations refuse to touch root-level (decision level 0) assignments:
//! those are consequences of the formula itself, not choices of this model.

use super::*;

/// Per-clause support census entry used by the bulk minimizer.
///
/// `true_count` is the number of *occurrences* of currently-true literals in
/// the clause (duplicates counted), kept current as retractions commit.
/// `external` records whether the clause holds an unassigned literal outside
/// the active domain (S2 support) — frozen for the whole minimization, since
/// retraction never moves a variable out of the domain and never assigns
/// anything.
struct LiftClause {
    off: u32,
    true_count: u32,
    external: bool,
}

impl Solver {
    /// Try to withdraw `var`'s assignment while keeping every live clause
    /// supported (S1/S2 as defined in the module doc).
    ///
    /// Returns:
    /// - `true` if `var` was already unassigned (trivially a don't-care;
    ///   nothing changes), or if its assignment was successfully retracted.
    /// - `false` if `var` is fixed at decision level 0, if some clause relies
    ///   on `var` as its sole support, or if the solver is not in a quiescent
    ///   post-SAT state. On `false` the solver is untouched: the verdict is
    ///   computed on a read-only pass and state is only mutated after every
    ///   affected clause has produced a witness.
    ///
    /// On success the variable reads as unassigned everywhere (`value()`,
    /// literal values, the trail), no other assignment changes, and the
    /// watched-literal invariant holds for every clause, so later solves,
    /// clause additions, and further retractions behave normally.
    pub fn flip_to_none(&mut self, var: Variable) -> bool {
        let vi = var.index();
        if vi >= self.num_vars {
            // Out-of-range variables cannot hold an assignment worth keeping;
            // refuse rather than panic.
            return false;
        }
        if !self.var_is_assigned(vi) {
            // Already out of the model: trivially a don't-care.
            return true;
        }
        if self.var_data[vi].level == 0 {
            // Root-level assignments are consequences of the formula and are
            // immutable here.
            return false;
        }
        if !self.lift_state_ready() {
            return false;
        }

        let pos = Literal::positive(var);
        let true_lit = if self.lit_val(pos) > 0 {
            pos
        } else {
            pos.negated()
        };

        // Read-only verification pass: every live clause that contains the
        // true literal of `var` (the only clauses whose support can degrade)
        // must exhibit a witness that survives the retraction — another true
        // literal, or an unassigned out-of-domain literal. Collect the clauses
        // that will be left non-satisfied but externally supported; those are
        // the ones whose watches may need repair after the retraction.
        let mut external_only: Vec<u32> = Vec::new();
        for off in self.arena.live_indices() {
            let lits = self.arena.literals(off);
            if !lits.contains(&true_lit) {
                continue;
            }
            let mut other_true = false;
            let mut external = false;
            for &l in lits {
                if l == true_lit {
                    // All copies of the retracted literal become unassigned;
                    // `var` stays inside the active domain (it was assigned by
                    // a domain-restricted search), so it cannot serve as S2
                    // support either.
                    continue;
                }
                let v = self.lit_val(l);
                if v > 0 {
                    other_true = true;
                    break;
                }
                if v == 0 && !external {
                    external = self.lift_external_support(l);
                }
            }
            if other_true {
                continue;
            }
            if !external {
                // Sole support: the retraction is impossible. Nothing has
                // been mutated, so state is exactly as before the call.
                return false;
            }
            external_only.push(off as u32);
        }

        // Commit: withdraw the assignment, then restore the watch invariant
        // for the clauses that lost their last true literal, then drop the
        // literal from the trail.
        self.retire_lift_assignment(var, true_lit);
        for off in external_only {
            self.restore_nonfalse_watches(off as usize);
        }
        self.compact_trail_after_lift();
        true
    }

    /// Bulk lifting: starting from the held model, retract every assignment
    /// that can be withdrawn soundly, keeping `important_vars` and all
    /// root-level assignments, and return the remaining assignment as a cube
    /// (each still-assigned variable's literal in its assigned polarity).
    ///
    /// The result is a subset of the model's literals, so conjoining it with
    /// the formula stays satisfiable. When the solver does not hold a usable
    /// model state, an empty vector is returned and nothing is changed.
    pub fn minimize_model(&mut self, important_vars: &[Variable]) -> Vec<Literal> {
        if !self.lift_state_ready() {
            return Vec::new();
        }

        let trail_len = self.trail.len();
        let root_end = self.trail_lim.first().copied().unwrap_or(trail_len);
        // Candidates are the non-root trail suffix; snapshot it because
        // retractions edit `vals` as we go (the trail itself is compacted once
        // at the end).
        let candidates: Vec<Literal> = self.trail[root_end.min(trail_len)..].to_vec();
        if candidates.is_empty() {
            // Everything is fixed at the root: the cube is the full assignment.
            return self.trail.clone();
        }

        let mut keep = vec![false; self.num_vars];
        for &v in important_vars {
            if v.index() < self.num_vars {
                keep[v.index()] = true;
            }
        }

        // Support census + occurrence index (CSR) over the live clauses:
        // for every clause, how many true-literal occurrences it currently
        // has and whether it enjoys external (S2) support; for every literal
        // that is currently true, which clauses contain it. One occurrence
        // entry is pushed per literal occurrence, so duplicate literals in a
        // clause are represented faithfully (entries for the same clause end
        // up adjacent in a literal's bucket).
        let num_lit_slots = 2 * self.num_vars;
        let mut clauses: Vec<LiftClause> = Vec::new();
        let mut bucket_len = vec![0u32; num_lit_slots];
        for off in self.arena.live_indices() {
            let lits = self.arena.literals(off);
            let mut true_count = 0u32;
            let mut external = false;
            for &l in lits {
                let v = self.lit_val(l);
                if v > 0 {
                    true_count += 1;
                    bucket_len[l.index()] += 1;
                } else if v == 0 && !external {
                    external = self.lift_external_support(l);
                }
            }
            if true_count > 0 {
                clauses.push(LiftClause {
                    off: off as u32,
                    true_count,
                    external,
                });
                // Undo the bucket reservations only when the clause is not
                // indexed; indexed clauses need one slot per true occurrence.
            } else {
                for &l in lits {
                    if self.lit_val(l) > 0 {
                        // Unreachable (true_count == 0), kept for symmetry.
                        bucket_len[l.index()] -= 1;
                    }
                }
            }
        }
        let mut starts = vec![0u32; num_lit_slots + 1];
        for i in 0..num_lit_slots {
            starts[i + 1] = starts[i] + bucket_len[i];
        }
        let mut cursor = starts.clone();
        let mut items = vec![0u32; starts[num_lit_slots] as usize];
        for (dense, c) in clauses.iter().enumerate() {
            for &l in self.arena.literals(c.off as usize) {
                if self.lit_val(l) > 0 {
                    let li = l.index();
                    items[cursor[li] as usize] = dense as u32;
                    cursor[li] += 1;
                }
            }
        }

        // Examine candidates most-recent-first: late assignments are the
        // decisions and deep implications most likely to be don't-cares. Any
        // order is sound; this one is deterministic.
        let mut removed_any = false;
        for &lit in candidates.iter().rev() {
            let var = lit.variable();
            let vi = var.index();
            if keep[vi] || !self.var_is_assigned(vi) {
                continue;
            }
            if self.var_data[vi].level == 0 {
                // Chronological backtracking can leave root-level literals
                // above the root prefix; they are immutable like any other
                // root assignment.
                continue;
            }
            debug_assert!(self.lit_val(lit) > 0, "trail literal must be true");
            let s = starts[lit.index()] as usize;
            let e = starts[lit.index() + 1] as usize;

            // Verify: every clause containing this true literal must keep a
            // witness after losing all `dup` of its occurrences — another
            // true occurrence or external support.
            let mut ok = true;
            let mut i = s;
            while i < e {
                let dense = items[i] as usize;
                let mut dup = 1usize;
                while i + dup < e && items[i + dup] as usize == dense {
                    dup += 1;
                }
                let c = &clauses[dense];
                if !c.external && (c.true_count as usize) < dup + 1 {
                    ok = false;
                    break;
                }
                i += dup;
            }
            if !ok {
                continue;
            }

            // Commit this retraction: update the census and repair watches of
            // clauses that just lost their last true literal (externally
            // supported by the verification above).
            self.retire_lift_assignment(var, lit);
            for item in &items[s..e] {
                let dense = *item as usize;
                clauses[dense].true_count -= 1;
                if clauses[dense].true_count == 0 {
                    debug_assert!(clauses[dense].external);
                    let off = clauses[dense].off as usize;
                    self.restore_nonfalse_watches(off);
                }
            }
            removed_any = true;
        }

        if removed_any {
            self.compact_trail_after_lift();
        }
        self.trail.clone()
    }

    /// Quiescence gate shared by both entry points: retraction assumes a
    /// completed solve (propagation at fixpoint, watches connected). Anything
    /// else gets a graceful refusal instead of state surgery.
    #[inline]
    fn lift_state_ready(&self) -> bool {
        !self.has_empty_clause && !self.watches_disconnected && self.qhead == self.trail.len()
    }

    /// S2 support test for an *unassigned* literal: only meaningful under an
    /// active domain restriction, and only for variables outside the
    /// (BCP-cone-expanded) domain — those are external to the query and can
    /// be satisfied later. Mirrors the domain semantics of `set_domain`.
    #[inline]
    fn lift_external_support(&self, lit: Literal) -> bool {
        match &self.active_domain {
            Some(domain) => {
                let vi = lit.variable().index();
                vi < domain.len() && !domain[vi]
            }
            None => false,
        }
    }

    /// Withdraw a single assignment from `vals` and heuristic bookkeeping.
    ///
    /// Mirrors what backtracking does per variable — clear both value slots,
    /// save the model polarity as the preferred phase, drop any lazy
    /// reimplication note, and make the variable decidable again (VSIDS heap,
    /// VMTF, and the domain bucket queue when active). The trail entry is
    /// *not* touched here; callers run [`Self::compact_trail_after_lift`]
    /// once after all retractions.
    fn retire_lift_assignment(&mut self, var: Variable, true_lit: Literal) {
        let vi = var.index();
        let base = vi * 2;
        ay_prefetch::val_set(&mut self.vals, base, 0);
        ay_prefetch::val_set(&mut self.vals, base + 1, 0);
        self.phase[vi] = true_lit.sign_i8();
        self.lambda[vi] = None;
        if self.var_lifecycle.is_removed(vi) {
            // Eliminated variables must never re-enter decision heuristics.
            return;
        }
        self.vsids.insert_into_heap(var);
        self.vsids.vmtf_on_unassign(var);
        if self.bucket_queue_active && !self.vsids.bucket_queue_contains(var) {
            if let Some(ref domain) = self.active_domain {
                if vi < domain.len() && domain[vi] {
                    self.vsids.bucket_queue_insert(var);
                }
            }
        }
    }

    /// Re-establish the two-watched-literal invariant for live clause `off`
    /// after it lost its last true literal but kept external (S2) support:
    /// both watch slots (arena positions 0 and 1) must hold non-false
    /// literals, or future propagation could miss this clause becoming unit.
    ///
    /// The verification pass guarantees a non-false replacement exists: the
    /// freshly-unassigned literal and the external witness are distinct and
    /// both non-false. Binary clauses need nothing — their watches are their
    /// two literals, which are exactly the unassigned pair.
    fn restore_nonfalse_watches(&mut self, off: usize) {
        let len = self.arena.len_of(off);
        if len < 3 {
            return;
        }
        for slot in 0..2 {
            let watched = self.arena.literal(off, slot);
            if self.lit_val(watched) >= 0 {
                continue;
            }
            let co_watch = self.arena.literal(off, 1 - slot);
            // Find a non-false literal in the tail to take over this watch.
            let mut replacement = None;
            for k in 2..len {
                let cand = self.arena.literal(off, k);
                if self.lit_val(cand) >= 0 && cand != co_watch {
                    replacement = Some((k, cand));
                    break;
                }
            }
            let Some((k, cand)) = replacement else {
                debug_assert!(
                    false,
                    "BUG: externally supported clause {off} has no replacement watch"
                );
                continue;
            };
            // Unhook the parked watch entry for this clause. Long entries live
            // after the binary prefix of the list (binary-first layout), and
            // `swap_remove` preserves that partition.
            let list_len = self.watches.len_of(watched);
            let mut entry_idx = None;
            for i in self.watches.binary_count_of(watched)..list_len {
                if !self.watches.is_binary(watched, i)
                    && self.watches.clause_ref(watched, i).0 as usize == off
                {
                    entry_idx = Some(i);
                    break;
                }
            }
            let Some(i) = entry_idx else {
                debug_assert!(
                    false,
                    "BUG: watched literal of clause {off} carries no watch entry"
                );
                continue;
            };
            self.watches.swap_remove(watched, i);
            self.arena.swap_literals(off, slot, k);
            self.watches
                .add_watch(cand, Watcher::new(ClauseRef(off as u32), co_watch));
        }
    }

    /// Rebuild the trail after retractions: drop entries whose variable is no
    /// longer assigned, remapping every trail-position-valued piece of state
    /// (`trail_pos`, `trail_lim`, `qhead`, `no_conflict_until`) through the
    /// compaction. The decision-level structure is preserved — a level whose
    /// literals were all retracted simply becomes an empty span, which the
    /// normal backtracking machinery already tolerates.
    fn compact_trail_after_lift(&mut self) {
        let old_len = self.trail.len();
        let old_qhead = self.qhead;
        let old_ncu = self.no_conflict_until;
        let mut lim_idx = 0usize;
        let mut write = 0usize;
        let mut new_qhead = None;
        let mut new_ncu = None;
        let mut first_removed = None;
        for read in 0..old_len {
            while lim_idx < self.trail_lim.len() && self.trail_lim[lim_idx] == read {
                self.trail_lim[lim_idx] = write;
                lim_idx += 1;
            }
            if read == old_qhead {
                new_qhead = Some(write);
            }
            if read == old_ncu {
                new_ncu = Some(write);
            }
            let lit = self.trail[read];
            let vi = lit.variable().index();
            if self.var_is_assigned(vi) {
                debug_assert!(
                    self.var_lifecycle.is_removed(vi) || self.lit_val(lit) > 0,
                    "BUG: surviving trail literal {lit:?} is not true"
                );
                self.trail[write] = lit;
                self.var_data[vi].trail_pos = write as u32;
                write += 1;
            } else if first_removed.is_none() {
                first_removed = Some(read);
            }
        }
        while lim_idx < self.trail_lim.len() {
            // Remaining markers pointed at (or past) the old trail end.
            self.trail_lim[lim_idx] = write;
            lim_idx += 1;
        }
        self.trail.truncate(write);
        self.qhead = new_qhead.unwrap_or(write);
        self.no_conflict_until = new_ncu.unwrap_or(write);
        if let Some(fr) = first_removed {
            // Root-prefix positions below the first removal are unshifted;
            // clamp the LRAT root-unit cursor so shifted entries above it are
            // revisited rather than skipped.
            self.cold.lrat_level0_unit_materialize_cursor =
                self.cold.lrat_level0_unit_materialize_cursor.min(fr);
        }
        // Reason marks map clauses to trail state that just moved; force a
        // rebuild before the next consumer reads them.
        self.invalidate_reason_clause_marks();
    }
}
