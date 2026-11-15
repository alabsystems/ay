// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scope management (push/pop) for LRA.
//!
//! Incremental push/pop with trail-based bound restoration. Full/soft reset
//! and structural snapshot operations live in nested `state`; constructor,
//! config, and initialization are in `lifecycle`.

mod state;

use super::*;

impl LraSolver {
    /// Bound restorations the next `depth` `pop`s would replay.
    ///
    /// Read-only diagnostics with no solving semantics. It exists because a
    /// caller that pushes its own tentative scopes (NRA's sign-cut/patch
    /// scope) has no other way to tell "this scope is carrying live bounds
    /// that the pop will undo" from "this scope is empty": every other
    /// observable is either a monotone counter, which a pop never decrements,
    /// or a variable value, which `pop_inner` leaves untouched.
    pub fn bounds_in_top_scopes(&self, depth: usize) -> usize {
        if depth == 0 {
            return 0;
        }
        let index = self.scopes.len().saturating_sub(depth);
        match self.scopes.get(index) {
            Some(&(trail_mark, _)) => self.trail.len().saturating_sub(trail_mark),
            None => 0,
        }
    }

    pub(crate) fn push_inner(&mut self) {
        trace!(target: "ay::lra", depth = self.scopes.len() + 1, "push");
        // #lra-scope-trail: atoms asserted since the last check are applied
        // NOW, so their bound-trail entries sit below the marks recorded
        // next — in the scope of their assertion. See
        // `apply_pending_atoms_before_push` for the contract and the bug.
        self.apply_pending_atoms_before_push();
        self.scopes
            .push((self.trail.len(), self.asserted_trail.len()));
        // #inc-implied-trail: lockstep with `scopes`.
        self.implied_trail_scopes.push(self.implied_trail.len());
        // #inc-prop-trail: lockstep with `scopes`.
        self.propagated_trail_scopes
            .push(self.propagated_trail.len());
        self.cross_theory_asserted_scopes
            .push(self.cross_theory_asserted_trail.len());
        self.disequality_trail_scopes
            .push(self.disequality_trail.len());
        self.shared_disequality_trail_scopes
            .push(self.shared_disequality_trail.len());
        self.persistent_unsupported_scope_marks
            .push(self.persistent_unsupported_trail.len());
        self.last_simplex_feasible_scopes
            .push(self.last_simplex_feasible);
    }

    pub(crate) fn pop_inner(&mut self) {
        let Some((trail_mark, asserted_mark)) = self.scopes.pop() else {
            return;
        };
        trace!(target: "ay::lra", depth = self.scopes.len(), "pop");
        // Trail replay below restores (widens) bounds — one bump per pop is
        // enough to invalidate the LIA algebraic-detection memo.
        self.bump_bound_revision();

        // Track which variables had bounds restored during trail replay.
        // Used for targeted touched-row marking below (#8900).
        let mut changed_vars: SmallVec<[u32; 16]> = SmallVec::new();
        while self.trail.len() > trail_mark {
            let (var, which_bound, old_value) = self.trail.pop().unwrap();
            if (var as usize) < self.vars.len() {
                changed_vars.push(var);
                match which_bound {
                    BoundType::Lower => self.vars[var as usize].lower = old_value,
                    BoundType::Upper => self.vars[var as usize].upper = old_value,
                }
            }
        }
        let mut unasserted_atoms: Vec<TermId> = Vec::new();
        while self.asserted_trail.len() > asserted_mark {
            if let Some(key) = self.asserted_trail.pop() {
                if let Some(&val) = self.asserted.get(&key) {
                    self.bound_atoms.remove(&(key, val));
                }
                self.asserted.remove(&key);
                unasserted_atoms.push(key);
            }
        }
        if let Some(cross_mark) = self.cross_theory_asserted_scopes.pop() {
            while self.cross_theory_asserted_trail.len() > cross_mark {
                if let Some((key, prev)) = self.cross_theory_asserted_trail.pop() {
                    match prev {
                        None => {
                            self.cross_theory_asserted.remove(&key);
                        }
                        Some(value) => {
                            self.cross_theory_asserted.insert(key, value);
                        }
                    }
                }
            }
        }
        // #8765: Pop-surviving disequality atoms.
        //
        // The classic design pushed a position mark on every `push()` and
        // truncated back to it on `pop()`. That works when a disequality is
        // first parsed *inside* the pushed scope — its entry sits above the
        // mark and is correctly dropped. But an atom like
        // `(distinct loc1 loc2)` asserted *before* any push is first parsed
        // during a check-sat that happens *inside* a pushed scope. At that
        // point `disequality_trail.len()` is above every recorded mark, so
        // pop() truncates the entry away even though the atom itself is
        // still in `self.asserted` at the outer scope.
        //
        // After the trail is lost, `process_check_atoms_inner` never
        // re-parses the surviving atom (its bounds are cached in
        // `bound_atoms` and `last_check_trail_pos` is set to the new trail
        // length), so the disequality is invisible to `check_disequalities`
        // and `discover_model_value_equalities`. The DPLL layer reports SAT
        // with `loc1 == loc2 == 0`, which the #8373 model validator then
        // downgrades to Unknown.
        //
        // Fix (Z3's `assume_eqs`-style re-propagation after pop, per
        // the development design notes):
        // after the DPLL-level asserted-trail rewind removed the entries
        // that truly left `self.asserted`, drop the scope mark but *retain*
        // any trail entries whose `(term, value)` is still live in
        // `self.asserted`. Entries whose atom was unasserted have already
        // been removed from `self.asserted` above (see `unasserted_atoms`
        // loop), so this filter is exactly equivalent to the old truncation
        // for the legitimate case and additionally preserves the outer-scope
        // survivors that the truncation used to drop.
        if self.disequality_trail_scopes.pop().is_some() {
            // An entry can die only when its atom was unasserted by the
            // rewind above or its asserted value flipped in place since
            // the last scan (`asserted_value_flips`): `asserted` loses
            // keys nowhere else in a pop, entries are pushed only for
            // currently-asserted atoms, and resets/restore bump the flip
            // counter to force a rescan. When neither happened the
            // retain is a no-op, so skip the O(trail) scan outright —
            // paid on every backtrack, it was a top stack on Certora
            // 11775. With unasserts but no flips, liveness is exactly
            // "term not unasserted", tested against the small sorted
            // unasserted set instead of the full asserted map.
            let flips_changed = self.asserted_value_flips != self.diseq_retain_flip_snapshot;
            if !unasserted_atoms.is_empty() || flips_changed {
                #[cfg(debug_assertions)]
                let before: Vec<(TermId, bool)> = self
                    .disequality_trail
                    .iter()
                    .map(|(term, _expr, value)| (*term, *value))
                    .collect();
                self.diseq_retain_scans += 1;
                if flips_changed {
                    self.disequality_trail
                        .retain(|(term, _expr, value)| self.asserted.get(term) == Some(value));
                } else {
                    unasserted_atoms.sort_unstable_by_key(|term| term.0);
                    unasserted_atoms.dedup();
                    self.disequality_trail.retain(|(term, _expr, _value)| {
                        unasserted_atoms
                            .binary_search_by_key(&term.0, |dead| dead.0)
                            .is_err()
                    });
                }
                self.diseq_retain_flip_snapshot = self.asserted_value_flips;
                #[cfg(debug_assertions)]
                {
                    let expected: Vec<(TermId, bool)> = before
                        .into_iter()
                        .filter(|(term, value)| self.asserted.get(term) == Some(value))
                        .collect();
                    let actual: Vec<(TermId, bool)> = self
                        .disequality_trail
                        .iter()
                        .map(|(term, _expr, value)| (*term, *value))
                        .collect();
                    debug_assert_eq!(
                        actual, expected,
                        "optimized disequality retain diverged from the full predicate"
                    );
                }
            }
        }
        if let Some(shared_diseq_mark) = self.shared_disequality_trail_scopes.pop() {
            self.shared_disequality_trail.truncate(shared_diseq_mark);
        }
        self.pending_diseq_splits.clear();
        self.pending_expr_splits.clear();
        self.propagated_equality_pairs.clear();
        self.propagated_disequality_pairs.clear();
        self.pending_equalities.clear();
        self.fixed_term_value_table.clear();
        self.fixed_term_value_members.clear();
        self.pending_fixed_term_equalities.clear();
        self.pending_offset_equalities.clear();
        self.pending_propagations.clear();
        self.pending_bound_refinements.clear();
        // #inc-prop-trail: remove exactly the propagation markers inserted in
        // the popped scopes (their literals were just unassigned by the DPLL
        // backtrack) instead of wholesale-clearing. Outer-scope markers
        // persist — their literals remain assigned, so re-sending is
        // correctly suppressed. This kills the post-backtrack re-derivation
        // + re-insert flood that dominated the deep-BMC floor profile.
        let prop_mark = self.propagated_trail_scopes.pop().unwrap_or(0);
        while self.propagated_trail.len() > prop_mark {
            if let Some(entry) = self.propagated_trail.pop() {
                self.propagated_atoms.remove(&entry);
            }
        }
        self.propagation_dirty_vars.clear();
        // #8003: Targeted propagation dirty marking on pop. Instead of
        // marking ALL atom_index+compound_use_index vars as dirty (O(total_vars)),
        // only mark variables whose bounds actually changed. Atoms referencing
        // unchanged variables would compute the same intervals. The DPLL layer
        // handles backtracking of previously-propagated literals.
        //
        // Fallback to full scan when many vars changed (>25% of total) to
        // avoid O(changed * neighbors) being worse than O(total).
        //
        // #inc-pop-churn: a pop that restored NO bounds and unasserted NO atoms
        // changed nothing any atom's interval depends on — leave the dirty set
        // empty instead of the O(total_atoms) full extend (which forced a full
        // re-propagation sweep after every theory-invisible backtrack). When
        // atoms WERE unasserted (with or without bound changes), the original
        // branches below run unchanged, preserving the #6588 compound wakeup
        // guarantee. (#uflia-eager-sweep: the eager DPLL(T) lanes OPT OUT of
        // this and the other pop-persistence slices via
        // `eager_repropagate_on_pop` — see `eager_repropagate_reset_after_pop`
        // at the end of this function.)
        if changed_vars.is_empty() && unasserted_atoms.is_empty() && !self.eager_repropagate_on_pop
        {
            // theory-invisible pop: nothing to mark
        } else if changed_vars.len() * 4 >= self.vars.len() || changed_vars.is_empty() {
            self.propagation_dirty_vars
                .extend(self.atom_index.keys().copied());
            self.propagation_dirty_vars
                .extend(self.compound_use_index.keys().copied());
        } else {
            for &var in &changed_vars {
                if self.atom_index.contains_key(&var) {
                    self.propagation_dirty_vars.insert(var);
                }
                if self.compound_use_index.contains_key(&var) {
                    self.propagation_dirty_vars.insert(var);
                }
                // Also mark compound slack vars that reference this changed var,
                // since their intervals depend on it.
                if let Some(compounds) = self.compound_use_index.get(&var) {
                    for cref in compounds {
                        self.propagation_dirty_vars.insert(cref.slack);
                    }
                }
            }
        }
        // #inc-implied-trail: rewind derived implied-bound writes to the scope
        // mark instead of wholesale-clearing the overlay. Restored values are
        // valid by monotonicity (their antecedent direct bounds / rows still
        // hold at the outer scope). This eliminates the full re-derivation
        // sweep that previously followed every CDCL backtrack.
        //
        // Dirty-row pop: every variable whose slot this rewind changed is
        // stamped and its rows touched, so the next `compute_implied_bounds`
        // re-derives exactly what the popped scope may have displaced (a
        // bound derived inside the scope from outer-scope antecedents is
        // popped here although still valid — its row is now dirty and the
        // next call restores it). Rows containing no changed variable have
        // identical inputs and would derive nothing new, so they are not
        // swept; `tests/dirty_row_sweep.rs` checks this against a full
        // re-derivation.
        let implied_mark = self.implied_trail_scopes.pop().unwrap_or(0);
        let mut rewound_vars: SmallVec<[u32; 16]> = SmallVec::new();
        while self.implied_trail.len() > implied_mark {
            let (var, is_upper, old) = self.implied_trail.pop().unwrap();
            let vi = var as usize;
            if vi < self.implied_bounds.len() {
                if is_upper {
                    self.implied_bounds[vi].1 = old;
                } else {
                    self.implied_bounds[vi].0 = old;
                }
                rewound_vars.push(var);
            }
        }
        // Direct bounds this pop restored: direct-bound overlays are not
        // trailed, so drop stale direct-overlay slot entries and queue the
        // incremental re-overlay (`note_direct_bound_widened`); row-derived
        // entries stay. When most variables changed, mark every row instead
        // of walking columns (the overlay stays incremental: it is
        // O(changed), the row sweep is the expensive part).
        let many_changed = (changed_vars.len() + rewound_vars.len()) * 4 >= self.vars.len();
        if many_changed {
            self.bound_generation += 1;
            let cur_gen = self.bound_generation;
            for &var in changed_vars.iter().chain(rewound_vars.iter()) {
                let vi = var as usize;
                if vi < self.var_bound_gen.len() {
                    self.var_bound_gen[vi] = cur_gen;
                }
                if vi < self.implied_tighten_streak.len() {
                    self.implied_tighten_streak[vi] = 0;
                }
            }
            for &var in &changed_vars {
                let vi = var as usize;
                if let Some(slot) = self.implied_bounds.get_mut(vi) {
                    if slot.0.as_ref().is_some_and(|b| b.row_idx == usize::MAX) {
                        slot.0 = None;
                    }
                    if slot.1.as_ref().is_some_and(|b| b.row_idx == usize::MAX) {
                        slot.1 = None;
                    }
                }
                self.direct_bounds_changed_vars.push(var);
            }
            if !changed_vars.is_empty() {
                self.direct_bounds_changed_since_implied = true;
            }
            for i in 0..self.rows.len() {
                self.touched_rows.insert(i);
            }
        } else {
            for &var in &changed_vars {
                self.note_direct_bound_widened(var);
            }
            for &var in &rewound_vars {
                self.stamp_var_for_rederivation(var);
            }
        }
        if self.warm.enabled {
            // #warm-simplex: REPAIR the infeasible-candidate structures instead
            // of clearing them. Pop never rewrites variable VALUES (only the
            // bound slots restored by the trail replay above), so a var's
            // violation status can change only if its OWN bound slot changed —
            // exactly the `changed_vars` list. Re-validate those (basic vars
            // re-enter/leave the heap via `track_var_feasibility`; non-basic
            // vars join the persistent dirty set for the targeted SAT-exit
            // scan). Note this does NOT rely on pop being loosen-only: a
            // retraction trail entry (`retract_unjustified_var_bounds`) can
            // restore a TIGHTER bound than the pre-pop state, and the
            // re-validation handles both directions. Stale heap entries for
            // vars that became feasible are lazily dropped by
            // `pop_greatest_error`, which re-validates on extraction.
            // `heap_stale` is left untouched: if it was already true (e.g. a
            // row was added in the popped scope) the next simplex still does
            // the full rebuild.
            for &var in &changed_vars {
                if (var as usize) >= self.vars.len() {
                    continue;
                }
                if !self.heap_stale {
                    self.track_var_feasibility(var);
                }
                if matches!(self.vars[var as usize].status, Some(VarStatus::NonBasic))
                    && self.violates_bounds(var).is_some()
                {
                    self.warm_mark_nonbasic_dirty(var);
                }
            }
        } else {
            self.infeasible_heap.clear();
            // #inc-heap-epoch: O(1) logical clear of heap membership.
            self.bump_heap_epoch();
            self.heap_stale = true;
        }
        // #lra-scope-trail: a trivial conflict recorded inside a popped scope
        // goes with it; one recorded in a surviving scope — a constant
        // contradiction applied at push time in the scope of its assertion —
        // stays pending for the next check, exactly like a trailed bound.
        if self.trivial_conflict_scope > self.scopes.len() {
            self.trivial_conflict = None;
        }
        self.injected_to_int_axioms.clear();
        // #lra-scope-trail: clamp the check cursor to the rewound trail — never
        // advance it. Atoms below the mark that are still pending (a constant
        // contradiction `process_check_atoms` stopped at, an unsupported atom
        // #9217 keeps re-scanning) must stay in front of the next check;
        // advancing the cursor to the trail length silently dropped them, so
        // `true = false` asserted at scope 1 was forgotten by a pop of scope
        // 2 and a later check answered `Sat`. Re-scanning is cheap: atoms
        // whose bounds are in place are skipped through `bound_atoms`.
        self.last_check_trail_pos = self.last_check_trail_pos.min(self.asserted_trail.len());
        self.bounds_tightened_since_simplex = true;
        // #8187: pop() invalidates any previous simplex result — the
        // soundness gate flag is re-initialized on each check entry, so
        // clear it here for hygiene only.
        self.post_simplex_bounds_added = false;
        self.vars_tightened_since_simplex.clear();
        self.pre_scan_tightened_complete = false;
        // #inc-guard-memo: lifecycle reset — values/bounds may be rewritten
        // below, so the guard's clean memo no longer holds. Also breaks the
        // tracked-only chain (#inc-guard-chain) until a full verification.
        self.guard_clean_valid = false;
        self.note_phase_state_change();
        self.guard_tracked_only = false;
        self.bcp_implied_dry_streak = 0;
        self.bcp_cascade_dry_streak = 0;
        // #7772 F1: Reset Bland mode on pop. If Bland's rule was activated
        // during a pushed scope's simplex solve (due to basis cycling), the
        // anti-cycling flag should not persist into the outer scope where it
        // would unnecessarily slow down pivot selection. While simplex already
        // resets these at the start of solve_feasibility(), clearing them here
        // prevents stale state from affecting other code paths.
        self.bland_mode = false;
        self.pivots_before_bland = 0;
        if let Some(prev) = self.last_simplex_feasible_scopes.pop() {
            self.set_last_simplex_feasible(prev);
        }
        if let Some(mark) = self.persistent_unsupported_scope_marks.pop() {
            self.rewind_persistent_unsupported_atoms(mark);
        }
        self.dirty = true;
        // #8900: rows to re-analyze were seeded above (rows of the variables
        // whose direct bounds this pop restored or whose derived bounds it
        // rewound); rows already pending from an outer-scope cascade
        // continuation are kept — they are generation-skipped when their
        // inputs did not change.
        self.propagate_direct_touched_rows_pending = !self.touched_rows.is_empty();
        self.implied_bounds_fresh = false;
        self.lra_basis_region_requests.clear();
        self.lra_basis_region_candidate = None;
        for atom_term in unasserted_atoms {
            if let Some(Some(info)) = self.atom_cache.get(&atom_term).cloned() {
                // STAGE B: this atom just became unasserted — restore it as a
                // decision candidate (mirrors decision_index_note_registered).
                if !info.is_distinct && self.registered_atoms.contains(&atom_term) {
                    if info.is_eq {
                        self.decision_index.eq.insert(atom_term);
                    } else {
                        self.decision_index.ineq.insert(atom_term);
                    }
                }
                if !info.is_eq && !info.is_distinct {
                    for &(v, _) in &info.expr.coeffs {
                        let vi = v as usize;
                        if vi < self.unassigned_atom_count.len() {
                            self.unassigned_atom_count[vi] += 1;
                        }
                    }
                    if info.expr.coeffs.len() > 1 {
                        let mut key: Vec<_> = info
                            .expr
                            .coeffs
                            .iter()
                            .map(|(v, c)| (*v, c.clone()))
                            .collect();
                        key.sort_by_key(|(v, _)| *v);
                        let key_rat: Vec<(u32, Rational)> =
                            key.iter().map(|(v, c)| (*v, Rational::from(c))).collect();
                        if let Some(&(slack, _)) = self.expr_to_slack.get(&key_rat) {
                            let si = slack as usize;
                            if si < self.unassigned_atom_count.len() {
                                self.unassigned_atom_count[si] += 1;
                            }
                        }
                    }
                }
            }
        }
    }
}
