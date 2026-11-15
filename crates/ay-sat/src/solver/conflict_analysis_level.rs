// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) mod admitted;

impl Solver {
    /// Without chronological backtracking, backtrack to the level of a
    /// conflict that lies wholly below the current one and return that level.
    ///
    /// 1UIP needs a literal at the current level. BCP reports a conflict on
    /// the assignment that falsifies its last literal, but a theory conflict
    /// can lie wholly below the current level: the assumption loop consults
    /// its extension only once the assumption prefix is set, so a conflict
    /// among root or outer-level facts surfaces above them. The analysis then
    /// failed closed (back to level 0, nothing learned) and the theory
    /// re-derived the same conflict until the deadline. This is the chrono
    /// path's backtrack to the conflict level; at level 0 the clause database
    /// itself is refuted. The extension's lazy reasons that survive are
    /// materialized first; one the theory cannot rebuild is demoted to a
    /// decision, which the analysis that follows fails closed on if it
    /// resolves into it (#8707).
    pub(super) fn backtrack_to_lower_conflict_level(
        &mut self,
        conflict_ref: ClauseRef,
        ext: Option<&mut (dyn Extension + '_)>,
    ) -> Option<u32> {
        if self.chrono_enabled || self.decision_level == 0 {
            return None;
        }
        let lits = self.arena.literals(conflict_ref.0 as usize);
        let below = lits.len() >= 2
            && lits.iter().all(|&lit| {
                self.lit_val(lit) < 0
                    && self.var_data[lit.variable().index()].level < self.decision_level
            });
        if !below {
            return None;
        }
        let (conflict_level, _) = self.find_conflict_level(conflict_ref);
        if let Some(ext) = ext {
            self.materialize_lazy_reasons_through_level_for_backtrack(ext, conflict_level);
            ext.backtrack(conflict_level);
        }
        self.backtrack(conflict_level);
        Some(conflict_level)
    }

    /// Materialize the eager extension's current-level lazy reasons before
    /// the assumption loop's 1UIP, as the theory-backend loop does (#8467).
    ///
    /// A lazy reason that 1UIP meets makes it fail closed (back to level 0,
    /// nothing learned), and the extension re-propagates the same literals:
    /// the session-persistent QF_LRA lane spent 999,997 conflicts and 6 s on
    /// a two-conflict UNSAT check that way (ay-dpll `lra_inc_dead_atoms`). A
    /// reason the theory cannot rebuild is demoted to a decision, and 1UIP
    /// fails closed exactly when it resolves into such a var as a non-UIP
    /// current-level literal (the Decision arm, #8707). The sticky failure
    /// flag would abort EVERY analysis at this level, also those whose cone
    /// never meets the demoted var (363,646 bails on an 11-conflict session
    /// check), so it is disarmed here, and by the loop's backtrack hook after
    /// each through-level materialization.
    pub(super) fn materialize_lazy_reasons_for_assumption_analysis(
        &mut self,
        ext: Option<&mut (dyn Extension + '_)>,
    ) {
        if let Some(ext) = ext {
            self.materialize_current_level_lazy_reasons(ext);
        }
        self.cold.lazy_materialization_failed = false;
    }

    /// Find the actual conflict level: the maximum assignment level among
    /// all literals in the conflict clause (CaDiCaL analyze.cpp:572-644).
    ///
    /// With chronological backtracking + correct assignment levels, this may
    /// be lower than `decision_level`. Returns `(conflict_level, forced)` where
    /// `forced` is `Some(lit)` if exactly one literal is at the highest level
    /// (the "forced" early-return path from CaDiCaL SAT'18 paper Alg.1 lines 4-6).
    ///
    /// Levels are capped at `decision_level` to handle stale `var_data[].level`
    /// values from prior chrono BT out-of-order assignments (#9148). CaDiCaL
    /// maintains this invariant implicitly because `backtrack()` unassigns
    /// variables above `new_level` and resets their trail position. AY clears
    /// `vals[]` during backtrack but does NOT clear `var_data[].level`, so
    /// unassigned variables retain stale levels. Capping here matches CaDiCaL's
    /// `propagate.cpp:49` which returns `min(level, decision_level)` from
    /// `assignment_level()`.
    pub(super) fn find_conflict_level(
        &mut self,
        conflict_ref: ClauseRef,
    ) -> (u32, Option<Literal>) {
        match self.find_conflict_level_admitted(conflict_ref, &admitted::Ordinary) {
            Ok(result) => result,
            Err(never) => match never {},
        }
    }

    pub(in crate::solver) fn find_conflict_level_admitted<P: admitted::Policy>(
        &mut self,
        conflict_ref: ClauseRef,
        policy: &P,
    ) -> Result<(u32, Option<Literal>), P::Error> {
        policy.enter(self, conflict_ref)?;
        let clause_idx = conflict_ref.0 as usize;
        let lits = self.arena.literals(clause_idx);
        let len = lits.len();

        // Empty conflict clause: unconditional contradiction (UNSAT at level 0).
        // CaDiCaL analyze.cpp:577-592 handles this naturally — the loop body
        // never executes, leaving res=0 and forced=0 (no forced literal).
        if len == 0 {
            return Ok((0, None));
        }

        let dl = self.decision_level;
        let mut max_level = 0u32;
        let mut count = 0u32;
        let mut forced_lit = lits[0];
        for &lit in lits {
            policy.work(1)?;
            let idx = lit.variable().index();
            // Guard (#8360): skip unassigned ghost literals from prior
            // chrono-BT. Their var_data.level is stale and must not
            // influence conflict_level computation. Without this, ghost
            // literals can inflate conflict_level, causing the subsequent
            // backtrack to be a no-op while analyze_conflict (correctly)
            // skips them via lit_val() guard, leading to counter=0 panic.
            if self.lit_val(lit) >= 0 {
                continue;
            }
            // Cap at decision_level: var_data[].level may be stale for
            // variables that were unassigned by a prior chrono backtrack
            // (#9148). CaDiCaL's assignment_level() caps the same way
            // (propagate.cpp:49-52).
            let lvl = self.var_data[idx].level.min(dl);
            if lvl > max_level {
                max_level = lvl;
                forced_lit = lit;
                count = 1;
            } else if lvl == max_level {
                count += 1;
            }
        }

        if len >= 2 {
            self.repair_conflict_watches_admitted(conflict_ref, max_level, policy)?;
        }

        // Post-condition: conflict_level must be <= decision_level after capping.
        debug_assert!(
            max_level <= dl,
            "BUG: find_conflict_level returned {max_level} > decision_level {dl}",
        );

        if count == 1 {
            Ok((max_level, Some(forced_lit)))
        } else {
            Ok((max_level, None))
        }
    }

    fn repair_conflict_watches_admitted<P: admitted::Policy>(
        &mut self,
        conflict_ref: ClauseRef,
        max_level: u32,
        policy: &P,
    ) -> Result<(), P::Error> {
        let clause_idx = conflict_ref.index();
        let dl = self.decision_level;
        let target = conflict_ref.0;
        for i in 0..2usize {
            let (best_pos, _best_level) = {
                let lits_r = self.arena.literals(clause_idx);
                let mut bp = i;
                let mut bl = self.var_data[lits_r[i].variable().index()].level.min(dl);
                for (j, lit) in lits_r.iter().enumerate().skip(i + 1) {
                    policy.work(1)?;
                    let lvl = self.var_data[lit.variable().index()].level.min(dl);
                    if lvl > bl {
                        bp = j;
                        bl = lvl;
                        if bl == max_level {
                            break;
                        }
                    }
                }
                (bp, bl)
            };
            if best_pos == i {
                continue;
            }
            policy.relocation(self, conflict_ref, i, best_pos)?;
            // JIT-compiled clauses (len 3-12) may have their 2WL watches
            // intentionally detached (#8201, #8229). Rather than predicting
            // detachment status, check whether watch removal actually found
            // an entry. If not, skip the add to avoid creating orphan watches.
            let mut removed_watch = false;
            if best_pos > 1 {
                let old_watched = self.arena.literals(clause_idx)[i];
                let mut wl = self.watches.get_watches_mut(old_watched);
                let mut wi = 0;
                while wi < wl.len() {
                    if wl.clause_ref(wi).0 == target {
                        wl.swap_remove(wi);
                        removed_watch = true;
                    } else {
                        wi += 1;
                    }
                }
            }
            // `swap_literals`, not `literals_mut(..).swap(..)`: this is a
            // PERMUTATION of one clause's literals (watch repair), and
            // `literals_mut` conservatively bumps the arena's
            // `formula_epoch` — which would invalidate the incremental
            // relevancy frontier on every conflict for a mutation no
            // set-valued consumer can observe (#relevancy-frontier-incremental).
            self.arena.swap_literals(clause_idx, i, best_pos);
            // Only add the new watch if we actually removed the old one.
            if best_pos > 1 && removed_watch {
                let new_watched = self.arena.literals(clause_idx)[i];
                let other = self.arena.literals(clause_idx)[if i == 0 { 1 } else { 0 }];
                self.watches
                    .add_watch(new_watched, Watcher::new(conflict_ref, other));
            }
            policy.finish_move()?;
        }
        Ok(())
    }
}
