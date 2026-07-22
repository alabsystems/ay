// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Solver {
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
        let clause_idx = conflict_ref.0 as usize;
        let lits = self.arena.literals(clause_idx);
        let len = lits.len();

        // Empty conflict clause: unconditional contradiction (UNSAT at level 0).
        // CaDiCaL analyze.cpp:577-592 handles this naturally — the loop body
        // never executes, leaving res=0 and forced=0 (no forced literal).
        if len == 0 {
            return (0, None);
        }

        let dl = self.decision_level;
        let mut max_level = 0u32;
        let mut count = 0u32;
        let mut forced_lit = lits[0];
        for &lit in lits {
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
            let target = conflict_ref.0;
            for i in 0..2usize {
                let (best_pos, _best_level) = {
                    let lits_r = self.arena.literals(clause_idx);
                    let mut bp = i;
                    let mut bl = self.var_data[lits_r[i].variable().index()].level.min(dl);
                    for (j, lit) in lits_r.iter().enumerate().skip(i + 1) {
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
                self.arena.literals_mut(clause_idx).swap(i, best_pos);
                // Only add the new watch if we actually removed the old one.
                if best_pos > 1 && removed_watch {
                    let new_watched = self.arena.literals(clause_idx)[i];
                    let other = self.arena.literals(clause_idx)[if i == 0 { 1 } else { 0 }];
                    self.watches
                        .add_watch(new_watched, Watcher::new(conflict_ref, other));
                }
            }
        }

        // Post-condition: conflict_level must be <= decision_level after capping.
        debug_assert!(
            max_level <= dl,
            "BUG: find_conflict_level returned {max_level} > decision_level {dl}",
        );

        if count == 1 {
            (max_level, Some(forced_lit))
        } else {
            (max_level, None)
        }
    }
}
