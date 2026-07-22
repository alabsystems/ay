// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Kitten {
    fn assign(&mut self, lit: u32, reason: u32) {
        let not_lit = lit ^ 1;
        debug_assert_eq!(self.values[lit as usize], 0);
        debug_assert_eq!(self.values[not_lit as usize], 0);
        self.values[lit as usize] = 1;
        self.values[not_lit as usize] = -1;
        let idx = (lit / 2) as usize;
        self.phases[idx] = (lit & 1) as u8;
        self.trail.push(lit);
        let var = &mut self.vars[idx];
        var.level = self.level;

        let final_reason = if var.level == 0 && reason != INVALID {
            let size = self.clause_size(reason) as usize;
            if size > 1 {
                if self.track_antecedents {
                    self.resolved.push(reason);
                    let (start, end) = self.clause_lits_range(reason);
                    for i in start..end {
                        let other = self.clause_data[i];
                        if other != lit {
                            let other_idx = (other / 2) as usize;
                            let other_ref = self.vars[other_idx].reason;
                            debug_assert!(other_ref != INVALID);
                            self.resolved.push(other_ref);
                        }
                    }
                }
                self.clause_buf.clear();
                self.clause_buf.push(lit);
                let buf = self.clause_buf.clone();
                let new_ref =
                    self.add_clause_to_arena(&buf, LEARNED_FLAG, self.resolved.len() as u32);
                // CaDiCaL kitten.c:1017 calls new_learned_klause() which
                // calls connect_new_klause(), adding size-1 clauses to the
                // units stack. Without this, completely_backtrack_to_root_level
                // misses unassigning level-0 propagated variables whose trail
                // entries were flushed by decide(). Stale assignments cause
                // false UNSAT on subsequent incremental solves (#7067).
                self.connect_clause(new_ref);
                self.resolved.clear();
                self.clause_buf.clear();
                new_ref
            } else {
                reason
            }
        } else {
            reason
        };
        self.vars[idx].reason = final_reason;
        debug_assert!(self.unassigned > 0);
        self.unassigned -= 1;
    }

    fn unassign(&mut self, lit: u32) {
        let not_lit = lit ^ 1;
        debug_assert!(self.values[lit as usize] != 0);
        self.values[lit as usize] = 0;
        self.values[not_lit as usize] = 0;
        let idx = (lit / 2) as usize;
        self.unassigned += 1;
        if self.links[idx].stamp > self.links[self.queue_search as usize].stamp {
            self.update_search(idx as u32);
        }
    }

    fn propagate_literal(&mut self, lit: u32) -> u32 {
        debug_assert!(self.values[lit as usize] > 0);
        let not_lit = lit ^ 1;

        let mut watch_list = std::mem::take(&mut self.watches[not_lit as usize]);
        let mut conflict = INVALID;
        let mut j = 0;
        let mut ticks: u64 = (watch_list.len() as u64 / 16) + 1;

        let mut i = 0;
        while i < watch_list.len() {
            let ref_ = watch_list[i];
            i += 1;
            ticks += 1;

            let lit0 = self.clause_lit(ref_, 0);
            let lit1 = self.clause_lit(ref_, 1);
            let other = lit0 ^ lit1 ^ not_lit;
            let other_value = self.values[other as usize];

            if other_value > 0 {
                watch_list[j] = ref_;
                j += 1;
                continue;
            }

            let size = self.clause_size(ref_) as usize;
            let mut replacement = INVALID;
            let mut replacement_value: i8 = -1;
            let mut replacement_pos = 0;
            for k in 2..size {
                let r = self.clause_lit(ref_, k);
                let rv = self.values[r as usize];
                if rv >= 0 {
                    replacement = r;
                    replacement_value = rv;
                    replacement_pos = k;
                    break;
                }
            }

            if replacement_value >= 0 {
                debug_assert!(replacement != INVALID);
                self.set_clause_lit(ref_, 0, other);
                self.set_clause_lit(ref_, 1, replacement);
                self.set_clause_lit(ref_, replacement_pos, not_lit);
                self.watches[replacement as usize].push(ref_);
            } else if other_value < 0 {
                self.conflicts += 1;
                conflict = ref_;
                watch_list[j] = ref_;
                j += 1;
                break;
            } else {
                debug_assert_eq!(other_value, 0);
                self.assign(other, ref_);
                watch_list[j] = ref_;
                j += 1;
            }
        }

        while i < watch_list.len() {
            watch_list[j] = watch_list[i];
            j += 1;
            i += 1;
        }
        watch_list.truncate(j);
        self.watches[not_lit as usize] = watch_list;
        self.ticks += ticks;
        conflict
    }

    fn propagate(&mut self) -> u32 {
        debug_assert_eq!(self.inconsistent, INVALID);
        let mut propagated_count: u64 = 0;
        let mut conflict = INVALID;
        while conflict == INVALID && self.propagated < self.trail.len() {
            let lit = self.trail[self.propagated];
            conflict = self.propagate_literal(lit);
            self.propagated += 1;
            propagated_count += 1;
        }
        self.propagations += propagated_count;
        conflict
    }

    fn analyze(&mut self, conflict_ref: u32) {
        debug_assert!(self.level > 0);
        debug_assert_eq!(self.inconsistent, INVALID);
        debug_assert!(self.analyzed.is_empty());
        debug_assert!(self.resolved.is_empty());
        debug_assert!(self.clause_buf.is_empty());

        self.clause_buf.push(INVALID);

        let mut reason = conflict_ref;
        let level = self.level;
        let mut p = self.trail.len();
        let mut open = 0u32;
        let mut jump = 0u32;
        let mut uip;

        loop {
            debug_assert!(reason != INVALID);
            self.resolved.push(reason);
            let (start, end) = self.clause_lits_range(reason);
            for i in start..end {
                let mut lit = self.clause_data[i];
                let idx = (lit / 2) as usize;
                if self.marks[idx] != 0 {
                    continue;
                }
                debug_assert!(self.values[lit as usize] < 0);
                self.marks[idx] = 1;
                self.analyzed.push(idx as u32);
                let var_level = self.vars[idx].level;
                if var_level < level {
                    if var_level > jump {
                        jump = var_level;
                        if self.clause_buf.len() > 1 {
                            std::mem::swap(&mut self.clause_buf[1], &mut lit);
                        }
                    }
                    self.clause_buf.push(lit);
                } else {
                    open += 1;
                }
            }

            loop {
                debug_assert!(p > 0);
                p -= 1;
                uip = self.trail[p];
                if self.marks[(uip / 2) as usize] != 0 {
                    break;
                }
            }
            debug_assert!(open > 0);
            open -= 1;
            if open == 0 {
                break;
            }
            reason = self.vars[(uip / 2) as usize].reason;
        }

        let not_uip = uip ^ 1;
        self.clause_buf[0] = not_uip;

        for &idx in &self.analyzed {
            self.marks[idx as usize] = 0;
        }
        let analyzed: Vec<u32> = self.analyzed.drain(..).collect();
        for idx in analyzed {
            self.move_to_front(idx);
        }

        let lits = self.clause_buf.clone();
        let aux = if self.track_antecedents {
            self.resolved.len() as u32
        } else {
            0
        };
        let learned_ref = self.add_clause_to_arena(&lits, LEARNED_FLAG, aux);
        self.connect_clause(learned_ref);

        self.resolved.clear();
        self.clause_buf.clear();

        self.backtrack(jump);
        self.assign(not_uip, learned_ref);
    }

    fn backtrack(&mut self, jump_level: u32) {
        debug_assert!(jump_level < self.level);
        while let Some(&lit) = self.trail.last() {
            let idx = (lit / 2) as usize;
            if self.vars[idx].level == jump_level {
                break;
            }
            self.trail.pop();
            self.unassign(lit);
        }
        self.propagated = self.trail.len();
        self.level = jump_level;
    }

    /// Analyze why assumptions failed. Marks all contributing assumptions
    /// as failed and records a failing reason clause.
    ///
    /// Ported from CaDiCaL kitten.c:1246-1431 `failing()`.
    /// Three cases:
    /// 1. `failed_unit`: assumption falsified at level 0 by unit propagation
    /// 2. `failed_clashing`: assumption clashes with another assumption (no reason)
    /// 3. `first_failed`: assumption falsified by propagation, walk implication graph
    fn failing_analysis(&mut self) {
        debug_assert_eq!(self.inconsistent, INVALID);
        debug_assert!(!self.assumptions.is_empty());
        debug_assert!(self.analyzed.is_empty());

        let assumptions = self.assumptions.clone();

        // CaDiCaL kitten.c:1258-1271: scan assumptions for the three cases.
        let mut failed_clashing: u32 = INVALID;
        let mut first_failed: u32 = INVALID;
        let mut failed_unit: u32 = INVALID;

        for &assumption in &assumptions {
            let val = self.values[assumption as usize];
            if val >= 0 {
                continue;
            }
            if first_failed == INVALID {
                first_failed = assumption;
            }
            let idx = (assumption / 2) as usize;
            let var = &self.vars[idx];
            if var.level == 0 {
                failed_unit = assumption;
                break;
            }
            if failed_clashing == INVALID && var.reason == INVALID {
                failed_clashing = assumption;
            }
        }

        // CaDiCaL kitten.c:1272-1278: pick best failed assumption.
        let failed = if failed_unit != INVALID {
            failed_unit
        } else if failed_clashing != INVALID {
            failed_clashing
        } else {
            first_failed
        };
        debug_assert!(failed != INVALID);

        self.failed[failed as usize] = true;

        // Case 1: unit-level failure. CaDiCaL kitten.c:1286-1292.
        if failed_unit != INVALID {
            let idx = (failed / 2) as usize;
            let reason = self.vars[idx].reason;
            debug_assert!(reason != INVALID);
            self.failing = reason;
            return;
        }

        // Case 2: clashing assumptions. CaDiCaL kitten.c:1294-1299.
        if failed_clashing != INVALID {
            let not_failed = failed ^ 1;
            self.failed[not_failed as usize] = true;
            // self.failing remains INVALID (no reason clause, clash is direct)
            return;
        }

        // Case 3: general failure. Walk the implication graph backwards from
        // the failed assumption to find all contributing assumptions.
        // CaDiCaL kitten.c:1302-1376.
        let failed_idx = (failed / 2) as usize;
        let not_failed = failed ^ 1;
        self.marks[failed_idx] = 1;
        self.analyzed.push(failed_idx as u32);
        self.clause_buf.push(not_failed);

        // Walk trail backwards to find all contributing literals.
        let mut p = self.trail.len();
        let mut open = 1u32;
        while open > 0 {
            open -= 1;
            // Find next marked literal on trail.
            let mut uip;
            loop {
                debug_assert!(p > 0);
                p -= 1;
                uip = self.trail[p];
                if self.marks[(uip / 2) as usize] != 0 {
                    break;
                }
            }

            let idx = (uip / 2) as usize;
            let reason = self.vars[idx].reason;
            if reason == INVALID {
                // This is an assumption — mark it as failed.
                let mut lit = idx as u32 * 2;
                if self.values[lit as usize] < 0 {
                    lit ^= 1;
                }
                if !self.failed[lit as usize] {
                    self.failed[lit as usize] = true;
                }
                let not_lit = lit ^ 1;
                self.clause_buf.push(not_lit);
            } else {
                // Propagated literal — analyze its reason clause.
                self.resolved.push(reason);
                let (start, end) = self.clause_lits_range(reason);
                for i in start..end {
                    let other = self.clause_data[i];
                    let other_idx = (other / 2) as usize;
                    if self.marks[other_idx] != 0 {
                        continue;
                    }
                    self.marks[other_idx] = 1;
                    debug_assert!(self.values[other as usize] != 0);
                    if self.vars[other_idx].level > 0 {
                        open += 1;
                    }
                    self.analyzed.push(other_idx as u32);
                }
            }
        }

        // Process level-0 variables in BFS order (CaDiCaL kitten.c:1359-1376).
        let mut next = 0;
        let analyzed_snapshot: Vec<u32> = self.analyzed.clone();
        while next < analyzed_snapshot.len() {
            let idx = analyzed_snapshot[next] as usize;
            next += 1;
            if self.vars[idx].level != 0 {
                continue;
            }
            let reason = self.vars[idx].reason;
            if reason == INVALID {
                let mut lit = idx as u32 * 2;
                if self.values[lit as usize] < 0 {
                    lit ^= 1;
                }
                if !self.failed[lit as usize] {
                    self.failed[lit as usize] = true;
                }
                let not_lit = lit ^ 1;
                self.clause_buf.push(not_lit);
            } else {
                self.resolved.push(reason);
            }
        }

        // Clean up marks.
        for &idx in &self.analyzed {
            self.marks[idx as usize] = 0;
        }
        self.analyzed.clear();

        // Build the failing reason clause from resolved antecedents.
        // CaDiCaL kitten.c:1418-1427.
        if self.resolved.len() == 1 {
            self.failing = self.resolved[0];
        } else if !self.resolved.is_empty() {
            let lits = self.clause_buf.clone();
            let aux = if self.track_antecedents {
                self.resolved.len() as u32
            } else {
                0
            };
            let learned_ref = self.add_clause_to_arena(&lits, LEARNED_FLAG, aux);
            self.failing = learned_ref;
        }

        self.resolved.clear();
        self.clause_buf.clear();
    }

    fn decide(&mut self) -> i32 {
        if self.level == 0 && !self.trail.is_empty() {
            self.propagated = 0;
            self.trail.clear();
        }

        let assumptions = self.assumptions.clone();
        while (self.level as usize) < assumptions.len() {
            let assumption = assumptions[self.level as usize];
            let val = self.values[assumption as usize];
            if val < 0 {
                self.failing_analysis();
                return 20;
            } else if val > 0 {
                self.level += 1;
            } else {
                self.decisions += 1;
                self.level += 1;
                self.assign(assumption, INVALID);
                return 0;
            }
        }

        if self.unassigned == 0 {
            return 10;
        }

        if self.ticks >= self.ticks_limit {
            return -1;
        }

        let mut idx = self.queue_search;
        loop {
            debug_assert!(idx != INVALID, "BUG: VMTF queue exhausted");
            if self.values[(idx * 2) as usize] == 0 {
                break;
            }
            idx = self.links[idx as usize].prev;
        }
        self.update_search(idx);
        let phase = self.phases[idx as usize];
        let decision = idx * 2 + u32::from(phase);

        self.decisions += 1;
        self.level += 1;
        self.assign(decision, INVALID);
        0
    }

    pub(super) fn mark_inconsistent(&mut self, ref_: u32) {
        debug_assert_eq!(self.inconsistent, INVALID);

        if !self.track_antecedents {
            self.inconsistent = ref_;
            return;
        }

        self.analyzed.clear();
        self.resolved.clear();

        let mut next = 0;
        let mut current_ref = ref_;
        loop {
            debug_assert!(current_ref != INVALID);
            self.resolved.push(current_ref);
            let (start, end) = self.clause_lits_range(current_ref);
            for i in start..end {
                let lit = self.clause_data[i];
                let idx = (lit / 2) as usize;
                if self.marks[idx] != 0 {
                    continue;
                }
                self.marks[idx] = 1;
                self.analyzed.push(idx as u32);
            }
            if next >= self.analyzed.len() {
                break;
            }
            let idx = self.analyzed[next] as usize;
            next += 1;
            debug_assert_eq!(self.vars[idx].level, 0);
            current_ref = self.vars[idx].reason;
        }

        self.clause_buf.clear();
        let lits = self.clause_buf.clone();
        let aux = self.resolved.len() as u32;
        let empty_ref = self.add_clause_to_arena(&lits, LEARNED_FLAG, aux);
        self.inconsistent = empty_ref;

        for &idx in &self.analyzed {
            self.marks[idx as usize] = 0;
        }
        self.analyzed.clear();
        self.resolved.clear();
    }

    fn propagate_units(&mut self) -> i32 {
        if self.inconsistent != INVALID {
            return 20;
        }
        if self.units.is_empty() {
            return 0;
        }
        let units = self.units.clone();
        for &ref_ in &units {
            debug_assert!(ref_ != INVALID);
            let unit = self.clause_lit(ref_, 0);
            let val = self.values[unit as usize];
            if val > 0 {
                continue;
            }
            if val < 0 {
                self.mark_inconsistent(ref_);
                return 20;
            }
            self.assign(unit, ref_);
        }
        let conflict = self.propagate();
        if conflict != INVALID {
            self.mark_inconsistent(conflict);
            return 20;
        }
        0
    }

    /// Unassign ALL variables including level-0 units.
    /// CaDiCaL kitten.c:1153-1179 completely_backtrack_to_root_level.
    ///
    /// The next propagate_units() re-assigns all unit clauses and
    /// propagate() re-discovers all implications from scratch, including
    /// those involving learned clauses that are now unit at level 0.
    pub(super) fn completely_backtrack_to_root_level(&mut self) {
        for i in (0..self.trail.len()).rev() {
            let lit = self.trail[i];
            self.unassign(lit);
        }
        self.trail.clear();
        // Also unassign level-0 units from the units stack.
        // CaDiCaL kitten.c:1167-1175: these remain in the units stack
        // and get re-derived by propagate_units() at the next solve().
        for i in 0..self.units.len() {
            let ref_ = self.units[i];
            let lit = self.clause_lit(ref_, 0);
            if self.values[lit as usize] > 0 {
                self.unassign(lit);
            }
        }
        self.propagated = 0;
        self.level = 0;
    }

    /// Clear assumptions and their failed marks.
    /// CaDiCaL kitten.c:1630-1640 reset_assumptions.
    fn reset_assumptions(&mut self) {
        for &assumption in &self.assumptions {
            self.failed[assumption as usize] = false;
        }
        self.assumptions.clear();
    }

    pub(super) fn reset_incremental(&mut self) {
        self.completely_backtrack_to_root_level();
        self.status = 0;
        self.failing = INVALID;
        self.failed.iter_mut().for_each(|v| *v = false);
        self.assumptions.clear();
    }

    /// Solve under current assumptions.
    /// Returns 10 (SAT), 20 (UNSAT), 0 (unknown/limit hit).
    pub(crate) fn solve(&mut self) -> i32 {
        if self.status != 0 {
            self.reset_incremental();
        } else {
            // CaDiCaL kitten.c:1862-1863: even when status==0, fully backtrack
            // to root level before solving. Ensures clean re-propagation of
            // all unit clauses including those from learned clauses.
            self.completely_backtrack_to_root_level();
        }

        let res = self.propagate_units();
        if res != 0 {
            self.status = res;
            return res;
        }

        loop {
            let conflict = self.propagate();
            if conflict != INVALID {
                if self.level == 0 {
                    self.mark_inconsistent(conflict);
                    self.status = 20;
                    return 20;
                }
                self.analyze(conflict);
            } else {
                let decision_result = self.decide();
                if decision_result != 0 {
                    self.status = if decision_result < 0 {
                        0
                    } else {
                        decision_result
                    };
                    // CaDiCaL kitten.c:1893-1894: when solve returns unknown
                    // (0, e.g. ticks limit hit), reset assumptions so they
                    // don't accumulate across incremental solves. Without this,
                    // the next assume() call sees status==0 and skips
                    // reset_incremental(), appending new assumptions on top of
                    // stale ones. The corrupted assumption stack causes false
                    // UNSAT in subsequent probes (#8530).
                    if self.status == 0 && !self.assumptions.is_empty() {
                        self.reset_assumptions();
                    }
                    return self.status;
                }
            }
        }
    }
}
