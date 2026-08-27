// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental maintenance for theory-aware decision candidates.

use ay_core::TheorySolver;
use ay_sat::{SolverContext, Variable};

use super::types::{TheoryExtension, UNASSIGNED_NIL};

impl<T: TheorySolver> TheoryExtension<'_, T> {
    /// Rebuild the unassigned free-list from the SAT context's source of truth.
    pub(super) fn rebuild_unassigned_list(&self, ctx: &dyn SolverContext) {
        let mut prev = self.unassigned_prev.borrow_mut();
        let mut next = self.unassigned_next.borrow_mut();
        let mut linked = self.unassigned_linked.borrow_mut();
        let mut head = UNASSIGNED_NIL;
        let mut last = UNASSIGNED_NIL;
        for pos in 0..self.seed_index.len() {
            let (sat_var, _atom) = self.seed_index[pos];
            if ctx.value(Variable::new(sat_var)).is_none() {
                prev[pos] = last;
                next[pos] = UNASSIGNED_NIL;
                linked[pos] = true;
                if last == UNASSIGNED_NIL {
                    head = pos as u32;
                } else {
                    next[last as usize] = pos as u32;
                }
                last = pos as u32;
            } else {
                linked[pos] = false;
            }
        }
        self.unassigned_head.set(head);
        self.unassigned_scan_pos.set(ctx.trail().len());
        self.unassigned_dirty.set(false);
    }

    /// Unlink seed positions assigned since the last free-list maintenance.
    pub(super) fn advance_unassigned_scan(&self, ctx: &dyn SolverContext) {
        let trail = ctx.trail();
        let scan_pos = self.unassigned_scan_pos.get();
        let trail_len = trail.len();
        if scan_pos > trail_len {
            self.rebuild_unassigned_list(ctx);
            return;
        }
        if scan_pos == trail_len {
            return;
        }
        let mut prev = self.unassigned_prev.borrow_mut();
        let mut next = self.unassigned_next.borrow_mut();
        let mut linked = self.unassigned_linked.borrow_mut();
        for &lit in &trail[scan_pos..] {
            let var_id = lit.variable().id() as usize;
            if var_id >= self.sat_var_to_seed_pos.len() {
                continue;
            }
            let pos = self.sat_var_to_seed_pos[var_id];
            if pos == UNASSIGNED_NIL {
                continue;
            }
            let pos = pos as usize;
            if !linked[pos] {
                continue;
            }
            linked[pos] = false;
            let previous = prev[pos];
            let following = next[pos];
            if previous == UNASSIGNED_NIL {
                self.unassigned_head.set(following);
            } else {
                next[previous as usize] = following;
            }
            if following != UNASSIGNED_NIL {
                prev[following as usize] = previous;
            }
        }
        self.unassigned_scan_pos.set(trail_len);
    }
}
