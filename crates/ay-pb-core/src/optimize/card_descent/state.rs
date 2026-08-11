// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The fixed-cardinality search state and its ONE move.
//!
//! [`Descent`] holds a selection `S` over the [`CoverView`]'s ground set plus
//! the derived violation structure (per-row LHS, the violated-row index, the
//! unweighted shortfall total) and the dynamic row weights.
//!
//! [`Descent::swap_step`] is the only move: remove one member, add one
//! non-member, then bump the weight of every row that is still violated. `|S|`
//! is INVARIANT across it — that is the whole point of the arm, and it is
//! pinned by `swap_step_preserves_cardinality` in the sibling test module.
//!
//! The one operation that changes `|S|` is [`Descent::set_selection`], which
//! RE-DERIVES the entire violation structure from scratch. Shrinking by
//! patching (dropping a variable and adjusting in place) silently corrupts the
//! search state, so there is deliberately no in-place shrink at all.

use super::cover::CoverView;
use crate::optimize::lns::SplitMix64;

/// Best-from-multiple-selections sample size for the REMOVE half of a swap
/// (NuMVC's BMS): score this many random members and take the least damaging,
/// instead of an O(|S|) exact minimum.
const BMS_SAMPLES: usize = 64;

/// Per-row weight ceiling. Weights only ever steer move selection, so
/// saturating them costs nothing and removes every overflow question.
const WEIGHT_CAP: i64 = 1 << 20;

/// Cap on candidates scored per greedy construction pick.
const GREEDY_CAND_CAP: usize = 2048;

/// Sentinel for "absent" in the position side-tables.
const NONE: u32 = u32::MAX;

pub(super) struct Descent<'a> {
    view: &'a CoverView,
    in_set: Vec<bool>,
    members: Vec<u32>,
    member_pos: Vec<u32>,
    pub(super) lhs: Vec<i64>,
    weight: Vec<i64>,
    pub(super) violated: Vec<u32>,
    viol_pos: Vec<u32>,
    /// Unweighted total shortfall — the progress signal for stall detection.
    /// Feasibility is decided by `violated.is_empty()`, never by this.
    pub(super) total_shortfall: i64,
    age: Vec<u64>,
    steps: u64,
    last_added: u32,
    pub(super) rng: SplitMix64,
}

impl<'a> Descent<'a> {
    pub(super) fn new(view: &'a CoverView, seed: u64) -> Self {
        let rows = view.num_rows();
        let mut descent = Descent {
            view,
            in_set: vec![false; view.num_vars],
            members: Vec::new(),
            member_pos: vec![NONE; view.num_vars],
            lhs: vec![0; rows],
            weight: vec![1; rows],
            violated: Vec::new(),
            viol_pos: vec![NONE; rows],
            total_shortfall: 0,
            age: vec![0; view.num_vars],
            steps: 0,
            last_added: NONE,
            rng: SplitMix64::new(seed),
        };
        descent.set_selection(&[]);
        descent
    }

    fn shortfall(&self, row: usize) -> i64 {
        (self.view.rhs[row] - self.lhs[row]).max(0)
    }

    pub(super) fn is_feasible(&self) -> bool {
        self.violated.is_empty()
    }

    pub(super) fn selection(&self) -> &[u32] {
        &self.members
    }

    /// Re-derives the ENTIRE search state from an explicit selection: `in_set`,
    /// `members`, every row LHS, the violated-row index and the shortfall
    /// total. Row WEIGHTS are deliberately preserved (they encode which rows
    /// are hard, which is exactly the knowledge worth carrying across a
    /// cardinality shrink); everything derived from the selection is rebuilt.
    pub(super) fn set_selection(&mut self, selection: &[u32]) {
        for &var in &self.members {
            self.in_set[var as usize] = false;
            self.member_pos[var as usize] = NONE;
        }
        self.members.clear();
        for &var in selection {
            let index = var as usize;
            if index >= self.view.num_vars || self.in_set[index] {
                continue;
            }
            self.in_set[index] = true;
            self.member_pos[index] = self.members.len() as u32;
            self.members.push(var);
        }
        self.lhs.iter_mut().for_each(|value| *value = 0);
        let view = self.view;
        for &var in &self.members {
            for (row, coeff) in view.var_entries(var as usize) {
                self.lhs[row as usize] += coeff;
            }
        }
        for slot in self.viol_pos.iter_mut() {
            *slot = NONE;
        }
        self.violated.clear();
        self.total_shortfall = 0;
        for row in 0..view.num_rows() {
            let short = self.shortfall(row);
            if short > 0 {
                self.viol_pos[row] = self.violated.len() as u32;
                self.violated.push(row as u32);
                self.total_shortfall = self.total_shortfall.saturating_add(short);
            }
        }
        self.last_added = NONE;
    }

    fn add_var(&mut self, var: u32) {
        let index = var as usize;
        if self.in_set[index] {
            return;
        }
        self.in_set[index] = true;
        self.member_pos[index] = self.members.len() as u32;
        self.members.push(var);
        let lo = self.view.var_start[index] as usize;
        let hi = self.view.var_start[index + 1] as usize;
        for slot in lo..hi {
            let row = self.view.var_row[slot] as usize;
            let before = self.shortfall(row);
            self.lhs[row] += self.view.var_coeff[slot];
            let after = self.shortfall(row);
            if after != before {
                self.total_shortfall = self.total_shortfall.saturating_sub(before - after);
                if after == 0 {
                    self.drop_violated(row);
                }
            }
        }
        self.age[index] = self.steps;
    }

    fn remove_var(&mut self, var: u32) {
        let index = var as usize;
        if !self.in_set[index] {
            return;
        }
        let at = self.member_pos[index] as usize;
        // `in_set[index]` implies `members` contains `var`, so both of these
        // hold. Fail CLOSED (no-op) rather than panic if they ever do not:
        // this tracker is advisory, and a panicking primal worker would take
        // its whole solve with it.
        debug_assert!(at < self.members.len(), "member position must be in range");
        let Some(&last) = self.members.last() else {
            return;
        };
        if at >= self.members.len() {
            return;
        }
        self.in_set[index] = false;
        self.members.swap_remove(at);
        if last != var {
            self.member_pos[last as usize] = at as u32;
        }
        self.member_pos[index] = NONE;
        let lo = self.view.var_start[index] as usize;
        let hi = self.view.var_start[index + 1] as usize;
        for slot in lo..hi {
            let row = self.view.var_row[slot] as usize;
            let before = self.shortfall(row);
            self.lhs[row] -= self.view.var_coeff[slot];
            let after = self.shortfall(row);
            if after != before {
                self.total_shortfall = self.total_shortfall.saturating_add(after - before);
                if before == 0 {
                    self.viol_pos[row] = self.violated.len() as u32;
                    self.violated.push(row as u32);
                }
            }
        }
        self.age[index] = self.steps;
    }

    fn drop_violated(&mut self, row: usize) {
        let at = self.viol_pos[row] as usize;
        // Same fail-closed posture as `remove_var`: a violated row always has
        // a live index here, but never panic on the advisory path.
        debug_assert!(
            at < self.violated.len(),
            "violated position must be in range"
        );
        let Some(&last) = self.violated.last() else {
            return;
        };
        let last = last as usize;
        if at >= self.violated.len() {
            return;
        }
        self.violated.swap_remove(at);
        if last != row {
            self.viol_pos[last] = at as u32;
        }
        self.viol_pos[row] = NONE;
    }

    /// Weighted cost INCREASE from removing `var` (>= 0).
    pub(super) fn remove_cost(&self, var: u32) -> i64 {
        let index = var as usize;
        let lo = self.view.var_start[index] as usize;
        let hi = self.view.var_start[index + 1] as usize;
        let mut total: i64 = 0;
        for slot in lo..hi {
            let row = self.view.var_row[slot] as usize;
            let before = self.shortfall(row);
            let after = (self.view.rhs[row] - (self.lhs[row] - self.view.var_coeff[slot])).max(0);
            total = total.saturating_add(self.weight[row].saturating_mul(after - before));
        }
        total
    }

    /// Weighted cost DECREASE from adding `var` (>= 0).
    fn add_gain(&self, var: u32) -> i64 {
        let index = var as usize;
        let lo = self.view.var_start[index] as usize;
        let hi = self.view.var_start[index + 1] as usize;
        let mut total: i64 = 0;
        for slot in lo..hi {
            let row = self.view.var_row[slot] as usize;
            let before = self.shortfall(row);
            let after = (self.view.rhs[row] - (self.lhs[row] + self.view.var_coeff[slot])).max(0);
            total = total.saturating_add(self.weight[row].saturating_mul(before - after));
        }
        total
    }

    /// RWLS plateau escape: bump (saturating at [`WEIGHT_CAP`]) the weight of
    /// every currently violated row.
    fn bump_weights(&mut self) {
        for &row in &self.violated {
            let slot = &mut self.weight[row as usize];
            if *slot < WEIGHT_CAP {
                *slot += 1;
            }
        }
    }

    /// BMS pick of the least-damaging member to remove, ties broken toward the
    /// least recently touched variable. Never picks the variable added by the
    /// previous swap unless it is the only member.
    fn pick_removal(&mut self) -> Option<u32> {
        let count = self.members.len();
        if count == 0 {
            return None;
        }
        let samples = BMS_SAMPLES.min(count);
        let mut best: Option<(u32, i64, u64)> = None;
        for _ in 0..samples {
            let pick = self.rng.below(count);
            let var = self.members[pick];
            if var == self.last_added && count > 1 {
                continue;
            }
            let cost = self.remove_cost(var);
            let age = self.age[var as usize];
            let better = best.is_none_or(|(_, best_cost, best_age)| {
                cost < best_cost || (cost == best_cost && age < best_age)
            });
            if better {
                best = Some((var, cost, age));
            }
        }
        if let Some((var, _, _)) = best {
            return Some(var);
        }
        let pick = self.rng.below(count);
        Some(self.members[pick])
    }

    /// Picks the variable to add: the best-gain non-selected variable of a
    /// RANDOM violated row (NuMVC's "random uncovered edge"), ties broken
    /// toward the least recently touched variable.
    fn pick_addition(&mut self, exclude: u32) -> Option<u32> {
        if self.violated.is_empty() {
            return None;
        }
        let pick = self.rng.below(self.violated.len());
        let row = self.violated[pick] as usize;
        let view = self.view;
        let mut best: Option<(u32, i64, u64)> = None;
        for (var, _) in view.row_entries(row) {
            if self.in_set[var as usize] || var == exclude {
                continue;
            }
            let gain = self.add_gain(var);
            let age = self.age[var as usize];
            let better = best.is_none_or(|(_, best_gain, best_age)| {
                gain > best_gain || (gain == best_gain && age < best_age)
            });
            if better {
                best = Some((var, gain, age));
            }
        }
        if let Some((var, _, _)) = best {
            return Some(var);
        }
        self.random_unselected().or(Some(exclude))
    }

    fn random_unselected(&mut self) -> Option<u32> {
        let count = self.view.ground.len();
        if count == 0 {
            return None;
        }
        for _ in 0..32 {
            let pick = self.rng.below(count);
            let var = self.view.ground[pick];
            if !self.in_set[var as usize] {
                return Some(var);
            }
        }
        None
    }

    /// One fixed-cardinality swap: remove one member, add one non-member, then
    /// bump the weights of the rows that are still violated. `|S|` is
    /// invariant across this call.
    pub(super) fn swap_step(&mut self) {
        self.steps += 1;
        let Some(out) = self.pick_removal() else {
            return;
        };
        self.remove_var(out);
        if let Some(into) = self.pick_addition(out) {
            self.add_var(into);
            self.last_added = into;
        } else {
            self.add_var(out);
            self.last_added = NONE;
        }
        self.bump_weights();
    }

    /// Greedy covering construction from the CURRENT selection: repeatedly add
    /// the best-gain candidate drawn from the violated rows until nothing is
    /// violated. Terminates because every violated row provably has a
    /// non-selected variable (rows that cannot reach their own rhs were
    /// rejected at build time) and each pick strictly lowers the shortfall.
    pub(super) fn greedy_complete(&mut self, stop: &dyn Fn() -> bool) -> bool {
        let mut guard = self.view.ground.len().saturating_add(1);
        while !self.violated.is_empty() {
            if guard == 0 || stop() {
                return false;
            }
            guard -= 1;
            let Some(var) = self.best_greedy_candidate() else {
                return false;
            };
            self.add_var(var);
        }
        true
    }

    fn best_greedy_candidate(&self) -> Option<u32> {
        let view = self.view;
        let mut best: Option<(u32, i64)> = None;
        let mut scored = 0usize;
        for index in 0..self.violated.len() {
            let row = self.violated[index] as usize;
            for (var, _) in view.row_entries(row) {
                if self.in_set[var as usize] {
                    continue;
                }
                let gain = self.add_gain(var);
                if best.is_none_or(|(_, best_gain)| gain > best_gain) {
                    best = Some((var, gain));
                }
                scored += 1;
            }
            if scored >= GREEDY_CAND_CAP && best.is_some() {
                break;
            }
        }
        best.map(|(var, _)| var)
    }
}
