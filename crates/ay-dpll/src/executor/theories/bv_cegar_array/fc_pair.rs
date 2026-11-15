// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    pub(super) fn append_fc_group_refinement(
        &mut self,
        group: &[FcConcreteSelect],
        already_covered: &HashSet<FcCoverKey>,
        build: &mut CegarArrayBuild,
    ) -> bool {
        // Each edge joins two currently unequal values. Connect the anchor
        // to every different-valued member, then one such member to the other
        // anchor-valued members. This gives a violated spanning tree: n-1
        // valid FC axioms force all values equal when these indices coincide,
        // while later models with changed indices are audited again. The old
        // all-pairs scan exceeded MAX_PAIR_ATTEMPTS at 182 selects, even
        // though only the last select disagreed with the other 181.
        let Some(anchor) = group.first() else {
            return true;
        };
        let Some(opposite) = group
            .iter()
            .skip(1)
            .find(|entry| entry.value != anchor.value)
        else {
            return true;
        };
        for right in group.iter().skip(1) {
            if !self.count_pair_attempt(build) {
                return false;
            }
            let left = if right.value == anchor.value {
                opposite
            } else {
                anchor
            };
            if left.select == right.select {
                continue;
            }
            if !self.append_fc_pair_refinement(left, right, &[], &[], already_covered, build) {
                return false;
            }
        }
        true
    }

    /// Shared per-pair budget/abort accounting for the group loops.
    pub(super) fn count_pair_attempt(&mut self, build: &mut CegarArrayBuild) -> bool {
        build.pair_attempts = build.pair_attempts.saturating_add(1);
        build.pair_attempts <= budget::MAX_PAIR_ATTEMPTS
            && !(build.pair_attempts & 0xff == 0 && self.should_abort_theory_loop())
    }

    /// Emit the FC axiom for one disagreeing select pair, with
    /// value clauses guarded by `guards` (empty for the unguarded
    /// same-array lemma; the equality-path atoms for the
    /// conditional cross-array congruence) and restricted away
    /// from `stored_idx_bits` (store indices on a definition path).
    pub(super) fn append_fc_pair_refinement(
        &mut self,
        left: &FcConcreteSelect,
        right: &FcConcreteSelect,
        guards: &[i32],
        stored_idx_bits: &[BvBits],
        already_covered: &HashSet<FcCoverKey>,
        build: &mut CegarArrayBuild,
    ) -> bool {
        let (lo, hi) = if left.select < right.select {
            (left.select, right.select)
        } else {
            (right.select, left.select)
        };
        let mut key_guards: Vec<i32> = guards.to_vec();
        key_guards.sort_unstable();
        key_guards.dedup();
        let mut key_stored: Vec<BvBits> = stored_idx_bits.to_vec();
        key_stored.sort();
        let key: FcCoverKey = (lo, hi, key_guards, key_stored);
        if already_covered.contains(&key) {
            return false;
        }
        let Some((pair_vars, pair_clauses)) = budget::pair_cost(
            &left.index_lits,
            &right.index_lits,
            &left.value_lits,
            &right.value_lits,
            stored_idx_bits,
        ) else {
            return false;
        };
        let Some(next_vars) = build.new_vars.checked_add(pair_vars) else {
            return false;
        };
        let Some(next_clauses) = build.clauses.len().checked_add(pair_clauses) else {
            return false;
        };
        let last_var = (build.next_var as usize).saturating_add(pair_vars.saturating_sub(1));
        if pair_clauses == 0 {
            return false;
        }
        if next_vars > budget::MAX_NEW_VARS
            || next_clauses > budget::MAX_NEW_CLAUSES
            || (pair_vars > 0 && last_var > i32::MAX as usize)
        {
            // Out of per-check budget: skip WITHOUT covering, so a
            // later round can emit this instance; the caller turns
            // the clauses accumulated so far into a partial
            // refinement.
            build.budget_exhausted = true;
            return true;
        }
        if !build.newly_covered.insert(key) {
            return true;
        }
        let clauses = generate_fc_axiom_clauses(
            &left.index_lits,
            &right.index_lits,
            &left.value_lits,
            &right.value_lits,
            guards,
            stored_idx_bits,
            &mut build.next_var,
        );
        if clauses.len() != pair_clauses {
            return false;
        }
        build.new_vars = next_vars;
        build.clauses.extend(clauses);
        true
    }
}
