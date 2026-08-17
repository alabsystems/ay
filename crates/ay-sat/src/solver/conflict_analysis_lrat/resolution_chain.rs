// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Backward LRAT resolution-chain traversal.

use super::super::*;
use crate::kani_compat::DetHashSet;

impl Solver {
    /// `rup_satisfied`: literals satisfied by the RUP assumption for the derived
    /// clause. Reason clauses containing any of these literals are trivially
    /// satisfied and must be omitted from the hint chain — strict checkers
    /// reject hints with non-falsified literals (#5026).
    pub(crate) fn collect_resolution_chain(
        &mut self,
        seed_clause: ClauseRef,
        skip_var: Option<usize>,
        rup_satisfied: &DetHashSet<Literal>,
    ) -> Vec<u64> {
        self.collect_resolution_chain_impl(seed_clause, skip_var, rup_satisfied)
            .0
    }

    /// Collect a complete chain, refusing to silently omit a required clause.
    pub(in crate::solver) fn collect_complete_resolution_chain(
        &mut self,
        seed_clause: ClauseRef,
        skip_var: Option<usize>,
        rup_satisfied: &DetHashSet<Literal>,
    ) -> Option<Vec<u64>> {
        let (chain, complete) =
            self.collect_resolution_chain_impl(seed_clause, skip_var, rup_satisfied);
        complete.then_some(chain)
    }

    fn collect_resolution_chain_impl(
        &mut self,
        seed_clause: ClauseRef,
        skip_var: Option<usize>,
        rup_satisfied: &DetHashSet<Literal>,
    ) -> (Vec<u64>, bool) {
        let mut chain = Vec::new();
        let mut complete = true;
        self.clear_resolution_chain_marks();

        let seed_idx = seed_clause.0 as usize;
        if seed_idx >= self.arena.len() {
            return (chain, false);
        }
        let seed_id = self.clause_id(seed_clause);
        let seed_lits = self.arena.literals(seed_idx);
        // Under RUP, a seed containing an assumed-true literal cannot conflict.
        // Its transitive dependencies still need to be marked and traversed.
        let seed_is_satisfied =
            !rup_satisfied.is_empty() && seed_lits.iter().any(|l| rup_satisfied.contains(l));
        if seed_id != 0 && !seed_is_satisfied {
            chain.push(seed_id);
        } else if !seed_is_satisfied {
            complete = false;
        }
        for &lit in seed_lits {
            let vi = lit.variable().index();
            if vi < self.num_vars && self.min.minimize_flags[vi] & LRAT_A == 0 {
                self.min.minimize_flags[vi] |= LRAT_A;
                self.min.lrat_to_clear.push(vi);
            }
        }

        for trail_idx in (0..self.trail.len()).rev() {
            let trail_lit = self.trail[trail_idx];
            let vi = trail_lit.variable().index();
            if vi >= self.num_vars
                || self.min.minimize_flags[vi] & LRAT_A == 0
                || skip_var == Some(vi)
            {
                continue;
            }
            let vd = self.var_data[vi];
            let reason_raw = vd.reason;
            // Lazy-theory reasons contain a table index, not an arena offset.
            // Treat them like deleted reasons and use only authenticated unit
            // fallbacks; fabricating an arena antecedent would be unsound.
            if is_clause_reason(reason_raw) && !vd.is_lazy_theory_reason() {
                complete &=
                    self.append_resolution_reason(ClauseRef(reason_raw), rup_satisfied, &mut chain);
                continue;
            }
            // A deleted reason whose propagated literal is assumed true would
            // itself be satisfied and must not appear in the RUP chain (#5026).
            if !rup_satisfied.is_empty() && rup_satisfied.contains(&trail_lit) {
                continue;
            }
            if let Some(unit_id) = self.visible_unit_proof_id_for_lit(trail_lit) {
                chain.push(unit_id);
            } else if let Some(id) = self.level0_var_proof_id(vi) {
                chain.push(id);
            } else {
                complete = false;
            }
        }

        self.clear_resolution_chain_marks();
        (chain, complete)
    }

    fn append_resolution_reason(
        &mut self,
        reason_ref: ClauseRef,
        rup_satisfied: &DetHashSet<Literal>,
        chain: &mut Vec<u64>,
    ) -> bool {
        let reason_idx = reason_ref.0 as usize;
        if reason_idx >= self.arena.len() {
            return false;
        }
        let reason_lits = self.arena.literals(reason_idx);
        let reason_is_satisfied =
            !rup_satisfied.is_empty() && reason_lits.iter().any(|l| rup_satisfied.contains(l));
        let reason_id = self.clause_id(reason_ref);
        if !reason_is_satisfied && reason_id != 0 {
            chain.push(reason_id);
        }
        for &reason_lit in reason_lits {
            let vi = reason_lit.variable().index();
            if vi < self.num_vars && self.min.minimize_flags[vi] & LRAT_A == 0 {
                self.min.minimize_flags[vi] |= LRAT_A;
                self.min.lrat_to_clear.push(vi);
            }
        }
        reason_is_satisfied || reason_id != 0
    }

    fn clear_resolution_chain_marks(&mut self) {
        for &idx in &self.min.lrat_to_clear {
            self.min.minimize_flags[idx] &= !LRAT_A;
        }
        self.min.lrat_to_clear.clear();
    }
}
