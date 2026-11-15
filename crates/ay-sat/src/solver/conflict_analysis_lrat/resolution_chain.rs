// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Backward LRAT resolution-chain traversal.

use super::super::*;
use crate::kani_compat::DetHashSet;
use crate::solver::clause_add::terminal;
use crate::solver::conflict_analysis_minimize_lrat::root;

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
        match self.collect_resolution_chain_admitted(
            seed_clause,
            skip_var,
            rup_satisfied,
            &root::Ordinary,
        ) {
            Ok((chain, _)) => chain,
            Err(never) => match never {},
        }
    }

    /// Collect a complete chain, refusing to silently omit a required clause.
    pub(in crate::solver) fn collect_complete_resolution_chain(
        &mut self,
        seed_clause: ClauseRef,
        skip_var: Option<usize>,
        rup_satisfied: &DetHashSet<Literal>,
    ) -> Option<Vec<u64>> {
        match self.collect_resolution_chain_admitted(
            seed_clause,
            skip_var,
            rup_satisfied,
            &root::Ordinary,
        ) {
            Ok((chain, complete)) => complete.then_some(chain),
            Err(never) => match never {},
        }
    }

    pub(in crate::solver) fn collect_resolution_chain_admitted<P: terminal::Policy>(
        &mut self,
        seed_clause: ClauseRef,
        skip_var: Option<usize>,
        rup_satisfied: &DetHashSet<Literal>,
        p: &P,
    ) -> Result<(Vec<u64>, bool), P::Error> {
        let mut chain = Vec::new();
        let mut complete = true;
        self.clear_resolution_chain_marks_admitted(p)?;

        let seed_idx = seed_clause.0 as usize;
        if seed_idx >= self.arena.len() {
            return Ok((chain, false));
        }
        p.work(8)?;
        let seed_id = self.clause_id(seed_clause);
        let seed_lits = self.arena.literals(seed_idx);
        // Under RUP, a seed containing an assumed-true literal cannot conflict.
        // Its transitive dependencies still need to be marked and traversed.
        let seed_is_satisfied = Self::resolution_clause_satisfied(seed_lits, rup_satisfied, p)?;
        if seed_id != 0 && !seed_is_satisfied {
            p.work(2)?;
            p.reserve(&mut chain, 1)?;
            chain.push(seed_id);
        } else if !seed_is_satisfied {
            complete = false;
        }
        for &lit in seed_lits {
            p.work(8)?;
            let vi = lit.variable().index();
            if vi < self.num_vars && self.min.minimize_flags[vi] & LRAT_A == 0 {
                p.reserve(&mut self.min.lrat_to_clear, 1)?;
                p.work(3)?; // mark, dirty registration, exceptional retirement
                self.min.minimize_flags[vi] |= LRAT_A;
                self.min.lrat_to_clear.push(vi);
            }
        }

        for trail_idx in (0..self.trail.len()).rev() {
            p.work(32)?;
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
                complete &= self.append_resolution_reason_admitted(
                    ClauseRef(reason_raw),
                    rup_satisfied,
                    &mut chain,
                    p,
                )?;
                continue;
            }
            // A deleted reason whose propagated literal is assumed true would
            // itself be satisfied and must not appear in the RUP chain (#5026).
            if !rup_satisfied.is_empty() {
                p.filter(rup_satisfied)?;
            }
            if !rup_satisfied.is_empty() && rup_satisfied.contains(&trail_lit) {
                continue;
            }
            if let Some(unit_id) = self.visible_unit_proof_id_for_lit(trail_lit) {
                p.reserve(&mut chain, 1)?;
                chain.push(unit_id);
            } else if let Some(id) = self.level0_var_proof_id(vi) {
                p.reserve(&mut chain, 1)?;
                chain.push(id);
            } else {
                complete = false;
            }
        }

        self.clear_resolution_chain_marks_admitted(p)?;
        Ok((chain, complete))
    }

    fn append_resolution_reason_admitted<P: terminal::Policy>(
        &mut self,
        reason_ref: ClauseRef,
        rup_satisfied: &DetHashSet<Literal>,
        chain: &mut Vec<u64>,
        p: &P,
    ) -> Result<bool, P::Error> {
        p.work(8)?;
        let reason_idx = reason_ref.0 as usize;
        if reason_idx >= self.arena.len() {
            return Ok(false);
        }
        let reason_lits = self.arena.literals(reason_idx);
        let reason_is_satisfied = Self::resolution_clause_satisfied(reason_lits, rup_satisfied, p)?;
        let reason_id = self.clause_id(reason_ref);
        if !reason_is_satisfied && reason_id != 0 {
            p.reserve(chain, 1)?;
            chain.push(reason_id);
        }
        for &reason_lit in reason_lits {
            p.work(8)?;
            let vi = reason_lit.variable().index();
            if vi < self.num_vars && self.min.minimize_flags[vi] & LRAT_A == 0 {
                p.reserve(&mut self.min.lrat_to_clear, 1)?;
                p.work(3)?;
                self.min.minimize_flags[vi] |= LRAT_A;
                self.min.lrat_to_clear.push(vi);
            }
        }
        Ok(reason_is_satisfied || reason_id != 0)
    }

    fn clear_resolution_chain_marks_admitted<P: terminal::Policy>(
        &mut self,
        p: &P,
    ) -> Result<(), P::Error> {
        p.work(self.min.lrat_to_clear.len())?;
        for &idx in &self.min.lrat_to_clear {
            self.min.minimize_flags[idx] &= !LRAT_A;
        }
        self.min.lrat_to_clear.clear();
        Ok(())
    }

    fn resolution_clause_satisfied<P: terminal::Policy>(
        lits: &[Literal],
        filter: &DetHashSet<Literal>,
        p: &P,
    ) -> Result<bool, P::Error> {
        if filter.is_empty() {
            return Ok(false);
        }
        for lit in lits {
            p.work(1)?;
            p.filter(filter)?;
            if filter.contains(lit) {
                return Ok(true);
            }
        }
        Ok(false)
    }
}
