// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The actual original-ledger and live-arena validators, shared by ordinary
//! publication and the counted model transaction. No diagnostic allocation is
//! needed to locate a violation.

use super::*;
use crate::reconstruct::admitted::Work;
use crate::reconstruct::replay::clause_satisfied_admitted;

pub(in crate::solver) enum ArenaMode {
    Full,
    SkipInprocessing,
}

pub(in crate::solver) enum OriginalDomain {
    Full,
    Configured,
}

impl Solver {
    pub(in crate::solver) fn current_model_admitted<P: Work>(
        &self,
        policy: &P,
    ) -> Result<Vec<bool>, P::Error> {
        let mut model = policy.zeros(self.num_vars)?;
        for (v, value) in model.iter_mut().enumerate() {
            policy.work(1)?;
            *value = self.vals[v * 2] > 0;
        }
        Ok(model)
    }

    pub(in crate::solver) fn external_model_admitted<P: Work>(
        &self,
        model: &[bool],
        policy: &P,
    ) -> Result<Vec<bool>, P::Error> {
        let mut external = policy.zeros(self.cold.e2i.len())?;
        for (ext, value) in external.iter_mut().enumerate() {
            policy.work(1)?;
            let internal = self.cold.e2i[ext];
            if internal == compact::UNMAPPED {
                if ext < self.cold.eliminated_ext_vals.len() {
                    *value = self.cold.eliminated_ext_vals[ext];
                }
            } else if (internal as usize) < model.len() {
                // The supplied model, not vals, is authoritative for walk SAT.
                *value = model[internal as usize];
            }
        }
        Ok(external)
    }

    pub(in crate::solver) fn internal_model_admitted<P: Work>(
        &self,
        external: &[bool],
        policy: &P,
    ) -> Result<(Vec<bool>, Option<(usize, usize)>), P::Error> {
        let mut internal = policy.zeros(self.num_vars)?;
        for (var, value) in internal.iter_mut().enumerate() {
            policy.work(1)?;
            let ext = self.cold.i2e[var] as usize;
            if ext >= external.len() {
                return Ok((internal, Some((var, ext))));
            }
            *value = external[ext];
        }
        Ok((internal, None))
    }

    pub(in crate::solver) fn first_unit_model_violation_admitted<P: Work>(
        &self,
        model: &[bool],
        policy: &P,
    ) -> Result<Option<(usize, Literal, usize, bool)>, P::Error> {
        for (index, clause) in self.cold.original_ledger.iter_clauses().enumerate() {
            policy.work(1)?;
            if clause.len() != 1 {
                continue;
            }
            let lit = clause[0];
            let ext = lit.variable().index();
            if ext >= self.cold.e2i.len() {
                continue;
            }
            let internal = self.cold.e2i[ext];
            if internal != compact::UNMAPPED {
                let var = internal as usize;
                if var < model.len() && model[var] != lit.is_positive() {
                    return Ok(Some((index, lit, var, model[var])));
                }
            }
        }
        Ok(None)
    }

    pub(in crate::solver) fn first_original_violation_admitted<P: Work>(
        &self,
        model: &[bool],
        domain: OriginalDomain,
        policy: &P,
    ) -> Result<Option<usize>, P::Error> {
        for (index, clause) in self.cold.original_ledger.iter_clauses().enumerate() {
            policy.work(1)?;
            if self.original_clause_is_outside_model(clause, &domain, policy)? {
                continue;
            }
            if !clause_satisfied_admitted(clause, model, policy)? {
                return Ok(Some(index));
            }
        }
        Ok(None)
    }

    fn original_clause_is_outside_model<P: Work>(
        &self,
        clause: &[Literal],
        selection: &OriginalDomain,
        policy: &P,
    ) -> Result<bool, P::Error> {
        if self.cold.has_ever_scoped {
            for lit in clause {
                policy.work(1)?;
                let ext = lit.variable().index();
                if ext < self.cold.was_scope_selector.len() && self.cold.was_scope_selector[ext] {
                    return Ok(true);
                }
            }
        }
        if let (OriginalDomain::Configured, Some(domain)) = (selection, &self.active_domain) {
            for lit in clause {
                policy.work(1)?;
                let ext = lit.variable().index();
                let internal = self.cold.e2i.get(ext).copied().unwrap_or(compact::UNMAPPED);
                if internal == compact::UNMAPPED
                    || internal as usize >= domain.len()
                    || !domain[internal as usize]
                {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    pub(in crate::solver) fn first_arena_violation_admitted<P: Work>(
        &self,
        model: &[bool],
        mode: ArenaMode,
        policy: &P,
    ) -> Result<Option<usize>, P::Error> {
        // ArenaIter can skip multiple zero/deleted headers in one next().
        // Prepay its whole bounded header-stride walk before the first next;
        // literal inspection below is separately charged at each real visit.
        policy.work(self.arena.len())?;
        for index in self.arena.indices() {
            policy.work(1)?;
            if self.arena.is_empty_clause(index) || self.arena.is_garbage_any(index) {
                continue;
            }
            let lits = self.arena.literals(index);
            if matches!(mode, ArenaMode::SkipInprocessing) {
                let mut skip = false;
                for lit in lits {
                    policy.work(1)?;
                    let var = lit.variable().index();
                    if var >= self.user_num_vars
                        || (var < self.var_lifecycle.len() && self.var_lifecycle.is_removed(var))
                    {
                        skip = true;
                        break;
                    }
                }
                if skip {
                    continue;
                }
            }
            if !clause_satisfied_admitted(lits, model, policy)? {
                return Ok(Some(index));
            }
        }
        Ok(None)
    }
}
