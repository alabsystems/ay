// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exclusive, fresh source registration using the ordinary allocator/ledger.

use super::*;
use crate::counted_storage::{try_reserved_exact, Result};
use crate::decision_trace::counted_decision::invalid;
use crate::initial_cnf::CountedInitialCnf;
use ay_core::original_query::CountedAdmission;

mod empty;
mod reserve;
#[cfg(test)]
mod tests;

pub(in crate::solver) struct InstalledOriginals {
    pub(in crate::solver) ids: Vec<Option<u64>>,
    pub(in crate::solver) empty: Option<(usize, u64)>,
}

/// No solver borrow escapes. Only the shared source-empty publication kernel
/// may interleave a derived ID; each transition advances the expected state.
struct Fresh<'a> {
    solver: &'a mut Solver,
    owner: &'a CountedAdmission,
    registered: usize,
    next: u64,
    next_original: u64,
    issued: u64,
    prefix: usize,
    previous: Option<u64>,
}

pub(in crate::solver) fn install(
    solver: &mut Solver,
    input: &CountedInitialCnf,
    owner: &CountedAdmission,
) -> Result<InstalledOriginals> {
    if !input.owner().shares_ledger_with(owner) || input.num_vars() != solver.num_vars {
        return Err(invalid(
            owner,
            "fresh original input owner or namespace mismatch",
        ));
    }
    let mut session = Fresh::new(solver, owner)?;
    let mut installed = InstalledOriginals {
        ids: try_reserved_exact(owner, input.len())?,
        empty: None,
    };
    for index in 0..input.len() {
        owner.admit(4, 0)?;
        let row = input
            .clause(index)?
            .ok_or_else(|| invalid(owner, "missing original source row"))?;
        if !row.original().is_empty() {
            // Same original-add pending marker, including skipped tautologies.
            session.solver.cold.ic3_new_clauses_pending = true;
        }
        let id = if let Some(literals) = row.normalized() {
            let id = session.append(literals)?;
            if literals.is_empty() && installed.empty.is_none() {
                installed.empty = Some((index, id));
            }
            Some(id)
        } else {
            session.skip(row.original())?
        };
        installed.ids.push(id);
    }
    owner.check()?;
    Ok(installed)
}

impl<'a> Fresh<'a> {
    fn new(solver: &'a mut Solver, owner: &'a CountedAdmission) -> Result<Self> {
        owner.admit(128, 0)?;
        if !solver.arena.is_empty()
            || !solver.cold.original_ledger.is_empty()
            || solver.has_empty_clause
            || solver.cold.next_clause_id != 1
            || solver.cold.next_original_clause_id != 1
            || solver.cold.issued_original_clause_id_max != 0
            || !solver.cold.original_clause_id_bits.is_empty()
            || solver.cold.registered_original_clause_id.is_some()
            || solver.proof_manager.is_some()
            || solver.cold.forward_checker.is_some()
            || solver.cold.internal_lrat_enabled
            || solver.cold.proof_bookkeeping_budget.is_some()
            || solver.consuming_trace_pending()
            || !solver.cold.scope_selectors.is_empty()
            || solver.cold.diagnostic_trace.is_some()
            || solver.gc_occ.is_some()
            || solver.cold.decision_trace.is_some()
            || solver.cold.replay_trace.is_some()
            || solver.cold.factor_marks_undo.is_some()
            || solver.cold.incremental_solve_count != 0
            || solver.cold.has_solved_once
            || !solver.trail.is_empty()
            || !solver
                .cold
                .counted_admission
                .as_ref()
                .is_some_and(|a| a.shares_ledger_with(owner))
            || solver.cold.clause_trace.as_ref().is_some_and(|t| {
                !t.entries().is_empty() || t.is_truncated() || t.proof_work_exhausted()
            })
        {
            return Err(invalid(
                owner,
                "original registration requires an exclusive fresh namespace",
            ));
        }
        if solver.cold.lrat_enabled != solver.cold.clause_trace.is_some() {
            return Err(invalid(owner, "fresh original trace selection mismatch"));
        }
        Ok(Self {
            solver,
            owner,
            registered: 0,
            next: 1,
            next_original: 1,
            issued: 0,
            prefix: 0,
            previous: None,
        })
    }

    fn next_id(&self) -> Result<u64> {
        self.owner.admit(32, 0)?;
        if self.solver.cold.next_clause_id != self.next
            || self.solver.cold.next_original_clause_id != self.next_original
            || self.solver.cold.original_ledger.num_clauses() != self.registered
            || self.solver.cold.issued_original_clause_id_max != self.issued
        {
            return Err(invalid(
                self.owner,
                "interleaved original or derived ID issuance",
            ));
        }
        let id = self.next.max(self.next_original);
        if id >= u64::MAX - 1 {
            return Err(invalid(self.owner, "fresh original ID namespace exhausted"));
        }
        Ok(id)
    }

    fn skip(&mut self, raw: &[Literal]) -> Result<Option<u64>> {
        let id = self.next_id()?;
        if !self.solver.cold.lrat_enabled {
            return Ok(None);
        }
        reserve::identity(self.solver, self.owner)?;
        self.owner.check()?;
        self.solver.reserve_skipped_original_lrat_id(raw);
        self.next = id + 1;
        self.next_original = id + 1;
        self.issued = id;
        self.next_id()?;
        Ok(Some(id))
    }

    fn append(&mut self, literals: &[Literal]) -> Result<u64> {
        let id = self.next_id()?;
        let owner = self.owner;
        let offset = reserve::row(self.solver, literals.len(), owner)?;
        if let Some(trace) = self.solver.cold.clause_trace.as_mut() {
            let authority = FreshInputTraceEvent {
                id,
                prefix: self.prefix,
                previous: self.previous,
                kind: FreshEventKind::Original,
                owner,
            };
            let prepared = trace.prepare_counted_original(&authority, literals)?;
            owner.check()?;
            // Commit is callback/allocation-free. The following shared identity
            // and DB kernels cannot observe external state; this private solver
            // never escapes if their postcondition or the final fence fails.
            prepared.commit();
            self.prefix += 1;
            self.previous = Some(id);
        } else {
            owner.check()?;
        }
        let issued = self
            .solver
            .register_original_identity(literals, OriginalLifetime::Scoped);
        if issued != id {
            return Err(invalid(
                owner,
                "ordinary original allocator changed reserved identity",
            ));
        }
        self.solver.cold.incremental_original_boundary =
            self.solver.cold.original_ledger.num_clauses();
        self.solver.cold.uniform_formula_cache = None;
        self.registered += 1;
        self.next = id + 1;
        self.next_original = id + 1;
        self.issued = id;
        if let Some(offset) = offset {
            if self
                .solver
                .add_registered_original_clause_db(literals, issued)
                != offset
            {
                return Err(invalid(owner, "admitted original arena offset changed"));
            }
        } else {
            self.empty(id)?;
        }
        self.next_id()?;
        owner.check()?;
        Ok(issued)
    }
}
