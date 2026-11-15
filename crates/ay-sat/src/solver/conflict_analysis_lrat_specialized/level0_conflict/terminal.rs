// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One root-proof graph for ordinary and counted terminal publication.
use super::*;
use crate::solver::clause_add::terminal::Policy;

impl Solver {
    pub(in crate::solver) fn record_lrat_level0_conflict_admitted<P: Policy>(
        &mut self,
        reference: ClauseRef,
        p: &P,
    ) -> Result<(), P::Error> {
        p.conflict(self, reference)?;
        self.materialize_level0_unit_proofs_impl(false, p)?;
        p.enter_chain(self, &[])?;
        let len = self.arena.literals(reference.0 as usize).len();
        p.work(len)?;
        let mut lits = Vec::new();
        p.reserve(&mut lits, len)?;
        lits.extend_from_slice(self.arena.literals(reference.0 as usize));
        self.seed_terminal_chain_admitted(&lits, p)?;
        let mut units = Vec::new();
        self.emit_level0_unit_chain_filtered(None, p, |_, id| {
            p.reserve(&mut units, 1)?;
            units.push(id);
            Ok(())
        })?;
        p.work(8)?;
        let id = self.materialize_level0_conflict_clause_id(reference, &lits);
        let mut hints = Vec::new();
        for hint in units.into_iter().rev() {
            p.work(2)?;
            if hint != 0 {
                p.reserve(&mut hints, 1)?;
                hints.push(hint);
            }
        }
        if id != 0 {
            p.reserve(&mut hints, 1)?;
            hints.push(id);
        }
        let trace_chain = self.terminal_trace_chain_admitted(reference, p)?;
        // The selected external proof-manager route is refused at counted
        // entry. Ordinary still runs its exact visibility check here.
        let proof_complete = self.level0_conflict_proof_chain_complete(&lits, &hints, id);
        let trace_complete =
            self.terminal_trace_complete_admitted(trace_chain.as_deref(), id, p)?;
        if !proof_complete || !trace_complete {
            // Never attach a partial terminal chain. The semantic UNSAT result
            // remains valid, while every certificate consumer fails closed.
            //
            // The consumer reports this as "proof bookkeeping was exhausted",
            // the same marker the #A2b work budget sets, so name the real
            // cause here: no budget is involved, and the usual culprit is a
            // root assignment with no derivation at all.
            tracing::debug!(
                proof_complete,
                trace_complete,
                conflict_len = lits.len(),
                unjustified_root_assignments = self.unjustified_root_assignment_count(),
                "level-0 conflict chain incomplete: clause trace marked proof_work_exhausted \
                 (not a budget exhaustion)"
            );
            if let Some(trace) = self.live_clause_trace_mut() {
                trace.mark_proof_work_exhausted();
            }
            self.refresh_proof_consumer_state();
            self.mark_empty_clause_deferred_for_bounded_proof();
            return Ok(());
        }
        self.mark_empty_clause_admitted(&hints, trace_chain.unwrap_or_default(), p)
    }

    fn seed_terminal_chain_admitted<P: Policy>(
        &mut self,
        lits: &[Literal],
        p: &P,
    ) -> Result<(), P::Error> {
        p.work(self.min.lrat_to_clear.len())?;
        for &idx in &self.min.lrat_to_clear {
            self.min.minimize_flags[idx] &= !LRAT_A;
        }
        self.min.lrat_to_clear.clear();
        for &lit in lits {
            p.work(4)?;
            let vi = lit.variable().index();
            if vi < self.var_data.len() && self.min.minimize_flags[vi] & LRAT_A == 0 {
                p.mark(self)?;
                self.min.minimize_flags[vi] |= LRAT_A;
                self.min.lrat_to_clear.push(vi);
            }
        }
        Ok(())
    }

    fn terminal_trace_chain_admitted<P: Policy>(
        &mut self,
        reference: ClauseRef,
        p: &P,
    ) -> Result<Option<Vec<u64>>, P::Error> {
        let filter = p.new_filter(0)?;
        let (mut chain, complete) =
            self.collect_resolution_chain_admitted(reference, None, &filter, p)?;
        if !complete {
            return Ok(None);
        }
        p.work(chain.len())?;
        chain.reverse();
        let mut seen = p.new_ids(chain.len())?;
        let mut retained = 0;
        for i in 0..chain.len() {
            p.work(3)?;
            p.ids(&seen)?;
            let id = chain[i];
            if seen.insert(id) {
                chain[retained] = id;
                retained += 1;
            }
        }
        chain.truncate(retained);
        Ok(Some(chain))
    }

    fn terminal_trace_complete_admitted<P: Policy>(
        &mut self,
        chain: Option<&[u64]>,
        id: u64,
        p: &P,
    ) -> Result<bool, P::Error> {
        if self.live_clause_trace().is_none() {
            return Ok(true);
        }
        let Some(chain) = chain else {
            return Ok(false);
        };
        let mut missing = p.new_ids(chain.len())?;
        for &id in chain {
            p.work(1)?;
            p.ids(&missing)?;
            missing.insert(id);
        }
        if self.consuming_trace_pending() {
            for id in chain {
                p.work(1)?;
                match self.consuming_original_contains(*id) {
                    Some(true) => {
                        p.ids(&missing)?;
                        missing.remove(id);
                    }
                    Some(false) => (),
                    None => return Ok(false),
                }
            }
        }
        let Some(trace) = self.live_clause_trace() else {
            return Ok(false);
        };
        for entry in trace.entries() {
            p.work(2)?;
            p.ids(&missing)?;
            missing.remove(&entry.id);
            if missing.is_empty() {
                break;
            }
        }
        p.work(chain.len().saturating_add(4))?;
        Ok(!trace.is_truncated()
            && !trace.proof_work_exhausted()
            && chain.last() == Some(&id)
            && chain.iter().all(|&id| id != 0)
            && missing.is_empty())
    }
}
