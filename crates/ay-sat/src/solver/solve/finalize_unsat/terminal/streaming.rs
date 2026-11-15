// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

impl Solver {
    pub(in crate::solver) fn finalize_streaming_core_admitted<P: root::Policy>(
        &mut self,
        p: &P,
    ) -> Result<(), P::Error> {
        let num_originals = self.cold.streaming_core_num_originals;
        if num_originals == 0 || self.cold.streaming_core.is_none() {
            return Ok(());
        }

        // Phase 1: Collect original clause IDs to mark (avoids borrow conflicts).
        let mut ids_to_mark: Vec<u64> = Vec::new();

        // Mark any falsified original clause.
        // live_indices (husk adjudication): skip garbage-kept husks, and keep
        // scanning past falsified clauses without a usable original ID
        // (cid==0 husks previously hit the unconditional `break`, silently
        // emptying the streaming-support seed).
        // The arena iterator can skip dead records internally; its total
        // header/skip work is bounded by the actual word length, paid first.
        p.work(self.arena.len())?;
        for offset in self.arena.live_indices() {
            p.work(8)?;
            let lits = self.arena.literals(offset);
            if lits.is_empty() {
                continue;
            }
            p.work(lits.len())?;
            if lits.iter().all(|lit| self.lit_val(*lit) < 0) {
                let cid = if offset < self.cold.clause_ids.len() {
                    self.cold.clause_ids[offset]
                } else {
                    0
                };
                if cid > 0 && cid <= num_originals && self.is_original_clause_id(cid) {
                    p.reserve(&mut ids_to_mark, 1)?;
                    ids_to_mark.push(cid);
                    // Only need first falsified original clause.
                    break;
                }
            }
        }

        // Mark original clauses referenced by level-0 trail variable reasons.
        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        for i in 0..level0_end {
            p.work(32)?;
            let var_idx = self.trail[i].variable().index();
            if var_idx >= self.var_data.len() || self.var_data[var_idx].level != 0 {
                continue;
            }

            // Check arena reason.
            // #8467: lazy theory reasons are table indexes, not arena offsets —
            // indexing clause_ids with one would mark an unrelated original.
            let reason_raw = self.var_data[var_idx].reason;
            if is_clause_reason(reason_raw) && !self.var_data[var_idx].is_lazy_theory_reason() {
                let reason_offset = reason_raw as usize;
                let reason_id = if reason_offset < self.cold.clause_ids.len() {
                    self.cold.clause_ids[reason_offset]
                } else {
                    0
                };
                if reason_id > 0
                    && reason_id <= num_originals
                    && self.is_original_clause_id(reason_id)
                {
                    p.reserve(&mut ids_to_mark, 1)?;
                    ids_to_mark.push(reason_id);
                }
            }

            // Check signed unit proof IDs (for clauses whose arena reference was cleared).
            let lit = self.trail[i];
            if let Some(pid) = self.visible_unit_proof_id_for_lit(lit) {
                if pid > 0 && pid <= num_originals && self.is_original_clause_id(pid) {
                    p.reserve(&mut ids_to_mark, 1)?;
                    ids_to_mark.push(pid);
                }
            }

            // Check signed level0_proof_id fallback.
            if let Some(pid) = self.level0_var_proof_id_for_lit(lit) {
                if pid > 0 && pid <= num_originals && self.is_original_clause_id(pid) {
                    p.reserve(&mut ids_to_mark, 1)?;
                    ids_to_mark.push(pid);
                }
            }
        }

        // Phase 2: Apply marks to the bitmap.
        if let Some(ref mut bitmap) = self.cold.streaming_core {
            for cid in ids_to_mark {
                p.work(1)?;
                bitmap[(cid - 1) as usize] = true;
            }
        }
        Ok(())
    }

    pub(in crate::solver) fn extract_streaming_core_admitted<P: root::Policy>(
        &self,
        p: &P,
    ) -> Result<Option<Vec<u64>>, P::Error> {
        let Some(bitmap) = self.cold.streaming_core.as_ref() else {
            return Ok(None);
        };
        let mut core = Vec::new();
        for (i, &marked) in bitmap.iter().enumerate() {
            p.work(2)?;
            if marked {
                p.reserve(&mut core, 1)?;
                core.push((i as u64) + 1);
            }
        }
        // Reservation charges replacement-capacity retirement already. This
        // also prepays terminal result destruction if the enclosing driver
        // refuses at its final original-owner fence after we return it.
        p.work(core.capacity().saturating_add(1))?;
        Ok((!core.is_empty()).then_some(core))
    }
}
