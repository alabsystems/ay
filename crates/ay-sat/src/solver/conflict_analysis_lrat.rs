// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LRAT learned clause management, resolution chain collection, and
//! eager subsumption for conflict analysis.
//!
//! Proof ID queries and level-0 unit chain BFS are in
//! `conflict_analysis_lrat_unit_chain.rs`.
//! Resolution-chain traversal is in `conflict_analysis_lrat/resolution_chain.rs`.

mod resolution_chain;

use super::*;
use crate::solver_log::solver_log;

impl Solver {
    #[allow(clippy::ptr_arg)]
    pub(super) fn add_learned_clause_inner(
        &mut self,
        lits: &mut Vec<Literal>,
        lbd: u32,
        resolution_chain: &[u64],
    ) -> ClauseRef {
        self.add_learned_clause_inner_with_proof_hints(lits, lbd, resolution_chain, None)
    }

    #[allow(clippy::ptr_arg)]
    fn add_learned_clause_inner_with_proof_hints(
        &mut self,
        lits: &mut Vec<Literal>,
        lbd: u32,
        resolution_chain: &[u64],
        precomputed_lrat_hints: Option<&[u64]>,
    ) -> ClauseRef {
        // CaDiCaL analyze.cpp:521: learned clause must be non-empty
        debug_assert!(
            !lits.is_empty(),
            "BUG: add_learned_clause called with empty clause"
        );
        // No duplicate literals in learned clause
        debug_assert!(
            {
                let mut sorted = lits.iter().map(|l| l.0).collect::<Vec<_>>();
                sorted.sort_unstable();
                sorted.windows(2).all(|w| w[0] != w[1])
            },
            "BUG: learned clause contains duplicate literals"
        );

        // Soundness-triage (--sat-ab-triage-clause): dump the resolution chain
        // with arena content + garbage flags when learning the target clause.
        {
            use std::sync::OnceLock;
            static TARGET: OnceLock<Option<Vec<i64>>> = OnceLock::new();
            let target = TARGET.get_or_init(|| {
                ay_core::misc_cli_flags()
                    .ab_triage_clause
                    .as_deref()
                    .map(|s| {
                        let mut v: Vec<i64> =
                            s.split(',').filter_map(|t| t.trim().parse().ok()).collect();
                        v.sort_unstable();
                        v
                    })
            });
            if target.is_some() {
                let mut mine: Vec<i64> = lits
                    .iter()
                    .map(|l| {
                        let v = i64::from(l.variable().0) + 1;
                        if l.is_positive() {
                            v
                        } else {
                            -v
                        }
                    })
                    .collect();
                mine.sort_unstable();
                if target.as_ref() == Some(&mine) {
                    eprintln!("TRIAGE_CHAIN: ids={resolution_chain:?}");
                    // Dump the full justification of every trail literal at
                    // levels 1..current (reasons with content + cid), so the
                    // minimization bottom-out chain can be checked offline.
                    {
                        let trail_snapshot: Vec<Literal> = self.trail().to_vec();
                        for tl in trail_snapshot {
                            let vi = tl.variable().index();
                            let lvl = self.var_level(tl.variable());
                            let (rs, cid) = match self.var_reason(vi) {
                                Some(r) => {
                                    let lits: Vec<String> = self
                                        .arena
                                        .literals(r.0 as usize)
                                        .iter()
                                        .map(|l| l.index().to_string())
                                        .collect();
                                    (
                                        format!("[{}]", lits.join(" ")),
                                        self.cold
                                            .clause_ids
                                            .get(r.0 as usize)
                                            .copied()
                                            .unwrap_or(0),
                                    )
                                }
                                None => ("NONE".to_string(), 0),
                            };
                            eprintln!(
                                "TRIAGE_TRAIL: lit={} level={:?} cid={} reason={}",
                                tl.index(),
                                lvl,
                                cid,
                                rs
                            );
                        }
                    }
                    conflict_analysis::TRIAGE_ANTECEDENTS.with(|b| {
                        for &off in b.borrow().iter() {
                            let lits: Vec<String> = self
                                .arena
                                .literals(off as usize)
                                .iter()
                                .map(|l| l.index().to_string())
                                .collect();
                            eprintln!(
                                "TRIAGE_ANTE_REF: off={} empty={} learned={} cid={} lits=[{}]",
                                off,
                                self.arena.is_empty_clause(off as usize),
                                self.arena.is_learned(off as usize),
                                self.cold.clause_ids.get(off as usize).copied().unwrap_or(0),
                                lits.join(" ")
                            );
                        }
                    });
                    let chain: std::collections::HashSet<u64> =
                        resolution_chain.iter().copied().collect();
                    for idx in self.arena.indices() {
                        let cid = self.cold.clause_ids.get(idx).copied().unwrap_or(0);
                        if cid != 0 && chain.contains(&cid) {
                            let cl: Vec<String> = self
                                .arena
                                .literals(idx)
                                .iter()
                                .map(|l| l.index().to_string())
                                .collect();
                            eprintln!(
                                "TRIAGE_ANTE: id={} idx={} garbage={} lits=[{}]",
                                cid,
                                idx,
                                self.arena.is_empty_clause(idx),
                                cl.join(" ")
                            );
                        }
                    }
                }
            }
        }
        // Reorder so lits[1] is the highest-level non-UIP literal (#3785).
        // Matches CaDiCaL analyze.cpp:826-841.
        let watched = self.prepare_watched_literals(lits, WatchOrderPolicy::LearnedBacktrack);
        self.maybe_reorder_learned_tail_at_creation(lits);

        // Log the learned clause to proof if enabled.
        // #8105: With backward LRAT reconstruction as the primary proof path,
        // learned clauses in LRAT mode are reserved (ID allocated without writing
        // to the proof file) during solving. The backward reconstruction writes
        // them post-UNSAT with proper hints. DRAT mode continues to emit as
        // before (no hints needed).
        let fmla_learned_lrat_authority_fail_closed =
            self.should_record_fmla_learned_lrat_authority_fail_closed(resolution_chain);
        let fmla_learned_lrat_authority_hints =
            fmla_learned_lrat_authority_fail_closed.then(|| {
                self.fmla_forward_lrat_fail_closed_authority_hints(
                    resolution_chain,
                    precomputed_lrat_hints,
                )
            });
        let emitted_id = if self.cold.lrat_enabled
            && (resolution_chain.is_empty() || fmla_learned_lrat_authority_fail_closed)
        {
            if fmla_learned_lrat_authority_fail_closed {
                if let Some(ref mut manager) = self.proof_manager {
                    manager.mark_lrat_authority_fail_closed();
                }
            }
            // LRAT backward path: reserve an ID without writing to the proof file.
            // The backward reconstruction will produce proper LRAT additions with
            // hints after UNSAT is determined.
            if let Some(ref mut manager) = self.proof_manager {
                let reserved = manager.reserve_lrat_id_for_backward();
                if let Some(file_lrat_hints) = fmla_learned_lrat_authority_hints.as_deref() {
                    manager.record_fmla_learned_lrat_authority_fail_closed(
                        reserved,
                        lits,
                        resolution_chain,
                        file_lrat_hints,
                    );
                }
                Some(reserved)
            } else {
                Some(0)
            }
        } else {
            // DRAT mode or forward LRAT fallback (non-empty resolution chain).
            let reversed_chain: Vec<u64>;
            let emit_hints = if self.cold.lrat_enabled && !resolution_chain.is_empty() {
                if let Some(hints) = precomputed_lrat_hints {
                    hints
                } else {
                    reversed_chain = Self::lrat_reverse_hints(resolution_chain);
                    &reversed_chain[..]
                }
            } else {
                resolution_chain
            };
            self.proof_emit_add_prechecked(lits, emit_hints, ProofAddKind::Derived)
                .ok()
        };
        // Sync next_clause_id to match the proof writer's assigned ID.
        //
        // This sets next_clause_id = id (not id+1) so that the subsequent
        // add_clause_db_checked assigns the SAME ID the proof writer used.
        // proof_emit_add_prechecked already advanced next_clause_id to id+1
        // (to prevent ID reuse in batch-emission paths like factorize), but
        // add_learned_clause needs the DB ID to match the proof ID exactly.
        // Setting next_clause_id = id here ensures add_clause_db_checked
        // consumes `id` and then advances to id+1 (#8093).
        if let Some(id) = emitted_id {
            if id != 0 {
                self.cold.next_clause_id = id;
            }
        }

        // Atomic clause+hints insertion (#4435): hints are attached in a single
        // add_clause_db_checked call, eliminating the two-step add/set_resolution_hints
        // pattern that was the root cause of hint-loss regressions.
        // Learned clauses are always derived (forward_check_derived=true).
        // The LRAT-mode forward DRUP skip is handled inside add_clause_db_checked
        // (#7108) to avoid conflating the forward check flag with LRAT ID
        // assignment and ProofManager registration.
        let clause_idx = self.add_clause_db_checked(lits, true, true, resolution_chain);
        let clause_ref = ClauseRef(clause_idx as u32);
        self.arena.set_lbd(clause_idx, lbd);
        // CaDiCaL clause.cpp:140: mark_added only for likely_to_be_kept (#7393).
        // Deferred from add_clause_db_checked because LBD wasn't set yet.
        self.mark_subsume_dirty_if_kept(clause_idx);
        // CaDiCaL analyze.cpp:535: new learned clauses start with max_used protection
        self.arena
            .set_used(clause_idx, crate::clause_arena::MAX_USED);
        let clause_id = self.clause_id(clause_ref);
        let trace_clause_id = if clause_id == 0 {
            (clause_idx as u64) + 1
        } else {
            clause_id
        };
        self.trace_learn(trace_clause_id);
        solver_log!(
            self,
            "learn clause #{} lbd={} size={}",
            clause_idx,
            lbd,
            lits.len()
        );

        if let Some(watched) = watched {
            // Watch literals[0] (UIP) and literals[1] (highest level non-UIP).
            self.attach_clause_watches(clause_ref, watched, lits.len() == 2);
        }

        // Track for eager subsumption (CaDiCaL analyze.cpp:728-766).
        // Bound the trail: only the last EAGER_SUBSUME_LIMIT entries are
        // ever read (see eager_subsume). Without truncation the trail grows
        // to O(num_conflicts), wasting ~80 MB on 10M-conflict solves (#6278/F3).
        self.cold.learned_clause_trail.push(clause_idx);
        const TRAIL_CAPACITY: usize = 1024;
        if self.cold.learned_clause_trail.len() > TRAIL_CAPACITY {
            let keep = TRAIL_CAPACITY / 2;
            let drain = self.cold.learned_clause_trail.len() - keep;
            self.cold.learned_clause_trail.drain(..drain);
        }

        clause_ref
    }

    /// Add a learned clause and return its reference (test-only convenience).
    ///
    /// Production code uses `add_conflict_learned_clause` for buffer recycling.
    /// This simpler API takes a borrowed chain and is used only in tests.
    #[cfg(test)]
    #[allow(clippy::needless_pass_by_value)]
    pub(super) fn add_learned_clause(
        &mut self,
        lits: Vec<Literal>,
        lbd: u32,
        resolution_chain: &[u64],
    ) -> ClauseRef {
        let mut lits = lits;
        let clause_ref = self.add_learned_clause_inner(&mut lits, lbd, resolution_chain);
        self.conflict.return_learned_buf(lits);
        clause_ref
    }

    #[allow(clippy::needless_pass_by_value)]
    pub(super) fn add_conflict_learned_clause(
        &mut self,
        lits: Vec<Literal>,
        lbd: u32,
        mut resolution_chain: Vec<u64>,
    ) -> ClauseRef {
        let mut lits = lits;
        // Official LRAT hot path: conflict analysis hands us ownership of the
        // chain buffer, and normal DIMACS proof runs do not observe raw hint
        // order through clause_trace or diagnostic_trace. Reuse that buffer as
        // the reversed LRAT hint slice instead of allocating a second Vec.
        let fmla_learned_lrat_authority_fail_closed =
            self.should_record_fmla_learned_lrat_authority_fail_closed(&resolution_chain);
        let can_reuse_chain_for_lrat_hints = self.cold.lrat_enabled
            && !resolution_chain.is_empty()
            && !resolution_chain.contains(&0)
            && !fmla_learned_lrat_authority_fail_closed
            && self.cold.clause_trace.is_none()
            && self.cold.diagnostic_trace.is_none();
        let clause_ref = if can_reuse_chain_for_lrat_hints {
            resolution_chain.reverse();
            self.add_learned_clause_inner_with_proof_hints(
                &mut lits,
                lbd,
                &resolution_chain,
                Some(&resolution_chain),
            )
        } else {
            self.add_learned_clause_inner(&mut lits, lbd, &resolution_chain)
        };
        self.conflict.return_learned_buf(lits);
        self.conflict.return_chain_buf(resolution_chain);
        clause_ref
    }

    fn should_fail_closed_fmla_forward_lrat_learned_clause(
        &self,
        _resolution_chain: &[u64],
    ) -> bool {
        if !self.cold.lrat_enabled {
            return false;
        }
        let stats = self.inproc.decompose_engine.lrat_preflight_stats();
        stats.main_rewrite_materializer_records > 0
            && stats.main_rewrite_materializer_fail_closed > 0
    }

    fn should_record_fmla_learned_lrat_authority_fail_closed(
        &self,
        resolution_chain: &[u64],
    ) -> bool {
        self.should_fail_closed_fmla_forward_lrat_learned_clause(resolution_chain)
            || self.has_unchecked_fmla_materializer_lrat_rows()
    }

    fn has_unchecked_fmla_materializer_lrat_rows(&self) -> bool {
        if !self.cold.lrat_enabled {
            return false;
        }
        let Some(proof_manager) = self.proof_manager.as_ref() else {
            return false;
        };
        proof_manager
            .scoped_decompose_proof_emit_records()
            .iter()
            .any(|record| {
                Self::is_fmla_guarded_equiv_materializer_record(record)
                    && !record.external_checker_verified
                    && Self::fmla_materializer_record_available_for_learned_lrat_authority(
                        proof_manager,
                        record,
                    )
            })
    }

    fn is_fmla_guarded_equiv_materializer_record(
        record: &crate::decompose::DecomposeProofEmitRecord,
    ) -> bool {
        record
            .context
            .sidecar_context_token
            .starts_with("fmla-guarded-equiv-")
    }

    fn fmla_forward_lrat_fail_closed_authority_hints(
        &self,
        resolution_chain: &[u64],
        precomputed_lrat_hints: Option<&[u64]>,
    ) -> Vec<u64> {
        let mut file_lrat_hints = precomputed_lrat_hints.map_or_else(
            || Self::lrat_reverse_hints(resolution_chain),
            ToOwned::to_owned,
        );

        // This is retained dry-run evidence only. The learned row remains
        // fail-closed until a checker validates the materializer+learned
        // fragment; adding an emitted materializer hint here only prevents
        // losing the bounded materializer rows before that checker step.
        if !self.fmla_lrat_hints_contain_available_materializer_dependency(&file_lrat_hints) {
            if let Some(materializer_id) = self.latest_available_fmla_materializer_lrat_hint() {
                // The fallback row is not a proof-derived learned dependency.
                // Keep the materializer row visible while forcing learned
                // replay to stay fail-closed/incomplete.
                file_lrat_hints.push(0);
                file_lrat_hints.push(materializer_id);
            }
        }

        file_lrat_hints
    }

    fn fmla_lrat_hints_contain_available_materializer_dependency(&self, hints: &[u64]) -> bool {
        let Some(proof_manager) = self.proof_manager.as_ref() else {
            return false;
        };
        hints.iter().any(|&hint| {
            proof_manager
                .scoped_decompose_proof_emit_records()
                .iter()
                .any(|record| {
                    record.checker_visible_id == hint
                        && Self::fmla_materializer_record_available_for_learned_lrat_authority(
                            proof_manager,
                            record,
                        )
                })
        })
    }

    fn latest_available_fmla_materializer_lrat_hint(&self) -> Option<u64> {
        let proof_manager = self.proof_manager.as_ref()?;
        proof_manager
            .scoped_decompose_proof_emit_records()
            .iter()
            .rev()
            .find(|record| {
                Self::fmla_materializer_record_available_for_learned_lrat_authority(
                    proof_manager,
                    record,
                )
            })
            .map(|record| record.checker_visible_id)
    }

    fn fmla_materializer_record_available_for_learned_lrat_authority(
        proof_manager: &ProofManager,
        record: &crate::decompose::DecomposeProofEmitRecord,
    ) -> bool {
        if record.proof_out_record_kind != crate::decompose::DecomposeProofOutRecordKind::Add
            || record.checker_visible_id == 0
            || !proof_manager.lrat_id_usable_as_hint(record.checker_visible_id)
            || record.proof_manager_mode != "lrat"
            || !record.solver_runtime_emitted
            || record.proof_writer_io_error
            || record.lrat_hints.is_empty()
        {
            return false;
        }

        let mut seen = Vec::with_capacity(record.lrat_hints.len());
        for &hint in &record.lrat_hints {
            if hint == 0 || !proof_manager.lrat_id_usable_as_hint(hint) || seen.contains(&hint) {
                return false;
            }
            seen.push(hint);
        }
        true
    }

    /// Eagerly subsume recently learned clauses using the new clause.
    ///
    /// CaDiCaL `analyze.cpp:728-766`: after learning clause `c`, walk backward
    /// through the last `EAGER_SUBSUME_LIMIT` learned clauses. If `c` subsumes
    /// a candidate `d` (all literals of `c` appear in `d`), mark `d` as garbage.
    ///
    /// Uses `lit_marks` to mark the new clause's literals, then checks each
    /// candidate. Marks garbage with `mark_garbage_keep_data` so the clause data
    /// remains intact (the clause might still serve as a reason for an assigned
    /// variable). Cleanup happens during the next `reduce_db`.
    pub(super) fn eager_subsume(&mut self, new_clause_off: usize) {
        const EAGER_SUBSUME_LIMIT: usize = 20;

        let new_len = self.arena.len_of(new_clause_off);
        if new_len == 0 {
            return;
        }

        // Mark all literals in the new clause. One slice construction (single
        // bounds check) instead of a bounds-checked `arena.literal()` read per
        // literal — matches CaDiCaL's `mark(c)` pointer walk (analyze.cpp:731).
        // Disjoint field borrows: `arena` immutable, `lit_marks` mutable.
        for &lit in self.arena.literals(new_clause_off) {
            self.lit_marks.mark(lit);
        }

        // Walk backward through recently learned clauses (skip the last entry
        // which is the new clause itself).
        let trail_len = self.cold.learned_clause_trail.len();
        let end = trail_len.saturating_sub(1);
        let start = end.saturating_sub(EAGER_SUBSUME_LIMIT);

        for i in (start..end).rev() {
            let cand_off = self.cold.learned_clause_trail[i];
            if self.is_pending_theory_conflict_clause(cand_off) {
                continue;
            }

            // Skip deleted, irredundant, or garbage clauses. Single combined
            // header read (two words, one bounds check) replaces the previous
            // four separate accessor calls; CaDiCaL reads one `Clause*` header
            // for the same checks (analyze.cpp:740-746).
            let candidate = self.arena.eager_subsume_candidate_len(cand_off);
            #[cfg(debug_assertions)]
            {
                // Parity check against the original accessor-based filter.
                let reference = if !self.arena.is_active(cand_off)
                    || !self.arena.is_learned(cand_off)
                    || self.arena.is_garbage(cand_off)
                {
                    None
                } else {
                    Some(self.arena.len_of(cand_off))
                };
                debug_assert_eq!(
                    candidate, reference,
                    "eager_subsume candidate-filter parity (shave #2)"
                );
            }
            let Some(cand_len) = candidate else {
                continue;
            };

            // Check if the new clause subsumes this candidate:
            // all literals of new_clause must appear in candidate.
            // Slice iteration: one bounds check for the whole clause instead
            // of one per literal (CaDiCaL's range-for over `*d`).
            let subsumed = {
                let mut needed = new_len as i32;
                for &lit in self.arena.literals(cand_off) {
                    if self.lit_marks.get(lit.variable()) == lit.sign_i8() {
                        needed -= 1;
                        if needed == 0 {
                            break;
                        }
                    }
                }
                needed == 0
            };
            #[cfg(debug_assertions)]
            {
                // Parity check against the original indexed subsumption scan.
                let mut needed_ref = new_len as i32;
                for j in 0..cand_len {
                    let lit = self.arena.literal(cand_off, j);
                    if self.lit_marks.get(lit.variable()) == lit.sign_i8() {
                        needed_ref -= 1;
                        if needed_ref == 0 {
                            break;
                        }
                    }
                }
                debug_assert_eq!(
                    subsumed,
                    needed_ref == 0,
                    "eager_subsume subsumption-decision parity (shave #2)"
                );
            }

            if subsumed {
                // New clause subsumes candidate — mark as garbage.
                // Keep data intact so it can still serve as a reason clause.
                // Mark watched literals dirty for targeted flush (#8101).
                // `cand_len` reused from the header snapshot (previously a
                // third `len_of` header read).
                if cand_len > 2 {
                    let (w0, w1) = self.arena.watched_literals(cand_off);
                    if w0.index() < self.dirty_watches.len() {
                        self.dirty_watches[w0.index()] = true;
                        self.dirty_watch_list.push(w0.index() as u32);
                    }
                    if w1.index() < self.dirty_watches.len() {
                        self.dirty_watches[w1.index()] = true;
                        self.dirty_watch_list.push(w1.index() as u32);
                    }
                }
                self.stats.clear_bcp_learned_1963_blocker_cert(cand_off);
                self.arena.mark_garbage_keep_data(cand_off);
                self.cold.num_eager_subsumptions += 1;
            }
        }

        // Unmark (CaDiCaL `unmark(c)`, analyze.cpp:761). Re-taking the slice
        // is sound: the loop above only sets header flag bits
        // (`mark_garbage_keep_data` flips word[2] flags, keeps length and
        // literal words) and never reallocates the arena, so the new clause's
        // literal slice is unchanged.
        let lits = self.arena.literals(new_clause_off);
        self.lit_marks.clear_clause(lits);
    }
}
