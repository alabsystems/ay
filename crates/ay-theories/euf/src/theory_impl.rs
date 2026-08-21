// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheorySolver` trait implementation for `EufSolver`.
//!
//! Implements the DPLL(T) theory interface: assert, check, propagate, push/pop.
//! Conflict detection helpers are in `theory_check.rs`, propagation helpers
//! in `theory_propagate.rs`.

use ay_core::safe_eprintln;
use ay_core::term::TermId;
use ay_core::{
    unwrap_not, DiscoveredEquality, EqualityPropagationResult, TheoryLit, TheoryPropagation,
    TheoryResult, TheorySolver,
};

use crate::shared_equality::reason_is_self_evidencing_shared_eq;
use crate::solver::EufSolver;
use crate::types::{CongruenceTable, EqualityReason, MergeReason, UndoRecord};

impl TheorySolver for EufSolver<'_> {
    /// #euf-atom-filter: restrict negative-congruence propagation candidates to
    /// equalities that have a SAT variable. Forwards to the inherent env-gated
    /// installer. Sound for a STANDALONE EUF solver (pure QF_UF), whose
    /// propagations reach only the SAT boundary; the array combiner deliberately
    /// does NOT forward this (its EUF shares interface disequalities).
    fn set_sat_atom_terms(&mut self, term_to_var: &ay_core::kani_compat::DetHashMap<TermId, u32>) {
        self.install_sat_atom_filter(term_to_var);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        let debug = self.debug_euf;

        assert!(
            (literal.0 as usize) < self.terms.len(),
            "BUG: EUF assert_literal: term {} out of range (term store len={})",
            literal.0,
            self.terms.len()
        );

        let (term, val) = unwrap_not(self.terms, literal, value);
        if debug && term != literal {
            safe_eprintln!(
                "[EUF ASSERT] NOT term {} unwrapped to inner {} with value {}",
                literal.0,
                term.0,
                val
            );
        }

        if debug {
            // Check if it's an equality
            if let Some((lhs, rhs)) = self.decode_eq(term) {
                safe_eprintln!(
                    "[EUF ASSERT] eq term {} (terms {} == {}) = {}",
                    term.0,
                    lhs.0,
                    rhs.0,
                    val
                );
            }
        }
        self.record_assignment(term, val);
    }

    fn check(&mut self) -> TheoryResult {
        self.check_count += 1;
        // Soundness gate (#8454): if an earlier pop() detected trail underflow
        // (corrupted E-graph state), refuse to produce a SAT/UNSAT result.
        if self.poisoned {
            safe_eprintln!(
                "BUG: EUF check() skipped — solver poisoned by earlier invariant violation"
            );
            return TheoryResult::Unknown;
        }
        let debug = self.debug_euf;
        tracing::debug!(
            assigns = self.assigns.len(),
            dirty = self.dirty,
            incremental = true,
            "EUF check"
        );

        if debug {
            safe_eprintln!(
                "[EUF] check() called: dirty={}, assigns={}, incremental={}",
                self.dirty,
                self.assigns.len(),
                true
            );
        }

        // 0) Direct conflict: term assigned both true and false
        if let Some(conflict_term) = self.pending_conflict.take() {
            if debug {
                safe_eprintln!("[EUF CHECK] Direct conflict on term {}", conflict_term.0);
            }
            debug_assert!(
                (conflict_term.0 as usize) < self.terms.len(),
                "BUG: EUF direct conflict: term {} out of range (term store len={})",
                conflict_term.0,
                self.terms.len()
            );
            // Return conflict clause: {term=true, term=false} -> both are in conflict
            self.conflict_count += 1;
            return TheoryResult::Unsat(vec![
                TheoryLit::new(conflict_term, true),
                TheoryLit::new(conflict_term, false),
            ]);
        }

        // 0b) #8469: Shared disequality conflict from assert_shared_disequality.
        // Arithmetic told us a != b, but EUF has a = b.
        if let Some(conflict) = self.pending_shared_diseq_conflict.take() {
            if debug {
                safe_eprintln!(
                    "[EUF CHECK] Shared disequality conflict ({} reasons)",
                    conflict.len()
                );
            }
            self.conflict_count += 1;
            return TheoryResult::Unsat(conflict);
        }

        self.rebuild_closure();

        if debug {
            let eq_count = self
                .assigns
                .iter()
                .filter(|(t, &v)| v && self.decode_eq(**t).is_some())
                .count();
            safe_eprintln!("[EUF CHECK] {} equalities asserted true", eq_count);
        }

        // 0c) #8469: Check shared disequalities from other theories after
        // rebuild_closure(), since new merges may create conflicts.
        if let Some(result) = self.check_shared_disequality_conflicts() {
            return result;
        }

        // 1-4) Check for conflicts in priority order (see theory_check.rs)
        if let Some(result) = self.check_disequality_conflicts() {
            return result;
        }
        if let Some(result) = self.check_distinct_conflicts() {
            return result;
        }
        if let Some(result) = self.check_constant_conflicts() {
            return result;
        }
        if let Some(result) = self.check_bool_congruence_conflicts() {
            return result;
        }

        // #bool-arg-congruence SOUND fallback: refuse to certify a model that is
        // provably non-congruent over Bool UF-arguments. This downgrades `Sat`
        // to `Unknown` ONLY (never asserts UNSAT), so it cannot cause a false
        // UNSAT — it just declines to claim SAT for a model whose Bool-arg
        // congruence cannot be confirmed (e.g. the `uf_fs2` witness, where the
        // formula-level lemma cannot relate two syntactically-distinct but
        // model-equal complex Bool args nested under UFs). Without it, EUF would
        // return a false SAT for such models.
        if !self.bool_arg_model_is_congruent() {
            if debug {
                safe_eprintln!(
                    "[EUF CHECK] Non-congruent Bool-arg model — returning Unknown (sound)"
                );
            }
            return TheoryResult::Unknown;
        }

        if debug {
            safe_eprintln!("[EUF CHECK] Returning SAT");
        }

        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        // Rebuild closure if needed
        if self.dirty {
            self.rebuild_closure();
        }

        // Ensure eq_terms index is built (lazy, one-time O(|terms|) scan)
        self.init_eq_terms();

        // #8599: Reuse persistent buffer — clear() preserves capacity from prior calls.
        let mut propagations = std::mem::take(&mut self.propagation_output_buf);
        propagations.clear();

        // Positive equality propagation (see theory_propagate.rs)
        self.propagate_positive_equalities(&mut propagations);
        // Disequality propagation (#5575, see theory_propagate.rs)
        self.propagate_disequalities(&mut propagations);

        self.propagation_count += propagations.len() as u64;
        // Store the allocation back for reuse, then move its elements into the
        // independently owned result without discarding the reusable capacity.
        self.propagation_output_buf = propagations;
        let mut output = Vec::with_capacity(self.propagation_output_buf.len());
        output.append(&mut self.propagation_output_buf);
        output
    }

    fn push(&mut self) {
        // #euf-inc-cong-undo: safe switch point — the trail is checked empty
        // inside, so record/replay modes can never disagree for a live scope.
        self.maybe_latch_undo();
        self.scopes.push(self.trail.len());
        // For incremental mode: save undo trail position
        self.undo_scopes.push(self.undo_trail.len());
    }

    fn pop(&mut self) {
        // #euf-inc-undo-adaptive: charge the from-scratch path for what this pop
        // is about to cost. When the incremental path is already active there is
        // no rebuild, so nothing accrues and the crossover stays where it is.
        if !self.cong_undo_active() {
            self.rebuild_work = self
                .rebuild_work
                .saturating_add(self.func_apps.len() as u64);
        }
        let Some(mark) = self.scopes.pop() else {
            return;
        };
        // #euf-inc-neg-pop: opt-in delta recording (`--euf-inc-neg-pop`).
        // While OFF every branch below behaves exactly as it did before — the
        // dirty sets are cleared and the full negative rescan is armed — so the
        // flag-off path is byte-identical to baseline.
        let pop_delta = self.inc_neg_pop_enabled;
        // Set if this pop hit a state whose delta we cannot certify; forces the
        // sound full rescan below.
        let mut pop_delta_hazard = false;
        // Production soundness gate (#8454): if scope mark exceeds trail
        // length, the E-graph state is already corrupted. Clamp to prevent
        // further damage and poison the solver so next check() returns Unknown.
        let mark = if mark > self.trail.len() {
            safe_eprintln!(
                "BUG: EUF pop: scope mark {} exceeds trail length {} — clamping and poisoning solver",
                mark,
                self.trail.len()
            );
            self.poisoned = true;
            self.trail.len()
        } else {
            mark
        };
        while self.trail.len() > mark {
            // SAFETY: while-loop guard guarantees trail is non-empty.
            let (term, prev) = self
                .trail
                .pop()
                .expect("invariant: trail.len() > mark guarantees non-empty trail");
            match prev {
                Some(v) => {
                    self.assigns.insert(term, v);
                    // #euf-inc-neg-pop: a RESTORED previous value can add a
                    // disequality to the index (true -> false) without any
                    // representative changing, which the delta does not cover.
                    // `record_assignment` only ever trails `None` (it treats a
                    // conflicting re-assert as a pending conflict instead of
                    // overwriting), so this arm is unreachable today; refuse the
                    // delta rather than rely on that.
                    pop_delta_hazard = true;
                }
                None => {
                    self.assigns.remove(&term);
                    // #euf-inc-neg-pop: this equality atom just became
                    // UNASSIGNED, so it is a negative-propagation candidate for
                    // the first time. The representative delta cannot cover it
                    // (its classes need not have changed at all), so record the
                    // atom itself. Same-sort filtering and the index probe are
                    // done by the scan, exactly as the full pass does them.
                    if pop_delta {
                        if let Some((a, b)) = self.decode_eq(term) {
                            self.neg_pop_retracted.push((term, a, b));
                        }
                    }
                }
            }
        }

        // Replay undo records to restore E-graph state
        // This must always happen when undo_scopes is non-empty, regardless of
        // incremental/legacy EUF mode. The undo_scopes track E-graph merges
        // that need to be undone on backtrack.
        if !self.undo_scopes.is_empty() {
            let undo_mark = self.undo_scopes.pop().unwrap_or(0);
            // Production soundness gate (#8454): clamp undo mark and poison.
            let undo_mark = if undo_mark > self.undo_trail.len() {
                safe_eprintln!(
                    "BUG: EUF pop: undo scope mark {} exceeds undo trail length {} — clamping and poisoning solver",
                    undo_mark,
                    self.undo_trail.len()
                );
                self.poisoned = true;
                self.undo_trail.len()
            } else {
                undo_mark
            };
            while self.undo_trail.len() > undo_mark {
                // SAFETY: while-loop guard guarantees undo_trail is non-empty.
                let record = self
                    .undo_trail
                    .pop()
                    .expect("invariant: undo_trail.len() > undo_mark guarantees non-empty trail");
                match record {
                    UndoRecord::SetRoot {
                        node,
                        old_root,
                        old_next,
                    } => {
                        if (node as usize) < self.enodes.len() {
                            self.enodes[node as usize].root = old_root;
                            self.enodes[node as usize].next = old_next;
                            // #euf-inc-neg-pop: `old_root` is the representative
                            // this node is being handed back to, and it is itself
                            // a post-pop representative: it was a root when the
                            // record was written, and every later merge that
                            // absorbed it wrote its own `SetRoot { node: old_root,
                            // old_root }` record, which this same reverse replay
                            // undoes (records above this one in the trail were
                            // already replayed by this or an earlier pop). So the
                            // set of `old_root`s IS the set of class
                            // representatives this pop split apart — exactly the
                            // reps whose `class_eqs` bucket can hold an equality
                            // atom whose `(min_rep,max_rep)` key changed, and
                            // exactly the reps under which the replayed
                            // `DiseqSet`/`DiseqRemove` records rekey the index
                            // (merge-time rekeying always keys by the ABSORBED
                            // rep). Verified in debug by
                            // `debug_assert_neg_dirty_reps_are_roots`, which also
                            // covers the one way a stale entry can survive here
                            // (a rep recorded by an earlier pop of the same
                            // backjump, absorbed since by a merge in an outer
                            // scope this pop did not unwind).
                            //
                            // Recorded in the SPLIT set, not the event set: these
                            // reps need the direct index probe but must NOT drive
                            // the cong-neg lookahead, because the baseline
                            // post-pop pass runs zero lookahead simulations over
                            // them (see `neg_pop_split_reps`).
                            if pop_delta {
                                self.neg_pop_split_reps.insert(old_root);
                            }
                            // Incremental UF-mirror sync: this node's root was just
                            // restored, so its representative may now differ from
                            // its `uf.parent` mirror entry. Record it so the next
                            // sync refreshes it. See the completeness note at the
                            // end of pop() for why this dirty set is a full cover.
                            if self.inc_sync_enabled && !self.uf_full_sync_needed {
                                self.uf_dirty_nodes.insert(node);
                            }
                        }
                    }
                    UndoRecord::SetClassSize { node, old_size } => {
                        if (node as usize) < self.enodes.len() {
                            self.enodes[node as usize].class_size = old_size;
                        }
                    }
                    UndoRecord::RemoveParent { node } => {
                        if (node as usize) < self.enodes.len() {
                            self.enodes[node as usize].parents.pop();
                        }
                    }
                    UndoRecord::RemoveEqualityEdge(a, b) => {
                        self.equality_edges.remove(&(a, b));
                    }
                    UndoRecord::UnmergeProofForest { node, old_root } => {
                        self.unmerge_proof_forest(node, old_root);
                    }
                    UndoRecord::RemoveSharedEqualityReason(a, b) => {
                        self.shared_equality_reasons.remove(&(a, b));
                    }
                    UndoRecord::RemoveSharedDisequality(a, b) => {
                        self.shared_disequalities.remove(&(a, b));
                    }
                    // #euf-inc-cong-undo: replay the exact congruence-table
                    // mutations in reverse, restoring the pre-scope mapping.
                    UndoRecord::CongSet { sig, term } => {
                        self.cong_table.set(sig, term);
                    }
                    UndoRecord::CongRemove { sig } => {
                        self.cong_table.remove(&sig);
                    }
                    // #euf-inc-diseq-undo: replay the exact disequality-pair-index
                    // mutations in reverse, restoring the pre-scope mapping. Both
                    // carry the exact key/entry, so they do not depend on the
                    // (concurrently-restored) root state. The incremental-vs-
                    // fallback decision is made after the loop; if we fall back,
                    // these applications are simply overwritten by the clear.
                    UndoRecord::DiseqSet { key, entry } => {
                        self.diseq_pair_index.insert(key, entry);
                    }
                    UndoRecord::DiseqRemove { key } => {
                        self.diseq_pair_index.remove(&key);
                    }
                    // #euf-inc-diseq-undo: undo a sync insertion. Remove the
                    // index entry, and if the disequality assignment SURVIVED
                    // this pop (the assigns trail was already restored above), it
                    // was indexed at a deeper scope than it was asserted — put it
                    // back on the pending queue so the completeness guard forces
                    // a full rebuild and the diseq is not lost.
                    UndoRecord::DiseqUnsync { key, entry } => {
                        self.diseq_pair_index.remove(&key);
                        if self.assigns.get(&entry.2) == Some(&false) {
                            self.pending_neg_eqs.push((entry.2, entry.0, entry.1));
                        }
                    }
                }
            }
            self.to_merge.clear();
            // Rebuild congruence table from current enode state.
            // After undo replay, roots are restored correctly but the cong_table
            // is stale. Rebuilding from scratch is O(func_apps) — much cheaper than
            // storing and replaying Signature Vecs in undo records (#5575).
            //
            // #euf-inc-cong-undo: when enabled, `incremental_merge` recorded
            // CongSet/CongRemove undo entries that the replay above already
            // applied, so the table is exact — skip the O(func_apps) rebuild.
            // The restored table's KEY SET (distinct live signatures under the
            // restored roots) is identical to the rebuild's; only the canonical
            // term per signature may differ, and that is verified at every
            // consumption site. A debug-only cross-check enforces the key-set
            // invariant so any incompleteness surfaces in tests/fuzzing.
            if self.enodes_init && self.func_apps_init {
                if self.cong_undo_active() {
                    #[cfg(debug_assertions)]
                    self.debug_assert_cong_table_key_set_matches_rebuild();
                } else {
                    self.cong_table.clear();
                    for meta in &self.func_apps {
                        let sig = CongruenceTable::make_signature(
                            meta.func_hash,
                            &meta.args,
                            &self.enodes,
                        );
                        self.cong_table.insert(meta.term_id, sig);
                    }
                }
            }
        }

        // Clear N-O state on pop (#318, pattern from [P]90)
        // #8599: propagated_eqs and propagated_eq_pairs are deduplication sets
        // for Nelson-Oppen equality propagation. Full clear on pop is correct:
        // after backtracking, equalities from the popped scope may need to be
        // re-propagated in the restored scope. shrink_to_fit() reclaims memory
        // when deep scopes with many propagations are popped.
        self.propagated_eqs.clear();
        self.propagated_eqs.shrink_to_fit();
        self.propagated_eq_pairs.clear();
        self.propagated_eq_pairs.shrink_to_fit();
        self.pending_propagations.clear();
        self.propagated_diseq_pairs.clear();
        self.propagated_diseq_pairs.shrink_to_fit(); // #8469
                                                     // #8471: Invalidate diseq scan epoch after pop — the E-graph structure
                                                     // changed (merges undone), so disequalities must be re-scanned. Without
                                                     // this, collect_implied_disequalities would see diseq_scan_epoch ==
                                                     // merge_epoch and skip scanning, missing disequalities in the restored
                                                     // outer scope.
        self.merge_epoch = self.merge_epoch.wrapping_add(1);
        // #8471: Clear fine-grained dirty tracking on pop — the next scan after
        // pop must do a full scan since equivalence classes were undone.
        self.dirty_merge_reps.clear();
        self.new_negated_eqs.clear();
        // Class membership/state was reset — the `class_eqs` index is now stale;
        // force a full positive rescan (which rebuilds it) on the next propagate.
        self.pos_full_scan_needed = true;
        self.pos_dirty_reps.clear();
        // #inc-neg / #euf-inc-diseq-undo: the disequality pair index is keyed by
        // representatives the undo replay just restored. When the incremental
        // (trail-based) restore is active AND valid for THIS pop, the replay
        // above already rebuilt `diseq_pair_index` exactly — skip the
        // O(|assigns|) from-scratch rebuild (the confirmed #1 Certora
        // search-phase cost). Otherwise force a full negative rescan (the
        // byte-identical baseline).
        //
        // Either way the next scan skips the cong-neg LOOKAHEAD sweep: every
        // lookahead implication proposed before this pop lives on as a permanent
        // SAT clause that BCP re-fires by itself (see `neg_full_scan_la_needed`,
        // deliberately NOT re-armed here).
        let diseq_incremental_ok = self.diseq_undo_active()
            && self.enodes_init
            && self.func_apps_init
            // Index was live (reflected the pre-pop state), not pending a
            // from-scratch rebuild (init / reset / prior fallback pop).
            && (!self.neg_full_scan_needed || self.neg_index_prebuilt)
            // Not popping below the depth the index was last built from scratch;
            // those entries carry no undo records (see `diseq_index_base_depth`).
            // `self.scopes` was already popped at the top of pop(), so its len is
            // the post-pop depth.
            && self.scopes.len() >= self.diseq_index_base_depth
            // Completeness guard: every asserted disequality is already in the
            // index (none stranded in `pending_neg_eqs` that the undo trail did
            // not cover). Empty in the normal flow — propagate/check drains it
            // before every decision — so this rarely blocks the fast path; a
            // non-empty queue means we cannot certify the restored index is
            // complete, so fall back to the sound from-scratch rebuild.
            && self.pending_neg_eqs.is_empty()
            // A disequality asserted while its endpoints were merged lives only
            // as a collapse candidate: it has no forward-index mutation (and
            // therefore no undo record) to replay.  If this pop splits that pair,
            // ad-hoc reinsertion would not be tied to the assignment's scope and
            // could survive a later pop that retracts the disequality.  Collapse
            // candidates are rare; fail over to the authoritative assigns scan,
            // which re-derives both live split pairs and surviving conflicts.
            && self.pending_diseq_conflicts.is_empty();

        // #euf-inc-neg-pop: can the next negative scan skip the FULL candidate
        // pass over `eq_terms` and visit only this pop's deltas?
        //
        // What the full pass would find that a delta pass must also find:
        //  (1) an unassigned equality whose `(min_rep,max_rep)` key CHANGED —
        //      then one endpoint's representative changed, so that endpoint's
        //      post-pop rep is one of the replayed `SetRoot.old_root`s recorded
        //      into `neg_pop_split_reps` above, and the atom sits in that rep's
        //      `class_eqs` bucket (rebuilt by the positive full scan that always
        //      runs first in the same `propagate`, since `pos_full_scan_needed`
        //      is armed just above);
        //  (2) an unassigned equality whose key is unchanged but whose key
        //      became a LIVE index key — index keys only appear here by the
        //      replay's `DiseqSet` (whose key is the pre-merge key, containing
        //      the ABSORBED rep -> in `neg_pop_split_reps`) or, on the
        //      from-scratch rebuild branch, by a disequality whose endpoint reps
        //      changed (same argument as (1)) or whose collapsed pair SPLIT
        //      (likewise a rep change). A key that DISAPPEARS only removes
        //      candidates;
        //  (3) an equality this pop UNASSIGNED — recorded in `neg_pop_retracted`.
        // Merges asserted after this pop are covered by the existing
        // `incremental_merge` trigger (it inserts the survivor rep into
        // `neg_dirty_reps`).
        //
        // The two rep sets are consumed together but play different roles: the
        // pop-split reps get the DIRECT index probe only, while the event set
        // (`neg_dirty_reps`) additionally drives the cong-neg lookahead — exactly
        // matching what a baseline post-pop full pass does (see
        // `neg_pop_split_reps`).
        //
        // The cover is anchored at the last COMPLETE candidate pass, so it must
        // CHAIN. Either this pop's predecessor already handed over a valid delta
        // that is still pending (`neg_pop_delta_valid` — deep backjumps pop many
        // levels before a single `propagate`, and `neg_pop_split_reps` /
        // `neg_pop_retracted` simply accumulate), or no rescan is outstanding at
        // all (`!neg_full_scan_needed`, i.e. the last scan WAS the complete pass).
        // Any other state means some earlier event demanded a full pass that has
        // not happened yet — in particular a preceding pop whose delta we refused
        // and discarded — and this pop's own delta would not cover it.
        //
        // Refused when a full LOOKAHEAD sweep is armed (`neg_full_scan_la_needed`
        // — only after reset/soft-reset/unwind, never after a plain pop), and
        // when a disequality is stranded outside the index (`pending_neg_eqs`
        // non-empty: the next sync would index it under a possibly-unchanged key,
        // which no delta covers).
        //
        // Conditions added when this was rebased onto the adaptive-backoff /
        // measured-crossover code (#cong-neg-cold, #cong-neg-scan-gate,
        // #euf-inc-undo-adaptive, #euf-atom-filter), each re-derived against what
        // the CURRENT post-pop full pass does beyond the delta:
        //  - `eq_terms_init`: the cover is a statement about the candidate set
        //    the anchor pass walked. `set_sat_atom_eq_terms` (#euf-atom-filter)
        //    drops `eq_terms` and `class_eqs` and arms a full pass over the
        //    NEW candidate set; until `init_eq_terms` has rebuilt it there is
        //    no set to certify against. (That setter also discards the delta
        //    state itself, so a delta pending ACROSS the reinstall is refused
        //    by the chain condition below, not merely by this one.)
        //  - `!poisoned`: a clamped scope/undo mark (#8454) means the trail the
        //    delta was read off is not the trail the e-graph was restored from;
        //    nothing read above can be trusted as a cover.
        //  - `cong_neg_scan_suspended` (#cong-neg-scan-gate) needs NO condition:
        //    it advances its re-probe counter once per scan in BOTH the full and
        //    the incremental scan, and the delta path runs exactly one
        //    incremental scan in place of exactly one full scan, so the counter
        //    — and hence the per-scan skip decision — is bit-identical. Likewise
        //    `cong_neg_ever_fired` / the cold cap only shape the memo's own
        //    backoff, which both scans call through the same `la_dirty`-gated
        //    atoms (the split set is denied the lookahead on both paths).
        //  - the undo-mode latch (`maybe_latch_undo`, #euf-inc-undo-adaptive)
        //    needs NO condition: it flips only at a `push` with no open scope,
        //    so every scope this pop unwinds was recorded and replayed in ONE
        //    mode, and `diseq_incremental_ok` above still decides prebuilt vs.
        //    rebuild per pop — both restoration branches are handled by the
        //    consumption site. `diseq_undo_active()` losing its size floor
        //    (#euf-inc-diseq-undo) only changes WHICH branch is taken, never
        //    the cover argument.
        //
        // A refusal is always safe: it takes the baseline full pass. A wrongly
        // GRANTED delta costs lost propagation hints — never a wrong verdict —
        // because `check()` is the conflict authority and the index-restoration
        // duties below/next-scan are unchanged (see `inc_neg_pop_enabled`).
        let pop_delta_ok = pop_delta
            && !pop_delta_hazard
            && !self.poisoned
            && self.enodes_init
            && self.func_apps_init
            && self.eq_terms_init
            && self.inc_neg_enabled
            && self.inc_pos_enabled
            && !self.neg_full_scan_la_needed
            && self.pending_neg_eqs.is_empty()
            && (self.neg_pop_delta_valid || !self.neg_full_scan_needed);
        self.neg_pop_delta_valid = pop_delta_ok;
        if !pop_delta_ok {
            self.neg_dirty_reps.clear();
            self.neg_pop_split_reps.clear();
            self.neg_pop_retracted.clear();
        } else {
            // #euf-inc-neg-pop parity: baseline `pop` clears `neg_dirty_reps`
            // UNCONDITIONALLY, so no pre-pop EVENT rep survives a pop with
            // lookahead rights and the post-pop pass runs ZERO cong-neg
            // simulations. Carrying them would re-introduce exactly the cost the
            // baseline pop path deliberately suppresses (and would accumulate
            // across a deep backjump). Move them to the split set instead: they
            // keep the cheap DIRECT `diseq_pair_index` probe, but are denied the
            // lookahead — restoring baseline parity while preserving coverage.
            for rep in std::mem::take(&mut self.neg_dirty_reps) {
                self.neg_pop_split_reps.insert(rep);
            }
        }
        // NOTE: `debug_assert_neg_dirty_reps_are_roots` is deliberately NOT called
        // here. The delta sets accumulate across every pop of one backjump, so a
        // per-pop O(|set|) walk is O(pops^2) and throttles debug fuzzing; the
        // invariant is asserted once at the consumption site instead (see
        // `propagate_disequalities`).
        if diseq_incremental_ok {
            // The undo replay restored `diseq_pair_index` exactly. Keep it, mark
            // it prebuilt so the next full negative scan runs only the candidate
            // pass (byte-identical to a rebuild, over identical contents), and
            // defer the inverse-index rebuild to first use (a deep backtrack of
            // many pops then pays it once).
            self.neg_full_scan_needed = true;
            self.neg_index_prebuilt = true;
            self.diseq_keys_dirty = true;
            #[cfg(debug_assertions)]
            self.debug_assert_diseq_index_matches_rebuild();
        } else {
            // Fallback: clear and force a from-scratch rebuild next propagate
            // (the rebuild re-derives collapse candidates by scanning assigns).
            self.neg_full_scan_needed = true;
            self.neg_index_prebuilt = false;
            self.diseq_keys_dirty = false;
            self.pending_neg_eqs.clear();
            self.diseq_pair_index.clear();
            self.diseq_keys_by_rep.clear();
            self.pending_diseq_conflicts.clear();
        }
        // #euf-inc-neg-pop: `pending_diseq_match_keys` holds index keys a
        // `sync_diseq_index` inserted that NO negative scan has matched against
        // `class_eqs` yet (assert-then-pop with no `propagate` in between). The
        // baseline covers them with its post-pop O(n_eqs) sweep; a delta scan will
        // not, and the clear below throws them away. Fold their endpoints into the
        // EVENT set so the delta pass revisits those classes. Both endpoints are
        // needed (`class_eqs` indexes an atom under both of its endpoint reps),
        // and a key endpoint was a representative before this pop, so — since a
        // pop only ever SPLITS classes — it still is one. Sub-classes it split
        // into are in `neg_pop_split_reps`, so the union stays a cover. These are
        // event reps (a newly indexed disequality), which the baseline treats as
        // lookahead-worthy in `sync_diseq_index`.
        if pop_delta_ok && !self.pending_diseq_match_keys.is_empty() {
            let keys = std::mem::take(&mut self.pending_diseq_match_keys);
            for &(key, _) in &keys {
                // Split set, NOT the event set: `sync_diseq_index` does not treat
                // these endpoints as lookahead-worthy — it dirties only the
                // ARGUMENT classes of their application members
                // (`dirty_app_member_args`), never the endpoints themselves. They
                // need the direct probe; giving them lookahead diverges from
                // baseline.
                self.neg_pop_split_reps.insert(key.0);
                self.neg_pop_split_reps.insert(key.1);
            }
            self.pending_diseq_match_keys = keys;
        }
        self.pending_diseq_match_keys.clear();
        // Incremental UF-mirror sync: the undo replay above restored each
        // affected node's root EXPLICITLY (overwriting any intervening path
        // compression, which only shortens chains and never changes the value
        // `enode_find_const` resolves to). Every node whose representative could
        // have changed during this pop therefore carries a `SetRoot` record and
        // was inserted into `uf_dirty_nodes` during replay. That dirty set is a
        // complete cover, so the next `sync_egraph_to_uf` can stay incremental.
        // (If a full sync was already pending — `uf_full_sync_needed` was true,
        // e.g. right after init — replay skipped the inserts and the pending full
        // sync still fixes everything, so we leave the flag untouched.)
        // shared_equality_reasons is now scope-aware via RemoveSharedEqualityReason
        // undo records (#4840). No blanket clear needed.
        self.func_app_values.clear(); // #385: derived from assignments

        // In incremental mode with active undo records, equality_edges are maintained
        // incrementally via RemoveEqualityEdge undo records (#5575). The blanket clear
        // is only needed for legacy mode where rebuild_closure() recreates all edges.
        // Clearing in incremental mode destroys lower-scope edges that explain() needs,
        // forcing unnecessary full rebuilds and degrading performance.
        if !self.enodes_init {
            // Enodes not yet initialized — blanket clear is safe.
            self.equality_edges.clear();
            self.dirty = true;
        } else {
            // Incremental mode: E-graph state is maintained by undo records above.
            // equality_edges are already cleaned by RemoveEqualityEdge records.
            // Refresh the UF mirror before returning so direct uf.find() readers
            // and extract_model() see the restored outer-scope partition.
            self.sync_egraph_to_uf();
            self.resync_func_app_values_from_assigns();
        }
        self.pending_conflict = None;
        // #euf-idle-rebuild: queued merges were discarded and applied merges
        // (incl. BoolValue class merges) unwound — force the next
        // incremental_rebuild to refill the queue and fully rescan the
        // bool-valued atoms from the surviving assignments.
        self.egraph_requeue_needed = true;
        self.ite_sweep_full_needed = true;
        self.bool_merge_pending.clear();
    }

    fn reset(&mut self) {
        let debug = self.debug_euf;
        if debug {
            safe_eprintln!(
                "[EUF] reset() called, clearing {} assigns",
                self.assigns.len()
            );
        }
        self.assigns.clear();
        self.trail.clear();
        self.scopes.clear();
        // #cong-neg-prop: the SAT clause DB is rebuilt after a reset, so the
        // once-per-solve emitted-clause dedup must start over.
        self.cong_neg_emitted.clear();
        self.uf.ensure_size(self.terms.len());
        self.uf.reset();
        self.equality_edges.clear();
        self.dirty = true;
        self.pending_conflict = None;

        // Reset incremental E-graph state
        self.enodes_init = false;
        self.enodes.clear();
        self.cong_table.clear();
        self.to_merge.clear();
        self.undo_trail.clear();
        self.undo_scopes.clear();
        // #euf-idle-rebuild: everything was discarded — full requeue + rescan.
        self.egraph_requeue_needed = true;
        self.ite_sweep_full_needed = true;
        self.bool_merge_pending.clear();
        self.bool_true_anchor = None;
        self.bool_false_anchor = None;
        // Clear Nelson-Oppen state
        self.shared_equality_reasons.clear();
        self.propagated_eqs.clear();
        self.propagated_eq_pairs.clear();
        self.pending_propagations.clear();
        // #8469: Full reset clears all disequality propagation state
        self.propagated_diseq_pairs.clear();
        self.shared_arith_terms.clear();
        self.merge_epoch = 0;
        self.diseq_scan_epoch = 0;
        // #8471: Clear fine-grained dirty tracking
        self.dirty_merge_reps.clear();
        self.new_negated_eqs.clear();
        // Class membership/state was reset — the `class_eqs` index is now stale;
        // force a full positive rescan (which rebuilds it) on the next propagate.
        self.pos_full_scan_needed = true;
        self.pos_dirty_reps.clear();
        // #inc-neg: the disequality pair index is keyed by representatives that
        // may have been undone — force a full negative rescan (rebuilds it).
        self.neg_full_scan_needed = true;
        // SAT clause DB state is not guaranteed here — re-arm the full
        // lookahead sweep (see `neg_full_scan_la_needed`).
        self.neg_full_scan_la_needed = true;
        self.neg_dirty_reps.clear();
        self.pending_neg_eqs.clear();
        self.diseq_pair_index.clear();
        self.diseq_keys_by_rep.clear();
        self.pending_diseq_conflicts.clear();
        self.pending_diseq_match_keys.clear();
        // #euf-inc-diseq-undo: index cleared — the next full negative scan must
        // rebuild it from scratch, not take the prebuilt skip.
        self.neg_index_prebuilt = false;
        // #euf-inc-neg-pop: the anchor for the delta cover (the last complete
        // candidate pass) is gone along with the index — the next scan must be a
        // full pass.
        self.neg_pop_delta_valid = false;
        self.neg_pop_retracted.clear();
        self.neg_pop_split_reps.clear();
        self.diseq_keys_dirty = false;
        self.diseq_index_base_depth = 0;
        // Incremental UF-mirror sync: E-graph partition was wiped; the mirror
        // must be rebuilt from scratch on the next sync.
        self.uf_full_sync_needed = true;
        self.uf_dirty_nodes.clear();
        // #8469: Clear shared disequalities from other theories
        self.shared_disequalities.clear();
        self.pending_shared_diseq_conflict = None;
        // Clear function application values (#385)
        self.func_app_values.clear();
        // #8599: Clear persistent propagation buffer
        self.propagation_output_buf.clear();
        // #euf-lazy-explain: assignment-derived witnesses are gone with the
        // assignments (entries self-validate, but there is nothing left for
        // them to validate against).
        self.lazy_neg_witness.clear();
        // Clear poisoned flag on full reset (#8454)
        self.poisoned = false;
    }

    fn soft_reset(&mut self) {
        let debug = self.debug_euf;
        if debug {
            safe_eprintln!(
                "[EUF] soft_reset() called, clearing {} assigns",
                self.assigns.len()
            );
        }
        // Clear assignments but preserve closure state
        // The closure will be validated/rebuilt lazily in rebuild_closure
        self.assigns.clear();
        self.trail.clear();
        self.scopes.clear();
        // #cong-neg-prop: see reset() — dedup restarts with the clause DB.
        self.cong_neg_emitted.clear();
        self.dirty = true;
        self.pending_conflict = None;

        // #qfuflia-egraph-preserve: unwind merges to the pristine post-init
        // structure instead of destroying it (see
        // unwind_all_merges_preserving_structure). Falls back to the full
        // clear when the e-graph was never initialized.
        if self.enodes_init {
            self.unwind_all_merges_preserving_structure();
        } else {
            self.enodes.clear();
            self.cong_table.clear();
            self.to_merge.clear();
            self.undo_trail.clear();
            self.undo_scopes.clear();
        }
        // #euf-idle-rebuild: assignments and merges were discarded/unwound —
        // full requeue + bool rescan (anchors are re-elected by the rescan).
        self.egraph_requeue_needed = true;
        self.ite_sweep_full_needed = true;
        self.bool_merge_pending.clear();
        self.bool_true_anchor = None;
        self.bool_false_anchor = None;
        self.equality_edges.clear();
        // Clear Nelson-Oppen state (equalities may change across soft resets)
        self.shared_equality_reasons.clear();
        self.propagated_eqs.clear();
        self.propagated_eq_pairs.clear();
        self.pending_propagations.clear();
        // #8469: Soft reset clears disequality propagation state
        self.propagated_diseq_pairs.clear();
        self.shared_arith_terms.clear();
        self.merge_epoch = 0;
        self.diseq_scan_epoch = 0;
        // #8471: Clear fine-grained dirty tracking
        self.dirty_merge_reps.clear();
        self.new_negated_eqs.clear();
        // Class membership/state was reset — the `class_eqs` index is now stale;
        // force a full positive rescan (which rebuilds it) on the next propagate.
        self.pos_full_scan_needed = true;
        self.pos_dirty_reps.clear();
        // #inc-neg: the disequality pair index is keyed by representatives that
        // may have been undone — force a full negative rescan (rebuilds it).
        self.neg_full_scan_needed = true;
        // SAT clause DB state is not guaranteed here — re-arm the full
        // lookahead sweep (see `neg_full_scan_la_needed`).
        self.neg_full_scan_la_needed = true;
        self.neg_dirty_reps.clear();
        self.pending_neg_eqs.clear();
        self.diseq_pair_index.clear();
        self.diseq_keys_by_rep.clear();
        self.pending_diseq_conflicts.clear();
        self.pending_diseq_match_keys.clear();
        // #euf-inc-diseq-undo: index cleared — the next full negative scan must
        // rebuild it from scratch, not take the prebuilt skip.
        self.neg_index_prebuilt = false;
        // #euf-inc-neg-pop: the anchor for the delta cover (the last complete
        // candidate pass) is gone along with the index — the next scan must be a
        // full pass.
        self.neg_pop_delta_valid = false;
        self.neg_pop_retracted.clear();
        self.neg_pop_split_reps.clear();
        self.diseq_keys_dirty = false;
        self.diseq_index_base_depth = 0;
        // Incremental UF-mirror sync: E-graph partition was wiped; the mirror
        // must be rebuilt from scratch on the next sync.
        self.uf_full_sync_needed = true;
        self.uf_dirty_nodes.clear();
        // #8469: Clear shared disequalities from other theories
        self.shared_disequalities.clear();
        self.pending_shared_diseq_conflict = None;
        // Clear function application values (#385) - derived from assignments
        self.func_app_values.clear();
        // #8599: Clear persistent propagation buffer
        self.propagation_output_buf.clear();
        // #euf-lazy-explain: see reset() — witnesses are assignment-derived.
        self.lazy_neg_witness.clear();
    }

    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        let debug = self.debug_euf;

        debug_assert!(
            (lhs.0 as usize) < self.terms.len(),
            "BUG: EUF assert_shared_equality: lhs term {} out of range (term store len={})",
            lhs.0,
            self.terms.len()
        );
        debug_assert!(
            (rhs.0 as usize) < self.terms.len(),
            "BUG: EUF assert_shared_equality: rhs term {} out of range (term store len={})",
            rhs.0,
            self.terms.len()
        );

        if debug {
            safe_eprintln!(
                "[EUF] assert_shared_equality: {} = {} (reason: {} literals)",
                lhs.0,
                rhs.0,
                reason.len()
            );
            for (i, r) in reason.iter().enumerate() {
                safe_eprintln!(
                    "[EUF]   reason[{}]: term {} value {} ({:?})",
                    i,
                    r.term.0,
                    r.value,
                    self.terms.get(r.term),
                );
            }
        }

        // #8742: Reject self-evidencing shared equalities. When the ONLY reason
        // for `lhs = rhs` is the equality atom `(= lhs rhs) = true` itself, the
        // reason is tautological. SAT already handles the atom assignment via
        // `record_assignment`, which queues the merge with
        // `EqualityReason::Direct(term)` and a correct proof justification.
        // Storing a `Shared` edge with a tautological reason would cause
        // conflict analysis to produce clauses of the form (not-T OR not-not-T)
        // that never backtrack the SAT decision forcing the equality atom true,
        // triggering false-UNSAT.
        //
        // TL11's guard at the bridge layer (interface_bridge/propagate.rs)
        // catches the LIA-discovered-equality path but several adapter paths
        // (auf_lira.rs, uf_nia.rs, uf_nra.rs, strings_lia.rs) call
        // assert_shared_equality directly from the arith sub-solver output.
        // This is the symmetric EUF-side sink.
        if reason_is_self_evidencing_shared_eq(self.terms, lhs, rhs, reason) {
            if debug {
                safe_eprintln!(
                    "[EUF] assert_shared_equality: SKIP self-evidencing {} = {} (reason is the equality atom itself; SAT will merge via Direct when atom is assigned)",
                    lhs.0,
                    rhs.0,
                );
            }
            return;
        }

        // SOUNDNESS (#cross-sort-alias wrong-UNSAT, AUFLIRA 2026-07): reject
        // shared equalities between terms of DIFFERENT sorts. Arithmetic N-O
        // propagation discovers equalities by grouping tight-bound variables by
        // numeric VALUE; in mixed Int/Real problems an Int constant and a
        // Real-sorted UF value can share a value (`5` and `(f 3) = 5.0`), and
        // the resulting `f(3) = 5` merge puts `Int(5)` and `Rational(5)` in one
        // class, which the constant-conflict check then "refutes" with the
        // innocent ground fact `(= (f 3) 5.0)` as the sole reason — a false
        // conflict that surfaced as a wrong UNSAT on satisfiable quantified
        // AUFLIRA inputs. A cross-sort equality is not expressible in
        // well-sorted SMT-LIB (EUF's own constant semantics treat Int(5) and
        // Rational(5) as distinct), so skipping it can never lose a sound
        // refutation. Emitters carry the same guard (see
        // `propagate_tight_bound_equalities`); this is the EUF-side sink,
        // symmetric to the #8742 self-evidencing sink above.
        if self.terms.sort(lhs) != self.terms.sort(rhs) {
            if debug {
                safe_eprintln!(
                    "[EUF] assert_shared_equality: SKIP cross-sort {} = {} (lhs sort {:?}, rhs sort {:?})",
                    lhs.0,
                    rhs.0,
                    self.terms.sort(lhs),
                    self.terms.sort(rhs),
                );
            }
            return;
        }

        // Store the reason for later explanation (#320)
        // Use scoped undo records so pop() only removes this scope's entries (#4840).
        let key = Self::edge_key(lhs.0, rhs.0);
        let is_new_entry = !self.shared_equality_reasons.contains_key(&key);
        match self.shared_equality_reasons.get_mut(&key) {
            Some(existing) => {
                if reason.len() < existing.len() {
                    *existing = reason.to_vec();
                }
            }
            None => {
                self.shared_equality_reasons.insert(key, reason.to_vec());
            }
        }
        if is_new_entry {
            self.undo_trail
                .push(UndoRecord::RemoveSharedEqualityReason(key.0, key.1));
        }
        self.dirty = true;

        // Fix for #321: In incremental mode, enqueue the merge directly
        // Previously only stored the reason without queueing, so incremental_rebuild()
        // never processed shared equalities from Nelson-Oppen.
        {
            // Ensure enodes are initialized
            if !self.enodes_init {
                self.init_enodes();
            }
            // Ensure enodes array covers these terms
            self.ensure_enodes_size(lhs.0);
            self.ensure_enodes_size(rhs.0);

            // Only queue if not already in the same class
            let lhs_root = self.enode_find_const(lhs.0);
            let rhs_root = self.enode_find_const(rhs.0);
            if lhs_root != rhs_root {
                self.to_merge.push_back(MergeReason {
                    a: lhs.0,
                    b: rhs.0,
                    reason: EqualityReason::Shared,
                });

                if debug {
                    safe_eprintln!(
                        "[EUF] assert_shared_equality: {} = {} queued for incremental merge",
                        lhs.0,
                        rhs.0
                    );
                }
            }
        }
    }

    fn assert_shared_disequality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        // #8469: Receive disequality from another theory (arith->EUF direction).
        // When arithmetic proves x != y (e.g., from disjoint tight bounds),
        // EUF must record this so that merging x and y's equivalence classes
        // triggers a conflict.
        let debug = self.debug_euf;

        debug_assert!(
            (lhs.0 as usize) < self.terms.len(),
            "BUG: EUF assert_shared_disequality: lhs term {} out of range (term store len={})",
            lhs.0,
            self.terms.len()
        );
        debug_assert!(
            (rhs.0 as usize) < self.terms.len(),
            "BUG: EUF assert_shared_disequality: rhs term {} out of range (term store len={})",
            rhs.0,
            self.terms.len()
        );

        if debug {
            safe_eprintln!(
                "[EUF] assert_shared_disequality: {} != {} (reason: {} literals)",
                lhs.0,
                rhs.0,
                reason.len()
            );
        }

        // SOUNDNESS (#cross-sort-alias): reject ill-sorted disequalities
        // between terms of different sorts (mirrors assert_shared_equality).
        // A cross-sort disequality is vacuous (the classes can never soundly
        // merge), but recording it lets a later — necessarily unsound —
        // cross-sort merge be "explained" with unrelated reason literals,
        // corrupting conflict analysis.
        if self.terms.sort(lhs) != self.terms.sort(rhs) {
            if debug {
                safe_eprintln!(
                    "[EUF] assert_shared_disequality: SKIP cross-sort {} != {} (lhs sort {:?}, rhs sort {:?})",
                    lhs.0,
                    rhs.0,
                    self.terms.sort(lhs),
                    self.terms.sort(rhs),
                );
            }
            return;
        }

        // Store the disequality with scoped undo support.
        let key = Self::edge_key(lhs.0, rhs.0);
        let is_new_entry = !self.shared_disequalities.contains_key(&key);
        match self.shared_disequalities.get_mut(&key) {
            Some(existing) => {
                // Keep the shorter (stronger) reason.
                if reason.len() < existing.len() {
                    *existing = reason.to_vec();
                }
            }
            None => {
                self.shared_disequalities.insert(key, reason.to_vec());
            }
        }
        if is_new_entry {
            self.undo_trail
                .push(UndoRecord::RemoveSharedDisequality(key.0, key.1));
        }

        // Check if lhs and rhs are already in the same equivalence class.
        // If so, this is an immediate conflict: arith says x != y but EUF says x = y.
        if self.enodes_init
            && (lhs.0 as usize) < self.enodes.len()
            && (rhs.0 as usize) < self.enodes.len()
        {
            let lhs_root = self.enode_find_const(lhs.0);
            let rhs_root = self.enode_find_const(rhs.0);
            if lhs_root == rhs_root {
                // Conflict: EUF has lhs = rhs but arith says lhs != rhs.
                // Build conflict from the disequality reason + EUF equality explanation.
                let mut conflict = reason.to_vec();
                let eq_reason = self.explain(lhs, rhs);
                conflict.extend(eq_reason);
                conflict.sort_unstable_by_key(|l| (l.term.0, l.value));
                conflict.dedup_by_key(|l| (l.term.0, l.value));

                if debug {
                    safe_eprintln!(
                        "[EUF] assert_shared_disequality: CONFLICT — {} and {} already equal ({} reasons)",
                        lhs.0,
                        rhs.0,
                        conflict.len()
                    );
                }

                // Store as pending conflict. The next check() will pick it up.
                if self.pending_conflict.is_none() {
                    // Use the conflict mechanism: store as a pending conflict that
                    // check() will return as Unsat. We store the full reason in
                    // pending_propagations as a conflict marker.
                    // Actually, use the shared_diseq_conflict field approach.
                    self.pending_shared_diseq_conflict = Some(conflict);
                }
            }
        }

        self.dirty = true;
    }

    fn supports_euf_semantic_check(&self) -> bool {
        true
    }

    fn propagate_equalities(&mut self) -> EqualityPropagationResult {
        // EUF discovers equalities via asserted equality literals and congruence closure.
        // Drain pending propagations and return them to the Nelson-Oppen loop.
        let mut equalities = Vec::new();
        // `mem::take` (not `drain`) so the deferred `explain` below can borrow
        // `&mut self` while we iterate the owned batch.
        let pending = std::mem::take(&mut self.pending_propagations);
        // Batch-lifetime explain cache (#i6-euf-explain-batch-memo): this drain
        // NEVER merges (it only reads `pending` and the proof forest), so the
        // forest is immutable for the whole loop and one `(a,b)→reasons` cache
        // is valid across every `explain` below — reusing the shared congruence
        // sub-proofs that the per-call memo used to re-walk. Taken from `self`
        // to keep its capacity; restored after the loop. Sound: see `ExplainMemo`.
        let mut batch_memo = std::mem::take(&mut self.explain_memo);
        batch_memo.clear();
        for (lhs, rhs, mut reason) in pending {
            // Lazy N-O reason: merge.rs queued congruence propagations with an
            // empty reason under `lazy_noprop_reasons`; compute the explanation
            // now, at the actual consumer. `explain(lhs,rhs)` walks the same
            // congruence proof-forest edge, so the reason is a valid, identical
            // justification. (Standalone QF_UF never reaches here at all.)
            if self.lazy_noprop_reasons && reason.is_empty() {
                reason = self.explain_using_memo(lhs, rhs, &mut batch_memo);
            }
            if matches!(self.terms.sort(lhs), ay_core::Sort::Array(_))
                && reason_is_self_evidencing_shared_eq(self.terms, lhs, rhs, &reason)
            {
                if self.debug_nelson_oppen {
                    safe_eprintln!(
                        "[EUF N-O] SKIP self-evidencing array equality {:?}:{:?} = {:?}:{:?}",
                        lhs,
                        self.terms.get(lhs),
                        rhs,
                        self.terms.get(rhs)
                    );
                }
                continue;
            }
            equalities.push(DiscoveredEquality::new(lhs, rhs, reason));
        }
        // Restore the cache shell (keeps its allocated capacity for next drain).
        self.explain_memo = batch_memo;

        let debug = self.debug_nelson_oppen;
        if debug && !equalities.is_empty() {
            safe_eprintln!(
                "[EUF N-O] Propagating {} equalities to other theories",
                equalities.len()
            );
            for eq in &equalities {
                safe_eprintln!(
                    "[EUF N-O]   eq {:?}:{:?} = {:?}:{:?} ({} reasons)",
                    eq.lhs,
                    self.terms.get(eq.lhs),
                    eq.rhs,
                    self.terms.get(eq.rhs),
                    eq.reason.len()
                );
            }
        }

        // #8469: Collect EUF-implied disequalities through the unified path.
        // When shared_arith_terms is populated (via set_shared_arith_terms()),
        // collect_disequalities_for_propagation scans negated equality
        // assignments and congruence closure, using internal dirty-epoch
        // tracking to skip redundant scans. No std::mem::take dance needed
        // because the method operates directly on self's fields.
        let disequalities = self.collect_disequalities_for_propagation();
        if debug && !disequalities.is_empty() {
            safe_eprintln!(
                "[EUF N-O] Propagating {} disequalities to other theories",
                disequalities.len()
            );
            for diseq in &disequalities {
                safe_eprintln!(
                    "[EUF N-O]   diseq {:?}:{:?} != {:?}:{:?} ({} reasons)",
                    diseq.lhs,
                    self.terms.get(diseq.lhs),
                    diseq.rhs,
                    self.terms.get(diseq.rhs),
                    diseq.reason.len()
                );
            }
        }

        EqualityPropagationResult {
            equalities,
            disequalities,
            conflict: None,
        }
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        vec![
            ("euf_checks", self.check_count),
            ("euf_conflicts", self.conflict_count),
            ("euf_propagations", self.propagation_count),
            ("euf_cong_neg_propagations", self.cong_neg_propagation_count),
            // #euf-lazy-explain (#8467): emitted vs actually-materialized is
            // the wasted-explain rate the lazy protocol saves.
            ("euf_lazy_props_emitted", self.lazy_emitted_count),
            ("euf_lazy_props_explained", self.lazy_explained_count),
            ("euf_lazy_props_rejected", self.lazy_explain_rejected_count),
        ]
    }

    fn set_lazy_propagation_supported(&mut self, supported: bool) {
        // #euf-lazy-explain: capability handshake (#8467). Only flips lazy
        // emission ON when the consumer declared support AND the kill switch
        // (`--no-euf-lazy-explain`) is not set — the A/B lever + safety
        // valve restoring eager reasons everywhere.
        let killed = ay_core::theory_disable_flags().no_euf_lazy_explain;
        self.lazy_explain_enabled = supported && !killed;
    }

    fn explain_propagation(&mut self, lit: TermId, reason_data: u64) -> Option<Vec<TheoryLit>> {
        self.explain_lazy_propagation(lit, reason_data)
    }

    fn mark_propagation_rejected(&mut self, lit: TermId, reason_data: u64) {
        // #euf-lazy-explain: nothing to invalidate — lazy tokens are
        // self-validating against the live e-graph at materialization time,
        // and `lazy_neg_witness` entries are overwritten on re-emission (a
        // stale entry can only cause a sound rejection). Count only tokens
        // that carry the EUF magic so combiner broadcasts of other theories'
        // rejections do not inflate the statistic.
        if reason_data & crate::theory_propagate::EUF_LAZY_MAGIC_MASK
            == crate::theory_propagate::EUF_LAZY_MAGIC
        {
            let _ = lit;
            self.lazy_explain_rejected_count += 1;
        }
    }

    fn supports_theory_aware_branching(&self) -> bool {
        true
    }

    fn wander_hand_to_vsids(&self) -> bool {
        // #euf-search-quality: when the search wanders (decisions >> conflicts)
        // the historical every-decision round-robin response is catastrophic
        // for EUF (NEQ027: 140k conflicts / 138s vs 8.5k / 16s with VSIDS).
        // Hand over to VSIDS + phase saving instead; implied polarities keep
        // flowing through `suggest_phase_implied`.
        true
    }

    fn suggest_phase_implied(&self, atom: TermId) -> Option<bool> {
        // E-graph-implied polarity only: an equality atom whose sides are
        // already in the same congruence class must be decided TRUE — the
        // opposite polarity is an immediate theory conflict. No preference
        // for anything else (VSIDS + phase saving decide).
        let (a, b) = self.decode_eq(atom)?;
        if self.enodes_init && self.enode_find_const(a.0) == self.enode_find_const(b.0) {
            return Some(true);
        }
        None
    }

    fn suggest_phase(&self, _atom: TermId) -> Option<bool> {
        // Force all theory atoms to be decided, prefer true (merge). Together
        // with the round-robin theory-atom walk in the DPLL extension this is
        // an in-order systematic cell enumeration that dominates on
        // conflict-rich EUF instances (QG-classification gensys family:
        // conflicts arrive at ~2 decisions/conflict and prune fast).
        //
        // On instances where this steering WANDERS (decisions >> conflicts —
        // NEQ/PEQ/large QG iso instances) the DPLL extension trips the sticky
        // wander latch (`wander_hand_to_vsids`, extension/mod.rs), clears the
        // seeded phases, and hands the search to VSIDS + phase saving; from
        // then on only `suggest_phase_implied` polarities flow. Measured on
        // the SMT-LIB QF_UF division: NEQ027_size8 139,999 conflicts / 138s
        // -> 9,719 / 18.6s; hwbench rushhour.2 6.1s -> 3.5s; gensys family
        // byte-identical search (never latches).
        //
        // Phase/decision suggestions only bias search order; they can never
        // change the sat/unsat verdict.
        Some(true)
    }
}

impl EufSolver<'_> {
    /// Unwind EVERY merge back to the pristine post-init e-graph structure
    /// (#qfuflia-egraph-preserve), refreshing derived tables exactly as
    /// `pop()` does. Used by `soft_reset` instead of destroying the e-graph:
    /// `init_enodes` leaves no undo records (the term store is hash-consed,
    /// so no two distinct terms are congruent before any assignment), so
    /// unwinding the whole trail restores exactly the freshly-initialized
    /// state — without the O(terms + apps) rebuild that the next
    /// `assert_literal` would otherwise run (measured: 290k full rebuilds in
    /// 15s on the SMT-COMP QF_UFLIA xs family, ~the entire solve budget).
    fn unwind_all_merges_preserving_structure(&mut self) {
        while let Some(record) = self.undo_trail.pop() {
            match record {
                UndoRecord::SetRoot {
                    node,
                    old_root,
                    old_next,
                } => {
                    if (node as usize) < self.enodes.len() {
                        self.enodes[node as usize].root = old_root;
                        self.enodes[node as usize].next = old_next;
                    }
                }
                UndoRecord::SetClassSize { node, old_size } => {
                    if (node as usize) < self.enodes.len() {
                        self.enodes[node as usize].class_size = old_size;
                    }
                }
                UndoRecord::RemoveParent { node } => {
                    if (node as usize) < self.enodes.len() {
                        self.enodes[node as usize].parents.pop();
                    }
                }
                UndoRecord::RemoveEqualityEdge(a, b) => {
                    self.equality_edges.remove(&(a, b));
                }
                UndoRecord::UnmergeProofForest { node, old_root } => {
                    self.unmerge_proof_forest(node, old_root);
                }
                UndoRecord::RemoveSharedEqualityReason(a, b) => {
                    self.shared_equality_reasons.remove(&(a, b));
                }
                UndoRecord::RemoveSharedDisequality(a, b) => {
                    self.shared_disequalities.remove(&(a, b));
                }
                // #euf-inc-cong-undo: apply the recorded cong_table inverses
                // during the drain so the table stays consistent even though the
                // trailing from-scratch rebuild below reconstructs it exactly.
                UndoRecord::CongSet { sig, term } => {
                    self.cong_table.set(sig, term);
                }
                UndoRecord::CongRemove { sig } => {
                    self.cong_table.remove(&sig);
                }
                // #euf-inc-diseq-undo: apply the recorded diseq index inverses
                // during the drain; the caller (soft_reset/unwind) clears the
                // index and re-arms `neg_full_scan_needed` afterwards, so this is
                // only to keep the structure consistent through the drain.
                UndoRecord::DiseqSet { key, entry } => {
                    self.diseq_pair_index.insert(key, entry);
                }
                UndoRecord::DiseqRemove { key } => {
                    self.diseq_pair_index.remove(&key);
                }
                // #euf-inc-diseq-undo: pure removal during the teardown drain;
                // the caller clears pending_neg_eqs and the index afterwards, so
                // no re-queue is needed here.
                UndoRecord::DiseqUnsync { key, entry: _ } => {
                    self.diseq_pair_index.remove(&key);
                }
            }
        }
        self.undo_scopes.clear();
        self.to_merge.clear();
        // #euf-idle-rebuild: every merge was unwound — full requeue + rescan.
        self.egraph_requeue_needed = true;
        self.ite_sweep_full_needed = true;
        self.bool_merge_pending.clear();
        self.bool_true_anchor = None;
        self.bool_false_anchor = None;
        // Rebuild congruence table from the restored enode state (same
        // rationale as pop(): O(func_apps), cheaper than signature undo).
        if self.enodes_init && self.func_apps_init {
            self.cong_table.clear();
            for meta in &self.func_apps {
                let sig = CongruenceTable::make_signature(meta.func_hash, &meta.args, &self.enodes);
                self.cong_table.insert(meta.term_id, sig);
            }
        }
        // Same cache invalidation as pop(): scan epochs, dirty sets, N-O
        // dedup state, and the UF mirror all reflect merged state.
        self.propagated_eqs.clear();
        self.propagated_eq_pairs.clear();
        self.pending_propagations.clear();
        self.propagated_diseq_pairs.clear();
        self.merge_epoch = self.merge_epoch.wrapping_add(1);
        self.dirty_merge_reps.clear();
        self.new_negated_eqs.clear();
        self.pos_full_scan_needed = true;
        self.pos_dirty_reps.clear();
        self.neg_full_scan_needed = true;
        // SAT clause DB state is not guaranteed here — re-arm the full
        // lookahead sweep (see `neg_full_scan_la_needed`).
        self.neg_full_scan_la_needed = true;
        self.neg_dirty_reps.clear();
        self.pending_neg_eqs.clear();
        self.diseq_pair_index.clear();
        self.diseq_keys_by_rep.clear();
        self.pending_diseq_conflicts.clear();
        self.pending_diseq_match_keys.clear();
        // #euf-inc-diseq-undo: index cleared — the next full negative scan must
        // rebuild it from scratch, not take the prebuilt skip.
        self.neg_index_prebuilt = false;
        // #euf-inc-neg-pop: the anchor for the delta cover (the last complete
        // candidate pass) is gone along with the index — the next scan must be a
        // full pass.
        self.neg_pop_delta_valid = false;
        self.neg_pop_retracted.clear();
        self.neg_pop_split_reps.clear();
        self.diseq_keys_dirty = false;
        self.diseq_index_base_depth = 0;
        self.uf_full_sync_needed = true;
        self.uf_dirty_nodes.clear();
    }
}
