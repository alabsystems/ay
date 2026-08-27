// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//\! Congruence closure for equivalence merging.

use super::super::*;
use crate::kani_compat::DetHashSet as HashSet;

mod proof_ladder;
mod rup_probing;

impl Solver {
    ///
    /// Extracts gates from the formula, then iteratively merges outputs of
    /// gates with the same type and equivalent inputs. Adds binary equivalence
    /// clauses to the clause DB for BCP and decompose's SCC to pick up.
    ///
    /// CaDiCaL architecture (#5237): congruence only discovers equivalences
    /// and adds binary implication clauses. All clause-level substitution
    /// (rewriting, deletion, variable marking, reconstruction) is handled by
    /// decompose() which runs after congruence in the inprocessing pipeline.
    /// CaDiCaL: congruence.cpp (gate rewriting only) + decompose.cpp (SCC
    /// clause DB substitution). internal.cpp: `if (extract_gates(true)) decompose();`
    ///
    /// Returns `true` if equivalences were found and decompose should run
    /// to perform the actual clause rewriting.
    ///
    /// Must be called at decision level 0.
    pub(in crate::solver) fn congruence(&mut self) -> bool {
        if ay_core::misc_cli_flags().ab_dump_db {
            self.dump_live_db_for_triage("congruence_round_start");
        }
        let equivs_before = self.inproc.congruence.stats().equivalences_found;
        let result = self.congruence_body();
        let equivs_after = self.inproc.congruence.stats().equivalences_found;
        let yield_this_round = equivs_after - equivs_before;

        if ay_core::misc_cli_flags().ab_subst_stats {
            let s = self.inproc.congruence.stats();
            eprintln!(
                "AB_CONGRUENCE: equivs_total={} this_round={} non_rup_equivs={} non_rup_units={} non_rup_contradiction_units={} subsumed={} parity_certified_applied={} xor_ladders={} ladder_fails={}",
                equivs_after,
                yield_this_round,
                s.non_rup_equivalences,
                s.non_rup_units,
                s.non_rup_contradiction_units,
                s.congruence_subsumed,
                s.parity_certified_units_applied,
                s.xor_ladders_emitted,
                s.xor_ladder_failures,
            );
        }

        // CaDiCaL congruence.cpp:7871-7874 uses a Delay mechanism:
        //   - No merges: bump_delay (interval += 1, limit = interval)
        //   - Merges found: reduce_delay (interval /= 2, limit = interval)
        // Translated to AY's conflict-interval scheduling:
        //   - No equivs: 2x growth (existing backoff)
        //   - Few equivs (<50): 1.5x growth (diminishing returns — O(clauses)
        //     gate extraction for ~10 equivs is poor ROI on 360K-clause formulas)
        //   - Many equivs (>=50): halve interval (high yield, rescan soon)
        // On FmlaEquivChain (4.7M clauses), this reduces congruence from 28
        // rounds (~5s overhead) to ~10 rounds while still capturing the 301
        // total equivalences that drive decompose substitution (#7279).
        const CONGRUENCE_HIGH_YIELD: u64 = 50;

        if yield_this_round >= CONGRUENCE_HIGH_YIELD {
            // High yield — halve the interval for timely follow-up.
            self.inproc_ctrl.congruence.reschedule_growing(
                self.num_conflicts,
                CONGRUENCE_INTERVAL,
                1,
                2, // halve
                CONGRUENCE_MAX_INTERVAL,
            );
        } else if yield_this_round > 0 {
            // Low yield — grow interval 1.5x (still productive but diminishing).
            self.inproc_ctrl.congruence.reschedule_growing(
                self.num_conflicts,
                CONGRUENCE_INTERVAL,
                3,
                2, // 1.5x growth
                CONGRUENCE_MAX_INTERVAL,
            );
        } else {
            // No equivalences — 2x exponential backoff (CaDiCaL pattern).
            // On large residuals (shuffling-2: 4.9M clauses), congruence is
            // O(clauses) and finds nothing repeatedly. 2× growth from 2K:
            // 2K → 4K → 8K → 16K → 32K → 64K limits total calls (#7135).
            self.inproc_ctrl.congruence.reschedule_growing(
                self.num_conflicts,
                CONGRUENCE_INTERVAL,
                2,
                1,
                CONGRUENCE_MAX_INTERVAL,
            );
        }
        if result {
            // Congruence-discovered equivalences must be rewritten immediately
            // by the following decompose pass, even if decompose already ran
            // earlier in the same inprocessing round.
            self.inproc_ctrl.decompose.next_conflict = 0;
        }
        result
    }

    /// Congruence body — early returns are safe; wrapper handles rescheduling.
    fn congruence_body(&mut self) -> bool {
        if !self.require_level_zero() {
            return false;
        }

        // Defense-in-depth: congruence equivalences are consumed by decompose
        // (push_equivalence_reconstruction + clause rewriting), which cannot
        // operate in incremental mode. Matches condition()/decompose() (#3662).
        if self.cold.has_been_incremental {
            return false;
        }

        // LRAT override handled centrally by inproc_ctrl.with_proof_overrides() (#4557).

        self.inproc.congruence.ensure_num_vars(self.num_vars);

        // V5 lifecycle guard (#3906 wave-2 D6): build a frozen bitmask instead
        // of cloning the full Vec<u32> freeze_counts (#5079 Finding 3). A variable
        // is frozen if it has a non-zero freeze_count OR is inactive (Eliminated,
        // Substituted, Fixed). Frozen variables are excluded from gate extraction
        // to prevent reconstruction order conflicts (BVE witnesses replay before
        // congruence equivalences).
        let congruence_frozen: Vec<bool> = (0..self.num_vars)
            .map(|i| {
                let explicitly_frozen =
                    i < self.cold.freeze_counts.len() && self.cold.freeze_counts[i] > 0;
                let lifecycle_frozen =
                    i < self.var_lifecycle.len() && self.var_lifecycle.is_inactive(i);
                explicitly_frozen || lifecycle_frozen
            })
            .collect();

        // Congruence-level gate rewriting consumes root assignments from the
        // live solver state. This re-enables the vals-aware simplification path
        // after the XOR polarity regression (#6997) that originally forced the
        // blanket disable in #3413.
        let result =
            self.inproc
                .congruence
                .run(&mut self.arena, Some(&self.vals), &congruence_frozen);

        if ay_core::misc_cli_flags().ab_subst_dump_edges {
            eprintln!(
                "DUMP_RESULT: is_unsat={} units={:?} edges={}",
                result.is_unsat,
                result.units.iter().map(|l| l.index()).collect::<Vec<_>>(),
                result.equivalence_edges.len(),
            );
            for &(a, b) in &result.equivalence_edges {
                eprintln!("DUMP_EDGE: {} {}", a.index(), b.index());
            }
        }

        // Set up watches for new binary clauses from hyper-ternary resolution.
        // These are RUP: (a,b,c) + (¬a,b) → (b,c) verified by setting ¬b,¬c
        // which forces a from the ternary, then ¬a→b from the binary conflicts.
        for &(clause_idx, lit0, lit1) in &result.new_binary_clauses {
            let off_header = clause_idx;
            if self.arena.is_empty_clause(off_header) {
                continue;
            }
            // HTR binary clauses are RUP by construction: (a,b,c) + (¬a,b) → (b,c).
            // Emit as Derived with LRAT hints when available (#5419).
            // When hints are empty (e.g., literal already true at level 0),
            // fall back to TrustedTransform in DRAT mode only. LRAT mode
            // cannot emit a non-unit clause with empty hints, so drop the
            // binary from the active DB instead of leaving behind an
            // unprovable reason clause.
            let htr_hints = self.collect_rup_binary_lrat_hints(lit0, lit1);
            if self.cold.lrat_enabled && htr_hints.is_empty() {
                // Mark watched literals dirty for targeted flush (#8101).
                let clen = self.arena.len_of(off_header);
                if clen > 2 {
                    let (w0, w1) = self.arena.watched_literals(off_header);
                    if w0.index() < self.dirty_watches.len() {
                        self.dirty_watches[w0.index()] = true;
                    }
                    if w1.index() < self.dirty_watches.len() {
                        self.dirty_watches[w1.index()] = true;
                    }
                }
                self.stats.clear_bcp_learned_1963_blocker_cert(off_header);
                self.arena.mark_garbage_keep_data(off_header);
                continue;
            }
            let htr_kind = if htr_hints.is_empty() {
                ProofAddKind::TrustedTransform
            } else {
                ProofAddKind::Derived
            };
            let proof_id = self
                .proof_emit_add(&[lit0, lit1], &htr_hints, htr_kind)
                .unwrap_or(0);
            // Register proof ID so later deletions emit correct LRAT ID (#5005).
            if self.cold.lrat_enabled && proof_id != 0 {
                self.cold.clause_ids_grow_for(clause_idx);
                self.cold.clause_ids[clause_idx] = proof_id;
            }
            let cref = ClauseRef(clause_idx as u32);
            let mut watched_lits = [lit0, lit1];
            let watched = self
                .prepare_watched_literals(&mut watched_lits, WatchOrderPolicy::Preserve)
                .expect("binary congruence clauses must expose two watch literals");
            self.attach_clause_watches(cref, watched, true);
        }

        // Proof gate (#4575, #5419): validate RUP and collect LRAT hints for
        // each equivalence edge. In DRAT mode this is a pure RUP check; in LRAT
        // mode the hints collected here are passed to proof_emit_add so the LRAT
        // checker can verify each binary. Non-RUP edges cause the entire batch
        // to be skipped (same as the original DRAT safety gate).
        //
        // Hint collection reuses the probe infrastructure already paid for in
        // congruence_edges_are_rup() — the only added cost is chain bookkeeping.
        let mut edge_hints: Vec<(Vec<u64>, Vec<u64>)> = Vec::new();
        // Per-edge RUP mask: true = edge passed RUP, false = non-RUP (skip).
        // In the proof-manager path, non-RUP is encoded as empty hints on
        // a non-trivial/non-dedup edge. In the no-proof path, this mask is
        // the explicit filter. (#7137 Phase 2: per-edge RUP filtering)
        let mut rup_mask: Vec<bool> = Vec::new();
        // Edges actually applied to the DB. Forward subsumption below must
        // never assume equivalences whose edges were SKIPPED by the proof
        // gate: subsuming with un-inserted equivalences deletes clauses that
        // are not redundant w.r.t. the real DB — observed as an internal SAT
        // on UNSAT 70da0b78 under --sat-no-drat-subst (caught by the
        // FINALIZE_SAT_FAIL gate). None = all closure edges were applied.
        let mut applied_edges: Option<Vec<(Literal, Literal)>> = None;
        if self.proof_manager.is_some() && !self.cold.lrat_enabled {
            // DRAT progressive path (#15 T3): per-edge probe -> XOR matching
            // ladder -> insert, in closure merge order so probes see earlier
            // edges' binaries. Fills rup_mask with false so the legacy
            // emission block below is a no-op (this path inserts directly).
            applied_edges = Some(self.emit_congruence_edges_drat_progressive(&result));
            rup_mask.resize(result.equivalence_edges.len(), false);
            edge_hints.resize(result.equivalence_edges.len(), (Vec::new(), Vec::new()));
        } else if self.proof_manager.is_some() {
            let saved_propagations = self.num_propagations;
            let saved_decisions = self.num_decisions;

            let mut seen = HashSet::default();
            for &(lhs, rhs) in &result.equivalence_edges {
                if lhs == rhs {
                    rup_mask.push(true);
                    edge_hints.push((Vec::new(), Vec::new()));
                    continue;
                }
                if lhs == rhs.negated() {
                    // Complementary contradiction edge (x ≡ ¬x): recorded by
                    // merge_or_contradict to close the a ≡ … ≡ ¬a cycle for
                    // the UNSAT witness unit's RUP probe. Its "equivalence
                    // binaries" degenerate to the duplicate-literal units
                    // [¬x,¬x]/[x,x] — never insertable (duplicate-watch ICE)
                    // and nonsensical as an applied equivalence. Mask it
                    // false so the emission loop skips it AND applied_edges
                    // excludes it from forward subsumption. The
                    // contradiction's proof obligation is discharged by the
                    // result.is_unsat witness-unit path below (wf_ff5991a1).
                    self.inproc
                        .congruence
                        .stats_mut()
                        .complementary_edges_skipped += 1;
                    rup_mask.push(false);
                    edge_hints.push((Vec::new(), Vec::new()));
                    continue;
                }
                let key = if lhs.index() <= rhs.index() {
                    (lhs, rhs)
                } else {
                    (rhs, lhs)
                };
                if !seen.insert(key) {
                    rup_mask.push(true);
                    edge_hints.push((Vec::new(), Vec::new()));
                    continue;
                }

                // Per-edge RUP filtering (#7137 Phase 2): accept edges
                // individually. Non-RUP edges are skipped during emission.
                // CaDiCaL never produces unprovable edges (constructive proof
                // chains), but AY's post-hoc RUP check can reject some edges
                // from ambiguous XOR/ITE extraction.
                if !self.cold.lrat_enabled {
                    let fwd_rup = self.is_rup_binary_under_negation(lhs.negated(), rhs);
                    let bwd_rup = self.is_rup_binary_under_negation(lhs, rhs.negated());
                    if !fwd_rup || !bwd_rup {
                        self.inproc.congruence.stats_mut().non_rup_equivalences += 1;
                        rup_mask.push(false);
                        edge_hints.push((Vec::new(), Vec::new()));
                        continue;
                    }
                    rup_mask.push(true);
                    edge_hints.push((Vec::new(), Vec::new()));
                } else {
                    let fwd_hints = self.collect_rup_binary_lrat_hints(lhs.negated(), rhs);
                    let bwd_hints = self.collect_rup_binary_lrat_hints(lhs, rhs.negated());
                    if fwd_hints.is_empty() || bwd_hints.is_empty() {
                        self.inproc.congruence.stats_mut().non_rup_equivalences += 1;
                        rup_mask.push(false);
                        edge_hints.push((Vec::new(), Vec::new()));
                        continue;
                    }
                    rup_mask.push(true);
                    edge_hints.push((fwd_hints, bwd_hints));
                }
            }

            // Restore counters to keep scheduling deterministic.
            self.num_propagations = saved_propagations;
            self.num_decisions = saved_decisions;
            applied_edges = Some(
                result
                    .equivalence_edges
                    .iter()
                    .zip(rup_mask.iter())
                    .filter(|(_, &ok)| ok)
                    .map(|(&e, _)| e)
                    .collect(),
            );
        } else {
            // No proof manager: trust gate extraction without RUP checking.
            // CaDiCaL never does post-hoc RUP on equivalence edges — it trusts
            // that gate extraction produces correct equivalences. AY's gate
            // extraction is sound when XOR parity is correct (#7137 parity fix
            // in gates.rs). XOR/ITE equivalences are RAT (not RUP), so RUP
            // checking unconditionally rejects them even though they're correct.
            // Skipping the RUP gate for no-proof mode matches CaDiCaL's design.
            rup_mask.resize(result.equivalence_edges.len(), true);
            edge_hints.resize(result.equivalence_edges.len(), (Vec::new(), Vec::new()));
        }

        // Add binary implication clauses for each direct merge edge.
        // CaDiCaL congruence.cpp: merge_literals() / really_merge_literals()
        // adds equivalence binaries to the clause DB. These become edges in
        // the binary implication graph that decompose's SCC will discover.
        //
        // Proof status by gate type (#4575):
        // - AND equivalences: the binaries ARE RUP.
        // - XOR/ITE equivalences: the binaries are RAT but NOT RUP.
        // Per-edge RUP filtering (#7137 Phase 2): non-RUP edges are skipped
        // via rup_mask. Only RUP-verified edges are emitted as Derived with
        // LRAT hints (#5419).
        {
            let mut emitted_pairs = HashSet::default();
            for (edge_idx, &(lhs, rhs)) in result.equivalence_edges.iter().enumerate() {
                if lhs == rhs {
                    continue;
                }
                // Skip non-RUP edges (#7137 Phase 2).
                if !rup_mask[edge_idx] {
                    continue;
                }
                if lhs == rhs.negated() {
                    // Complementary contradiction edge — see the rup_mask
                    // loop above. This guard is load-bearing in the no-proof
                    // path (rup_mask is all-true there): without it the
                    // duplicate-literal binaries [¬x,¬x]/[x,x] reach watch
                    // setup and trip the duplicate-watch debug_assert in
                    // clause_add (wf_ff5991a1 Defect 1, reproduced by
                    // group_fuzz cnf_fuzz_inprocessing_mixed_{small,dense}).
                    self.inproc
                        .congruence
                        .stats_mut()
                        .complementary_edges_skipped += 1;
                    continue;
                }
                let key = if lhs.index() <= rhs.index() {
                    (lhs, rhs)
                } else {
                    (rhs, lhs)
                };
                if !emitted_pairs.insert(key) {
                    continue;
                }
                let (ref fwd_hints, ref bwd_hints) = edge_hints[edge_idx];
                let fwd_hints = fwd_hints.clone();
                let bwd_hints = bwd_hints.clone();
                self.insert_congruence_equivalence_binary_pair(lhs, rhs, &fwd_hints, &bwd_hints);
            }
        }

        // Drain level-0 BCP: equivalence binaries may imply units (#5107).
        // Use record_level0_conflict_chain to build proper LRAT hints (#4596).
        if let Some(conflict_ref) = self.search_propagate() {
            self.record_level0_conflict_chain(conflict_ref);
            return false;
        }

        // Contradiction path ordering (2026-07-02, #15): like the ordinary-unit
        // loop below, contradiction units are probed AFTER the HTR/equivalence
        // binaries are in the DB. Without this, a genuine closure-derived UNSAT
        // (e.g. 70da0b78 with clause-driven XOR groups) is rejected because its
        // witness units are only RUP relative to F + the equivalence binaries.
        // Contradiction detected by congruence closure (e.g., XOR odd-cycle).
        // Soundness gate (#7137): only accept RUP-verified contradiction units.
        // Non-RUP units are skipped to prevent false UNSAT from wrong congruence
        // claims (e.g., asconhash-m5_6: 97K gates, 0 conflicts, false UNSAT).
        if result.is_unsat {
            debug_assert!(
                !result.units.is_empty(),
                "BUG: congruence UNSAT must provide contradiction unit witness(es)"
            );
            let mut any_enqueued = false;
            for unit in &result.units {
                let proof_unit = self.pick_congruence_contradiction_unit(*unit);
                let unit_hints = self.collect_rup_unit_lrat_hints(proof_unit);
                if self.has_empty_clause {
                    break;
                }
                let rup_pass = if unit_hints.is_empty() {
                    self.is_rup_unit_under_negation(proof_unit)
                } else {
                    true
                };
                if !rup_pass {
                    // Unit is not RUP — congruence claim is unsound. Skip it.
                    self.inproc
                        .congruence
                        .stats_mut()
                        .non_rup_contradiction_units += 1;
                    continue;
                }
                let proof_kind = if unit_hints.is_empty() {
                    ProofAddKind::TrustedTransform
                } else {
                    ProofAddKind::Derived
                };
                self.proof_emit_unit(proof_unit, &unit_hints, proof_kind);
                if !self.var_is_assigned(proof_unit.variable().index()) {
                    self.enqueue(proof_unit, None);
                    any_enqueued = true;
                }
            }
            if any_enqueued {
                // Let BCP detect the contradiction so record_level0_conflict_chain
                // builds proper LRAT hints for the empty clause (#4596).
                if !self.propagate_check_unsat() {
                    self.mark_empty_clause_with_level0_hints();
                }
                self.inproc_ctrl.congruence.next_conflict = u64::MAX;
                return false;
            }
            // ALL contradiction units failed RUP — reject the is_unsat claim.
            // Fall through to equivalence path (if any equivalences exist).
        }

        // T1 ordering fix (#15 substitution collapse, 2026-07-02): this unit
        // loop now runs AFTER the HTR binaries and equivalence binaries have
        // been inserted into the clause DB, so the per-unit RUP probe sees the
        // augmented formula. Previously units were probed against F alone and
        // rejected (non_rup_units) even when one-step RUP from F + repr binaries.
        // Process non-contradiction units discovered by gate simplification cascade.
        // CaDiCaL congruence.cpp:4848-4896: units from AND(false input) → output false,
        // AND(all true) → output true, complementary pair → output false, etc.
        // These units are discovered WITHIN congruence closure but are NOT contradiction
        // witnesses — they're forced by the gate structure. Enqueue them as level-0
        // assignments and propagate. Design: #3366 congruence-gate-simplification.md.
        //
        // Soundness gate (#7137): skip non-RUP units to prevent wrong assignments
        // from corrupting the trail and causing false UNSAT via subsequent BCP.
        // #7137-relax: machine-checked-parity trust. When
        // --sat-congruence-parity-trust, accept XOR full-collapse (arity-0)
        // units whose emitted polarity is the deductive-checks-discharged EXACT parity
        // (the development proof harness::xor_collapse_parity_verified — proven the
        // imperative `parity_flip` XOR-accumulator equals the GF(2) mod-2
        // popcount, order-independent, single-flip-sensitive) even when AY's
        // post-hoc RUP cannot reconstruct the (ambiguous) XOR chain. Such units
        // are sound by construction: correct gate extraction + valid UF/level-0
        // substitutions + now machine-checked parity (the documented asconhash
        // root cause). Default-off; RUP stays the backstop for everything else,
        // so asconhash-style wrong units (and any non-XOR non-RUP unit) are
        // still rejected.
        let parity_trust = ay_core::sat_ab_switches().congruence_parity_trust;
        let parity_certified: HashSet<Literal> = if parity_trust {
            result.parity_certified_units.iter().copied().collect()
        } else {
            HashSet::default()
        };
        if !result.is_unsat && !result.units.is_empty() {
            for &unit in &result.units {
                // Skip variables already assigned (including by side-effect propagation
                // from a prior iteration's collect_rup_unit_lrat_hints).
                if self.var_is_assigned(unit.variable().index()) {
                    continue;
                }
                // collect_rup_unit_lrat_hints calls probe_has_root_conflict() which
                // drains pending level-0 BCP. This side-effect propagation can assign
                // additional variables (including `unit`'s variable) and may discover
                // a root-level conflict. Re-check assignment after hint collection.
                let unit_hints = self.collect_rup_unit_lrat_hints(unit);
                if self.has_empty_clause {
                    return false;
                }
                // Re-check: hint collection's side-effect BCP may have assigned this var.
                if self.var_is_assigned(unit.variable().index()) {
                    continue;
                }
                if unit_hints.is_empty() && !self.is_rup_unit_under_negation(unit) {
                    if parity_trust && parity_certified.contains(&unit) {
                        // Machine-checked-parity certified XOR collapse: accept
                        // without RUP reconstruction (#7137-relax, default-off).
                        self.inproc
                            .congruence
                            .stats_mut()
                            .parity_certified_units_applied += 1;
                    } else {
                        self.inproc.congruence.stats_mut().non_rup_units += 1;
                        continue;
                    }
                }
                let proof_kind = if unit_hints.is_empty() {
                    ProofAddKind::TrustedTransform
                } else {
                    ProofAddKind::Derived
                };
                self.proof_emit_unit(unit, &unit_hints, proof_kind);
                // Re-check: collect_rup_unit_lrat_hints → probe_has_root_conflict
                // → search_propagate does permanent level-0 BCP that can assign
                // this variable between the check at line 426 and here.
                if self.var_is_assigned(unit.variable().index()) {
                    continue;
                }
                self.enqueue(unit, None);
            }
            // Level-0 BCP after unit enqueue: new units may cause conflict.
            // Use record_level0_conflict_chain to build proper LRAT hints (#4596).
            if let Some(conflict_ref) = self.search_propagate() {
                self.record_level0_conflict_chain(conflict_ref);
                return false;
            }
        }

        if !result.found_equivalences {
            return false;
        }

        // Mark clause_db as modified so incremental rebuild triggers.
        if !result.equivalence_edges.is_empty() {
            self.cold.inprocessing_modified_clause_db = true;
        }

        // Forward subsumption with equivalence-aware representatives.
        // CaDiCaL congruence.cpp:4955-5073. Must run AFTER proof emission
        // because RUP checks need gate-defining clauses alive.
        //
        // Soundness: the equivalence binaries added above (¬a ∨ b, a ∨ ¬b)
        // force the CDCL model to assign equivalent variables the same value.
        // Forward subsumption only deletes a clause when a shorter clause
        // with a subset of representative literals exists. Any model
        // satisfying the shorter clause therefore satisfies the longer one,
        // so the original_ledger verification in finalize_sat_model succeeds
        // regardless of whether decompose runs afterward.
        //
        // Forward subsumption with proof-aware deletion.
        // In LRAT mode, we collect subsumed indices and emit proof deletions.
        // In non-proof mode, mark_garbage_keep_data is used directly (#6270, #8382).
        let subsumed = if self.cold.lrat_enabled {
            let indices = self.inproc.congruence.forward_subsume_collect_indices(
                &self.arena,
                applied_edges
                    .as_deref()
                    .unwrap_or(&result.equivalence_edges),
            );
            let mut count = 0u64;
            for idx in indices {
                let cid = if idx < self.cold.clause_ids.len() {
                    self.cold.clause_ids[idx]
                } else {
                    0
                };
                // #6270 unit-rederivation (husk adjudication): this deletion
                // path bypasses delete_clause_observed, so re-derive any
                // level-0 unit proof that references this clause's ID BEFORE
                // emitting the delete — otherwise later LRAT chains cite a
                // deleted premise and the checker rejects the proof.
                if !self.lrat_rederive_units_referencing_clause(idx, cid) {
                    break;
                }
                let _ = self.proof_emit_delete_arena(idx, cid);
                // Clear the clause ID after emitting the proof deletion (#8488).
                // mark_garbage_keep_data keeps the clause data intact (for proof
                // reconstruction) but doesn't zero the length, so is_active()
                // still returns true. Later inprocessing passes (vivify, reduce_db)
                // may try to delete this clause again via delete_clause_checked →
                // delete_clause_observed → proof_emit_delete_arena, which reads
                // clause_ids[idx]. If the stale ID is still present, the proof
                // manager panics with "deleting unknown LRAT clause ID" because
                // the ID was already removed from known_lrat_ids above.
                if idx < self.cold.clause_ids.len() {
                    self.cold.clause_ids[idx] = 0;
                }
                self.stats.clear_bcp_learned_1963_blocker_cert(idx);
                self.arena.mark_garbage_keep_data(idx);
                count += 1;
            }
            count
        } else {
            self.stats.clear_bcp_learned_1963_blocker_certs();
            self.inproc.congruence.forward_subsume_with_equivalences(
                &mut self.arena,
                applied_edges
                    .as_deref()
                    .unwrap_or(&result.equivalence_edges),
            )
        };
        if subsumed > 0 {
            self.cold.inprocessing_modified_clause_db = true;
            self.inproc.congruence.stats_mut().congruence_subsumed += subsumed;
        }

        // All clause-level substitution (rewriting, deletion, variable marking,
        // reconstruction entry pushing) is deferred to decompose(), which runs
        // after congruence in the inprocessing pipeline. decompose's SCC finds
        // the equivalences through the binary clauses added above and rewrites
        // ALL clauses uniformly — including reason-protected clauses that
        // replace_clause_checked would skip (#5237).

        true
    }

    /// Emit and insert the two equivalence binaries for one congruence edge.
    ///
    /// CaDiCaL congruence.cpp:3075: equivalence binaries must be watched
    /// clauses in the clause DB for BCP propagation, not just proof
    /// emissions. Without this, congruence-derived units fail RUP checks and
    /// manual enqueue corrupts solver state (#5107). Clause IDs are assigned
    /// unconditionally (#8197, #8069 Phase 2a) so downstream consumers
    /// (decompose LRAT chain, backward proof, clause trace) can look up any
    /// arena offset.
    pub(super) fn insert_congruence_equivalence_binary_pair(
        &mut self,
        lhs: Literal,
        rhs: Literal,
        fwd_hints: &[u64],
        bwd_hints: &[u64],
    ) {
        let id_fwd = self.proof_emit_add(&[lhs.negated(), rhs], fwd_hints, ProofAddKind::Derived);
        let id_bwd = self.proof_emit_add(&[lhs, rhs.negated()], bwd_hints, ProofAddKind::Derived);

        let proof_ids = [id_fwd.unwrap_or(0), id_bwd.unwrap_or(0)];
        for (i, lits) in [[lhs.negated(), rhs], [lhs, rhs.negated()]]
            .into_iter()
            .enumerate()
        {
            let idx = self.arena.add(&lits, false);
            if let Some(ref mut gc_occ) = self.gc_occ {
                gc_occ.add_clause(idx, &lits);
            }
            // Notify BVE of new irredundant binary (#8096); wrapper also bumps
            // bve_marked and marks JIT dirty vars (#8202).
            self.note_irredundant_clause_added_for_bve(idx, &lits);
            {
                self.cold.clause_ids_grow_for(idx);
                let cid = if proof_ids[i] != 0 {
                    proof_ids[i]
                } else {
                    let id = self.cold.next_clause_id;
                    self.cold.next_clause_id += 1;
                    id
                };
                self.cold.clause_ids[idx] = cid;
            }
            let cref = ClauseRef(idx as u32);
            let mut watched_lits = lits;
            let watched = self
                .prepare_watched_literals(&mut watched_lits, WatchOrderPolicy::Preserve)
                .expect("equivalence binary must expose two watch literals");
            self.attach_clause_watches(cref, watched, true);
        }
    }

    /// Soundness-triage dump (--sat-ab-dump-db): the live clause DB + trail
    /// with the current DRAT proof offset, for divergence diffing against a
    /// checker replay of the proof prefix.
    pub(in crate::solver) fn dump_live_db_for_triage(&mut self, tag: &str) {
        let offset = self
            .proof_manager
            .as_ref()
            .map(|m| m.proof_adds_written())
            .unwrap_or(0);
        eprintln!(
            "DBDUMP begin tag={tag} proof_adds={offset} pass={:?} decision_level={}",
            self.cold.diagnostic_pass, self.decision_level
        );
        let trail_snapshot: Vec<Literal> = self.trail().to_vec();
        for lit in trail_snapshot {
            let vi = lit.variable().index();
            let reason = match self.var_reason(vi) {
                Some(r) => {
                    let lits: Vec<String> = self
                        .arena
                        .literals(r.0 as usize)
                        .iter()
                        .map(|l| l.index().to_string())
                        .collect();
                    format!("reason=[{}]", lits.join(" "))
                }
                None => "reason=NONE".to_string(),
            };
            eprintln!(
                "DBU: {} level={:?} {}",
                lit.index(),
                self.var_level(lit.variable()),
                reason
            );
        }
        for idx in self.arena.active_indices() {
            let lits: Vec<String> = self
                .arena
                .literals(idx)
                .iter()
                .map(|l| l.index().to_string())
                .collect();
            eprintln!("DBC: {}", lits.join(" "));
        }
        eprintln!("DBDUMP end tag={tag}");
    }
}
