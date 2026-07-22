// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! XOR matching ladders — DRAT-checkable justification for XOR-congruence
//! equivalence edges (#15 T3).
//!
//! An edge merging the outputs of two XOR gates with identical canonical
//! inputs is RAT-but-not-RUP, so the per-edge RUP gate rejected it in proof
//! mode and the substitution collapse never fired on the certified route.
//! Kissat justifies these merges by emitting a resolution ladder
//! (`add_xor_matching_proof_chain`, congruence.c:1084-1159) before the
//! equivalence binaries. This module ports that construction:
//!
//! For gates `l1 ≡ ⊕(v1..vn)` and `l2 ≡ ⊕(v1..vn)` and each implication
//! direction `D ∈ {(¬l1 ∨ l2), (l1 ∨ ¬l2)}`, emit levels k = n-1 down to 1
//! of clauses `D ∪ σ(v_{n-k+1}..v_n)` over all 2^k sign patterns σ. Each
//! level-(n-1) clause is RUP from the two gates' defining clauses (assigning
//! the pattern + the endpoints forces v1 through gate 1 and conflicts on
//! gate 2); each lower-level clause is the resolvent of two clauses from the
//! level above. The final k=0 clauses are the equivalence binaries
//! themselves, emitted by the caller. Every rung is individually RUP-probed
//! before emission — a failed probe rolls the ladder back and skips the edge
//! (fail-closed: coverage loss, never unsoundness). Rungs are deleted from
//! the proof and DB once the edge binaries are in.
//!
//! Emission is PROGRESSIVE (edge order = closure merge order): probes run
//! against the DB including previously inserted edge binaries, so chained
//! merges whose representatives depend on earlier merges verify.

use super::super::super::*;
use crate::congruence::{CongruenceResult, EdgeProvenance};
use crate::kani_compat::DetHashSet as HashSet;

impl Solver {
    /// Progressive DRAT-mode emission of congruence equivalence edges with
    /// XOR matching ladders. Replaces the two-phase mask+emission flow for
    /// the (proof manager present, LRAT off) configuration; the caller keeps
    /// the legacy flow for LRAT and no-proof modes.
    /// Returns the edges actually emitted+inserted, for downstream passes
    /// (forward subsumption) that must not assume skipped equivalences.
    pub(super) fn emit_congruence_edges_drat_progressive(
        &mut self,
        result: &CongruenceResult,
    ) -> Vec<(Literal, Literal)> {
        debug_assert!(self.proof_manager.is_some() && !self.cold.lrat_enabled);
        // The rung probes must see EXACTLY the state the DRAT checker will
        // reconstruct at this proof offset. Two live/checker divergence
        // sources are neutralized here:
        //  1. Stale watches let probes propagate through clauses whose proof
        //     deletion was already emitted (reduce_db / forward subsumption
        //     delete lazily) — flush first.
        //  2. The probes start from the solver's level-0 trail, which
        //     accumulates units from earlier probe side effects and BCP that
        //     are not necessarily proof adds at this offset. Mirror every
        //     level-0 assignment into the proof as a Derived unit — each is
        //     RUP from proof-visible clauses (it was BCP-derived from them),
        //     and re-adding an already-present unit is a trivially-RUP no-op
        //     for the checker.
        self.flush_watches();
        self.mirror_all_fixed_units();
        let mut mirrored_upto = self.trail().len();
        let saved_propagations = self.num_propagations;
        let saved_decisions = self.num_decisions;

        let mut emitted_pairs = HashSet::default();
        let mut emitted_edges: Vec<(Literal, Literal)> = Vec::new();
        for (edge_idx, &(lhs, rhs)) in result.equivalence_edges.iter().enumerate() {
            if lhs == rhs {
                continue;
            }
            if lhs == rhs.negated() {
                // Complementary contradiction edge (x ≡ ¬x): recorded by
                // merge_or_contradict to close the a ≡ … ≡ ¬a cycle for the
                // UNSAT witness unit's RUP probe. Its binaries degenerate to
                // the duplicate-literal units [¬x,¬x]/[x,x]: never insertable
                // (duplicate-watch ICE), and duplicate-literal DRAT add lines
                // are known dpr-trim hazards. Both degenerate RUP probes can
                // pass vacuously on a genuine contradiction (assuming ¬x
                // immediately conflicts), so guard BEFORE probing. The UNSAT
                // obligation is discharged by the caller's result.is_unsat
                // witness-unit path; excluding the edge from emitted_edges
                // also keeps it away from forward subsumption (wf_ff5991a1).
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

            let mut fwd = self.is_rup_binary_under_negation(lhs.negated(), rhs);
            let mut bwd = self.is_rup_binary_under_negation(lhs, rhs.negated());
            let mut rungs: Vec<usize> = Vec::new();
            // Ladder pattern variables by provenance: XOR-match edges use the
            // shared canonical inputs; ITE-match edges use the shared
            // condition (the two-rung-per-direction Kissat ITE chain,
            // congruence.c:1224-1266, is the k=1 instance of the same
            // enumeration). Every rung is RUP-probed before emission either
            // way, so a wrong pattern costs coverage, never soundness.
            let ladder_vars: Option<Vec<usize>> = match result.edge_provenance.get(edge_idx) {
                Some(EdgeProvenance::XorMatch { rhs: xrhs }) => Some(xrhs.clone()),
                Some(EdgeProvenance::IteMatch { cond }) => Some(vec![*cond]),
                _ => None,
            };
            let is_chain_candidate = ladder_vars.is_some();
            if (!fwd || !bwd) && is_chain_candidate {
                if let Some(vars) = ladder_vars {
                    if let Some(r) =
                        self.try_emit_xor_matching_ladder(lhs, rhs, &vars, &mut mirrored_upto)
                    {
                        rungs = r;
                        if !fwd {
                            fwd = self.is_rup_binary_under_negation(lhs.negated(), rhs);
                        }
                        if !bwd {
                            bwd = self.is_rup_binary_under_negation(lhs, rhs.negated());
                        }
                    }
                }
            }

            if !fwd || !bwd {
                self.inproc.congruence.stats_mut().non_rup_equivalences += 1;
                if is_chain_candidate {
                    self.inproc.congruence.stats_mut().xor_ladder_failures += 1;
                }
                // Rungs emitted before the failure STAY: each passed its RUP
                // probe (checker-valid implied clause), and deleting them
                // mid-pass makes the live probe state diverge from the
                // checker's view — later probes can propagate through
                // garbage-kept clauses via stale watches while the checker
                // honors the deletion, producing verdict-correct but
                // NOT-VERIFIED proofs (observed on eq.atree.braun.8/.10).
                // Normal clause management (reduce_db) reclaims them later
                // with properly ordered proof deletions.
                continue;
            }

            if !rungs.is_empty() {
                self.inproc.congruence.stats_mut().xor_ladders_emitted += 1;
            }
            self.mirror_new_trail_units(&mut mirrored_upto);
            self.insert_congruence_equivalence_binary_pair(lhs, rhs, &[], &[]);
            emitted_edges.push((lhs, rhs));
            // Rungs stay in the DB and proof — see the failure-path comment.
        }

        // Restore counters to keep scheduling deterministic (probe pattern).
        self.num_propagations = saved_propagations;
        self.num_decisions = saved_decisions;
        emitted_edges
    }

    /// Mirror level-0 trail literals assigned since the last mirror point
    /// into the proof as Derived unit adds. Probes make PERMANENT level-0
    /// assignments as side effects (probe_has_root_conflict drains pending
    /// propagations); a rung emitted after such a drain may be RUP only
    /// thanks to those units, so the checker needs them at an earlier proof
    /// offset than the eventual conflict-time emission (observed on braun.8:
    /// the needed unit was proof-emitted at add #848 of 849 while the rung
    /// depending on it sat at #671). Each mirrored unit is itself RUP (it
    /// was BCP-derived from proof-visible clauses); duplicate unit adds are
    /// trivially-RUP no-ops for the checker.
    fn mirror_new_trail_units(&mut self, mirrored_upto: &mut usize) {
        let tlen = self.trail().len();
        if tlen <= *mirrored_upto {
            return;
        }
        let new_units: Vec<Literal> = self.trail()[*mirrored_upto..tlen].to_vec();
        for unit in new_units {
            self.mirror_unit_once(unit);
        }
        *mirrored_upto = tlen;
    }

    /// Mirror every level-0 FIXED literal into the proof. Fixed literals are
    /// flushed off the trail between passes (Kissat-style), so the pass-start
    /// trail scan misses them: on 70da0b78, unit 28523 was level-0 true when
    /// a rung probed pre-falsified against it, but its first proof add sat
    /// 26k steps later — the rung was checker-rejected (step 143161). Scans
    /// `vals` via lit_value; the bitmap dedups across passes.
    fn mirror_all_fixed_units(&mut self) {
        for v in 0..self.num_vars {
            let lit = Literal::positive(Variable(v as u32));
            let lit = match self.lit_value(lit) {
                Some(true) => lit,
                Some(false) => lit.negated(),
                None => continue,
            };
            if self.var_data[v].level != 0 {
                continue;
            }
            self.mirror_unit_once(lit);
        }
    }

    /// Emit a Derived unit add once per literal (deduped by the persistent
    /// bitmap; duplicate adds are harmless but bloat the proof).
    pub(super) fn mirror_unit_once(&mut self, unit: Literal) {
        let li = unit.index();
        if self.cold.proof_mirrored_units.len() < self.num_vars * 2 {
            self.cold
                .proof_mirrored_units
                .resize(self.num_vars * 2, false);
        }
        if self.cold.proof_mirrored_units[li] {
            return;
        }
        self.cold.proof_mirrored_units[li] = true;
        self.proof_emit_unit(unit, &[], ProofAddKind::Derived);
    }

    /// Emit the intermediate ladder rungs for one XOR-match edge. Returns
    /// the arena indices of the inserted rungs, or `None` (with full
    /// rollback) if any rung fails its RUP probe.
    fn try_emit_xor_matching_ladder(
        &mut self,
        l1: Literal,
        l2: Literal,
        xrhs: &[usize],
        mirrored_upto: &mut usize,
    ) -> Option<Vec<usize>> {
        let n = xrhs.len();
        // n==1 is the ITE matching chain (two rungs per direction over
        // ±cond); cap the exponential at the extraction arity limit.
        if !(1..=5).contains(&n) {
            return None;
        }
        let num_lits = self.num_vars * 2;
        for &v in xrhs {
            let var = v / 2;
            if v >= num_lits || var == l1.variable().index() || var == l2.variable().index() {
                return None;
            }
        }

        let mut rungs: Vec<usize> = Vec::new();
        for (a, b) in [(l1.negated(), l2), (l1, l2.negated())] {
            for k in (1..n).rev() {
                let vars = &xrhs[n - k..];
                for mask in 0u32..(1u32 << k) {
                    let mut lits: Vec<Literal> = Vec::with_capacity(k + 2);
                    lits.push(a);
                    lits.push(b);
                    for (i, &v) in vars.iter().enumerate() {
                        lits.push(Literal::from_index(v ^ (((mask >> i) & 1) as usize)));
                    }
                    // Mirror any units fixed-and-FLUSHED since the last rung
                    // (BCP after an earlier edge, or decompose inside the
                    // fixpoint loop, fixes level-0 units and flushes them off
                    // the trail — the trail-based incremental mirror misses
                    // them, so a later rung leaning on such a unit is not
                    // checker-RUP; 70da0b78 step-143161 divergence). The vals
                    // scan + dedup bitmap makes this idempotent and cheap
                    // after the first pass.
                    self.mirror_all_fixed_units();
                    self.mirror_new_trail_units(mirrored_upto);
                    if !self.is_rup_clause_under_negation(&lits) {
                        // Keep already-emitted rungs (checker-valid; see the
                        // failure-path comment in the caller).
                        return None;
                    }
                    let idx = self.insert_ladder_rung(&lits);
                    rungs.push(idx);
                }
            }
        }
        Some(rungs)
    }

    /// Add one rung to the proof and the clause DB (learned, watched) so
    /// later rungs and the edge binaries can RUP-propagate through it.
    fn insert_ladder_rung(&mut self, lits: &[Literal]) -> usize {
        let pid = self
            .proof_emit_add(lits, &[], ProofAddKind::Derived)
            .unwrap_or(0);
        let idx = self.arena.add(lits, true);
        if idx >= self.cold.clause_ids.len() {
            self.cold.clause_ids.resize(idx + 1, 0);
        }
        self.cold.clause_ids[idx] = if pid != 0 {
            pid
        } else {
            let id = self.cold.next_clause_id;
            self.cold.next_clause_id += 1;
            id
        };
        let cref = ClauseRef(idx as u32);
        let mut watched_lits: Vec<Literal> = lits.to_vec();
        // A rung containing root-assigned literals may not expose two
        // watchable literals; leave it unwatched then (still in the proof and
        // arena — subsequent probes simply cannot propagate through it, which
        // at worst fails a later rung's probe and rolls the ladder back).
        //
        // is_binary MUST be computed from the clause length (f0bafebd root
        // cause, wf_0c7d84e9): rungs have k+2 >= 3 literals, and a >=3-lit
        // clause watched with BINARY_FLAG propagates its second watched
        // literal whenever the first falsifies — ignoring the remaining
        // literals (unsound propagation), skipping the BCP liveness check
        // (the binary path never reads the arena header), and surviving
        // deletion (delete_binary_clause_watches only unlinks true binaries).
        // On f0bafebd this produced a phantom level-0 unit (-1318 through the
        // deleted rung husk [1369 -1318 2820]) that collect_level0_garbage
        // later baked into strengthened clauses the DRAT checker rejects
        // (dpr-trim "RAT check on proof pivot failed [1163 -2820]").
        if let Some(watched) =
            self.prepare_watched_literals(&mut watched_lits, WatchOrderPolicy::Preserve)
        {
            self.attach_clause_watches(cref, watched, lits.len() == 2);
        }
        idx
    }

    /// Delete ladder rungs from the proof and mark them garbage in the DB
    /// (forward-subsumption deletion pattern + #8101 targeted watch flush).
    /// Currently UNUSED on the emission paths (rungs are kept — deleting
    /// mid-pass desyncs live probes from the checker); retained for a future
    /// end-of-pass batch cleanup.
    #[allow(dead_code)]
    pub(super) fn cleanup_ladder_rungs(&mut self, rungs: &[usize]) {
        for &idx in rungs {
            if self.arena.is_empty_clause(idx) {
                continue;
            }
            let cid = self.cold.clause_ids.get(idx).copied().unwrap_or(0);
            let _ = self.proof_emit_delete_arena(idx, cid);
            let clen = self.arena.len_of(idx);
            if clen > 2 {
                let (w0, w1) = self.arena.watched_literals(idx);
                if w0.index() < self.dirty_watches.len() {
                    self.dirty_watches[w0.index()] = true;
                }
                if w1.index() < self.dirty_watches.len() {
                    self.dirty_watches[w1.index()] = true;
                }
            }
            self.stats.clear_bcp_learned_1963_blocker_cert(idx);
            self.arena.mark_garbage_keep_data(idx);
            if idx < self.cold.clause_ids.len() {
                self.cold.clause_ids[idx] = 0;
            }
        }
    }
}
