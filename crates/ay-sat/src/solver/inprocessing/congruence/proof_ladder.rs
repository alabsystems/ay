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
//! (fail-closed: coverage loss, never unsoundness). Rungs stay in the proof;
//! in the solver they are unwatched arena clauses the edge's probes
//! (`frozen_probe.rs`) propagate through, rolled back out of the arena once
//! those probes are done, so the clause DB, its offsets and the watch lists
//! are the ones a run without a proof has.
//!
//! Emission is PROGRESSIVE (edge order = closure merge order): probes run
//! against the DB including previously inserted edge binaries, so chained
//! merges whose representatives depend on earlier merges verify.

use super::super::super::*;
use crate::clause_arena::ArenaAppendMark;
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
        //  1. Stale watches could let probes propagate through clauses whose
        //     proof deletion was already emitted (reduce_db / forward
        //     subsumption delete lazily). The probes (`frozen_rup_probe`)
        //     skip every dead clause, binary or long, instead of flushing the
        //     watch lists: a flush here, which a run without a proof never
        //     does, changed later tick charges (posture screen, 29a27e97).
        //  2. The probes start from the solver's level-0 trail, which
        //     accumulates units from earlier probe side effects and BCP that
        //     are not necessarily proof adds at this offset. Mirror every
        //     level-0 assignment into the proof as a Derived unit — each is
        //     RUP from proof-visible clauses (it was BCP-derived from them),
        //     and re-adding an already-present unit is a trivially-RUP no-op
        //     for the checker.
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

            // `--sat-veripb-hints`: the probes also read each binary's hint ids.
            let (mut fwd, mut fwd_ids) = self.rup_binary_with_veripb_hints(lhs.negated(), rhs, &[]);
            let (mut bwd, mut bwd_ids) = self.rup_binary_with_veripb_hints(lhs, rhs.negated(), &[]);
            let mut rungs: Vec<usize> = Vec::new();
            // Rungs are appended from here; the arena returns to this mark.
            let rung_mark = self.arena.append_mark();
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
                    if self.try_emit_xor_matching_ladder(
                        lhs,
                        rhs,
                        &vars,
                        &mut mirrored_upto,
                        &mut rungs,
                    ) {
                        if !fwd {
                            (fwd, fwd_ids) =
                                self.rup_binary_with_veripb_hints(lhs.negated(), rhs, &rungs);
                        }
                        if !bwd {
                            (bwd, bwd_ids) =
                                self.rup_binary_with_veripb_hints(lhs, rhs.negated(), &rungs);
                        }
                    }
                }
            }
            // The rungs served this edge's probes alone: once its binaries are
            // probed (subsumed by them, or refuted) they leave the solver.
            let retired = self.retire_ladder_rungs(&rungs, rung_mark);

            if !fwd || !bwd {
                self.inproc.congruence.stats_mut().non_rup_equivalences += 1;
                if is_chain_candidate {
                    self.inproc.congruence.stats_mut().xor_ladder_failures += 1;
                }
                // Nothing will cite the rungs: delete them from the proof too,
                // or they stay live in the checker's database for the rest of
                // the proof (every later `red` scans them).
                self.delete_retired_rungs(retired);
                continue;
            }

            if !rungs.is_empty() {
                self.inproc.congruence.stats_mut().xor_ladders_emitted += 1;
            }
            self.mirror_new_trail_units(&mut mirrored_upto);
            let (fwd_ids, bwd_ids) = (fwd_ids.unwrap_or_default(), bwd_ids.unwrap_or_default());
            self.insert_congruence_equivalence_binary_pair(lhs, rhs, &fwd_ids, &bwd_ids);
            // The binaries' hints may cite rungs, so the rungs go after them;
            // the binaries subsume every rung.
            self.delete_retired_rungs(retired);
            emitted_edges.push((lhs, rhs));
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
    ///
    /// Every XOR ladder rung repeats the scan, so a unit already mirrored is
    /// passed over on its value and the bitmap alone: on 30e8b477 the scan
    /// that read each fixed variable's level and called `mirror_unit_once`
    /// for it took 13 of 35 s of preprocessing.
    fn mirror_all_fixed_units(&mut self) {
        if self.cold.proof_mirrored_units.len() < self.num_vars * 2 {
            self.cold
                .proof_mirrored_units
                .resize(self.num_vars * 2, false);
        }
        for v in 0..self.num_vars {
            let lit = Literal::positive(Variable(v as u32));
            let lit = match self.vals[lit.index()] {
                0 => continue,
                val if val > 0 => lit,
                _ => lit.negated(),
            };
            if self.cold.proof_mirrored_units[lit.index()] || self.var_data[v].level != 0 {
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
        // `--sat-veripb-hints`: stated from its level-0 reason (veripb_units.rs).
        if !self.veripb_state_root_unit(unit, None) {
            self.proof_emit_unit(unit, &[], ProofAddKind::Derived);
        }
    }

    /// Emit the intermediate ladder rungs for one XOR-match edge, pushing
    /// their arena indices onto `rungs`. Returns `false` if any rung fails
    /// its RUP probe; the rungs emitted before it stay in `rungs` for the
    /// caller to retire with the rest.
    fn try_emit_xor_matching_ladder(
        &mut self,
        l1: Literal,
        l2: Literal,
        xrhs: &[usize],
        mirrored_upto: &mut usize,
        rungs: &mut Vec<usize>,
    ) -> bool {
        let n = xrhs.len();
        // n==1 is the ITE matching chain (two rungs per direction over
        // ±cond); cap the exponential at the extraction arity limit.
        if !(1..=5).contains(&n) {
            return false;
        }
        let num_lits = self.num_vars * 2;
        for &v in xrhs {
            let var = v / 2;
            if v >= num_lits || var == l1.variable().index() || var == l2.variable().index() {
                return false;
            }
        }

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
                    let (rup, veripb_ids) =
                        self.rup_clause_with_veripb_hints(&lits, rungs.as_slice());
                    if !rup {
                        // Already-emitted rungs stay in the proof
                        // (checker-valid; see the failure-path comment in the
                        // caller); the caller takes them out of the solver.
                        return false;
                    }
                    if let Some(ids) = &veripb_ids {
                        self.veripb_ready_hints(&lits, ids);
                    }
                    let idx = self.insert_ladder_rung(&lits);
                    rungs.push(idx);
                }
            }
        }
        true
    }

    /// Add one rung to the proof and the arena (irredundant, never watched):
    /// the edge's later rung and binary probes propagate through it as one of
    /// their `rungs` (`frozen_rup_probe`), and `retire_ladder_rungs` removes
    /// it once they are done. Unwatched, a rung cannot be the 3-literal
    /// clause watched as a binary that once propagated a phantom unit
    /// (f0bafebd, wf_0c7d84e9), nor move any watch a run without a proof has.
    /// Irredundant because a learned add grows the arena's learned index (a
    /// `Vec` and a hash table whose capacities `memory_bytes` reads, the table
    /// keeping a tombstone after the removal), which `rollback_appends`
    /// cannot return to its old capacity; nothing reads the flag of a clause
    /// that lives only for one edge's probes.
    fn insert_ladder_rung(&mut self, lits: &[Literal]) -> usize {
        let pid = self
            .proof_emit_add(lits, &[], ProofAddKind::Derived)
            .unwrap_or(0);
        let idx = self.arena.add(lits, false);
        let cid = if pid != 0 {
            pid
        } else {
            let id = self.cold.next_clause_id;
            self.cold.next_clause_id += 1;
            id
        };
        self.cold.record_clause_id(idx, cid);
        idx
    }

    /// Take one edge's rungs back out of the solver, keeping them in the
    /// proof. A checker holding more clauses than the solver accepts every
    /// RUP step, and every RAT/`red` step whose pivot or witness touches
    /// only fresh extension variables; the substitution-witness (symmetry)
    /// steps are written in preprocessing before congruence first runs, so
    /// no such step meets a rung. They were never watched and are no reason
    /// (every probe backtracked), and the arena returns to `mark`, taken
    /// before the first of them: the clause DB is word for word the one a run
    /// without a proof has, with the same offsets for the clauses added next.
    fn retire_ladder_rungs(
        &mut self,
        rungs: &[usize],
        mark: ArenaAppendMark,
    ) -> Vec<(Vec<Literal>, u64)> {
        let mut retired = Vec::with_capacity(rungs.len());
        for &idx in rungs {
            let lits = self.arena.literals(idx).to_vec();
            let id = self.cold.clause_ids.get_mut(idx).map_or(0, std::mem::take);
            retired.push((lits, id));
        }
        self.arena.rollback_appends(mark);
        retired
    }

    /// Delete rungs `retire_ladder_rungs` took out of the solver from the
    /// proof as well (by id, or by content where the writer numbers them).
    fn delete_retired_rungs(&mut self, retired: Vec<(Vec<Literal>, u64)>) {
        for (lits, id) in retired {
            let _ = self.proof_emit_delete(&lits, id);
        }
    }
}
