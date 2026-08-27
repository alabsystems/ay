// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core congruence closure engine with eager gate rewriting.
//!
//! Maintains a hash table of gates keyed by canonicalized signature.
//! When an equivalence is discovered, all gates containing the merged
//! literal are eagerly rewritten and re-hashed. Hash collisions between
//! gates with identical signatures trigger output merges, which cascade
//! until a fixpoint is reached.
//!
//! Submodules:
//! - `simplify`: Unit-literal gate simplification.
//! - `merge`: Gate rewriting after equivalence merges.
//!
//! Reference: CaDiCaL congruence.cpp (Biere, Faller, Fazekas, Pollitt 2024).

mod merge;
mod simplify;

#[cfg(test)]
mod tests;

use crate::gates::{Gate, GateType};
use crate::literal::Literal;
use hashbrown::HashMap;
use smallvec::SmallVec;
use std::collections::VecDeque;

use super::union_find::{merge_or_contradict, UnionFind};
use super::EdgeProvenance;
use super::{debug_congruence_enabled, CongruenceClosure};

/// Inline capacity for gate inputs/signatures.
///
/// XOR gates are capped at 5 inputs and ITE/Equiv are smaller, so the common
/// case stays allocation-free. Wider AND gates are legal and spill to the heap
/// instead of being truncated.
pub(super) const INLINE_GATE_INPUTS: usize = 5;

/// Canonical form of a gate for comparison.
/// Uses inline storage for the common <=5-input case while preserving all
/// inputs for wide AND gates. Inputs are sorted to handle commutativity.
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub(super) struct GateSignature {
    gate_type: GateType,
    inputs: SmallVec<[usize; INLINE_GATE_INPUTS]>,
}

/// Signature index for the congruence fixpoint, plus the reverse map that makes
/// a gate's entry REMOVABLE.
///
/// THE LEAK THIS CLOSES. The table used to be a bare
/// `HashMap<GateSignature, usize>`, and a gate's entry was removed by
/// RECOMPUTING its signature from its current inputs under the current
/// union-find:
///
/// ```ignore
/// let sig = Self::canonicalize(&gate_types[gi], &gate_inputs[gi], uf);
/// if gate_table.get(&sig) == Some(&gi) { gate_table.remove(&sig); }
/// ```
///
/// A gate is rewritten precisely BECAUSE a merge changed one of its inputs'
/// representatives — so by the time the removal runs, `canonicalize` produces a
/// DIFFERENT key from the one the gate was filed under, the lookup misses, and
/// the old entry is stranded. `reinsert_gate` then files a new one. Net effect:
/// the table grows by one entry per rewrite, forever, and rewrites are driven by
/// merges which schedule further merges.
///
/// Measured at `b2258ab6` on SAT-COMP 2026 `post-cbmc-aes-ee-r2` — a 33 MB
/// input that 28 of 31 official solvers solve: 17.6 GB resident and a `c memout`
/// 8 s in against `--memory 6000`. `--disable congruence` on the same instance
/// peaks at 705 MB, and a stack sample puts 4607 of 4704 samples inside
/// `compute_congruence_closure -> rewrite_gate_after_merge`.
///
/// (The source comment at the retired `--sat-congruence-memory-bound` guard
/// records this instance's runaway as "no longer reproducible". It is
/// reproducible at HEAD. That guard does not catch it either — it is gated on
/// 200 000 iterations of the fixpoint, and this explodes in fewer.)
///
/// WHY EXACT REMOVAL IS SEMANTICS-PRESERVING, not just smaller. Every key the
/// table can be QUERIED with is produced by [`CongruenceClosure::canonicalize`],
/// which maps each input through `uf.find` — so a matchable key contains only
/// CURRENT union-find representatives. A stranded key is stranded exactly
/// because a merge demoted one of its literals out of representative status, and
/// the union-find only ever merges further. A stranded key can therefore never
/// be produced by a later `canonicalize` call, and never matches again. It is
/// dead weight, and dropping it removes no equivalence the closure would have
/// found.
///
/// It is also FASTER: `remove_gate_signature` no longer canonicalizes at all,
/// and canonicalization under it was 1400+ of those 4704 samples.
pub(super) struct GateTable {
    map: HashMap<GateSignature, usize>,
    /// The signature each gate is CURRENTLY filed under, or `None` when the gate
    /// has no entry. Bounded by the gate count — unlike the stranded entries it
    /// replaces, which were bounded by the rewrite count.
    ///
    /// Empty under the legacy arm, which keeps the recompute-and-hope removal.
    filed_under: Vec<Option<GateSignature>>,
    exact_removal: bool,
}

impl GateTable {
    pub(super) fn new(gate_count: usize, exact_removal: bool) -> Self {
        Self {
            map: HashMap::with_capacity(gate_count),
            filed_under: if exact_removal {
                vec![None; gate_count]
            } else {
                Vec::new()
            },
            exact_removal,
        }
    }

    pub(super) fn get(&self, sig: &GateSignature) -> Option<usize> {
        self.map.get(sig).copied()
    }

    pub(super) fn contains_key(&self, sig: &GateSignature) -> bool {
        self.map.contains_key(sig)
    }

    /// Number of live signature entries — the quantity that used to grow
    /// without bound. Reported by `--sat-mem-probe`.
    pub(super) fn len(&self) -> usize {
        self.map.len()
    }

    pub(super) fn insert(&mut self, sig: GateSignature, gi: usize) {
        if self.exact_removal {
            if let Some(slot) = self.filed_under.get_mut(gi) {
                *slot = Some(sig.clone());
            }
        }
        self.map.insert(sig, gi);
    }

    /// Drop `gi`'s entry. `recompute` supplies the legacy arm's guessed key and
    /// is not called at all under exact removal.
    pub(super) fn remove_gate(&mut self, gi: usize, recompute: impl FnOnce() -> GateSignature) {
        if self.exact_removal {
            if let Some(slot) = self.filed_under.get_mut(gi) {
                if let Some(sig) = slot.take() {
                    self.map.remove(&sig);
                }
            }
            return;
        }
        let sig = recompute();
        if self.map.get(&sig) == Some(&gi) {
            self.map.remove(&sig);
        }
    }
}

/// Append `gi` to a literal's occurrence list, collapsing the list first when it
/// has doubled since its last collapse.
///
/// A gate is re-pushed onto its inputs' occurrence lists on EVERY reinsertion,
/// and reinsertion happens once per rewrite, so a gate rewritten `n` times
/// appears `n` times. Nothing reads a repeat: the drain iterates
/// `mem::take(&mut occs[lit])` and skips dead gates, and rewriting an
/// already-rewritten gate re-derives the same signature. Collapsing on a
/// doubling watermark keeps each list at O(gates using that literal) instead of
/// O(rewrites touching it), at an amortized O(len log len) per doubling.
///
/// Gated by `--sat-congruence-bounded-occs` (default OFF): duplicates DO change
/// how many times `rewrite_gate_after_merge` runs inside one drain, so this is a
/// scheduling change, not a pure lifetime fix, and it is unmeasured on the
/// corpus.
fn push_occurrence(occs: &mut [Vec<usize>], lit: usize, gi: usize) {
    if occs_are_bounded() {
        let list = &mut occs[lit];
        // 64 entries of slack before the first collapse: short lists are the
        // overwhelming majority and must not pay a sort.
        if list.len() >= OCCS_COLLAPSE_FLOOR && list.len().is_power_of_two() {
            list.sort_unstable();
            list.dedup();
        }
    }
    occs[lit].push(gi);
}

/// Shortest occurrence list that may be collapsed by [`push_occurrence`].
const OCCS_COLLAPSE_FLOOR: usize = 64;

fn occs_are_bounded() -> bool {
    use std::sync::OnceLock;
    static F: OnceLock<bool> = OnceLock::new();
    *F.get_or_init(|| {
        ay_core::sat_ab_switches()
            .congruence_bounded_occs
            .unwrap_or(false)
    })
}

impl CongruenceClosure {
    /// Reduce XOR inputs after UF rewriting.
    ///
    /// UF representatives can be complemented literals, so XOR simplification
    /// must handle both `x XOR x = 0` and `x XOR ¬x = 1`.
    fn reduce_xor_input_pairs(
        inputs: &mut SmallVec<[usize; 5]>,
        uf: &mut UnionFind,
        parity_flip: &mut bool,
    ) {
        for input in inputs.iter_mut() {
            *input = uf.find(*input);
        }
        inputs.sort_unstable();
        let mut write = 0usize;
        let mut i = 0usize;
        while i < inputs.len() {
            let current = inputs[i];
            if i + 1 < inputs.len() {
                let next = inputs[i + 1];
                if current == next {
                    i += 2;
                    continue;
                }
                if current == (next ^ 1) {
                    // Complementary pair `x ⊕ ¬x = true`: one GF(2) flip,
                    // folded through the shared, trust-checked parity step.
                    *parity_flip =
                        ay_sat_congruence_core::xor_accumulate_parity(*parity_flip, true);
                    i += 2;
                    continue;
                }
            }
            inputs[write] = current;
            write += 1;
            i += 1;
        }
        inputs.truncate(write);
    }

    /// Compute congruence closure with eager gate rewriting (CaDiCaL approach).
    ///
    /// Returns contradiction unit witness on UNSAT, otherwise
    /// `(found_equiv, discovered_units)` where `found_equiv` is true iff
    /// actual variable equivalences (merges) were discovered, and
    /// `discovered_units` are literals forced true by gate simplification.
    pub(super) fn compute_congruence_closure(
        &mut self,
        gates: &[Gate],
        uf: &mut UnionFind,
        vals: Option<&[i8]>,
        equivalence_edges: &mut Vec<(Literal, Literal)>,
        edge_provenance: &mut Vec<EdgeProvenance>,
        xor_certified_units: &mut Vec<Literal>,
    ) -> Result<(bool, Vec<Literal>), Literal> {
        let num_lits = self.num_vars * 2;

        // Mutable gate data: inputs as literal indices, output, alive flag
        let gate_count = gates.len();
        let mut gate_types: Vec<GateType> = Vec::with_capacity(gate_count);
        let mut gate_inputs: Vec<SmallVec<[usize; 5]>> = Vec::with_capacity(gate_count);
        let mut gate_outputs: Vec<usize> = Vec::with_capacity(gate_count);
        let mut gate_alive: Vec<bool> = vec![true; gate_count];

        for gate in gates {
            gate_types.push(gate.gate_type);
            gate_inputs.push(gate.inputs.iter().map(|lit| lit.index()).collect());
            let out_lit = if gate.negated_output {
                Literal::negative(gate.output)
            } else {
                Literal::positive(gate.output)
            };
            gate_outputs.push(out_lit.index());
        }

        let mut schedule: VecDeque<(usize, usize, EdgeProvenance)> = VecDeque::new();

        let mut unit_vals: Vec<i8> = vec![0; num_lits];
        if let Some(v) = vals {
            let copy_len = num_lits.min(v.len());
            unit_vals[..copy_len].copy_from_slice(&v[..copy_len]);
        }
        let mut units_to_propagate: VecDeque<usize> = VecDeque::new();
        let mut discovered_units: Vec<Literal> = Vec::new();
        let equivs_before_simplify = self.stats.equivalences_found;

        // Simplify gates using level-0 assignments (CaDiCaL
        // propagate_units_and_equivalences).
        if let Some(v) = vals {
            for gi in 0..gate_count {
                if !gate_alive[gi] {
                    continue;
                }
                let out_idx = gate_outputs[gi];
                if out_idx < v.len() && v[out_idx] != 0 {
                    gate_alive[gi] = false;
                    continue;
                }

                match gate_types[gi] {
                    GateType::And => {
                        let mut has_false = false;
                        gate_inputs[gi].retain(|inp| {
                            let inp = *inp;
                            if inp >= v.len() {
                                return true;
                            }
                            if v[inp] > 0 {
                                false
                            } else if v[inp] < 0 {
                                has_false = true;
                                false
                            } else {
                                true
                            }
                        });
                        if has_false {
                            let out = uf.find(out_idx);
                            gate_alive[gi] = false;
                            Self::record_unit(
                                out ^ 1,
                                &mut unit_vals,
                                &mut units_to_propagate,
                                &mut discovered_units,
                                num_lits,
                            )?;
                            continue;
                        }
                        match gate_inputs[gi].len() {
                            0 => {
                                let out = uf.find(out_idx);
                                gate_alive[gi] = false;
                                Self::record_unit(
                                    out,
                                    &mut unit_vals,
                                    &mut units_to_propagate,
                                    &mut discovered_units,
                                    num_lits,
                                )?;
                            }
                            1 => {
                                let out = uf.find(out_idx);
                                let inp = uf.find(gate_inputs[gi][0]);
                                if out != inp {
                                    merge_or_contradict(
                                        uf,
                                        out,
                                        inp,
                                        equivalence_edges,
                                        EdgeProvenance::Plain,
                                        edge_provenance,
                                        &mut self.stats,
                                    )?;
                                }
                                gate_alive[gi] = false;
                            }
                            _ => {}
                        }
                    }
                    GateType::Xor => {
                        if gate_inputs[gi].len() == 2 {
                            let (inp0, inp1) = (gate_inputs[gi][0], gate_inputs[gi][1]);
                            let v0 = if inp0 < v.len() { v[inp0] } else { 0 };
                            let v1 = if inp1 < v.len() { v[inp1] } else { 0 };
                            if v0 != 0 || v1 != 0 {
                                let out = uf.find(out_idx);
                                if v0 != 0 && v1 != 0 {
                                    let parity_flip = (v0 > 0) ^ (v1 > 0);
                                    gate_alive[gi] = false;
                                    let unit_lit = if parity_flip { out } else { out ^ 1 };
                                    Self::record_unit(
                                        unit_lit,
                                        &mut unit_vals,
                                        &mut units_to_propagate,
                                        &mut discovered_units,
                                        num_lits,
                                    )?;
                                } else {
                                    let (assigned_val, other) =
                                        if v0 != 0 { (v0, inp1) } else { (v1, inp0) };
                                    let target =
                                        uf.find(if assigned_val > 0 { other ^ 1 } else { other });
                                    if out != target {
                                        merge_or_contradict(
                                            uf,
                                            out,
                                            target,
                                            equivalence_edges,
                                            EdgeProvenance::Plain,
                                            edge_provenance,
                                            &mut self.stats,
                                        )?;
                                    }
                                    gate_alive[gi] = false;
                                }
                            }
                        }
                    }
                    GateType::Equiv => {
                        if gate_inputs[gi].len() == 1 {
                            let inp = gate_inputs[gi][0];
                            let vi = if inp < v.len() { v[inp] } else { 0 };
                            if vi != 0 {
                                let out = uf.find(out_idx);
                                gate_alive[gi] = false;
                                let unit_lit = if vi > 0 { out } else { out ^ 1 };
                                Self::record_unit(
                                    unit_lit,
                                    &mut unit_vals,
                                    &mut units_to_propagate,
                                    &mut discovered_units,
                                    num_lits,
                                )?;
                            }
                        }
                    }
                    GateType::Ite => {
                        if gate_inputs[gi].len() == 3 {
                            let cond = gate_inputs[gi][0];
                            let vc = if cond < v.len() { v[cond] } else { 0 };
                            if vc != 0 {
                                let out = uf.find(out_idx);
                                let target_idx = if vc > 0 { 1 } else { 2 };
                                let target = uf.find(gate_inputs[gi][target_idx]);
                                if out != target {
                                    merge_or_contradict(
                                        uf,
                                        out,
                                        target,
                                        equivalence_edges,
                                        EdgeProvenance::Plain,
                                        edge_provenance,
                                        &mut self.stats,
                                    )?;
                                }
                                gate_alive[gi] = false;
                            } else {
                                let then_inp = gate_inputs[gi][1];
                                let else_inp = gate_inputs[gi][2];
                                let vt = if then_inp < v.len() { v[then_inp] } else { 0 };
                                let ve = if else_inp < v.len() { v[else_inp] } else { 0 };
                                if vt != 0 && ve != 0 {
                                    let out = uf.find(out_idx);
                                    gate_alive[gi] = false;
                                    if (vt > 0) == (ve > 0) {
                                        let unit_lit = if vt > 0 { out } else { out ^ 1 };
                                        Self::record_unit(
                                            unit_lit,
                                            &mut unit_vals,
                                            &mut units_to_propagate,
                                            &mut discovered_units,
                                            num_lits,
                                        )?;
                                    } else if vt > 0 {
                                        let cond_repr = uf.find(cond);
                                        if out != cond_repr {
                                            merge_or_contradict(
                                                uf,
                                                out,
                                                cond_repr,
                                                equivalence_edges,
                                                EdgeProvenance::Plain,
                                                edge_provenance,
                                                &mut self.stats,
                                            )?;
                                        }
                                    } else {
                                        let neg_cond = uf.find(cond ^ 1);
                                        if out != neg_cond {
                                            merge_or_contradict(
                                                uf,
                                                out,
                                                neg_cond,
                                                equivalence_edges,
                                                EdgeProvenance::Plain,
                                                edge_provenance,
                                                &mut self.stats,
                                            )?;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Reduce XOR gates through seeded UF before building occurrence lists.
        for gi in 0..gate_count {
            if !gate_alive[gi] || gate_types[gi] != GateType::Xor {
                continue;
            }
            let out = uf.find(gate_outputs[gi]);
            let mut parity_flip = false;
            Self::reduce_xor_input_pairs(&mut gate_inputs[gi], uf, &mut parity_flip);
            match gate_inputs[gi].len() {
                0 => {
                    gate_alive[gi] = false;
                    let unit_lit = if parity_flip { out } else { out ^ 1 };
                    // Parity-certified XOR collapse: the emitted polarity is the
                    // machine-checked-exact parity (ay-sat-verified
                    // xor_collapse_parity_verified). #7137-relax.
                    if Self::record_unit(
                        unit_lit,
                        &mut unit_vals,
                        &mut units_to_propagate,
                        &mut discovered_units,
                        num_lits,
                    )? {
                        xor_certified_units.push(Literal::from_index(unit_lit));
                    }
                }
                1 => {
                    let inp = uf.find(gate_inputs[gi][0]);
                    let target = if parity_flip { inp ^ 1 } else { inp };
                    gate_alive[gi] = false;
                    if out != target {
                        if crate::congruence::dump_merges_enabled() {
                            eprintln!("DUMP_SCHED[gate_rewriting.rs:357]: {out} {target}");
                        }
                        schedule.push_back((out, target, EdgeProvenance::Plain));
                    }
                }
                _ => {
                    if parity_flip {
                        gate_outputs[gi] ^= 1;
                    }
                }
            }
        }

        // Occurrence lists: literal index -> gate indices that use it as input.
        let mut occs: Vec<Vec<usize>> = vec![Vec::new(); num_lits];
        for (gi, inputs) in gate_inputs.iter().enumerate() {
            if !gate_alive[gi] {
                continue;
            }
            for &lit_idx in inputs {
                if lit_idx < num_lits {
                    occs[lit_idx].push(gi);
                }
            }
        }

        // Gate table: signature -> first gate index with that signature.
        //
        // Tri-state `--sat-congruence-exact-gate-table`: `true` keys removal off
        // the signature the gate was actually filed under; the default restores
        // the recompute-and-hope removal that strands one entry per rewrite (see
        // `GateTable`). Both arms live in one binary, so a paired A/B needs no
        // second build.
        //
        // Default OFF, by measurement discipline rather than by preference: the
        // argument that stranded entries are unmatchable is in `GateTable`'s
        // docs and holds, but arming it alone did NOT convert the witness it was
        // derived from (`post-cbmc-aes-ee-r2` still memouts at 4842 MB), so it
        // has a cost and no demonstrated benefit. Flip it on a paired corpus
        // A/B, not on the argument.
        let mut gate_table = GateTable::new(
            gate_count,
            ay_core::sat_ab_switches()
                .congruence_exact_gate_table
                .unwrap_or(false),
        );

        for gi in 0..gate_count {
            if !gate_alive[gi] {
                continue;
            }
            let sig = Self::canonicalize(&gate_types[gi], &gate_inputs[gi], uf);
            if let Some(existing_gi) = gate_table.get(&sig) {
                let out_a = uf.find(gate_outputs[existing_gi]);
                let out_b = uf.find(gate_outputs[gi]);
                if out_a != out_b {
                    if crate::congruence::dump_merges_enabled() {
                        eprintln!("DUMP_SCHED[gate_rewriting.rs:393]: {out_b} {out_a}");
                    }
                    // XOR collisions carry the shared canonical inputs so the
                    // solver-side emitter can build the matching DRAT ladder
                    // (#15 T3); other gate types stay Plain (AND congruence
                    // edges are directly RUP).
                    let prov = if gate_types[gi] == GateType::Xor {
                        EdgeProvenance::XorMatch {
                            rhs: sig.inputs.to_vec(),
                        }
                    } else if gate_types[gi] == GateType::Ite {
                        EdgeProvenance::IteMatch {
                            cond: sig.inputs[0],
                        }
                    } else {
                        EdgeProvenance::Plain
                    };
                    schedule.push_back((out_b, out_a, prov));
                }
                gate_alive[gi] = false;
            } else {
                gate_table.insert(sig, gi);
            }
        }

        let simplification_equivs = self.stats.equivalences_found - equivs_before_simplify;
        let mut found_equiv = !schedule.is_empty() || simplification_equivs > 0;
        let initial_merges = schedule.len() as u64;
        let mut total_merges = 0u64;

        // Alternating unit-propagation + equivalence-propagation loop.
        // CaDiCaL congruence.cpp:4848-4896.
        //
        // MEMORY BOUND. This fixpoint had none, and merges schedule further
        // merges while growing the per-gate input vectors, so it can generate
        // work faster than it drains: measured on the SAT-COMP 2026 instance
        // `post-cbmc-aes-ee-r2` (a 33 MB file that 28 of 31 official solvers
        // solve) it grew at ~0.7 GB/s to 82.75 GB, straight past `--memory`.
        // `--memory` could not stop it because `poll_process_memory_limit` is
        // gated on a CONFLICT cadence and is only called from the search loop,
        // so nothing consults the limit while preprocessing runs.
        //
        // Consulting `ay_sys::process_memory_exceeded()` uses the operator's
        // ACTUAL configured limit rather than an invented constant, and the
        // exit is `Ok`, never `Err` — `Err` here carries a `Literal` and means
        // "contradiction found", so exiting through it would be reported as
        // UNSAT. A partial closure is sound: every equivalence and unit already
        // in `equivalence_edges` / `uf` was derived by a real congruence merge,
        // and stopping between merges simply discovers fewer of them.
        // Iterations before the memory check engages at all. A healthy
        // congruence closure converges in far fewer than this; only a runaway
        // fixpoint — one generating work faster than it drains — gets here. This
        // is the pass-LOCAL signal the bound needs: keying purely off the
        // process footprint fired on instances whose large clause database was
        // legitimate and congruence was earning its keep, costing 9 solved
        // instances on the official 400 (104 -> 95).
        const CONGRUENCE_RUNAWAY_ITERATIONS: u64 = 200_000;
        // `AY_SAT_CONGRUENCE_MEMORY_BOUND=0` compiles the bound out at runtime,
        // so one binary can carry both arms of a paired A/B. It exists because
        // the bound's price is genuinely unsettled: the full-400 delta against
        // an unbounded build (104 -> 95) sits inside the +/-8 borderline churn
        // measured between comparable runs, and re-shaping the bound recovered
        // only 1 of the 24 affected instances. Separate builds compared across
        // separate runs cannot resolve that; arms inside ONE sweep can.
        let bound_enabled = {
            use std::sync::OnceLock;
            static F: OnceLock<bool> = OnceLock::new();
            *F.get_or_init(|| {
                // DEFAULT OFF, by measurement. Two paired full-400 A/Bs at
                // 300 s (both arms inside ONE sweep, so machine drift cannot
                // masquerade as the effect) put the bound's price at a
                // consistent 3-4 solved instances:
                //
                //   rep 1   bound 94   no-bound  97
                //   rep 2   bound 96   no-bound 100
                //
                // against a between-rep drift of only 2-3, and PAR-2 worse with
                // it in both reps. Meanwhile the bound is INERT on the very
                // instance that motivated it: `post-cbmc-aes-ee-r2`'s 82.75 GB
                // runaway is no longer reproducible, because the XOR emission
                // budget and the preprocessing memory poll now catch it first.
                // So it was paying a real price to defend against a problem that
                // no longer exists.
                //
                // The mechanism is kept, not deleted: if a future change
                // reintroduces an unbounded congruence fixpoint, passing
                // `--sat-congruence-memory-bound` restores the guard without
                // re-deriving it. Re-measure before making it default again.
                ay_core::sat_ab_switches().congruence_memory_bound
            })
        };
        let mut budget_ticks: u64 = 0;
        // `--sat-mem-probe`: attribute a runaway fixpoint to the container that
        // is actually growing. Every accumulator below is unbounded in
        // principle, and the sample profile cannot tell them apart — it only
        // says "inside rewrite_gate_after_merge". Emitted on a coarse power-of-
        // two cadence so a healthy closure prints once and a runaway prints a
        // growth curve.
        let probe_state = ay_core::misc_cli_flags().sat_mem_probe;
        loop {
            // Poll on a coarse cadence; the call reads a cached limit but the
            // footprint query is a syscall on some platforms.
            budget_ticks = budget_ticks.wrapping_add(1);
            if probe_state && budget_ticks.is_multiple_of(1 << 12) {
                let occs_entries: usize = occs.iter().map(Vec::len).sum();
                let input_entries: usize = gate_inputs.iter().map(SmallVec::len).sum();
                let xor_rhs: usize = edge_provenance
                    .iter()
                    .map(|prov| match prov {
                        EdgeProvenance::XorMatch { rhs } => rhs.len(),
                        _ => 0,
                    })
                    .sum();
                eprintln!(
                    "c mem_probe congruence.loop ticks={budget_ticks} table={} schedule={} \
                     units_queued={} occs_entries={occs_entries} gate_input_entries={input_entries} \
                     edges={} xor_rhs={xor_rhs} discovered_units={} footprint={:.1} MB",
                    gate_table.len(),
                    schedule.len(),
                    units_to_propagate.len(),
                    equivalence_edges.len(),
                    discovered_units.len(),
                    ay_sys::current_footprint_bytes() as f64 / 1e6,
                );
            }
            // Engage only at the operator's declared limit — never earlier.
            //
            // This threshold is load-bearing and was calibrated by measurement,
            // not by reasoning about the mechanism, because the mechanism
            // reasoning was wrong twice:
            //
            //   50 % -> cost **24** solved instances on the official 400
            //           (104 -> 80), while driving memory losses to zero.
            //   85 % -> still cost 16 of those 24.
            //
            // Congruence earns its memory on ordinary instances, so ANY
            // fraction below the limit taxes healthy solves to defend against a
            // pathological few. `process_memory_exceeded()` (95 %, the same
            // signal the solver's own interrupt uses) leaves normal instances
            // untouched and does the one job actually needed: stop a runaway
            // from going FAR past the declared limit — the observed case was a
            // 33 MB input reaching 82.75 GB, which can take the machine down.
            if bound_enabled
                && budget_ticks > CONGRUENCE_RUNAWAY_ITERATIONS
                && budget_ticks.is_multiple_of(64)
                && ay_sys::process_memory_exceeded()
            {
                self.stats.memory_abandoned_closures =
                    self.stats.memory_abandoned_closures.saturating_add(1);
                break;
            }
            // Phase A: drain all pending units.
            //
            // The budget check has to live HERE as well as at the outer loop
            // top: this inner drain can run for a very long time without
            // returning, and it is where the growth actually happens, so an
            // outer-loop-only check never fires in time.
            while let Some(unit_lit) = units_to_propagate.pop_front() {
                budget_ticks = budget_ticks.wrapping_add(1);
                if bound_enabled
                    && budget_ticks > CONGRUENCE_RUNAWAY_ITERATIONS
                    && budget_ticks.is_multiple_of(64)
                    && ay_sys::process_memory_exceeded()
                {
                    self.stats.memory_abandoned_closures =
                        self.stats.memory_abandoned_closures.saturating_add(1);
                    units_to_propagate.clear();
                    schedule.clear();
                    break;
                }
                for &polarity in &[unit_lit, unit_lit ^ 1] {
                    if polarity >= num_lits {
                        continue;
                    }
                    let affected = std::mem::take(&mut occs[polarity]);
                    for &gi in &affected {
                        if !gate_alive[gi] {
                            continue;
                        }
                        Self::simplify_gate_with_unit(
                            gi,
                            &gate_types,
                            &mut gate_inputs,
                            &mut gate_outputs,
                            &mut gate_alive,
                            uf,
                            &mut schedule,
                            &mut units_to_propagate,
                            &mut unit_vals,
                            &mut discovered_units,
                            &mut gate_table,
                            &mut occs,
                            num_lits,
                            &mut self.stats,
                            equivalence_edges,
                            edge_provenance,
                            &mut found_equiv,
                            xor_certified_units,
                        )?;
                    }
                }
            }

            // Phase B: process one equivalence from schedule.
            let Some((src, dst, prov)) = schedule.pop_front() else {
                break;
            };
            let src_repr = uf.find(src);
            let dst_repr = uf.find(dst);
            if src_repr == dst_repr {
                continue;
            }

            if !merge_or_contradict(
                uf,
                src_repr,
                dst_repr,
                equivalence_edges,
                prov,
                edge_provenance,
                &mut self.stats,
            )? {
                continue;
            }
            total_merges += 1;

            let new_repr = uf.find(src_repr);
            let loser = if new_repr == src_repr {
                dst_repr
            } else {
                src_repr
            };

            for &polarity in &[loser, loser ^ 1] {
                if polarity >= num_lits {
                    continue;
                }
                let winner = uf.find(polarity);
                let affected = std::mem::take(&mut occs[polarity]);
                for &gi in &affected {
                    if !gate_alive[gi] {
                        continue;
                    }

                    Self::rewrite_gate_after_merge(
                        gi,
                        &mut gate_types,
                        &mut gate_inputs,
                        &mut gate_outputs,
                        &mut gate_alive,
                        uf,
                        &mut schedule,
                        &mut units_to_propagate,
                        &mut unit_vals,
                        &mut discovered_units,
                        &mut gate_table,
                        &mut occs,
                        num_lits,
                        &mut self.stats,
                        equivalence_edges,
                        edge_provenance,
                        &mut found_equiv,
                        xor_certified_units,
                    )?;

                    if gate_alive[gi] {
                        push_occurrence(&mut occs, winner, gi);
                    }
                }
            }
        }

        if ay_core::misc_cli_flags().sat_mem_probe {
            // The quantity the leak grew: entries live in the gate table when
            // the fixpoint ends, against the gate count it started from.
            eprintln!(
                "c mem_probe congruence gates={gate_count} table_entries={} merges={total_merges} \
                 footprint={:.1} MB",
                gate_table.len(),
                ay_sys::current_footprint_bytes() as f64 / 1e6,
            );
        }
        if debug_congruence_enabled() {
            let cascade = total_merges.saturating_sub(initial_merges);
            let alive = gate_alive.iter().filter(|&&a| a).count();
            let n_units = discovered_units.len();
            eprintln!(
                "[congruence] eager: initial={initial_merges}, cascade={cascade}, total={total_merges}, alive_gates={alive}/{gate_count}, units_discovered={n_units}"
            );
        }

        Ok((found_equiv, discovered_units))
    }

    /// Record a unit discovered during congruence gate simplification.
    ///
    /// Returns `Ok(true)` when the literal was newly recorded (so callers in the
    /// XOR-collapse paths can mark it parity-certified), `Ok(false)` when it was
    /// already known, or `Err(unit)` on a direct contradiction.
    fn record_unit(
        lit_idx: usize,
        unit_vals: &mut [i8],
        units_to_propagate: &mut VecDeque<usize>,
        discovered_units: &mut Vec<Literal>,
        num_lits: usize,
    ) -> Result<bool, Literal> {
        if crate::congruence::dump_merges_enabled() {
            eprintln!("DUMP_UNIT: {lit_idx}");
        }
        if lit_idx >= num_lits {
            return Ok(false);
        }
        let neg = lit_idx ^ 1;
        if unit_vals[lit_idx] < 0 {
            return Err(Literal::from_index(lit_idx));
        }
        if unit_vals[lit_idx] > 0 {
            return Ok(false);
        }
        unit_vals[lit_idx] = 1;
        if neg < num_lits {
            unit_vals[neg] = -1;
        }
        units_to_propagate.push_back(lit_idx);
        discovered_units.push(Literal::from_index(lit_idx));
        Ok(true)
    }

    /// Remove a gate's current signature from the gate table.
    fn remove_gate_signature(
        gi: usize,
        gate_types: &[GateType],
        gate_inputs: &[SmallVec<[usize; 5]>],
        gate_table: &mut GateTable,
        uf: &mut UnionFind,
    ) {
        gate_table.remove_gate(gi, || {
            Self::canonicalize(&gate_types[gi], &gate_inputs[gi], uf)
        });
    }

    /// Reinsert a (possibly simplified) gate into the gate table.
    #[allow(clippy::too_many_arguments)]
    fn reinsert_gate(
        gi: usize,
        gate_types: &[GateType],
        gate_inputs: &[SmallVec<[usize; 5]>],
        gate_outputs: &[usize],
        gate_alive: &mut [bool],
        uf: &mut UnionFind,
        schedule: &mut VecDeque<(usize, usize, EdgeProvenance)>,
        gate_table: &mut GateTable,
        occs: &mut [Vec<usize>],
        num_lits: usize,
        found_equiv: &mut bool,
    ) {
        let new_sig = Self::canonicalize(&gate_types[gi], &gate_inputs[gi], uf);
        if let Some(existing_gi) = gate_table.get(&new_sig) {
            let out_a = uf.find(gate_outputs[existing_gi]);
            let out_b = uf.find(gate_outputs[gi]);
            if out_a != out_b {
                if crate::congruence::dump_merges_enabled() {
                    eprintln!("DUMP_SCHED[gate_rewriting.rs:580]: {out_b} {out_a}");
                }
                let prov = if gate_types[gi] == GateType::Xor {
                    EdgeProvenance::XorMatch {
                        rhs: new_sig.inputs.to_vec(),
                    }
                } else if gate_types[gi] == GateType::Ite {
                    EdgeProvenance::IteMatch {
                        cond: new_sig.inputs[0],
                    }
                } else {
                    EdgeProvenance::Plain
                };
                schedule.push_back((out_b, out_a, prov));
                *found_equiv = true;
            }
            gate_alive[gi] = false;
        } else {
            gate_table.insert(new_sig, gi);
            for &inp in &gate_inputs[gi] {
                if inp < num_lits {
                    push_occurrence(occs, inp, gi);
                }
            }
        }
    }

    /// Speculative morph check for ITE→AND/XOR transformations.
    fn morph_would_find_match(
        target_type: &GateType,
        inputs: &[usize],
        uf: &mut UnionFind,
        gate_table: &GateTable,
    ) -> bool {
        let sig = Self::canonicalize(target_type, inputs, uf);
        gate_table.contains_key(&sig)
    }

    /// Canonicalize gate inputs: map through UF and sort for commutative gates.
    fn canonicalize(gate_type: &GateType, inputs: &[usize], uf: &mut UnionFind) -> GateSignature {
        let mut canonical: SmallVec<[usize; INLINE_GATE_INPUTS]> =
            inputs.iter().map(|&idx| uf.find(idx)).collect();
        match gate_type {
            GateType::Ite => {
                debug_assert_eq!(
                    canonical.len(),
                    3,
                    "BUG: ITE gates must have exactly 3 canonicalized inputs"
                );
            }
            GateType::And | GateType::Xor | GateType::Equiv => {
                canonical.sort_unstable();
                debug_assert!(
                    canonical.windows(2).all(|pair| pair[0] <= pair[1]),
                    "BUG: commutative gate canonical inputs must be sorted"
                );
            }
        }
        GateSignature {
            gate_type: *gate_type,
            inputs: canonical,
        }
    }
}
