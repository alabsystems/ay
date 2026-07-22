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

        // Gate table: signature -> first gate index with that signature
        let mut gate_table: HashMap<GateSignature, usize> = HashMap::with_capacity(gate_count);

        for gi in 0..gate_count {
            if !gate_alive[gi] {
                continue;
            }
            let sig = Self::canonicalize(&gate_types[gi], &gate_inputs[gi], uf);
            if let Some(&existing_gi) = gate_table.get(&sig) {
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
        loop {
            // Phase A: drain all pending units.
            while let Some(unit_lit) = units_to_propagate.pop_front() {
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
                        occs[winner].push(gi);
                    }
                }
            }
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
        gate_table: &mut HashMap<GateSignature, usize>,
        uf: &mut UnionFind,
    ) {
        let sig = Self::canonicalize(&gate_types[gi], &gate_inputs[gi], uf);
        if gate_table.get(&sig) == Some(&gi) {
            gate_table.remove(&sig);
        }
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
        gate_table: &mut HashMap<GateSignature, usize>,
        occs: &mut [Vec<usize>],
        num_lits: usize,
        found_equiv: &mut bool,
    ) {
        let new_sig = Self::canonicalize(&gate_types[gi], &gate_inputs[gi], uf);
        if let Some(&existing_gi) = gate_table.get(&new_sig) {
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
                    occs[inp].push(gi);
                }
            }
        }
    }

    /// Speculative morph check for ITE→AND/XOR transformations.
    fn morph_would_find_match(
        target_type: &GateType,
        inputs: &[usize],
        uf: &mut UnionFind,
        gate_table: &HashMap<GateSignature, usize>,
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
