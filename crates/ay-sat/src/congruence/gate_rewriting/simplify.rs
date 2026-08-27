// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit-literal simplification for congruence gates.
//!
//! After a unit literal is discovered, each gate containing that literal
//! is simplified: assigned inputs are removed, and forced outputs are
//! detected (unit propagation or equivalence collapse).
//!
//! Reference: CaDiCaL congruence.cpp:2744-2825 (simplify_and_gate).

use crate::gates::GateType;
use crate::literal::Literal;
use smallvec::SmallVec;
use std::collections::VecDeque;

use super::super::union_find::{merge_or_contradict, UnionFind};
use super::super::CongruenceStats;
use super::GateTable;

use super::super::CongruenceClosure;

impl CongruenceClosure {
    /// Simplify a gate after a unit literal is discovered.
    ///
    /// CaDiCaL congruence.cpp:2744-2825 (simplify_and_gate) and similar
    /// for XOR/ITE. Removes assigned inputs, detects forced outputs.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::congruence) fn simplify_gate_with_unit(
        gi: usize,
        gate_types: &[GateType],
        gate_inputs: &mut [SmallVec<[usize; 5]>],
        gate_outputs: &mut [usize],
        gate_alive: &mut [bool],
        uf: &mut UnionFind,
        schedule: &mut VecDeque<(usize, usize, crate::congruence::EdgeProvenance)>,
        units_to_propagate: &mut VecDeque<usize>,
        unit_vals: &mut [i8],
        discovered_units: &mut Vec<Literal>,
        gate_table: &mut GateTable,
        occs: &mut [Vec<usize>],
        num_lits: usize,
        stats: &mut CongruenceStats,
        equivalence_edges: &mut Vec<(Literal, Literal)>,
        edge_provenance: &mut Vec<crate::congruence::EdgeProvenance>,
        found_equiv: &mut bool,
        xor_certified_units: &mut Vec<Literal>,
    ) -> Result<(), Literal> {
        if !gate_alive[gi] {
            return Ok(());
        }

        Self::remove_gate_signature(gi, gate_types, gate_inputs, gate_table, uf);

        let out = uf.find(gate_outputs[gi]);

        match gate_types[gi] {
            GateType::And => {
                // Remove assigned inputs. CaDiCaL simplify_and_gate.
                let mut has_false = false;
                let mut has_neg_output = false;
                gate_inputs[gi].retain(|inp| {
                    let inp = *inp;
                    let repr = uf.find(inp);
                    let v = if repr < unit_vals.len() {
                        unit_vals[repr]
                    } else {
                        0
                    };
                    if v > 0 {
                        return false; // true: AND identity
                    }
                    if v < 0 {
                        has_false = true;
                        return false;
                    }
                    // ¬output in inputs → output forced false.
                    if repr == (out ^ 1) {
                        has_neg_output = true;
                    }
                    true
                });

                if has_false || has_neg_output {
                    gate_alive[gi] = false;
                    // Output forced false → unit ¬output.
                    Self::record_unit(
                        out ^ 1,
                        unit_vals,
                        units_to_propagate,
                        discovered_units,
                        num_lits,
                    )?;
                    return Ok(());
                }

                // Dedup and detect complementary pairs.
                gate_inputs[gi].sort_unstable();
                gate_inputs[gi].dedup();
                let has_complement = gate_inputs[gi]
                    .windows(2)
                    .any(|pair| uf.find(pair[0]) == (uf.find(pair[1]) ^ 1));
                if has_complement {
                    gate_alive[gi] = false;
                    Self::record_unit(
                        out ^ 1,
                        unit_vals,
                        units_to_propagate,
                        discovered_units,
                        num_lits,
                    )?;
                    return Ok(());
                }

                match gate_inputs[gi].len() {
                    0 => {
                        // AND() with all true → output true.
                        gate_alive[gi] = false;
                        Self::record_unit(
                            out,
                            unit_vals,
                            units_to_propagate,
                            discovered_units,
                            num_lits,
                        )?;
                    }
                    1 => {
                        // AND(x) → output ≡ x.
                        let inp = uf.find(gate_inputs[gi][0]);
                        gate_alive[gi] = false;
                        if inp != out {
                            merge_or_contradict(
                                uf,
                                out,
                                inp,
                                equivalence_edges,
                                crate::congruence::EdgeProvenance::Plain,
                                edge_provenance,
                                stats,
                            )?;
                            if crate::congruence::dump_merges_enabled() {
                                eprintln!("DUMP_SCHED[simplify.rs:134]: {out} {inp}");
                            }
                            schedule.push_back((
                                out,
                                inp,
                                crate::congruence::EdgeProvenance::Plain,
                            ));
                            *found_equiv = true;
                        }
                    }
                    _ => {
                        // Re-hash with reduced arity.
                        Self::reinsert_gate(
                            gi,
                            gate_types,
                            gate_inputs,
                            gate_outputs,
                            gate_alive,
                            uf,
                            schedule,
                            gate_table,
                            occs,
                            num_lits,
                            found_equiv,
                        );
                    }
                }
            }
            GateType::Xor => {
                // CaDiCaL-style: inputs are positive-normalized, output sign
                // carries XOR/XNOR polarity. parity_flip starts false because
                // output literal already encodes XOR vs XNOR (#7137).
                // CaDiCaL: negate = 0 (congruence.cpp:4769).
                let mut parity_flip = false;
                gate_inputs[gi].retain(|inp| {
                    let inp = *inp;
                    let repr = uf.find(inp);
                    let v = if repr < unit_vals.len() {
                        unit_vals[repr]
                    } else {
                        0
                    };
                    if v > 0 {
                        // True input `x ⊕ true = ¬x`: one GF(2) flip, folded
                        // through the shared, trust-checked parity step.
                        parity_flip =
                            ay_sat_congruence_core::xor_accumulate_parity(parity_flip, true);
                        return false;
                    }
                    if v < 0 {
                        // false input: XOR with false = identity → no flip.
                        return false;
                    }
                    true
                });
                Self::reduce_xor_input_pairs(&mut gate_inputs[gi], uf, &mut parity_flip);

                match gate_inputs[gi].len() {
                    0 => {
                        // All inputs removed. out_lit = constant.
                        // No flip: out_lit = false → record ¬out.
                        // Flip: out_lit = true → record out.
                        gate_alive[gi] = false;
                        let unit_lit = if parity_flip { out } else { out ^ 1 };
                        // Parity-certified XOR collapse (machine-checked-exact
                        // polarity, ay-sat-verified). #7137-relax.
                        if Self::record_unit(
                            unit_lit,
                            unit_vals,
                            units_to_propagate,
                            discovered_units,
                            num_lits,
                        )? {
                            xor_certified_units.push(Literal::from_index(unit_lit));
                        }
                    }
                    1 => {
                        let inp = uf.find(gate_inputs[gi][0]);
                        // out_lit = XOR(inp) with parity.
                        // No flip: out ≡ inp. Flip: out ≡ ¬inp.
                        let target = if parity_flip { inp ^ 1 } else { inp };
                        gate_alive[gi] = false;
                        if out != target {
                            merge_or_contradict(
                                uf,
                                out,
                                target,
                                equivalence_edges,
                                crate::congruence::EdgeProvenance::Plain,
                                edge_provenance,
                                stats,
                            )?;
                            if crate::congruence::dump_merges_enabled() {
                                eprintln!("DUMP_SCHED[simplify.rs:212]: {out} {target}");
                            }
                            schedule.push_back((
                                out,
                                target,
                                crate::congruence::EdgeProvenance::Plain,
                            ));
                            *found_equiv = true;
                        }
                    }
                    _ => {
                        // Apply accumulated parity to output before reinsertion.
                        // CaDiCaL: lhs sign flip (congruence.cpp:4784). (#7137)
                        if parity_flip {
                            gate_outputs[gi] ^= 1;
                        }
                        Self::reinsert_gate(
                            gi,
                            gate_types,
                            gate_inputs,
                            gate_outputs,
                            gate_alive,
                            uf,
                            schedule,
                            gate_table,
                            occs,
                            num_lits,
                            found_equiv,
                        );
                    }
                }
            }
            GateType::Ite => {
                if gate_inputs[gi].len() == 3 {
                    let cond = uf.find(gate_inputs[gi][0]);
                    let cv = if cond < unit_vals.len() {
                        unit_vals[cond]
                    } else {
                        0
                    };
                    if cv != 0 {
                        let target_idx = if cv > 0 { 1 } else { 2 };
                        let target = uf.find(gate_inputs[gi][target_idx]);
                        gate_alive[gi] = false;
                        if out != target {
                            merge_or_contradict(
                                uf,
                                out,
                                target,
                                equivalence_edges,
                                crate::congruence::EdgeProvenance::Plain,
                                edge_provenance,
                                stats,
                            )?;
                            if crate::congruence::dump_merges_enabled() {
                                eprintln!("DUMP_SCHED[simplify.rs:252]: {out} {target}");
                            }
                            schedule.push_back((
                                out,
                                target,
                                crate::congruence::EdgeProvenance::Plain,
                            ));
                            *found_equiv = true;
                        }
                    } else {
                        // Condition not assigned, keep gate.
                        Self::reinsert_gate(
                            gi,
                            gate_types,
                            gate_inputs,
                            gate_outputs,
                            gate_alive,
                            uf,
                            schedule,
                            gate_table,
                            occs,
                            num_lits,
                            found_equiv,
                        );
                    }
                }
            }
            GateType::Equiv => {
                // Equiv is handled like XOR with 1 input.
                if gate_inputs[gi].len() == 1 {
                    let inp = gate_inputs[gi][0];
                    let v = if inp < unit_vals.len() {
                        unit_vals[inp]
                    } else {
                        0
                    };
                    if v != 0 {
                        let unit_lit = if v > 0 { out } else { out ^ 1 };
                        gate_alive[gi] = false;
                        Self::record_unit(
                            unit_lit,
                            unit_vals,
                            units_to_propagate,
                            discovered_units,
                            num_lits,
                        )?;
                    } else {
                        Self::reinsert_gate(
                            gi,
                            gate_types,
                            gate_inputs,
                            gate_outputs,
                            gate_alive,
                            uf,
                            schedule,
                            gate_table,
                            occs,
                            num_lits,
                            found_equiv,
                        );
                    }
                }
            }
        }
        Ok(())
    }
}
