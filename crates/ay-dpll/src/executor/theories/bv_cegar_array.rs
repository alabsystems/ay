// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CEGAR-style array functional consistency refinement for QF_ABV (#8510).
//!
//! After the SAT solver finds a satisfying assignment for the bit-blasted
//! formula, this module checks whether the assignment respects array
//! functional consistency (FC): if two select terms on the same array
//! have equal concrete index values, their result values must also be equal.
//!
//! When FC violations are found, the corresponding FC axiom clauses are
//! generated and returned for injection into the SAT solver. The caller
//! re-solves until no violations remain or a max iteration count is reached.
//!
//! This is necessary because the upfront FC axiom budget
//! (`FC_CROSS_BASE_BUDGET_PER_ARRAY = 200`) can be insufficient for
//! formulas with many constant-indexed selects and few symbolic-indexed
//! selects. The CEGAR loop adds only the FC axioms that are actually
//! needed, keeping the clause count manageable.
//!
//! Strategy: when a select term is found in an FC violation, generate FC
//! axioms between that select and ALL other selects on the same array.
//! This prevents the SAT solver from simply shifting the symbolic index
//! to a different value that wasn't covered. One batch of axioms per
//! violating select covers all possible aliasing scenarios.

// #8529: Use deterministic hash maps in all builds.
use ay_bv::BvBits;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::TermId;
use ay_sat::Literal as SatLiteral;
use num_bigint::BigInt;

use super::super::Executor;
use super::bv_encoding;

/// Result of CEGAR array FC check: new clauses to add to the SAT solver.
pub(in crate::executor) struct CegarArrayResult {
    /// SAT-level clauses encoding violated FC axioms.
    pub(in crate::executor) clauses: Vec<Vec<SatLiteral>>,
    /// Number of new variables allocated for diff/eq encoding.
    pub(in crate::executor) num_new_vars: usize,
}

impl Executor {
    /// Check array functional consistency against a concrete SAT model.
    ///
    /// For each pair of select terms on the same root array where the
    /// concrete index values are equal but the concrete result values
    /// differ, identify the "violating" select terms and generate FC
    /// axiom clauses between each violating select and ALL other selects
    /// on the same array.
    ///
    /// Returns `None` if no violations found (model is FC-consistent).
    /// Returns `Some(result)` with the FC axiom clauses if violations found.
    ///
    /// `already_covered` tracks pairs that have had FC axioms generated
    /// in previous CEGAR iterations to avoid duplicate work.
    pub(in crate::executor) fn check_array_fc_violations(
        &self,
        sat_model: &[bool],
        term_bits: &HashMap<TermId, BvBits>,
        var_offset: i32,
        next_var_offset: usize,
        already_covered: &mut HashSet<(TermId, TermId)>,
    ) -> Option<CegarArrayResult> {
        // Collect select terms from assertions.
        let mut select_terms: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut store_terms: Vec<(TermId, TermId, TermId, TermId)> = Vec::new();
        let mut visited = HashSet::default();

        for &assertion in &self.ctx.assertions {
            self.collect_array_terms(assertion, &mut select_terms, &mut store_terms, &mut visited);
        }

        // Assertion traversal misses select terms that were materialized by the
        // bit-blaster or array axiom generator. Those terms still have concrete
        // SAT bits and must obey FC. If they conflict with assertion selects,
        // model extraction can only fail closed after SAT, instead of giving
        // CEGAR a chance to add the missing pair.
        let mut seen_select_terms: HashSet<TermId> =
            select_terms.iter().map(|(select, _, _)| *select).collect();
        for &term_id in term_bits.keys() {
            if !seen_select_terms.insert(term_id) {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(term_id) {
                if sym.name() == "select"
                    && args.len() == 2
                    && matches!(self.ctx.terms.get(args[0]), TermData::Var(_, _))
                {
                    select_terms.push((term_id, args[0], args[1]));
                }
            }
        }

        if select_terms.is_empty() {
            return None;
        }

        // Group selects by their DIRECT array operand, not root.
        //
        // FC (functional consistency) requires: if two selects are on the
        // SAME array and have equal indices, their values must be equal.
        // Selects on DIFFERENT arrays (even if they share a root through
        // store chains) can legitimately have different values at the same
        // index because stores modify the array.
        //
        // Example: select(a, 5) vs select(store(a, 5, v), 5)
        // These share root `a` but are on different arrays. The first
        // returns the original value, the second returns `v`. FC does
        // NOT require them to be equal.
        //
        // After expand_select_store, most selects are on base arrays,
        // but when the symbolic ITE budget is exhausted, selects on
        // intermediate store terms remain. Grouping by root would
        // incorrectly flag these as FC violations and add unsound axioms.
        let mut selects_by_array: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default();
        for &(select_term, array, index) in &select_terms {
            selects_by_array
                .entry(array)
                .or_default()
                .push((select_term, index));
        }

        let mut all_new_clauses: Vec<Vec<SatLiteral>> = Vec::new();
        let mut next_var = next_var_offset as u32 + 1; // 1-based DIMACS

        for (_array_root, selects) in &selects_by_array {
            if selects.len() < 2 {
                continue;
            }

            // Compute concrete index values for each select.
            let mut concrete_selects: Vec<(usize, BigInt, BigInt)> = Vec::new();

            for (i, &(select_term, index_term)) in selects.iter().enumerate() {
                let Some(idx_bits) = term_bits.get(&index_term) else {
                    continue;
                };
                let Some(sel_bits) = term_bits.get(&select_term) else {
                    continue;
                };

                let idx_val = self.concrete_bv_value(sat_model, idx_bits, var_offset);
                let sel_val = self.concrete_bv_value(sat_model, sel_bits, var_offset);

                concrete_selects.push((i, idx_val, sel_val));
            }

            // Group by concrete index value, find violations.
            let mut by_index: HashMap<BigInt, Vec<(usize, BigInt)>> = HashMap::default();
            for (i, idx_val, sel_val) in &concrete_selects {
                by_index
                    .entry(idx_val.clone())
                    .or_default()
                    .push((*i, sel_val.clone()));
            }

            for group in by_index.values() {
                if group.len() < 2 {
                    continue;
                }
                let first_val = &group[0].1;
                let has_violation = group.iter().skip(1).any(|e| e.1 != *first_val);
                if !has_violation {
                    continue;
                }

                // Add the concrete violated FC pairs first. Earlier versions
                // expanded each violating select against every other select on
                // the same array, which is too broad once generated/select
                // materialization terms are included in this scan.
                for a in 0..group.len() {
                    for b in (a + 1)..group.len() {
                        let (select_a_idx, value_a) = &group[a];
                        let (select_b_idx, value_b) = &group[b];
                        if value_a == value_b {
                            continue;
                        }
                        let (sel_a_term, idx_a_term) = selects[*select_a_idx];
                        let (sel_b_term, idx_b_term) = selects[*select_b_idx];
                        if sel_a_term == sel_b_term {
                            continue;
                        }
                        let pair_key = if sel_a_term < sel_b_term {
                            (sel_a_term, sel_b_term)
                        } else {
                            (sel_b_term, sel_a_term)
                        };
                        if already_covered.contains(&pair_key) {
                            continue;
                        }
                        already_covered.insert(pair_key);

                        let new_clauses = self.generate_fc_axiom_clauses(
                            term_bits,
                            var_offset,
                            idx_a_term,
                            idx_b_term,
                            sel_a_term,
                            sel_b_term,
                            &mut next_var,
                        );
                        all_new_clauses.extend(new_clauses);
                    }
                }
            }
        }

        if all_new_clauses.is_empty() {
            return None;
        }

        let num_new_vars = (next_var as usize).saturating_sub(next_var_offset + 1);
        Some(CegarArrayResult {
            clauses: all_new_clauses,
            num_new_vars,
        })
    }

    /// Compute the concrete BV value of a term given its SAT-level bit assignments.
    fn concrete_bv_value(&self, sat_model: &[bool], bits: &BvBits, var_offset: i32) -> BigInt {
        let mut value = BigInt::from(0u64);
        for (i, &bit_lit) in bits.iter().enumerate() {
            let offset_lit = bv_encoding::offset_cnf_lit(bit_lit, var_offset);
            let sat_var_idx = if offset_lit > 0 {
                (offset_lit - 1) as usize
            } else {
                (-offset_lit - 1) as usize
            };
            let bit_value = if sat_var_idx < sat_model.len() {
                let sat_val = sat_model[sat_var_idx];
                if offset_lit > 0 {
                    sat_val
                } else {
                    !sat_val
                }
            } else {
                false
            };
            if bit_value {
                value |= BigInt::from(1) << i;
            }
        }
        value
    }

    /// Generate FC axiom clauses for a single pair of selects.
    ///
    /// Encodes: `(idx_a == idx_b) -> (sel_a == sel_b)`
    /// as bit-level diff-XOR encoding, producing SAT-level literals.
    fn generate_fc_axiom_clauses(
        &self,
        term_bits: &HashMap<TermId, BvBits>,
        var_offset: i32,
        idx_a: TermId,
        idx_b: TermId,
        sel_a: TermId,
        sel_b: TermId,
        next_var: &mut u32,
    ) -> Vec<Vec<SatLiteral>> {
        let mut clauses: Vec<Vec<SatLiteral>> = Vec::new();

        let Some(idx_a_bits) = term_bits.get(&idx_a) else {
            return clauses;
        };
        let Some(idx_b_bits) = term_bits.get(&idx_b) else {
            return clauses;
        };
        let Some(sel_a_bits) = term_bits.get(&sel_a) else {
            return clauses;
        };
        let Some(sel_b_bits) = term_bits.get(&sel_b) else {
            return clauses;
        };

        if idx_a_bits.len() != idx_b_bits.len() || idx_a_bits.is_empty() {
            return clauses;
        }
        if sel_a_bits.len() != sel_b_bits.len() || sel_a_bits.is_empty() {
            return clauses;
        }

        let offset_bit = |bit: i32| -> i32 { bv_encoding::offset_cnf_lit(bit, var_offset) };

        let to_sat = |cnf_lit: i32| -> SatLiteral { crate::cnf_lit_to_sat(cnf_lit) };

        // Create diff variables for index bits: diff_k <-> (idx_a_k XOR idx_b_k)
        let mut diff_vars: Vec<i32> = Vec::with_capacity(idx_a_bits.len());
        for (&b1, &b2) in idx_a_bits.iter().zip(idx_b_bits.iter()) {
            // If both bits are the same literal, they're identical - skip
            if b1 == b2 {
                continue;
            }

            let ob1 = offset_bit(b1);
            let ob2 = offset_bit(b2);
            let diff_var = *next_var as i32;
            *next_var += 1;
            diff_vars.push(diff_var);

            // diff_var <-> (ob1 XOR ob2)
            clauses.push(vec![to_sat(-diff_var), to_sat(ob1), to_sat(ob2)]);
            clauses.push(vec![to_sat(-diff_var), to_sat(-ob1), to_sat(-ob2)]);
            clauses.push(vec![to_sat(-ob1), to_sat(ob2), to_sat(diff_var)]);
            clauses.push(vec![to_sat(ob1), to_sat(-ob2), to_sat(diff_var)]);
        }

        if diff_vars.is_empty() {
            // Indices are syntactically identical - FC requires values equal.
            for (&s1, &s2) in sel_a_bits.iter().zip(sel_b_bits.iter()) {
                if s1 == s2 {
                    continue;
                }
                let os1 = offset_bit(s1);
                let os2 = offset_bit(s2);
                clauses.push(vec![to_sat(-os1), to_sat(os2)]);
                clauses.push(vec![to_sat(os1), to_sat(-os2)]);
            }
            return clauses;
        }

        // eq_idx <-> NOT(OR(diff_vars))
        let eq_idx = *next_var as i32;
        *next_var += 1;

        // eq_idx -> NOT diff_k
        for &diff_var in &diff_vars {
            clauses.push(vec![to_sat(-eq_idx), to_sat(-diff_var)]);
        }

        // (diff_0 OR ... OR diff_n OR eq_idx)
        let mut eq_def: Vec<SatLiteral> = diff_vars.iter().map(|&d| to_sat(d)).collect();
        eq_def.push(to_sat(eq_idx));
        clauses.push(eq_def);

        // FC: eq_idx -> (sel_a_k == sel_b_k)
        for (&s1, &s2) in sel_a_bits.iter().zip(sel_b_bits.iter()) {
            if s1 == s2 {
                continue;
            }
            let os1 = offset_bit(s1);
            let os2 = offset_bit(s2);
            clauses.push(vec![to_sat(-eq_idx), to_sat(-os1), to_sat(os2)]);
            clauses.push(vec![to_sat(-eq_idx), to_sat(os1), to_sat(-os2)]);
        }

        clauses
    }
}
