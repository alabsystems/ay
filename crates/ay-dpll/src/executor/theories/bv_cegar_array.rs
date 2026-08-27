// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CEGAR-style array functional consistency refinement for QF_ABV (#8510).
//!
//! Audits bit-blasted SAT assignments for functional consistency (FC): selects
//! on the same array and concrete index must have equal result values.
//! When FC violations are found, the corresponding FC axiom clauses are
//! generated and returned for injection into the SAT solver. The caller
//! re-solves until no violations remain or a max iteration count is reached.
//!
//! Refinement covers only direct-array, equal-index, unequal-value pairs. Hard
//! traversal, bit, pair, variable, and clause budgets fail closed to `unknown`.

// #8529: Use deterministic hash maps in all builds.
use ay_bv::BvBits;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId};
use ay_sat::Literal as SatLiteral;
use num_bigint::BigInt;

use super::super::Executor;
use super::bv_encoding;

#[path = "bv_cegar_array_budget.rs"]
mod budget;
#[path = "bv_cegar_array_refine.rs"]
mod refine;

/// Result of CEGAR array FC check: new clauses to add to the SAT solver.
pub(in crate::executor) struct CegarArrayResult {
    /// SAT-level clauses encoding violated FC axioms.
    pub(in crate::executor) clauses: Vec<Vec<SatLiteral>>,
    /// Number of new variables allocated for diff/eq encoding.
    pub(in crate::executor) num_new_vars: usize,
}

/// A complete FC audit, a refinement batch, or a fail-closed incomplete audit.
pub(in crate::executor) enum CegarArrayCheck {
    Consistent,
    Refinement(CegarArrayResult),
    Incomplete,
}

struct CegarArrayBuild {
    clauses: Vec<Vec<SatLiteral>>,
    next_var: u32,
    new_vars: usize,
    inspected_bits: usize,
    pair_attempts: usize,
    newly_covered: HashSet<(TermId, TermId)>,
}

mod fc_check;

impl Executor {
    fn append_fc_group_refinement(
        &mut self,
        group: &[(TermId, TermId, BigInt)],
        term_bits: &HashMap<TermId, BvBits>,
        var_offset: i32,
        already_covered: &HashSet<(TermId, TermId)>,
        build: &mut CegarArrayBuild,
    ) -> bool {
        for a in 0..group.len() {
            for b in (a + 1)..group.len() {
                build.pair_attempts = build.pair_attempts.saturating_add(1);
                if build.pair_attempts > budget::MAX_PAIR_ATTEMPTS
                    || (build.pair_attempts & 0xff == 0 && self.should_abort_theory_loop())
                {
                    return false;
                }
                let (sel_a, idx_a, value_a) = &group[a];
                let (sel_b, idx_b, value_b) = &group[b];
                if value_a == value_b || sel_a == sel_b {
                    continue;
                }
                let pair = if sel_a < sel_b {
                    (*sel_a, *sel_b)
                } else {
                    (*sel_b, *sel_a)
                };
                if already_covered.contains(&pair) {
                    return false;
                }
                if !build.newly_covered.insert(pair) {
                    continue;
                }
                let Some((pair_vars, pair_clauses)) =
                    self.fc_pair_cost_for_terms(term_bits, *idx_a, *idx_b, *sel_a, *sel_b)
                else {
                    return false;
                };
                let Some(next_vars) = build.new_vars.checked_add(pair_vars) else {
                    return false;
                };
                let Some(next_clauses) = build.clauses.len().checked_add(pair_clauses) else {
                    return false;
                };
                let last_var =
                    (build.next_var as usize).saturating_add(pair_vars.saturating_sub(1));
                if pair_clauses == 0
                    || next_vars > budget::MAX_NEW_VARS
                    || next_clauses > budget::MAX_NEW_CLAUSES
                    || (pair_vars > 0 && last_var > i32::MAX as usize)
                {
                    return false;
                }
                let clauses = self.generate_fc_axiom_clauses(
                    term_bits,
                    var_offset,
                    *idx_a,
                    *idx_b,
                    *sel_a,
                    *sel_b,
                    &mut build.next_var,
                );
                if clauses.len() != pair_clauses {
                    return false;
                }
                build.new_vars = next_vars;
                build.clauses.extend(clauses);
            }
        }
        true
    }

    /// Does the bit-blaster OWE this term an entry in `term_bits`?
    ///
    /// True exactly for the sorts it can represent as a bit string: `BitVec`,
    /// `Bool` (a single literal) and `FloatingPoint` (its IEEE encoding). For
    /// those, a missing entry means the audit cannot read a value it should
    /// have been able to read — an incomplete audit, which fails closed.
    ///
    /// Every other sort — an uninterpreted sort, a datatype, `Int`/`Real`,
    /// `Seq`, `String`, `RegLan`, a nested `Array` — has no bit encoding in
    /// this blaster at all, so a `(select A i)` at that sort is not something
    /// the BIT-LEVEL FC audit failed to check; it is something the audit does
    /// not speak about. Its congruence obligation lives in the
    /// model-validation layer (`#array-select-congruence-gate`) instead.
    fn fc_audit_owes_bits(&self, term: TermId) -> bool {
        matches!(
            self.ctx.terms.sort(term),
            Sort::BitVec(_) | Sort::Bool | Sort::FloatingPoint(_, _)
        )
    }

    fn collect_fc_select_terms(
        &mut self,
        term_bits: &HashMap<TermId, BvBits>,
    ) -> Option<Vec<(TermId, TermId, TermId)>> {
        if self.ctx.assertions.len() > budget::MAX_TERMS || term_bits.len() > budget::MAX_TERM_BITS
        {
            return None;
        }
        let mut pending = self.ctx.assertions.clone();
        let mut visited = HashSet::default();
        let mut selects = Vec::new();
        let mut seen_selects = HashSet::default();
        while let Some(term) = pending.pop() {
            if !visited.insert(term) {
                continue;
            }
            if visited.len() > budget::MAX_TERMS
                || (visited.len() & 0xff == 0 && self.should_abort_theory_loop())
            {
                return None;
            }
            match self.ctx.terms.get(term) {
                TermData::App(sym, args) => {
                    if pending.len().saturating_add(args.len()) > budget::MAX_TERMS {
                        return None;
                    }
                    if sym.name() == "select" && args.len() == 2 && seen_selects.insert(term) {
                        if selects.len() >= budget::MAX_SELECTS {
                            return None;
                        }
                        selects.push((term, args[0], args[1]));
                    }
                    pending.extend(args.iter().copied());
                }
                TermData::Not(inner) => pending.push(*inner),
                TermData::Ite(cond, then_term, else_term) => {
                    if pending.len() > budget::MAX_TERMS.saturating_sub(3) {
                        return None;
                    }
                    pending.extend([*cond, *then_term, *else_term]);
                }
                _ => {}
            }
        }

        // Include base-array selects materialized by bit-blasting/axiomatization.
        for (position, &term) in term_bits.keys().enumerate() {
            if position & 0xff == 0 && self.should_abort_theory_loop() {
                return None;
            }
            if seen_selects.contains(&term) {
                continue;
            }
            let generated = match self.ctx.terms.get(term) {
                TermData::App(sym, args)
                    if sym.name() == "select"
                        && args.len() == 2
                        && matches!(self.ctx.terms.get(args[0]), TermData::Var(_, _)) =>
                {
                    Some((term, args[0], args[1]))
                }
                _ => None,
            };
            if let Some(select) = generated {
                if selects.len() >= budget::MAX_SELECTS {
                    return None;
                }
                seen_selects.insert(term);
                selects.push(select);
            }
        }
        Some(selects)
    }

    fn concrete_bv_value_bounded(
        &mut self,
        sat_model: &[bool],
        bits: &BvBits,
        var_offset: i32,
        inspected_bits: &mut usize,
    ) -> Option<BigInt> {
        if bits.len() > budget::MAX_SINGLE_WIDTH {
            return None;
        }
        *inspected_bits = inspected_bits.checked_add(bits.len())?;
        if *inspected_bits > budget::MAX_TOTAL_BITS {
            return None;
        }
        let mut value = BigInt::from(0u64);
        for (i, &bit_lit) in bits.iter().enumerate() {
            if i & 0xff == 0 && self.should_abort_theory_loop() {
                return None;
            }
            let offset_lit = if bit_lit > 0 {
                bit_lit.checked_add(var_offset)?
            } else {
                bit_lit.checked_sub(var_offset)?
            };
            let sat_var_idx = usize::try_from(offset_lit.unsigned_abs())
                .ok()?
                .checked_sub(1)?;
            let sat_val = *sat_model.get(sat_var_idx)?;
            let bit_value = if offset_lit > 0 { sat_val } else { !sat_val };
            if bit_value {
                value |= BigInt::from(1) << i;
            }
        }
        Some(value)
    }

    fn fc_pair_cost_for_terms(
        &self,
        term_bits: &HashMap<TermId, BvBits>,
        idx_a: TermId,
        idx_b: TermId,
        sel_a: TermId,
        sel_b: TermId,
    ) -> Option<(usize, usize)> {
        budget::pair_cost(
            term_bits.get(&idx_a)?,
            term_bits.get(&idx_b)?,
            term_bits.get(&sel_a)?,
            term_bits.get(&sel_b)?,
        )
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
