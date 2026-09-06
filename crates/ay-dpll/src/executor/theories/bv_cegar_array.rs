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
//!
//! The audit reads and constrains terms through [`FcAuditLits`], a view in the
//! FINAL CNF numbering: `BitVec`/`FloatingPoint` terms are their bit-blasted
//! bits, and a `Bool` term (a Bool-element `select`, or a Bool array index) is
//! the single atom literal the bit-blaster or the Boolean skeleton assigned
//! it. This is the same resolution `scalar_elem_lits` uses for the upfront
//! ROW/FC axioms in `bv_axioms_array.rs`; before it, every Bool-element
//! select was "owed" term bits the blaster never allocates, so any array with
//! two Bool selects failed the audit closed to `unknown`.

// #8529: Use deterministic hash maps in all builds.
use std::collections::BTreeMap;

use ay_bv::BvBits;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{CnfLit, Sort, TermId, TermStore};
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

/// One audited select with its index and result resolved to final-numbered
/// literals and to the concrete values those literals take in the SAT model.
struct FcConcreteSelect {
    select: TermId,
    index_lits: BvBits,
    value_lits: BvBits,
    index_value: BigInt,
    value: BigInt,
}

/// The literal view the FC audit reads values from and constrains, in the
/// FINAL CNF numbering the SAT solver was loaded with.
///
/// `term_bits` and `bv_bool_to_var` carry the bit-blaster's own numbering and
/// are shifted by `var_offset` (the Tseitin variable count); the Boolean
/// skeleton's `tseitin_term_to_var` is already final. A `Bool` term resolves to
/// its single atom literal from the bit-blaster, else from the skeleton — the
/// two are linked by `bv_encoding`'s atom-linking pass, so either one is the
/// term's value under the model.
pub(in crate::executor) struct FcAuditLits<'a> {
    term_bits: &'a HashMap<TermId, BvBits>,
    bv_bool_to_var: &'a HashMap<TermId, CnfLit>,
    tseitin_term_to_var: &'a BTreeMap<TermId, u32>,
    var_offset: i32,
}

impl<'a> FcAuditLits<'a> {
    pub(in crate::executor) fn new(
        term_bits: &'a HashMap<TermId, BvBits>,
        bv_bool_to_var: &'a HashMap<TermId, CnfLit>,
        tseitin_term_to_var: &'a BTreeMap<TermId, u32>,
        var_offset: i32,
    ) -> Self {
        Self {
            term_bits,
            bv_bool_to_var,
            tseitin_term_to_var,
            var_offset,
        }
    }

    fn term_bits(&self) -> &'a HashMap<TermId, BvBits> {
        self.term_bits
    }

    /// Final-numbered literals encoding `term`'s value, or `None` when neither
    /// the bit-blaster nor the Boolean skeleton assigned it any.
    ///
    /// A Bool term absent from both maps was never encoded, so the SAT model
    /// carries no value for it; the caller decides whether that is owed
    /// (fail closed) or outside the bit-level audit's remit.
    fn scalar_lits(&self, terms: &TermStore, term: TermId) -> Option<BvBits> {
        if let Some(bits) = self.term_bits.get(&term) {
            if bits.is_empty() {
                return None;
            }
            return Some(
                bits.iter()
                    .map(|&bit| bv_encoding::offset_cnf_lit(bit, self.var_offset))
                    .collect(),
            );
        }
        if *terms.sort(term) != Sort::Bool {
            return None;
        }
        if let Some(&lit) = self.bv_bool_to_var.get(&term) {
            return Some(vec![bv_encoding::offset_cnf_lit(lit, self.var_offset)]);
        }
        let var = *self.tseitin_term_to_var.get(&term)?;
        Some(vec![CnfLit::try_from(var).ok()?])
    }
}

mod fc_check;

impl Executor {
    fn append_fc_group_refinement(
        &mut self,
        group: &[FcConcreteSelect],
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
                let (left, right) = (&group[a], &group[b]);
                if left.value == right.value || left.select == right.select {
                    continue;
                }
                let pair = if left.select < right.select {
                    (left.select, right.select)
                } else {
                    (right.select, left.select)
                };
                if already_covered.contains(&pair) {
                    return false;
                }
                if !build.newly_covered.insert(pair) {
                    continue;
                }
                let Some((pair_vars, pair_clauses)) = budget::pair_cost(
                    &left.index_lits,
                    &right.index_lits,
                    &left.value_lits,
                    &right.value_lits,
                ) else {
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
                let clauses = generate_fc_axiom_clauses(
                    &left.index_lits,
                    &right.index_lits,
                    &left.value_lits,
                    &right.value_lits,
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

    /// Does the encoding OWE this term a literal view the audit can read?
    ///
    /// True exactly for the sorts it can represent as a bit string: `BitVec`
    /// and `FloatingPoint` (their bit-blasted bits) and `Bool` (the single atom
    /// literal resolved through [`FcAuditLits::scalar_lits`]). For those, a
    /// missing view means the audit cannot read a value it should have been
    /// able to read — an incomplete audit, which fails closed.
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

    /// The value `lits` (final numbering) take in `sat_model`, bounded by the
    /// audit's per-term and aggregate bit budgets.
    fn concrete_value_bounded(
        &mut self,
        sat_model: &[bool],
        lits: &[CnfLit],
        inspected_bits: &mut usize,
    ) -> Option<BigInt> {
        if lits.len() > budget::MAX_SINGLE_WIDTH {
            return None;
        }
        *inspected_bits = inspected_bits.checked_add(lits.len())?;
        if *inspected_bits > budget::MAX_TOTAL_BITS {
            return None;
        }
        let mut value = BigInt::from(0u64);
        for (i, &lit) in lits.iter().enumerate() {
            if i & 0xff == 0 && self.should_abort_theory_loop() {
                return None;
            }
            let sat_var_idx = usize::try_from(lit.unsigned_abs()).ok()?.checked_sub(1)?;
            let sat_val = *sat_model.get(sat_var_idx)?;
            let bit_value = if lit > 0 { sat_val } else { !sat_val };
            if bit_value {
                value |= BigInt::from(1) << i;
            }
        }
        Some(value)
    }
}

/// Generate FC axiom clauses for a single pair of selects.
///
/// Encodes: `(idx_a == idx_b) -> (sel_a == sel_b)` as a bit-level diff-XOR
/// encoding over literals already in final CNF numbering, producing SAT-level
/// literals. Fresh diff/eq variables are drawn from `next_var`.
fn generate_fc_axiom_clauses(
    idx_a_bits: &[CnfLit],
    idx_b_bits: &[CnfLit],
    sel_a_bits: &[CnfLit],
    sel_b_bits: &[CnfLit],
    next_var: &mut u32,
) -> Vec<Vec<SatLiteral>> {
    let mut clauses: Vec<Vec<SatLiteral>> = Vec::new();

    if idx_a_bits.len() != idx_b_bits.len() || idx_a_bits.is_empty() {
        return clauses;
    }
    if sel_a_bits.len() != sel_b_bits.len() || sel_a_bits.is_empty() {
        return clauses;
    }

    let to_sat = |cnf_lit: i32| -> SatLiteral { crate::cnf_lit_to_sat(cnf_lit) };

    // Create diff variables for index bits: diff_k <-> (idx_a_k XOR idx_b_k)
    let mut diff_vars: Vec<i32> = Vec::with_capacity(idx_a_bits.len());
    for (&ob1, &ob2) in idx_a_bits.iter().zip(idx_b_bits.iter()) {
        // If both bits are the same literal, they're identical - skip
        if ob1 == ob2 {
            continue;
        }

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
        for (&os1, &os2) in sel_a_bits.iter().zip(sel_b_bits.iter()) {
            if os1 == os2 {
                continue;
            }
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
    for (&os1, &os2) in sel_a_bits.iter().zip(sel_b_bits.iter()) {
        if os1 == os2 {
            continue;
        }
        clauses.push(vec![to_sat(-eq_idx), to_sat(-os1), to_sat(os2)]);
        clauses.push(vec![to_sat(-eq_idx), to_sat(os1), to_sat(-os2)]);
    }

    clauses
}

#[cfg(test)]
mod tests {
    use super::{generate_fc_axiom_clauses, FcAuditLits};
    use ay_core::kani_compat::DetHashMap as HashMap;
    use ay_core::{Sort, TermStore};
    use num_bigint::BigInt;
    use std::collections::BTreeMap;

    /// A Bool-element select has no term bits; its value is the bit-blaster's
    /// atom (offset into final numbering), else the skeleton's atom (already
    /// final). A Bool term in neither map has no value to audit.
    #[test]
    fn bool_terms_resolve_to_their_single_atom_literal() {
        let mut terms = TermStore::new();
        let array_sort = Sort::array(Sort::bitvec(8), Sort::Bool);
        let array = terms.mk_var("a", array_sort);
        let index = terms.mk_var("i", Sort::bitvec(8));
        let blasted = terms.mk_select(array, index);
        let one = terms.mk_bitvec(BigInt::from(1), 8);
        let skeleton = terms.mk_select(array, one);
        let two = terms.mk_bitvec(BigInt::from(2), 8);
        let unencoded = terms.mk_select(array, two);

        let mut term_bits = HashMap::default();
        term_bits.insert(index, vec![1, -2, 3, 4, 5, 6, 7, 8]);
        let mut bv_bool_to_var = HashMap::default();
        bv_bool_to_var.insert(blasted, -9);
        let mut tseitin_term_to_var = BTreeMap::new();
        tseitin_term_to_var.insert(skeleton, 4u32);
        let var_offset = 10;
        let lits = FcAuditLits::new(
            &term_bits,
            &bv_bool_to_var,
            &tseitin_term_to_var,
            var_offset,
        );

        assert_eq!(
            lits.scalar_lits(&terms, index),
            Some(vec![11, -12, 13, 14, 15, 16, 17, 18])
        );
        assert_eq!(lits.scalar_lits(&terms, blasted), Some(vec![-19]));
        assert_eq!(lits.scalar_lits(&terms, skeleton), Some(vec![4]));
        assert_eq!(lits.scalar_lits(&terms, unencoded), None);
        assert_eq!(lits.scalar_lits(&terms, array), None);
    }

    /// A one-bit result pair yields the same shape the BitVec path produces:
    /// per differing index bit an XOR definition, one eq_idx, and the two
    /// implication clauses forcing the atoms equal under eq_idx.
    #[test]
    fn single_atom_results_get_fc_implications() {
        let mut next_var = 100;
        let clauses = generate_fc_axiom_clauses(&[1, 2], &[1, -3], &[7], &[-8], &mut next_var);
        // One differing index bit: 4 XOR clauses + 1 (eq -> !diff) + 1 (diff | eq)
        // + 2 value implications.
        assert_eq!(clauses.len(), 8);
        assert_eq!(next_var, 102);

        let mut next_var = 100;
        let identical = generate_fc_axiom_clauses(&[1, 2], &[1, 2], &[7], &[-8], &mut next_var);
        assert_eq!(identical.len(), 2);
        assert_eq!(next_var, 100);
    }
}
