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

/// Coverage key for one emitted FC instance: the select pair
/// plus its guard instance (sorted guard literals and sorted
/// avoided-store bit vectors). The same pair may need several
/// instances — a candidate can violate it under a different
/// equality path than the instance already emitted — so coverage
/// is per instance, not per pair.
type FcCoverKey = (TermId, TermId, Vec<i32>, Vec<BvBits>);

struct CegarArrayBuild {
    clauses: Vec<Vec<SatLiteral>>,
    next_var: u32,
    new_vars: usize,
    inspected_bits: usize,
    pair_attempts: usize,
    newly_covered: HashSet<FcCoverKey>,
    /// A pair was skipped because the per-check var/clause budget
    /// ran out. The check then returns the clauses accumulated so
    /// far as a (partial) refinement — every emitted clause is a
    /// valid lemma and the next candidate is re-audited — unless
    /// nothing was emitted, which stays incomplete.
    budget_exhausted: bool,
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

mod fc_axiom;
mod fc_check;
mod fc_collect;
mod fc_pair;
mod fc_stored;
mod nested_fc;

use fc_axiom::generate_fc_axiom_clauses;

pub(in crate::executor) use nested_fc::NestedReadPaths;

impl Executor {
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

#[cfg(test)]
#[path = "bv_cegar_array_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "bv_cegar_array_partition_tests.rs"]
mod partition_tests;
