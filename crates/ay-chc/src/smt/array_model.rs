// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array model extraction helpers for CHC SMT.
//!
//! Builds the term-values map that `ArraySolver::extract_model` requires
//! (combining LIA, SAT-Bool, and BV bit-level assignments), and converts
//! `ArrayInterpretation` into the CHC-level `SmtValue` representation.

use super::context::SmtContext;
use super::types::SmtValue;
use super::value_parse;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HbHashMap;
use ay_core::{Constant, Sort, TermData, TermId, TermStore};
use num_bigint::BigInt;

fn sat_literal_value(bit_lit: i32, sat_model: &[bool], bv_var_offset: i32) -> Option<bool> {
    let offset = u32::try_from(bv_var_offset).ok()?;
    let sat_index = bit_lit.unsigned_abs().checked_add(offset)?.checked_sub(1)? as usize;
    let assigned = *sat_model.get(sat_index)?;
    Some(if bit_lit > 0 { assigned } else { !assigned })
}

impl SmtContext {
    /// Build a term-values map from the current model for array model extraction.
    /// Maps TermId → String value, combining LIA model, SAT Bool assignments, and BV values.
    /// This is the "EUF model" substitute that ArraySolver::extract_model needs.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn build_term_values_map(
        terms: &TermStore,
        lia_model: &Option<ay_lia::LiaModel>,
        sat_model: &[bool],
        term_to_var: &std::collections::BTreeMap<TermId, u32>,
        bv_term_to_bits: &HbHashMap<TermId, Vec<i32>>,
        bv_var_offset: i32,
    ) -> HbHashMap<TermId, String> {
        let mut term_values: HbHashMap<TermId, String> = HbHashMap::default();

        // Array extraction asks for the values of store indices/values and
        // select terms, not just named variables. Seed every exact scalar
        // constant so ground array cells remain available even though constants
        // are intentionally absent from `var_map` and the theory models.
        for tid in terms.term_ids() {
            let value = match terms.get(tid) {
                TermData::Const(Constant::Bool(value)) => Some(value.to_string()),
                TermData::Const(Constant::Int(value)) => Some(value.to_string()),
                TermData::Const(Constant::Rational(value)) => {
                    let value = &value.0;
                    if value.is_integer() {
                        Some(value.to_integer().to_string())
                    } else {
                        Some(format!("(/ {} {})", value.numer(), value.denom()))
                    }
                }
                // Canonical BV printer: hex is only well-formed at multiple-of-4
                // widths, otherwise the literal reparses at the wrong width.
                TermData::Const(Constant::BitVec { value, width }) => {
                    Some(ay_dpll::format_bitvec(value, *width))
                }
                _ => None,
            };
            if let Some(value) = value {
                term_values.insert(tid, value);
            }
        }

        // Add LIA model values (Int/Real terms)
        if let Some(ref m) = lia_model {
            for (&tid, val) in &m.values {
                term_values.insert(tid, val.to_string());
            }
        }

        // Boolean select terms are ordinary SAT terms and need not be named.
        // Walking the encoder map, rather than `var_map`, preserves those
        // assignments for Bool-valued arrays.
        for (&tid, &cnf_var) in term_to_var {
            if !matches!(terms.sort(tid), Sort::Bool) {
                continue;
            }
            let Some(sat_index) = cnf_var.checked_sub(1).map(|index| index as usize) else {
                continue;
            };
            if let Some(&value) = sat_model.get(sat_index) {
                term_values.insert(tid, if value { "true" } else { "false" }.to_string());
            }
        }

        // Likewise, BV selects and store subterms live in the bit-blast map but
        // are absent from `var_map`. Reconstruct every mapped BV term. BigInt
        // keeps the bridge exact for widths above 64 instead of truncating the
        // very cell value array validation is meant to replay.
        for (&tid, bits) in bv_term_to_bits {
            let Sort::BitVec(bvs) = terms.sort(tid) else {
                continue;
            };
            let mut value = BigInt::from(0u8);
            for (index, &bit_lit) in bits.iter().enumerate() {
                if sat_literal_value(bit_lit, sat_model, bv_var_offset) == Some(true) {
                    value += BigInt::from(1u8) << index;
                }
            }
            term_values.insert(tid, ay_dpll::format_bitvec(&value, bvs.width));
        }

        term_values
    }

    /// Convert an ArrayInterpretation from the array solver into an SmtValue.
    pub(super) fn array_interp_to_smt_value(
        interp: &ay_arrays::ArrayInterpretation,
        element_sort: &Sort,
        index_sort: &Sort,
    ) -> SmtValue {
        let default_val = interp
            .default
            .as_ref()
            .and_then(|d| value_parse::parse_smt_value_str(d, element_sort))
            .unwrap_or_else(|| value_parse::default_smt_value(element_sort));

        if interp.stores.is_empty() {
            SmtValue::ConstArray(Box::new(default_val))
        } else {
            let entries: Vec<(SmtValue, SmtValue)> = interp
                .stores
                .iter()
                // ArrayInterpretation stores are authoritative/newest first,
                // while ArrayMap lookup walks entries in reverse.  Convert to
                // its oldest-first representation so duplicate indices retain
                // the array solver's denotation.
                .rev()
                .map(|(k, v)| {
                    let key = value_parse::parse_smt_value_str(k, index_sort)
                        .unwrap_or_else(|| value_parse::default_smt_value(index_sort));
                    let val = value_parse::parse_smt_value_str(v, element_sort)
                        .unwrap_or_else(|| value_parse::default_smt_value(element_sort));
                    (key, val)
                })
                .collect();
            SmtValue::ArrayMap {
                default: Box::new(default_val),
                entries,
            }
        }
    }
}

#[cfg(test)]
#[path = "array_model_tests.rs"]
mod tests;
