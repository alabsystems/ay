// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT model extraction for the DPLL(T) theory loop.
//!
//! Extracts variable values from the SAT model, LIA model, BV bit-mappings,
//! and array solver into an `FxHashMap<String, SmtValue>` model.

use ay_arrays::ArraySolver;
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::{Sort, TermId, TermStore};
use ay_lia::LiaSolver;
use num_bigint::BigUint;
use num_traits::One;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HbHashMap;

use super::super::context::SmtContext;
use super::super::types::SmtValue;

fn extract_bitvec_from_sat_model(
    bits: &[i32],
    width: u32,
    sat_model: &[bool],
    bv_var_offset: i32,
) -> Option<SmtValue> {
    fn assigned_bit(bit_lit: i32, sat_model: &[bool], bv_var_offset: i32) -> Option<bool> {
        if bit_lit == 0 {
            return None;
        }
        let offset = u32::try_from(bv_var_offset).ok()?;
        let index = bit_lit.unsigned_abs().checked_add(offset)?.checked_sub(1)? as usize;
        let assigned = *sat_model.get(index)?;
        Some(if bit_lit > 0 { assigned } else { !assigned })
    }

    if width == 0
        || width > crate::MAX_BITVECTOR_WIDTH
        || bits.len() != usize::try_from(width).ok()?
    {
        return None;
    }

    if width <= 128 {
        let mut value = 0u128;
        for (index, &bit_lit) in bits.iter().enumerate() {
            if assigned_bit(bit_lit, sat_model, bv_var_offset)? {
                value |= 1u128 << index;
            }
        }
        return Some(SmtValue::BitVec(value, width));
    }

    let mut value = BigUint::from(0u8);
    for (index, &bit_lit) in bits.iter().enumerate() {
        if assigned_bit(bit_lit, sat_model, bv_var_offset)? {
            value |= BigUint::from(1u8) << index;
        }
    }
    Some(SmtValue::bitvec_from_biguint(value, width))
}

/// Result of value extraction from a theory-SAT assignment.
pub(super) enum ExtractResult {
    /// Values were extracted successfully.
    Values(FxHashMap<String, SmtValue>),
    /// Exact extraction failed (overflow or malformed/incomplete model); return Unknown.
    Overflow,
}

/// Extract variable values from a theory-SAT assignment.
///
/// Iterates over `var_map` and extracts values from the LIA model, SAT model,
/// BV bit-mappings, and array solver.
///
/// This is a free function (not a method on SmtContext) to avoid borrow conflicts
/// with the LIA solver which holds a reference to the shared TermStore.
#[allow(clippy::too_many_arguments)]
pub(super) fn extract_theory_sat_values(
    terms: &TermStore,
    var_map: &FxHashMap<String, TermId>,
    var_original_names: &FxHashMap<String, String>,
    sat_model: &[bool],
    term_to_var: &std::collections::BTreeMap<TermId, u32>,
    lia: &mut LiaSolver<'_>,
    bv_term_to_bits: &HbHashMap<TermId, Vec<i32>>,
    bv_var_offset: i32,
    has_array_ops: bool,
    array_solver: &mut Option<ArraySolver<'_>>,
) -> ExtractResult {
    let mut values = FxHashMap::default();
    let lia_model = lia.extract_model();

    // ArraySolver::extract_model reconstructs every tracked array, so doing it
    // inside the named-variable loop repeats the full TermStore/CNF/BV scan and
    // cache rebuild once per array. Build the scalar bridge and array model once
    // for this SAT assignment, then perform only O(1) interpretation lookups
    // below. Avoid the work entirely when the query exposes no named array.
    let needs_array_model = has_array_ops
        && var_map
            .values()
            .any(|&term_id| matches!(terms.sort(term_id), Sort::Array(_)));
    let array_model = if needs_array_model {
        match array_solver.as_mut() {
            Some(arr) => {
                let Some(term_values) = SmtContext::build_term_values_map(
                    terms,
                    &lia_model,
                    sat_model,
                    term_to_var,
                    bv_term_to_bits,
                    bv_var_offset,
                ) else {
                    return ExtractResult::Overflow;
                };
                Some(arr.extract_model(&term_values))
            }
            None => return ExtractResult::Overflow,
        }
    } else {
        None
    };

    for (qualified_name, &term_id) in var_map {
        // #6100: var_map keys are sort-qualified; emit
        // original CHC names in the model for downstream
        // lookups via `model.get(&v.name)`.
        let name = var_original_names
            .get(qualified_name)
            .map(String::as_str)
            .unwrap_or(qualified_name);
        match terms.sort(term_id) {
            Sort::Bool => {
                if let Some(&cnf_var) = term_to_var.get(&term_id) {
                    let sat_var = ay_sat::Variable::new(cnf_var - 1);
                    if let Some(value) = sat_model.get(sat_var.index()) {
                        values.insert(name.to_owned(), SmtValue::Bool(*value));
                    }
                }
            }
            Sort::Int => {
                if let Some(m) = &lia_model {
                    if let Some(v) = m.values.get(&term_id) {
                        // Phase-2 BigInt escape: the internal LIA lane solves
                        // exactly in BigInt; carry beyond-i128 witnesses as
                        // canonical SmtValue::BigInt instead of skipping them
                        // (#3827 used to skip, which demoted verified Sat
                        // verdicts to Unknown via the missing-var gate).
                        values.insert(name.to_owned(), SmtValue::int_from_bigint(v.clone()));
                        continue;
                    }
                }

                // Fallback: LIA may not include all `Int` vars in its extracted model,
                // but the underlying LRA solver still tracks their values.
                if let Some(v) = lia.lra_solver().get_value(term_id) {
                    if v.denom().is_one() {
                        // Phase-2 BigInt escape (see LIA lane above).
                        values.insert(
                            name.to_owned(),
                            SmtValue::int_from_bigint(v.numer().clone()),
                        );
                    } else {
                        return ExtractResult::Overflow;
                    }
                }
            }
            Sort::BitVec(bv_sort) => {
                // Extract BV value from SAT model using bit mappings.
                if let Some(bits) = bv_term_to_bits.get(&term_id) {
                    let Some(value) = extract_bitvec_from_sat_model(
                        bits,
                        bv_sort.width,
                        sat_model,
                        bv_var_offset,
                    ) else {
                        return ExtractResult::Overflow;
                    };
                    values.insert(name.to_owned(), value);
                }
            }
            Sort::Real => {
                // Extract rational value from the LRA solver.
                if let Some(v) = lia.lra_solver().get_value(term_id) {
                    values.insert(name.to_owned(), SmtValue::Real(v.clone()));
                }
            }
            Sort::Array(arr_sort) if has_array_ops => {
                let Some(interp) = array_model
                    .as_ref()
                    .and_then(|model| model.array_values.get(&term_id))
                else {
                    return ExtractResult::Overflow;
                };
                let Some(smt_val) = SmtContext::array_interp_to_smt_value(
                    interp,
                    &arr_sort.element_sort,
                    &arr_sort.index_sort,
                ) else {
                    return ExtractResult::Overflow;
                };
                values.insert(name.to_owned(), smt_val);
            }
            _ => {}
        }
    }

    ExtractResult::Values(values)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn theory_model_extraction_preserves_bit_128() {
        let bits: Vec<i32> = (1..=129).collect();
        let mut sat_model = vec![false; 129];
        sat_model[128] = true;
        assert_eq!(
            extract_bitvec_from_sat_model(&bits, 129, &sat_model, 0),
            Some(SmtValue::bitvec_from_biguint(
                BigUint::from(1u8) << 128,
                129
            ))
        );
    }

    #[test]
    fn theory_model_extraction_keeps_u128_fast_path() {
        let bits: Vec<i32> = (1..=128).collect();
        let sat_model = vec![true; 128];
        assert_eq!(
            extract_bitvec_from_sat_model(&bits, 128, &sat_model, 0),
            Some(SmtValue::BitVec(u128::MAX, 128))
        );
    }

    #[test]
    fn theory_model_extraction_rejects_missing_or_unassigned_bits() {
        let bits: Vec<i32> = (1..=128).collect();
        let sat_model = vec![false; 128];
        assert_eq!(
            extract_bitvec_from_sat_model(&bits, 129, &sat_model, 0),
            None
        );

        let bits: Vec<i32> = (1..=129).collect();
        assert_eq!(
            extract_bitvec_from_sat_model(&bits, 129, &sat_model, 0),
            None
        );

        let mut bits: Vec<i32> = (1..=129).collect();
        bits[17] = 0;
        let sat_model = vec![false; 129];
        assert_eq!(
            extract_bitvec_from_sat_model(&bits, 129, &sat_model, 0),
            None
        );
    }
}
