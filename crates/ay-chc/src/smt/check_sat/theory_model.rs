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
use num_traits::One;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HbHashMap;

use super::super::context::SmtContext;
use super::super::types::SmtValue;

/// Result of value extraction from a theory-SAT assignment.
pub(super) enum ExtractResult {
    /// Values were extracted successfully.
    Values(FxHashMap<String, SmtValue>),
    /// An integer overflow was encountered; return Unknown.
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
        array_solver.as_mut().map(|arr| {
            let term_values = SmtContext::build_term_values_map(
                terms,
                &lia_model,
                sat_model,
                term_to_var,
                bv_term_to_bits,
                bv_var_offset,
            );
            arr.extract_model(&term_values)
        })
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
                    let mut bv_val: u128 = 0;
                    for (i, &bit_lit) in bits.iter().enumerate() {
                        // Skip bits beyond u128 capacity.
                        if i >= 128 {
                            break;
                        }
                        // #6090: use u32 arithmetic to avoid i32 overflow.
                        let abs_lit = bit_lit.unsigned_abs();
                        let offset_var = abs_lit
                            .checked_add(bv_var_offset as u32)
                            .and_then(|v| v.checked_sub(1));
                        let Some(offset_var) = offset_var else {
                            continue;
                        };
                        let sat_var = ay_sat::Variable::new(offset_var);
                        if let Some(&val) = sat_model.get(sat_var.index()) {
                            let bit_val = if bit_lit > 0 { val } else { !val };
                            if bit_val {
                                bv_val |= 1u128 << i;
                            }
                        }
                    }
                    values.insert(name.to_owned(), SmtValue::BitVec(bv_val, bv_sort.width));
                }
            }
            Sort::Real => {
                // Extract rational value from the LRA solver.
                if let Some(v) = lia.lra_solver().get_value(term_id) {
                    values.insert(name.to_owned(), SmtValue::Real(v.clone()));
                }
            }
            Sort::Array(arr_sort) if has_array_ops => {
                if let Some(interp) = array_model
                    .as_ref()
                    .and_then(|model| model.array_values.get(&term_id))
                {
                    let smt_val = SmtContext::array_interp_to_smt_value(
                        interp,
                        &arr_sort.element_sort,
                        &arr_sort.index_sort,
                    );
                    values.insert(name.to_owned(), smt_val);
                }
            }
            _ => {}
        }
    }

    ExtractResult::Values(values)
}
