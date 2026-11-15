// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FP model extraction: reconstruct IEEE 754 values from SAT assignments.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};
use ay_fp::{FpDecomposed, FpModel, FpModelValue, RmBits};
use num_bigint::BigUint;

use super::super::Executor;

impl Executor {
    /// Extract an FP model from SAT solver bit assignments.
    ///
    /// Given a SAT model and the FpSolver's term-to-decomposition mapping,
    /// reconstruct concrete IEEE 754 values for every mapped FP-sorted term.
    /// A malformed shape, namespace, or missing assignment refuses the entire
    /// model; no partial/default-filled model is published.
    ///
    /// Every declared rounding-mode constant with bits (`rm_terms`) gets its
    /// mode; bits outside the five codes refuse the model like any malformed
    /// field.
    pub(in crate::executor) fn extract_fp_model_from_bits_controlled(
        sat_model: &[bool],
        term_to_fp: &HashMap<TermId, FpDecomposed>,
        rm_terms: &HashMap<TermId, RmBits>,
        var_offset: i32,
        terms: &TermStore,
        poll: &mut dyn FnMut() -> bool,
    ) -> Option<FpModel> {
        if var_offset < 0 || !poll() {
            return None;
        }
        let mut values = HashMap::default();
        for (&term_id, decomposed) in term_to_fp {
            let value = Self::extract_fp_value_from_bits_controlled(
                sat_model, term_id, decomposed, var_offset, terms, poll,
            )?;
            values.insert(term_id, value);
        }
        let mut rm_values = HashMap::default();
        for (&term_id, bits) in rm_terms {
            if !poll() {
                return None;
            }
            // An `ite` over modes has no value of its own: it evaluates.
            if !matches!(terms.get(term_id), TermData::Var(..)) {
                continue;
            }
            let mode = bits.decode(|lit| read_cnf_bit_checked(sat_model, lit, var_offset))?;
            rm_values.insert(term_id, mode);
        }
        poll().then_some(FpModel { values, rm_values })
    }

    /// Decode one completely assigned FP decomposition without a temporary map.
    /// The original caller is polled before allocation, at each field limb,
    /// and before publication. A partial field or cancelled model cannot escape.
    pub(in crate::executor) fn extract_fp_value_from_bits_controlled(
        sat_model: &[bool],
        term_id: TermId,
        decomposed: &FpDecomposed,
        var_offset: i32,
        terms: &TermStore,
        poll: &mut dyn FnMut() -> bool,
    ) -> Option<FpModelValue> {
        if term_id.index() >= terms.len() || var_offset < 0 || !poll() {
            return None;
        }
        let Sort::FloatingPoint(eb, sb) = terms.sort(term_id) else {
            return None;
        };
        if !(2..=ay_fp::MAX_ENCODING_EXPONENT_BITS).contains(eb)
            || !(2..=ay_fp::MAX_ENCODING_SIGNIFICAND_BITS).contains(sb)
            || eb.checked_add(*sb).is_none()
        {
            return None;
        }
        if decomposed.precision.exponent_bits() != *eb
            || decomposed.precision.significand_bits() != *sb
            || decomposed.exponent.len() != *eb as usize
            || decomposed.significand.len() != (*sb - 1) as usize
        {
            return None;
        }
        let sign = read_cnf_bit_checked(sat_model, decomposed.sign, var_offset)?;
        let mut exponent = BigUint::default();
        for (i, &lit) in decomposed.exponent.iter().enumerate() {
            if i % 64 == 0 && !poll() {
                return None;
            }
            if read_cnf_bit_checked(sat_model, lit, var_offset)? {
                exponent.set_bit(i as u64, true);
            }
        }
        let mut significand = BigUint::default();
        for (i, &lit) in decomposed.significand.iter().enumerate() {
            if i % 64 == 0 && !poll() {
                return None;
            }
            if read_cnf_bit_checked(sat_model, lit, var_offset)? {
                significand.set_bit(i as u64, true);
            }
        }
        if !poll() {
            return None;
        }
        FpModelValue::from_exact_fields(sign, exponent, significand, *eb, *sb)
    }

    #[cfg(test)]
    pub(in crate::executor) fn extract_fp_model_from_bits(
        sat_model: &[bool],
        term_to_fp: &HashMap<TermId, FpDecomposed>,
        rm_terms: &HashMap<TermId, RmBits>,
        var_offset: i32,
        terms: &TermStore,
    ) -> Option<FpModel> {
        Self::extract_fp_model_from_bits_controlled(
            sat_model,
            term_to_fp,
            rm_terms,
            var_offset,
            terms,
            &mut || true,
        )
    }

    #[cfg(test)]
    pub(in crate::executor) fn extract_fp_value_from_bits(
        sat_model: &[bool],
        term_id: TermId,
        decomposed: &FpDecomposed,
        var_offset: i32,
        terms: &TermStore,
    ) -> Option<FpModelValue> {
        Self::extract_fp_value_from_bits_controlled(
            sat_model,
            term_id,
            decomposed,
            var_offset,
            terms,
            &mut || true,
        )
    }

    /// Extract a BV model from SAT solver bit assignments for BV terms
    /// that were bitblasted during FP solving (#3586).
    ///
    /// When the FP solver handles `to_fp`/`to_fp_unsigned` with variable BV
    /// arguments, it creates CNF variables for BV bits in its variable space.
    /// After SAT solving, this function reads those bits back to produce
    /// concrete BigInt values for model validation.
    pub(in crate::executor) fn extract_bv_model_from_fp_bits(
        sat_model: &[bool],
        bv_term_bits: &HashMap<TermId, Vec<i32>>,
        var_offset: i32,
        terms: &TermStore,
    ) -> ay_bv::BvModel {
        use num_bigint::BigInt;

        let mut values = HashMap::default();

        for (&term_id, bits) in bv_term_bits {
            // Only extract values for BV-sorted terms
            let Sort::BitVec(_) = terms.sort(term_id) else {
                continue;
            };

            let mut val = BigInt::from(0);
            for (i, &lit) in bits.iter().enumerate() {
                if read_cnf_bit(sat_model, lit, var_offset) {
                    val |= BigInt::from(1) << i;
                }
            }
            values.insert(term_id, val);
        }

        ay_bv::BvModel {
            values,
            term_to_bits: HashMap::default(),
            bool_overrides: HashMap::default(),
        }
    }
}

/// Checked FP read: do not negate i32::MIN, overflow an offset, or invent a bit.
fn read_cnf_bit_checked(sat_model: &[bool], lit: i32, var_offset: i32) -> Option<bool> {
    let offset = u32::try_from(var_offset).ok()?;
    let magnitude = lit.unsigned_abs();
    let shifted = magnitude.checked_add(offset)?;
    if magnitude == 0 || shifted > i32::MAX as u32 {
        return None;
    }
    let index = usize::try_from(shifted.checked_sub(1)?).ok()?;
    let value = *sat_model.get(index)?;
    Some(if lit > 0 { value } else { !value })
}

/// Read a single bit from the SAT model via its CNF literal.
///
/// CNF literals are 1-indexed: positive means the variable is true,
/// negative means negated. `var_offset` shifts the variable index
/// when the FP namespace is offset from the Tseitin namespace.
pub(super) fn read_cnf_bit(sat_model: &[bool], lit: i32, var_offset: i32) -> bool {
    let offset_lit = if lit > 0 {
        lit + var_offset
    } else {
        lit - var_offset
    };
    let sat_var_idx = if offset_lit > 0 {
        (offset_lit - 1) as usize
    } else {
        (-offset_lit - 1) as usize
    };
    let raw_val = if sat_var_idx < sat_model.len() {
        sat_model[sat_var_idx]
    } else {
        false
    };
    if offset_lit > 0 {
        raw_val
    } else {
        !raw_val
    }
}

#[cfg(test)]
#[path = "fp_model_tests.rs"]
mod tests;
