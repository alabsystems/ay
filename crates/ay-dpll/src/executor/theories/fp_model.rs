// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FP model extraction: reconstruct IEEE 754 values from SAT assignments.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Sort, TermId, TermStore};
use ay_fp::{FpDecomposed, FpModel, FpModelValue};

use super::super::Executor;

impl Executor {
    /// Extract an FP model from SAT solver bit assignments.
    ///
    /// Given a SAT model and the FpSolver's term-to-decomposition mapping,
    /// reconstruct concrete IEEE 754 values for each FP-sorted term.
    pub(in crate::executor) fn extract_fp_model_from_bits(
        sat_model: &[bool],
        term_to_fp: &HashMap<TermId, FpDecomposed>,
        var_offset: i32,
        terms: &TermStore,
    ) -> FpModel {
        let mut values = HashMap::default();

        for (&term_id, decomposed) in term_to_fp {
            let sort = terms.sort(term_id);
            let Sort::FloatingPoint(eb, sb) = sort else {
                continue;
            };

            let sign = read_cnf_bit(sat_model, decomposed.sign, var_offset);

            let mut exponent: u64 = 0;
            for (i, &lit) in decomposed.exponent.iter().enumerate() {
                if read_cnf_bit(sat_model, lit, var_offset) {
                    exponent |= 1 << i;
                }
            }

            let mut significand: u64 = 0;
            for (i, &lit) in decomposed.significand.iter().enumerate() {
                if read_cnf_bit(sat_model, lit, var_offset) {
                    significand |= 1 << i;
                }
            }

            let max_exponent = (1u64 << eb) - 1;
            let fp_value = if exponent == max_exponent && significand != 0 {
                // NaN: exponent all-ones, significand non-zero
                FpModelValue::NaN { eb: *eb, sb: *sb }
            } else if exponent == max_exponent && significand == 0 {
                // Infinity: exponent all-ones, significand zero
                if sign {
                    FpModelValue::NegInf { eb: *eb, sb: *sb }
                } else {
                    FpModelValue::PosInf { eb: *eb, sb: *sb }
                }
            } else if exponent == 0 && significand == 0 {
                // Zero: exponent zero, significand zero
                if sign {
                    FpModelValue::NegZero { eb: *eb, sb: *sb }
                } else {
                    FpModelValue::PosZero { eb: *eb, sb: *sb }
                }
            } else {
                // Normal or subnormal finite value
                FpModelValue::Fp {
                    sign,
                    exponent,
                    significand,
                    eb: *eb,
                    sb: *sb,
                }
            };

            values.insert(term_id, fp_value);
        }

        FpModel { values }
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
