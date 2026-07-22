// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! FP blocking clause construction for the FP-to-Real refinement loop.
//!
//! Extracted from `to_real.rs` for code health (#5970).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::CnfClause;
use ay_fp::FpModelValue;

use super::super::fp_model::read_cnf_bit;
use super::to_real::FpToRealSite;

/// Offset a CNF literal by a variable count.
///
/// CNF variables are 1-indexed. Adding `offset` to the absolute value shifts
/// the variable namespace while preserving polarity.
pub(super) fn offset_cnf_lit(lit: i32, offset: i32) -> i32 {
    if lit > 0 {
        lit + offset
    } else {
        lit - offset
    }
}

/// Build a blocking clause that excludes the current FP valuation's binade for the given sites.
///
/// For each `FpToRealSite`, reads the current SAT assignment for the sign and
/// exponent bits of the FP argument. The blocking clause is a disjunction
/// requiring at least one sign/exponent bit to differ. This blocks an entire
/// "binade" (power-of-2 range) at once, making the refinement loop converge
/// in O(2^eb) iterations rather than O(2^(eb+sb)).
fn build_fp_binade_blocking_clause(
    sat_model: &[bool],
    sites: &[FpToRealSite],
    term_to_fp: &HashMap<ay_core::TermId, ay_fp::FpDecomposed>,
    var_offset: i32,
) -> CnfClause {
    let mut lits = Vec::new();

    for site in sites {
        if let Some(decomposed) = term_to_fp.get(&site.arg) {
            // Sign bit
            let sign_val = read_cnf_bit(sat_model, decomposed.sign, var_offset);
            let sign_offset = offset_cnf_lit(decomposed.sign, var_offset);
            lits.push(if sign_val { -sign_offset } else { sign_offset });

            // Exponent bits (blocks the entire binade)
            for &exp_lit in &decomposed.exponent {
                let val = read_cnf_bit(sat_model, exp_lit, var_offset);
                let lit = offset_cnf_lit(exp_lit, var_offset);
                lits.push(if val { -lit } else { lit });
            }
        }
    }

    CnfClause::new(lits)
}

/// Build a blocking clause that excludes the exact FP value (all bits) for the given sites.
///
/// Unlike binade blocking, this includes significand bits, blocking only the
/// specific FP value that failed the mixed subproblem. This allows the SAT
/// solver to explore other values within the same binade (#6241).
fn build_fp_exact_blocking_clause(
    sat_model: &[bool],
    sites: &[FpToRealSite],
    term_to_fp: &HashMap<ay_core::TermId, ay_fp::FpDecomposed>,
    var_offset: i32,
) -> CnfClause {
    let mut lits = Vec::new();

    for site in sites {
        if let Some(decomposed) = term_to_fp.get(&site.arg) {
            // Sign bit
            let sign_val = read_cnf_bit(sat_model, decomposed.sign, var_offset);
            let sign_offset = offset_cnf_lit(decomposed.sign, var_offset);
            lits.push(if sign_val { -sign_offset } else { sign_offset });

            // Exponent bits
            for &exp_lit in &decomposed.exponent {
                let val = read_cnf_bit(sat_model, exp_lit, var_offset);
                let lit = offset_cnf_lit(exp_lit, var_offset);
                lits.push(if val { -lit } else { lit });
            }

            // Significand bits (blocks this exact value, not the whole binade)
            for &sig_lit in &decomposed.significand {
                let val = read_cnf_bit(sat_model, sig_lit, var_offset);
                let lit = offset_cnf_lit(sig_lit, var_offset);
                lits.push(if val { -lit } else { lit });
            }
        }
    }

    CnfClause::new(lits)
}

/// Build unit clauses that force specific FP bit values for a target f64 value.
///
/// Converts the f64 to the nearest representable FP value in the given format
/// and produces unit clauses (one per bit). Returns `None` for NaN/Inf targets
/// or conversion failures.
pub(super) fn build_fp_target_unit_clauses(
    decomposed: &ay_fp::FpDecomposed,
    var_offset: i32,
    target_f64: f64,
    eb: u32,
    sb: u32,
) -> Option<Vec<CnfClause>> {
    let fp_val = FpModelValue::from_f64_with_format(target_f64, eb, sb)?;

    let mut clauses = Vec::new();
    match fp_val {
        FpModelValue::Fp {
            sign,
            exponent,
            significand,
            ..
        } => {
            // Sign bit: true (1) → positive literal, false (0) → negative literal
            let sign_offset = offset_cnf_lit(decomposed.sign, var_offset);
            clauses.push(CnfClause::new(vec![if sign {
                sign_offset
            } else {
                -sign_offset
            }]));

            // Exponent bits (LSB first — matches FpDecomposed/extract_fp_model_from_bits)
            for (i, &exp_lit) in decomposed.exponent.iter().enumerate() {
                let bit = (exponent >> i) & 1;
                let lit = offset_cnf_lit(exp_lit, var_offset);
                clauses.push(CnfClause::new(vec![if bit == 1 { lit } else { -lit }]));
            }

            // Significand bits (LSB first — matches FpDecomposed/extract_fp_model_from_bits)
            for (i, &sig_lit) in decomposed.significand.iter().enumerate() {
                let bit = (significand >> i) & 1;
                let lit = offset_cnf_lit(sig_lit, var_offset);
                clauses.push(CnfClause::new(vec![if bit == 1 { lit } else { -lit }]));
            }
        }
        FpModelValue::PosZero { .. } | FpModelValue::NegZero { .. } => {
            let is_neg = matches!(fp_val, FpModelValue::NegZero { .. });
            let sign_offset = offset_cnf_lit(decomposed.sign, var_offset);
            clauses.push(CnfClause::new(vec![if is_neg {
                sign_offset
            } else {
                -sign_offset
            }]));
            for &exp_lit in &decomposed.exponent {
                let lit = offset_cnf_lit(exp_lit, var_offset);
                clauses.push(CnfClause::new(vec![-lit]));
            }
            for &sig_lit in &decomposed.significand {
                let lit = offset_cnf_lit(sig_lit, var_offset);
                clauses.push(CnfClause::new(vec![-lit]));
            }
        }
        // NaN/Inf: not useful as targets
        _ => return None,
    }

    Some(clauses)
}

/// Extract the binade fingerprint (sign + exponent bit values) for tracking.
fn binade_fingerprint(
    sat_model: &[bool],
    sites: &[FpToRealSite],
    term_to_fp: &HashMap<ay_core::TermId, ay_fp::FpDecomposed>,
    var_offset: i32,
) -> Vec<bool> {
    let mut bits = Vec::new();
    for site in sites {
        if let Some(decomposed) = term_to_fp.get(&site.arg) {
            bits.push(read_cnf_bit(sat_model, decomposed.sign, var_offset));
            for &exp_lit in &decomposed.exponent {
                bits.push(read_cnf_bit(sat_model, exp_lit, var_offset));
            }
        }
    }
    bits
}

/// Choose a blocking clause based on how many times this binade has been tried.
///
/// Returns the blocking clause and whether binade-level blocking was used.
pub(super) fn choose_blocking_clause(
    sat_model: &[bool],
    sites: &[FpToRealSite],
    term_to_fp: &HashMap<ay_core::TermId, ay_fp::FpDecomposed>,
    var_offset: i32,
    binade_attempts: &mut HashMap<Vec<bool>, usize>,
    exact_per_binade: usize,
) -> (CnfClause, bool) {
    let fingerprint = binade_fingerprint(sat_model, sites, term_to_fp, var_offset);
    let count = binade_attempts.entry(fingerprint).or_insert(0);
    *count += 1;

    if *count > exact_per_binade {
        (
            build_fp_binade_blocking_clause(sat_model, sites, term_to_fp, var_offset),
            true,
        )
    } else {
        (
            build_fp_exact_blocking_clause(sat_model, sites, term_to_fp, var_offset),
            false,
        )
    }
}
