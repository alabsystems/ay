// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cheap axiom checks for delayed BV operations (#7015, #8285).
//!
//! These are the per-operation checks that provide cheap conflict clauses
//! before escalating to full circuit construction:
//!
//! **Multiplication (bvmul):**
//! - Zero: `a == 0 => result == 0` (symmetric)
//! - One: `a == 1 => result == b` (symmetric)
//! - Power-of-2: `a == 2^k => result == b << k` (#8285, symmetric)
//! - Invertibility: `(a | -a) & result == result` (Niemetz-Preiner)
//!
//! **Division (bvudiv, bvsdiv):**
//! - By one: `divisor == 1 => result == dividend`
//! - Unsigned by zero: `divisor == 0 => result == ~0`
//! - Unsigned self: `a == b != 0 => result == 1` (#8285)
//! - Signed by zero: `divisor == 0 => result = sign-dependent` (#8285)
//!
//! **Remainder (bvurem, bvsrem, bvsmod):**
//! - By one: `divisor == 1 => result == 0`
//! - Unsigned by zero: `divisor == 0 => result == dividend`
//! - Signed rem by zero: `divisor == 0 => result == dividend` (#8285)
//! - Signed mod by one/-1: `divisor in {1, -1} => result == 0`
//! - Signed mod by zero: `divisor == 0 => result == dividend`
//!
//! **Addition (bvadd):**
//! - Zero: `a == 0 => result == b` (symmetric)
//!
//! Core evaluation helpers (`eval_lit`, `eval_bits`, `eval_op`) and the
//! main `check()` method are in the parent module.

use super::*;

/// Complement of a CNF literal: `neg_lit(lit) == -lit` for every literal.
///
/// CNF literals are DIMACS `±var` with `var` in `1..=i32::MAX`, a domain on
/// which negation never overflows, so `wrapping_neg` is total and identical to
/// `-lit` there. This is the same form as ay-core's own literal complement
/// (`Tseitin::negate`, crates/ay-core/src/tseitin/mod.rs). `i32::MIN` is not a
/// literal of any variable; it is the one value `wrapping_neg` maps to itself.
#[inline]
const fn neg_lit(lit: CnfLit) -> CnfLit {
    lit.wrapping_neg()
}

/// An empty literal vector pre-sized for `capacity` literals. The reservation
/// is only a sizing hint, so it is made fallibly: a refused one forgoes it and
/// `push` grows the vector itself.
fn lits_with_capacity(capacity: usize) -> Vec<CnfLit> {
    let mut lits = Vec::new();
    let _ = lits.try_reserve_exact(capacity);
    lits
}

impl DelayedBvState {
    /// Check multiplication zero axiom. Returns clauses in BV literal space.
    pub(super) fn check_mul_zero(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        let zero = num_bigint::BigInt::from(0);
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);

        if result_val == zero {
            return None;
        }

        for &arg in &op.args {
            if let Some(bits) = self.term_to_bits.get(&arg) {
                let arg_val = self.eval_bits(bits, model, var_offset);
                if arg_val == zero {
                    // arg=0 but result!=0: clause: (some arg bit true) OR (all result bits false)
                    let mut lits: Vec<CnfLit> = Vec::new();
                    for &bit in bits {
                        lits.push(bit); // arg bit must be true
                    }
                    for &bit in &op.result_bits {
                        lits.push(neg_lit(bit)); // result bit must be false
                    }
                    return Some(vec![CnfClause::new(lits)]);
                }
            }
        }
        None
    }

    /// Check multiplication one axiom. Returns clauses in BV literal space.
    ///
    /// If arg[i] == 1, then result == arg[other]. This is encoded as
    /// implicational clauses with the antecedent "arg[i] != 1" so that
    /// the equality is only enforced when the argument IS one.
    ///
    /// Antecedent: negate "arg[i] == 1" (bit 0 true, all higher bits false).
    /// Negated: bit 0 false OR some higher bit true.
    pub(super) fn check_mul_one(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        let (arg0, arg1) = match op.args.as_slice() {
            [arg0, arg1] => (arg0, arg1),
            _ => return None,
        };
        let one = num_bigint::BigInt::from(1);

        // Each argument in turn, paired with the other one.
        for (arg, other) in [(arg0, arg1), (arg1, arg0)] {
            if let Some(bits) = self.term_to_bits.get(arg) {
                let arg_val = self.eval_bits(bits, model, var_offset);
                if arg_val == one {
                    if let Some(other_bits) = self.term_to_bits.get(other) {
                        let other_val = self.eval_bits(other_bits, model, var_offset);
                        let result_val = self.eval_bits(&op.result_bits, model, var_offset);

                        if result_val == other_val {
                            return None; // Consistent
                        }

                        // Antecedent: negate "arg == 1" => bit[0]=false OR bit[1]=true OR ...
                        // "arg == 1" means bit[0]=true and all higher bits false.
                        // Negation: bit[0]=false (push -bits[0]) OR any higher bit true (push bits[j]).
                        // `arg_val == 1` means `bits` has a true bit 0, so it is
                        // never empty here.
                        let (&bit0, higher) = bits.split_first()?;
                        let mut antecedent = lits_with_capacity(bits.len());
                        antecedent.push(neg_lit(bit0)); // bit 0 must be true, negated
                        for &b in higher {
                            antecedent.push(b); // higher bits must be false, positive = negated
                        }

                        // Implicational clauses: (arg != 1) OR (result[j] <=> other[j])
                        let mut clauses = Vec::new();
                        for (&r, &o) in op.result_bits.iter().zip(other_bits.iter()) {
                            let mut c1 = antecedent.clone();
                            c1.push(neg_lit(r));
                            c1.push(o);
                            clauses.push(CnfClause::new(c1));
                            let mut c2 = antecedent.clone();
                            c2.push(r);
                            c2.push(neg_lit(o));
                            clauses.push(CnfClause::new(c2));
                        }
                        return Some(clauses);
                    }
                }
            }
        }
        None
    }

    /// Check multiplication power-of-2 axiom (#8285).
    ///
    /// If model(a) is a power of 2 (= 2^k), then result == b << k.
    /// Symmetrically for model(b). This avoids building the full multiplier
    /// circuit for common patterns like `x * 4`, `8 * y`, etc.
    ///
    /// Reference: Z3's check_mul in bv_delay_internalize.cpp
    pub(super) fn check_mul_power_of_2(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        let (arg0, arg1) = match op.args.as_slice() {
            [arg0, arg1] => (arg0, arg1),
            _ => return None,
        };

        let width = op.result_bits.len();

        // Each argument in turn, paired with the other one.
        for (arg, other) in [(arg0, arg1), (arg1, arg0)] {
            let arg_bits = self.term_to_bits.get(arg)?;
            let arg_val = self.eval_bits(arg_bits, model, var_offset);

            // Check if arg_val is a power of 2
            if arg_val <= num_bigint::BigInt::from(0) {
                continue;
            }
            // A positive integer is a power of 2 iff (val & (val - 1)) == 0
            let val_minus_one = &arg_val - 1;
            if (&arg_val & &val_minus_one) != num_bigint::BigInt::from(0) {
                continue;
            }

            // arg_val == 2^k. Find k: a positive value has at least one bit.
            let Some(k) = usize::try_from(arg_val.bits())
                .ok()
                .and_then(|bits| bits.checked_sub(1))
            else {
                continue;
            };
            let other_bits = self.term_to_bits.get(other)?;

            // Compute expected: other << k, truncated to width
            let result_val = self.eval_bits(&op.result_bits, model, var_offset);
            let other_val = self.eval_bits(other_bits, model, var_offset);
            let mask = (num_bigint::BigInt::from(1) << width) - 1;
            let expected = (&other_val << k) & &mask;

            if result_val == expected {
                return None; // Already consistent
            }

            // Build implicational clauses:
            // (arg != 2^k) OR (result[j] <=> other[j-k] for j>=k, result[j]=0 for j<k)
            //
            // Antecedent: negate "arg == 2^k" -> at least one bit differs
            let mut antecedent = lits_with_capacity(arg_bits.len());
            for (bit_idx, &bit) in arg_bits.iter().enumerate() {
                if bit_idx == k {
                    antecedent.push(neg_lit(bit)); // bit k must be true, negated
                } else {
                    antecedent.push(bit); // other bits must be false, negated
                }
            }

            let mut clauses = Vec::new();
            let result_bits = &op.result_bits[..width];
            for (j, &result_bit) in result_bits.iter().enumerate() {
                if j < k {
                    // result[j] must be 0 (shifted out)
                    let mut c = antecedent.clone();
                    c.push(neg_lit(result_bit));
                    clauses.push(CnfClause::new(c));
                } else {
                    let src = j - k;
                    if src < other_bits.len() {
                        // result[j] <=> other[src]
                        let mut c1 = antecedent.clone();
                        c1.push(neg_lit(result_bit));
                        c1.push(other_bits[src]);
                        clauses.push(CnfClause::new(c1));
                        let mut c2 = antecedent.clone();
                        c2.push(result_bit);
                        c2.push(neg_lit(other_bits[src]));
                        clauses.push(CnfClause::new(c2));
                    } else {
                        // src out of range: result[j] must be 0
                        let mut c = antecedent.clone();
                        c.push(neg_lit(result_bit));
                        clauses.push(CnfClause::new(c));
                    }
                }
            }
            return Some(clauses);
        }
        None
    }

    /// Check multiplication invertibility: (y | -y) & z = z.
    /// Returns clauses in BV literal space.
    pub(super) fn check_mul_invertibility(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }

        let width = op.result_bits.len() as u32;
        let mask = (num_bigint::BigInt::from(1) << width) - 1;
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);

        for &arg in &op.args {
            if let Some(bits) = self.term_to_bits.get(&arg) {
                let arg_val = self.eval_bits(bits, model, var_offset);
                let neg_arg = ((!&arg_val) + 1) & &mask;
                let reach_mask = (&arg_val | &neg_arg) & &mask;
                let check = &reach_mask & &result_val;

                if check != result_val {
                    // Invertibility violated: block current assignment
                    let mut lits: Vec<CnfLit> = Vec::new();
                    for &bit in &op.result_bits {
                        let val = self.eval_lit(bit, model, var_offset);
                        lits.push(if val { neg_lit(bit) } else { bit });
                    }
                    for &bit in bits {
                        let val = self.eval_lit(bit, model, var_offset);
                        lits.push(if val { neg_lit(bit) } else { bit });
                    }
                    return Some(vec![CnfClause::new(lits)]);
                }
            }
        }
        None
    }

    /// Check div-by-one axiom: if divisor=1, then quotient=dividend.
    /// Applies to both bvudiv and bvsdiv. Returns clauses in BV literal space.
    pub(super) fn check_div_by_one(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let divisor_bits = self.term_to_bits.get(&op.args[1])?;
        let divisor_val = self.eval_bits(divisor_bits, model, var_offset);
        if divisor_val != num_bigint::BigInt::from(1) {
            return None;
        }

        // divisor=1 => quotient = dividend
        let dividend_bits = self.term_to_bits.get(&op.args[0])?;
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);
        let dividend_val = self.eval_bits(dividend_bits, model, var_offset);
        if result_val == dividend_val {
            return None; // Already consistent
        }

        // Implicational clauses: (divisor != 1) OR (result[j] <=> dividend[j])
        // Antecedent negated: bit[0]=0 OR bit[1]=1 OR ... OR consequent
        // `divisor_val == 1` means `divisor_bits` has a true bit 0, so it is
        // never empty here.
        let (&bit0, higher) = divisor_bits.split_first()?;
        let mut antecedent = lits_with_capacity(divisor_bits.len());
        antecedent.push(neg_lit(bit0)); // bit 0 must be true (negated)
        for &b in higher {
            antecedent.push(b); // higher bits must be false (positive = negated false)
        }
        let mut clauses = Vec::new();
        for (&res_bit, &div_bit) in op.result_bits.iter().zip(dividend_bits.iter()) {
            let mut c1 = antecedent.clone();
            c1.push(neg_lit(res_bit));
            c1.push(div_bit);
            clauses.push(CnfClause::new(c1));
            let mut c2 = antecedent.clone();
            c2.push(res_bit);
            c2.push(neg_lit(div_bit));
            clauses.push(CnfClause::new(c2));
        }
        Some(clauses)
    }

    /// Check rem-by-one axiom: if divisor=1, then remainder=0.
    /// Applies to both bvurem and bvsrem. Returns clauses in BV literal space.
    pub(super) fn check_rem_by_one(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let divisor_bits = self.term_to_bits.get(&op.args[1])?;
        let divisor_val = self.eval_bits(divisor_bits, model, var_offset);
        if divisor_val != num_bigint::BigInt::from(1) {
            return None;
        }

        // divisor=1 => remainder = 0
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);
        if result_val == num_bigint::BigInt::from(0) {
            return None; // Already consistent
        }

        // Implicational clauses: (divisor != 1) OR (result[j] = false)
        // `divisor_val == 1` means `divisor_bits` has a true bit 0, so it is
        // never empty here.
        let (&bit0, higher) = divisor_bits.split_first()?;
        let mut antecedent = lits_with_capacity(divisor_bits.len());
        antecedent.push(neg_lit(bit0));
        for &b in higher {
            antecedent.push(b);
        }
        let mut clauses = Vec::new();
        for &r_bit in &op.result_bits {
            let mut c = antecedent.clone();
            c.push(neg_lit(r_bit)); // result bit must be false
            clauses.push(CnfClause::new(c));
        }
        Some(clauses)
    }

    /// Check unsigned div-by-zero axiom: bvudiv(a, 0) = ~0 (all ones).
    /// SMT-LIB BV semantics. Returns clauses in BV literal space.
    pub(super) fn check_udiv_by_zero(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let divisor_bits = self.term_to_bits.get(&op.args[1])?;
        let divisor_val = self.eval_bits(divisor_bits, model, var_offset);
        if divisor_val != num_bigint::BigInt::from(0) {
            return None;
        }

        // divisor=0 => result = all ones
        let width = op.result_bits.len() as u32;
        let all_ones = (num_bigint::BigInt::from(1) << width) - 1;
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);
        if result_val == all_ones {
            return None; // Already consistent
        }

        // Implicational clauses: (some divisor bit true) OR (result[j] = true)
        let mut clauses = Vec::new();
        for &r_bit in &op.result_bits {
            let mut c: Vec<CnfLit> = divisor_bits.clone();
            c.push(r_bit); // result bit must be true
            clauses.push(CnfClause::new(c));
        }
        Some(clauses)
    }

    /// Check unsigned rem-by-zero axiom: bvurem(a, 0) = a (dividend).
    /// SMT-LIB BV semantics. Returns clauses in BV literal space.
    pub(super) fn check_urem_by_zero(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let divisor_bits = self.term_to_bits.get(&op.args[1])?;
        let divisor_val = self.eval_bits(divisor_bits, model, var_offset);
        if divisor_val != num_bigint::BigInt::from(0) {
            return None;
        }

        // divisor=0 => remainder = dividend
        let dividend_bits = self.term_to_bits.get(&op.args[0])?;
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);
        let dividend_val = self.eval_bits(dividend_bits, model, var_offset);
        if result_val == dividend_val {
            return None; // Already consistent
        }

        // Implicational clauses: (some divisor bit true) OR (result[j] <=> dividend[j])
        let mut clauses = Vec::new();
        for (&res_bit, &div_bit) in op.result_bits.iter().zip(dividend_bits.iter()) {
            let mut c1: Vec<CnfLit> = divisor_bits.clone();
            c1.push(neg_lit(res_bit));
            c1.push(div_bit);
            clauses.push(CnfClause::new(c1));
            let mut c2: Vec<CnfLit> = divisor_bits.clone();
            c2.push(res_bit);
            c2.push(neg_lit(div_bit));
            clauses.push(CnfClause::new(c2));
        }
        Some(clauses)
    }

    /// Check smod-by-one (or -1) axiom: bvsmod(a, 1) = 0 and bvsmod(a, -1) = 0.
    /// Returns clauses in BV literal space.
    pub(super) fn check_smod_by_one(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let divisor_bits = self.term_to_bits.get(&op.args[1])?;
        let divisor_val = self.eval_bits(divisor_bits, model, var_offset);

        let width = op.result_bits.len() as u32;
        let mask = (num_bigint::BigInt::from(1) << width) - 1;
        let one = num_bigint::BigInt::from(1);
        // -1 in two's complement = all ones
        let neg_one = &mask;

        if divisor_val != one && divisor_val != *neg_one {
            return None;
        }

        // divisor is 1 or -1 => result must be 0
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);
        if result_val == num_bigint::BigInt::from(0) {
            return None; // Already consistent
        }

        // Implicational: block current divisor assignment OR force result=0
        let mut divisor_block: Vec<CnfLit> = Vec::new();
        for &bit in divisor_bits.iter() {
            let val = self.eval_lit(bit, model, var_offset);
            divisor_block.push(if val { neg_lit(bit) } else { bit });
        }
        let mut clauses = Vec::new();
        for &r_bit in &op.result_bits {
            let mut c = divisor_block.clone();
            c.push(neg_lit(r_bit)); // result bit must be false (zero)
            clauses.push(CnfClause::new(c));
        }
        Some(clauses)
    }

    /// Check smod-by-zero axiom: bvsmod(a, 0) = a (dividend).
    /// SMT-LIB BV semantics. Returns clauses in BV literal space.
    pub(super) fn check_smod_by_zero(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let divisor_bits = self.term_to_bits.get(&op.args[1])?;
        let divisor_val = self.eval_bits(divisor_bits, model, var_offset);
        if divisor_val != num_bigint::BigInt::from(0) {
            return None;
        }

        // divisor=0 => result = dividend
        let dividend_bits = self.term_to_bits.get(&op.args[0])?;
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);
        let dividend_val = self.eval_bits(dividend_bits, model, var_offset);
        if result_val == dividend_val {
            return None; // Already consistent
        }

        // Implicational clauses: (some divisor bit true) OR (result[j] <=> dividend[j])
        // `zip` stops at the shorter of the two, the common width.
        let mut clauses = Vec::new();
        for (&rb, &db) in op.result_bits.iter().zip(dividend_bits.iter()) {
            let mut c1 = divisor_bits.clone();
            c1.push(neg_lit(rb));
            c1.push(db);
            clauses.push(CnfClause::new(c1));
            let mut c2 = divisor_bits.clone();
            c2.push(rb);
            c2.push(neg_lit(db));
            clauses.push(CnfClause::new(c2));
        }
        Some(clauses)
    }

    /// Check div-self axiom (#8285): if dividend == divisor, then quotient == 1.
    ///
    /// Applies to bvudiv only (signed division has sign complications).
    /// If both operands evaluate to the same non-zero value, the quotient must be 1.
    ///
    /// Reference: Z3's check_udiv in bv_delay_internalize.cpp
    pub(super) fn check_udiv_self(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let a_bits = self.term_to_bits.get(&op.args[0])?;
        let b_bits = self.term_to_bits.get(&op.args[1])?;
        let a_val = self.eval_bits(a_bits, model, var_offset);
        let b_val = self.eval_bits(b_bits, model, var_offset);

        if a_val != b_val || a_val == num_bigint::BigInt::from(0) {
            return None;
        }

        // a == b != 0 => result must be 1
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);
        if result_val == num_bigint::BigInt::from(1) {
            return None; // Already consistent
        }

        // Block current assignment of both operands and result.
        // This is a valid conflict clause: "the current values of a,b can't have this result"
        let mut lits: Vec<CnfLit> = Vec::new();
        for &bit in a_bits {
            let val = self.eval_lit(bit, model, var_offset);
            lits.push(if val { neg_lit(bit) } else { bit });
        }
        for &bit in b_bits {
            let val = self.eval_lit(bit, model, var_offset);
            lits.push(if val { neg_lit(bit) } else { bit });
        }
        for &bit in &op.result_bits {
            let val = self.eval_lit(bit, model, var_offset);
            lits.push(if val { neg_lit(bit) } else { bit });
        }
        Some(vec![CnfClause::new(lits)])
    }

    /// Check signed div-by-zero axiom (#8285): bvsdiv(a, 0).
    ///
    /// SMT-LIB semantics: bvsdiv(a, 0) = if a < 0 then 1 else (2^w - 1).
    /// Returns clauses in BV literal space.
    pub(super) fn check_sdiv_by_zero(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let divisor_bits = self.term_to_bits.get(&op.args[1])?;
        let divisor_val = self.eval_bits(divisor_bits, model, var_offset);
        if divisor_val != num_bigint::BigInt::from(0) {
            return None;
        }

        let width = op.result_bits.len() as u32;
        let a_bits = self.term_to_bits.get(&op.args[0])?;
        let a_val = self.eval_bits(a_bits, model, var_offset);

        // Check sign of a: if MSB is set, a is negative. A BV result has at
        // least one bit, so the MSB index exists for every real operation.
        let msb_idx = width.checked_sub(1)?;
        let half = num_bigint::BigInt::from(1) << msb_idx;
        let a_is_negative = a_val >= half;
        let expected = if a_is_negative {
            // a negative => result = 1
            num_bigint::BigInt::from(1)
        } else {
            // a non-negative => result = 2^w - 1 (all ones)
            (num_bigint::BigInt::from(1) << width) - 1
        };

        let result_val = self.eval_bits(&op.result_bits, model, var_offset);
        if result_val == expected {
            return None; // Already consistent
        }

        // MSB literal of operand a — used as sign antecedent in each clause.
        // The clause must be conditioned on the sign of a because the expected
        // result differs between positive and negative operands (#8371).
        let a_msb = *a_bits.get(usize::try_from(msb_idx).ok()?)?;
        // Antecedent literal: negate the current sign so the clause fires only
        // when a has the same sign as in this model evaluation.
        // If a is negative (MSB=true), add -a_msb (clause fires when MSB is true).
        // If a is non-negative (MSB=false), add a_msb (clause fires when MSB is false).
        let sign_antecedent = if a_is_negative { neg_lit(a_msb) } else { a_msb };

        // Block: (some divisor bit true) OR (sign mismatch) OR (result matches expected)
        // For each result bit, constrain to expected value
        let mut clauses = Vec::new();
        for (j, &r_bit) in op.result_bits.iter().enumerate() {
            let expected_bit = (&expected >> j) & num_bigint::BigInt::from(1);
            let mut c: Vec<CnfLit> = divisor_bits.clone(); // some divisor bit true
            c.push(sign_antecedent); // sign of a must match
            if expected_bit == num_bigint::BigInt::from(1) {
                c.push(r_bit); // result bit must be true
            } else {
                c.push(neg_lit(r_bit)); // result bit must be false
            }
            clauses.push(CnfClause::new(c));
        }
        Some(clauses)
    }

    /// Check signed rem-by-zero axiom (#8285): bvsrem(a, 0) = a.
    ///
    /// SMT-LIB semantics: bvsrem(a, 0) = a.
    /// Returns clauses in BV literal space.
    pub(super) fn check_srem_by_zero(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let divisor_bits = self.term_to_bits.get(&op.args[1])?;
        let divisor_val = self.eval_bits(divisor_bits, model, var_offset);
        if divisor_val != num_bigint::BigInt::from(0) {
            return None;
        }

        // divisor=0 => remainder = dividend
        let dividend_bits = self.term_to_bits.get(&op.args[0])?;
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);
        let dividend_val = self.eval_bits(dividend_bits, model, var_offset);
        if result_val == dividend_val {
            return None; // Already consistent
        }

        // Implicational clauses: (some divisor bit true) OR (result[j] <=> dividend[j])
        // `zip` stops at the shorter of the two, the common width.
        let mut clauses = Vec::new();
        for (&rb, &db) in op.result_bits.iter().zip(dividend_bits.iter()) {
            let mut c1 = divisor_bits.clone();
            c1.push(neg_lit(rb));
            c1.push(db);
            clauses.push(CnfClause::new(c1));
            let mut c2 = divisor_bits.clone();
            c2.push(rb);
            c2.push(neg_lit(db));
            clauses.push(CnfClause::new(c2));
        }
        Some(clauses)
    }

    /// Check add-by-zero axiom: bvadd(a, 0) = a or bvadd(0, b) = b.
    /// Returns clauses in BV literal space.
    pub(super) fn check_add_zero(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        let (arg0, arg1) = match op.args.as_slice() {
            [arg0, arg1] => (arg0, arg1),
            _ => return None,
        };
        let zero = num_bigint::BigInt::from(0);

        // Each argument in turn, paired with the other one.
        for (arg, other) in [(arg0, arg1), (arg1, arg0)] {
            if let Some(bits) = self.term_to_bits.get(arg) {
                let arg_val = self.eval_bits(bits, model, var_offset);
                if arg_val == zero {
                    if let Some(other_bits) = self.term_to_bits.get(other) {
                        let other_val = self.eval_bits(other_bits, model, var_offset);
                        let result_val = self.eval_bits(&op.result_bits, model, var_offset);

                        if result_val == other_val {
                            return None; // Consistent
                        }

                        // arg=0 => result = other: antecedent negation of all-zero
                        let mut antecedent: Vec<CnfLit> = Vec::new();
                        for &b in bits.iter() {
                            antecedent.push(b); // positive = "some bit is true"
                        }
                        // `zip` stops at the shorter of the two, the common width.
                        let mut clauses = Vec::new();
                        for (&rb, &ob) in op.result_bits.iter().zip(other_bits.iter()) {
                            let mut c1 = antecedent.clone();
                            c1.push(neg_lit(rb));
                            c1.push(ob);
                            clauses.push(CnfClause::new(c1));
                            let mut c2 = antecedent.clone();
                            c2.push(rb);
                            c2.push(neg_lit(ob));
                            clauses.push(CnfClause::new(c2));
                        }
                        return Some(clauses);
                    }
                }
            }
        }
        None
    }
}
