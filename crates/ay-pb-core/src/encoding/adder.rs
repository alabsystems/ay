// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Binary adder network PB-to-CNF encoding.
//!
//! Encodes a PB constraint by building a binary adder circuit that computes
//! the weighted sum in binary, then compares the result against the threshold.
//!
//! This encoding is useful for constraints with very large coefficients where
//! BDD/totalizer size would explode, since the adder size is proportional to
//! n * log(max_coeff) rather than n * rhs.
//!
//! # Approach
//!
//! 1. Represent each term `c_i * l_i` as a binary number gated by `l_i`.
//! 2. Add all gated numbers using a tree of binary ripple-carry adders.
//! 3. Compare the result against `rhs` using a binary comparator.
//!
//! # References
//! - Warners, "A Linear-Time Transformation of Linear Inequalities into CNF", 1998
//! - Een & Sorensson, "Translating Pseudo-Boolean Constraints into SAT", 2006

/// Encodes a normalized `sum(coeffs[i] * lits[i]) >= rhs` using binary adder networks.
///
/// All coefficients must be positive and `rhs > 0`.
/// Clauses are appended to `clauses`; new variables are allocated via `next_var`.
pub(crate) fn encode_adder(
    coeffs: &[i128],
    lits: &[i32],
    rhs: i128,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
) {
    let n = coeffs.len();
    debug_assert!(n > 0);
    debug_assert!(rhs > 0);
    debug_assert!(coeffs.iter().all(|&c| c > 0));

    // Determine the number of bits needed to represent the maximum possible sum.
    let max_sum: i128 = coeffs.iter().sum();
    let num_bits = bit_width(max_sum);

    // Step 1: Create gated binary representations for each term.
    // c_i * l_i in binary: bit j of c_i is ANDed with l_i.
    let mut binary_numbers: Vec<Vec<i32>> = Vec::with_capacity(n);
    for i in 0..n {
        let mut bits = Vec::with_capacity(num_bits);
        for j in 0..num_bits {
            if (coeffs[i] >> j) & 1 == 1 {
                // Bit j of c_i is 1, so this bit equals l_i.
                bits.push(lits[i]);
            } else {
                // Bit j of c_i is 0, so this bit is always 0 (represented as 0).
                bits.push(0); // sentinel for constant false
            }
        }
        binary_numbers.push(bits);
    }

    // Step 2: Add all binary numbers using a tree of adders.
    let result = tree_add(&binary_numbers, num_bits, clauses, next_var);

    // Step 3: Assert result >= rhs using a binary comparator.
    encode_ge_comparator(&result, rhs, num_bits, clauses, next_var);
}

/// Returns the number of bits needed to represent `val`.
fn bit_width(val: i128) -> usize {
    if val <= 0 {
        return 1;
    }
    // `val` is i128 (128 bits): use i128::BITS, not a hardcoded 64. With 64 here,
    // a small positive i128 (leading_zeros ~125) underflows `64 - lz` to a huge
    // usize, making the adder allocate billions of bits (OOM).
    (i128::BITS - val.leading_zeros()) as usize
}

/// Adds all binary numbers using a balanced tree of ripple-carry adders.
fn tree_add(
    numbers: &[Vec<i32>],
    num_bits: usize,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
) -> Vec<i32> {
    if numbers.len() == 1 {
        return numbers[0].clone();
    }

    let mut current = numbers.to_vec();

    while current.len() > 1 {
        let mut next_level = Vec::with_capacity(current.len().div_ceil(2));
        let mut i = 0;
        while i < current.len() {
            if i + 1 < current.len() {
                let sum =
                    ripple_carry_add(&current[i], &current[i + 1], num_bits, clauses, next_var);
                next_level.push(sum);
                i += 2;
            } else {
                next_level.push(current[i].clone());
                i += 1;
            }
        }
        current = next_level;
    }

    current
        .into_iter()
        .next()
        .expect("invariant: at least one number")
}

/// Ripple-carry adder: adds two binary numbers bit by bit.
///
/// Returns a vector of DIMACS literals representing the sum bits.
/// Each bit is an auxiliary variable (or 0 for constant false, or a literal
/// for a direct pass-through).
fn ripple_carry_add(
    a: &[i32],
    b: &[i32],
    num_bits: usize,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
) -> Vec<i32> {
    let max_bits = a.len().max(b.len()).max(num_bits);
    let mut result = Vec::with_capacity(max_bits + 1);
    let mut carry: i32 = 0; // 0 = constant false

    for j in 0..max_bits {
        let a_bit = if j < a.len() { a[j] } else { 0 };
        let b_bit = if j < b.len() { b[j] } else { 0 };

        let (sum_bit, new_carry) = full_adder(a_bit, b_bit, carry, clauses, next_var);
        result.push(sum_bit);
        carry = new_carry;
    }

    // Include the final carry as the MSB if it's not constant false.
    if carry != 0 {
        result.push(carry);
    }

    result
}

/// Full adder for three bits (a, b, carry_in), producing (sum, carry_out).
///
/// Handles constant-false inputs (represented as 0) specially to avoid
/// unnecessary auxiliary variables.
fn full_adder(
    a: i32,
    b: i32,
    c: i32,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
) -> (i32, i32) {
    // Count how many inputs are constant false.
    let non_zero = [a, b, c].iter().filter(|&&x| x != 0).count();

    match non_zero {
        0 => (0, 0), // 0 + 0 + 0 = 0, carry 0
        1 => {
            // One non-zero input: sum = that input, carry = 0.
            let the_one = if a != 0 {
                a
            } else if b != 0 {
                b
            } else {
                c
            };
            (the_one, 0)
        }
        2 => {
            // Two non-zero inputs: half adder.
            let (x, y) = if a != 0 && b != 0 {
                (a, b)
            } else if a != 0 {
                (a, c)
            } else {
                (b, c)
            };
            half_adder(x, y, clauses, next_var)
        }
        3 => {
            // All three non-zero: full adder circuit.
            // sum = a XOR b XOR c
            // carry = (a AND b) OR (a AND c) OR (b AND c) = majority(a, b, c)

            let sum_var = *next_var as i32;
            *next_var += 1;
            let carry_var = *next_var as i32;
            *next_var += 1;

            // Encode sum = a XOR b XOR c.
            // sum is true when an odd number of {a, b, c} are true.
            // Clauses for XOR of three variables:
            // sum -> (a OR b OR c) AND (!a OR !b OR c) AND (!a OR b OR !c) AND (a OR !b OR !c)
            // !sum -> (!a OR !b OR !c) AND (a OR b OR !c) AND (a OR !b OR c) AND (!a OR b OR c)
            //
            // Combined: 8 clauses.
            clauses.push(vec![-sum_var, a, b, c]); // sum -> at least one true
            clauses.push(vec![-sum_var, -a, -b, c]); // sum -> not(a,b both true with c false)
            clauses.push(vec![-sum_var, -a, b, -c]);
            clauses.push(vec![-sum_var, a, -b, -c]);
            clauses.push(vec![sum_var, -a, -b, -c]); // !sum -> not all true
            clauses.push(vec![sum_var, a, b, -c]); // !sum -> clauses for even parity
            clauses.push(vec![sum_var, a, -b, c]);
            clauses.push(vec![sum_var, -a, b, c]);

            // Encode carry = majority(a, b, c).
            // carry is true when at least 2 of {a, b, c} are true.
            // carry -> (a OR b) AND (a OR c) AND (b OR c)
            // !carry -> (!a OR !b) AND (!a OR !c) AND (!b OR !c)
            clauses.push(vec![-carry_var, a, b]);
            clauses.push(vec![-carry_var, a, c]);
            clauses.push(vec![-carry_var, b, c]);
            clauses.push(vec![carry_var, -a, -b]);
            clauses.push(vec![carry_var, -a, -c]);
            clauses.push(vec![carry_var, -b, -c]);

            (sum_var, carry_var)
        }
        _ => unreachable!(),
    }
}

/// Half adder for two bits: sum = a XOR b, carry = a AND b.
fn half_adder(a: i32, b: i32, clauses: &mut Vec<Vec<i32>>, next_var: &mut u32) -> (i32, i32) {
    let sum_var = *next_var as i32;
    *next_var += 1;
    let carry_var = *next_var as i32;
    *next_var += 1;

    // sum = a XOR b
    // sum -> (a OR b), sum -> (!a OR !b)
    // !sum -> (!a OR b), !sum -> (a OR !b)
    clauses.push(vec![-sum_var, a, b]);
    clauses.push(vec![-sum_var, -a, -b]);
    clauses.push(vec![sum_var, -a, b]);
    clauses.push(vec![sum_var, a, -b]);

    // carry = a AND b
    clauses.push(vec![-carry_var, a]);
    clauses.push(vec![-carry_var, b]);
    clauses.push(vec![carry_var, -a, -b]);

    (sum_var, carry_var)
}

/// Encodes `result >= rhs` where `result` is a binary number represented
/// as a vector of DIMACS bit variables (LSB first).
fn encode_ge_comparator(
    result_bits: &[i32],
    rhs: i128,
    _num_bits: usize,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
) {
    let n = result_bits.len();

    // ge[i] means "the comparison of bits i..n concludes result >= rhs"
    // (considering bits from MSB down to bit i).
    //
    // We process from MSB to LSB. At each bit position:
    // - If rhs bit is 1: result bit must be 1, or a higher bit was already >
    // - If rhs bit is 0: result bit being 1 gives us slack, being 0 continues
    //
    // Use a chain of auxiliary "at least as large from bit i up" variables.
    // g[i] = 1 means "result[i..] >= rhs[i..]" (suffix comparison).
    // e[i] = 1 means "result[i..] == rhs[i..]" (suffix equality).

    // Allocate g[i] and e[i] for i in 0..n.
    let g_base = *next_var;
    *next_var += n as u32;
    let e_base = *next_var;
    *next_var += n as u32;

    let g = |i: usize| -> i32 { (g_base + i as u32) as i32 };
    let e = |i: usize| -> i32 { (e_base + i as u32) as i32 };

    // Process from MSB (bit n-1) down to LSB (bit 0).
    for i in (0..n).rev() {
        let r_bit = result_bits[i]; // DIMACS literal for this bit
        let rhs_bit = (rhs >> i) & 1 == 1;

        if i == n - 1 {
            // MSB: g[n-1] iff result_bit > rhs_bit or (result_bit == rhs_bit, trivially ge from suffix)
            if rhs_bit {
                // rhs MSB = 1: g[n-1] iff result_bit = 1
                if r_bit == 0 {
                    // Result bit is constant 0, rhs bit is 1: impossible to be >=
                    // g[n-1] = false
                    clauses.push(vec![-g(i)]);
                    clauses.push(vec![-e(i)]);
                } else {
                    // g[n-1] <-> r_bit (which means result MSB is 1)
                    clauses.push(vec![-g(i), r_bit]);
                    clauses.push(vec![g(i), -r_bit]);
                    // e[n-1] <-> r_bit (both are 1)
                    clauses.push(vec![-e(i), r_bit]);
                    clauses.push(vec![e(i), -r_bit]);
                }
            } else {
                // rhs MSB = 0: g[n-1] always true (result MSB >= 0)
                clauses.push(vec![g(i)]);
                // e[n-1] <-> !r_bit (both are 0)
                if r_bit == 0 {
                    clauses.push(vec![e(i)]); // constant 0 == 0
                } else {
                    clauses.push(vec![-e(i), -r_bit]);
                    clauses.push(vec![e(i), r_bit]);
                }
            }
        } else {
            // Non-MSB bit: g[i] <-> (g[i+1] AND NOT e[i+1]) OR (e[i+1] AND result_bit >= rhs_bit)
            // Simplified: g[i] <-> (result[i+1..] > rhs[i+1..]) OR (result[i+1..] == rhs[i+1..] AND result[i] >= rhs[i])
            //
            // Let "strictly_greater" = g[i+1] AND NOT e[i+1]
            // g[i] <-> strictly_greater OR (e[i+1] AND current_ge)
            // where current_ge = (result_bit >= rhs_bit)

            if rhs_bit {
                // rhs bit = 1: current_ge iff result_bit = 1
                if r_bit == 0 {
                    // current_ge is false, current_eq is false
                    // g[i] <-> strictly_greater = g[i+1] AND NOT e[i+1]
                    // But actually: g[i] <-> g[i+1] AND NOT e[i+1]
                    // because the only way to be >= is to have been strictly greater above
                    clauses.push(vec![-g(i), g(i + 1)]);
                    clauses.push(vec![-g(i), -e(i + 1)]);
                    clauses.push(vec![g(i), -g(i + 1), e(i + 1)]);
                    // e[i] = false (result bit 0 != rhs bit 1)
                    clauses.push(vec![-e(i)]);
                } else {
                    // current_ge iff r_bit = true
                    // g[i] <-> (g[i+1] AND NOT e[i+1]) OR (e[i+1] AND r_bit)
                    // Forward: g[i+1] AND NOT e[i+1] -> g[i]
                    clauses.push(vec![-g(i + 1), e(i + 1), g(i)]);
                    // Forward: e[i+1] AND r_bit -> g[i]
                    clauses.push(vec![-e(i + 1), -r_bit, g(i)]);
                    // Backward: g[i] -> g[i+1]
                    clauses.push(vec![-g(i), g(i + 1)]);
                    // Backward: g[i] AND e[i+1] -> r_bit
                    clauses.push(vec![-g(i), -e(i + 1), r_bit]);

                    // e[i] <-> e[i+1] AND r_bit
                    clauses.push(vec![-e(i), e(i + 1)]);
                    clauses.push(vec![-e(i), r_bit]);
                    clauses.push(vec![e(i), -e(i + 1), -r_bit]);
                }
            } else {
                // rhs bit = 0: current_ge is always true, current_eq iff result_bit = 0
                // g[i] <-> (g[i+1] AND NOT e[i+1]) OR e[i+1] = g[i+1]
                // Because: either strictly greater above, or equal above and current >= 0 (always true)
                clauses.push(vec![-g(i), g(i + 1)]);
                clauses.push(vec![g(i), -g(i + 1)]);

                // e[i] <-> e[i+1] AND NOT result_bit
                if r_bit == 0 {
                    // result_bit is constant 0: e[i] <-> e[i+1]
                    clauses.push(vec![-e(i), e(i + 1)]);
                    clauses.push(vec![e(i), -e(i + 1)]);
                } else {
                    clauses.push(vec![-e(i), e(i + 1)]);
                    clauses.push(vec![-e(i), -r_bit]);
                    clauses.push(vec![e(i), -e(i + 1), r_bit]);
                }
            }
        }
    }

    // The constraint is satisfied iff g[0] is true.
    clauses.push(vec![g(0)]);
}
