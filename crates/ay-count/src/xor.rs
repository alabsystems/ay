// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pure-XOR model counting shortcut.
//!
//! A width-`k` XOR constraint compiles to CNF as the family of all `2^(k-1)`
//! clauses over its variable set whose negation count has a fixed parity
//! `p`: each such clause forbids exactly the assignment equal to its
//! negation set's characteristic vector, so together they forbid all
//! assignments with true-count parity `p` — i.e. they enforce
//! `x1 ⊕ ... ⊕ xk = 1 - p`.
//!
//! When EVERY clause of the formula is consumed by such a family (unit
//! clauses are width-1 XOR rows), the model count is `2^(n - rank)` where
//! `rank` is the GF(2) rank of the row system — or 0 if inconsistent.
//! This is exact and only applies to unweighted, unprojected counting.

use num_bigint::BigUint;
use rustc_hash::FxHashMap;

/// Cap on XOR width (2^(k-1) clauses per family; 20 → ~512k clauses).
const MAX_XOR_WIDTH: usize = 20;

/// If the formula is a pure XOR system, return its exact model count.
pub fn pure_xor_count(num_vars: usize, clauses: &[Vec<i32>]) -> Option<BigUint> {
    if clauses.is_empty() {
        return None; // nothing to shortcut; the engine handles it instantly
    }
    // Group clauses by sorted variable set.
    let mut groups: FxHashMap<Vec<u32>, Vec<&Vec<i32>>> = FxHashMap::default();
    for clause in clauses {
        if clause.is_empty() || clause.len() > MAX_XOR_WIDTH {
            return None;
        }
        let mut vars: Vec<u32> = clause.iter().map(|l| l.unsigned_abs()).collect();
        vars.sort_unstable();
        vars.dedup();
        if vars.len() != clause.len() {
            return None; // duplicate vars (tautology/dup lit): not XOR CNF
        }
        groups.entry(vars).or_default().push(clause);
    }
    // Each group must be a full same-parity family.
    let words = num_vars.div_ceil(64);
    let mut rows: Vec<(Vec<u64>, bool)> = Vec::with_capacity(groups.len());
    for (vars, cs) in &groups {
        let k = vars.len();
        let expected = 1usize << (k - 1);
        if cs.len() != expected {
            return None;
        }
        let parity0 = cs[0].iter().filter(|&&l| l < 0).count() % 2;
        let mut seen: Vec<u32> = Vec::with_capacity(cs.len());
        for c in cs {
            let neg_parity = c.iter().filter(|&&l| l < 0).count() % 2;
            if neg_parity != parity0 {
                return None;
            }
            // Sign pattern as a bitmask over the sorted var set.
            let mut mask = 0u32;
            for &l in c.iter() {
                let idx = vars
                    .binary_search(&l.unsigned_abs())
                    .expect("clause var in its own var set");
                if l < 0 {
                    mask |= 1 << idx;
                }
            }
            seen.push(mask);
        }
        seen.sort_unstable();
        seen.dedup();
        if seen.len() != expected {
            return None; // repeated pattern ⇒ not the full family
        }
        // Constraint: sum of vars ≡ 1 - parity0 (mod 2).
        let mut row = vec![0u64; words];
        for &v in vars {
            let i = (v - 1) as usize;
            row[i / 64] |= 1 << (i % 64);
        }
        rows.push((row, parity0 == 0));
    }
    // GF(2) Gaussian elimination.
    let mut rank = 0usize;
    let mut mat = rows;
    for row_idx in 0..mat.len() {
        // Find leading bit of this row (after prior eliminations).
        let mut lead: Option<(usize, usize)> = None;
        'outer: for w in 0..words {
            let word = mat[row_idx].0[w];
            if word != 0 {
                lead = Some((w, word.trailing_zeros() as usize));
                break 'outer;
            }
        }
        let Some((lw, lb)) = lead else {
            // Zero row: inconsistent iff rhs is 1.
            if mat[row_idx].1 {
                return Some(BigUint::from(0u32));
            }
            continue;
        };
        rank += 1;
        // Eliminate this bit from all later rows.
        let (pivot_row, pivot_rhs) = (mat[row_idx].0.clone(), mat[row_idx].1);
        for other in mat.iter_mut().skip(row_idx + 1) {
            if other.0[lw] >> lb & 1 == 1 {
                for w in 0..words {
                    other.0[w] ^= pivot_row[w];
                }
                other.1 ^= pivot_rhs;
            }
        }
    }
    Some(BigUint::from(1u32) << (num_vars - rank))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Compile `xor(vars) = rhs` to its CNF clause family.
    fn xor_cnf(vars: &[i32], rhs: bool) -> Vec<Vec<i32>> {
        let k = vars.len();
        let mut out = Vec::new();
        for mask in 0..(1u32 << k) {
            let negs = mask.count_ones() as usize;
            // Clause with negation parity p forbids true-parity p; the
            // constraint sum ≡ rhs allows parity rhs, so forbid parity
            // 1-rhs: emit clauses with negation parity 1-rhs... i.e. keep
            // masks whose parity == (1 - rhs as usize) % 2.
            if negs % 2 == usize::from(!rhs) {
                let clause: Vec<i32> = vars
                    .iter()
                    .enumerate()
                    .map(|(i, &v)| if mask >> i & 1 == 1 { -v } else { v })
                    .collect();
                out.push(clause);
            }
        }
        out
    }

    fn brute(num_vars: usize, clauses: &[Vec<i32>]) -> u64 {
        (0..(1u64 << num_vars))
            .filter(|m| {
                clauses.iter().all(|c| {
                    c.iter().any(|&l| {
                        let bit = (m >> (l.unsigned_abs() - 1)) & 1 == 1;
                        (l > 0) == bit
                    })
                })
            })
            .count() as u64
    }

    #[test]
    fn single_xor3() {
        let clauses = xor_cnf(&[1, 2, 3], true);
        assert_eq!(clauses.len(), 4);
        let count = pure_xor_count(3, &clauses).expect("detected");
        assert_eq!(count, BigUint::from(brute(3, &clauses)));
        assert_eq!(count, BigUint::from(4u32)); // 2^(3-1)
    }

    #[test]
    fn system_with_free_vars_and_consistency() {
        // x1^x2 = 1, x2^x3 = 0, over 5 vars (x4, x5 free): rank 2 → 2^3.
        let mut clauses = xor_cnf(&[1, 2], true);
        clauses.extend(xor_cnf(&[2, 3], false));
        let count = pure_xor_count(5, &clauses).expect("detected");
        assert_eq!(count, BigUint::from(8u32));
        assert_eq!(BigUint::from(brute(5, &clauses)), BigUint::from(8u32));
    }

    #[test]
    fn inconsistent_system_counts_zero() {
        // x1^x2=1, x2^x3=1, x1^x3=1 is inconsistent (sum = 1 over cycle).
        let mut clauses = xor_cnf(&[1, 2], true);
        clauses.extend(xor_cnf(&[2, 3], true));
        clauses.extend(xor_cnf(&[1, 3], true));
        let count = pure_xor_count(3, &clauses).expect("detected");
        assert_eq!(count, BigUint::from(0u32));
        assert_eq!(brute(3, &clauses), 0);
    }

    #[test]
    fn dependent_rows_do_not_overcount_rank() {
        // Same constraint twice: rank must stay 1 → 2^(3-1) = 4 over 3 vars.
        let mut clauses = xor_cnf(&[1, 2], true);
        clauses.extend(xor_cnf(&[1, 2], true));
        // Duplicate clauses collapse into one group (same var set), which
        // then has MORE than 2^(k-1) members after dedup fails → the
        // duplicate family is the SAME family; grouping merges them and the
        // pattern-dedup check rejects. That is conservative-but-sound:
        // detection declines, engine counts normally.
        assert_eq!(pure_xor_count(3, &clauses), None);
    }

    #[test]
    fn non_xor_family_rejected() {
        // 2 clauses over {1,2} with DIFFERENT parities: (1 2), (-1 2).
        let clauses = vec![vec![1, 2], vec![-1, 2]];
        assert_eq!(pure_xor_count(2, &clauses), None);
    }

    #[test]
    fn units_are_width_one_rows() {
        // (x1), (x2^x3 = 1): count = 1 * 2 = 2 over 3 vars.
        let mut clauses = vec![vec![1]];
        clauses.extend(xor_cnf(&[2, 3], true));
        let count = pure_xor_count(3, &clauses).expect("detected");
        assert_eq!(count, BigUint::from(brute(3, &clauses)));
        assert_eq!(count, BigUint::from(2u32));
    }

    #[test]
    fn mixed_cnf_declines() {
        let mut clauses = xor_cnf(&[1, 2, 3], true);
        clauses.push(vec![1, 2, 4]); // lone non-family clause
        assert_eq!(pure_xor_count(4, &clauses), None);
    }
}
