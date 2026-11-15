// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Hard resource ceilings and cost accounting for the post-SAT array FC audit.

use ay_bv::BvBits;

pub(super) const MAX_TERMS: usize = 250_000;
pub(super) const MAX_TERM_BITS: usize = 250_000;
pub(super) const MAX_SELECTS: usize = 8_192;
pub(super) const MAX_SINGLE_WIDTH: usize = 16_384;
pub(super) const MAX_TOTAL_BITS: usize = 2_000_000;
pub(super) const MAX_PAIR_ATTEMPTS: usize = 16_384;
pub(super) const MAX_NEW_VARS: usize = 262_144;
pub(super) const MAX_NEW_CLAUSES: usize = 524_288;

pub(super) fn pair_cost(
    idx_a_bits: &BvBits,
    idx_b_bits: &BvBits,
    sel_a_bits: &BvBits,
    sel_b_bits: &BvBits,
    stored_idx_bits: &[BvBits],
) -> Option<(usize, usize)> {
    if idx_a_bits.is_empty()
        || idx_a_bits.len() != idx_b_bits.len()
        || sel_a_bits.is_empty()
        || sel_a_bits.len() != sel_b_bits.len()
    {
        return None;
    }
    // Each avoided stored index pays its own diff/eq definition:
    // `d` differing bits -> d+1 fresh vars, 5d+1 clauses.
    let mut variables = 0usize;
    let mut clauses = 0usize;
    for stored in stored_idx_bits {
        if stored.len() != idx_a_bits.len() {
            return None;
        }
        let d = idx_a_bits
            .iter()
            .zip(stored.iter())
            .filter(|(left, right)| left != right)
            .count();
        variables = variables.checked_add(d.checked_add(1)?)?;
        clauses = clauses.checked_add(d.checked_mul(5)?.checked_add(1)?)?;
    }
    let diff_bits = idx_a_bits
        .iter()
        .zip(idx_b_bits.iter())
        .filter(|(left, right)| left != right)
        .count();
    let unequal_value_bits = sel_a_bits
        .iter()
        .zip(sel_b_bits.iter())
        .filter(|(left, right)| left != right)
        .count();
    clauses = clauses.checked_add(unequal_value_bits.checked_mul(2)?)?;
    if diff_bits == 0 {
        return Some((variables, clauses));
    }
    variables = variables.checked_add(diff_bits.checked_add(1)?)?;
    clauses = clauses.checked_add(diff_bits.checked_mul(5)?.checked_add(1)?)?;
    Some((variables, clauses))
}

#[cfg(test)]
mod tests {
    use super::pair_cost;
    use ay_bv::BvBits;

    fn bits(values: &[i32]) -> BvBits {
        values.to_vec()
    }

    #[test]
    fn counts_identical_indices_without_fresh_variables() {
        let index = bits(&[1, 2]);
        let left = bits(&[3, 4, 5]);
        let right = bits(&[3, -4, 6]);
        assert_eq!(pair_cost(&index, &index, &left, &right, &[]), Some((0, 4)));
    }

    #[test]
    fn counts_xor_definition_and_value_implications() {
        let left_index = bits(&[1, 2, 3]);
        let right_index = bits(&[1, -2, -3]);
        let left_value = bits(&[4, 5]);
        let right_value = bits(&[-4, 5]);
        assert_eq!(
            pair_cost(&left_index, &right_index, &left_value, &right_value, &[]),
            Some((3, 13))
        );
    }

    #[test]
    fn counts_stored_diseq_definitions() {
        // Identical select indices: stored definitions still cost
        // (d differing bits -> d+1 vars, 5d+1 clauses each).
        let index = bits(&[1, 2]);
        let left = bits(&[3]);
        let right = bits(&[-3]);
        let stored = vec![bits(&[1, -2]), bits(&[9, 10])];
        // stored[0]: d=1 -> (2, 6); stored[1]: d=2 -> (3, 11);
        // value implications: 2. Total (5, 19).
        assert_eq!(
            pair_cost(&index, &index, &left, &right, &stored),
            Some((5, 19))
        );
        // Width-mismatched stored bits are rejected.
        assert_eq!(
            pair_cost(&index, &index, &left, &right, &[bits(&[1])]),
            None
        );
    }

    #[test]
    fn rejects_zero_or_mismatched_widths() {
        assert_eq!(
            pair_cost(&bits(&[]), &bits(&[]), &bits(&[1]), &bits(&[2]), &[]),
            None
        );
        assert_eq!(
            pair_cost(&bits(&[1]), &bits(&[1, 2]), &bits(&[3]), &bits(&[4]), &[]),
            None
        );
        assert_eq!(
            pair_cost(&bits(&[1]), &bits(&[2]), &bits(&[3]), &bits(&[4, 5]), &[]),
            None
        );
    }
}
