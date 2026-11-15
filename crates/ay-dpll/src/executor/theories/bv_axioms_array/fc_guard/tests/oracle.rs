// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

//! Frozen FC guard emission from 70dea3edf, before cross-array sharing.
//! No current cache or extracted emitter is called by this oracle.

use super::*;

pub(super) fn emit(
    (left, right): (&[i32], &[i32]),
    bv: &BvSolver<'_>,
    offset: u32,
    next: &mut u32,
    result: &mut ArrayAxiomResult,
) -> i32 {
    let mut differences = Vec::with_capacity(left.len());
    for (&left_bit, &right_bit) in left.iter().zip(right) {
        let v1 = bv.bit_constant_value(left_bit);
        let v2 = bv.bit_constant_value(right_bit);
        if let (Some(c1), Some(c2)) = (v1, v2) {
            if c1 == c2 {
                continue;
            }
        }
        let ob1 = offset_bv_bit(left_bit, offset);
        let ob2 = offset_bv_bit(right_bit, offset);
        let difference = *next as i32;
        *next += 1;
        differences.push(difference);
        result
            .clauses
            .push(CnfClause::new(vec![-difference, ob1, ob2]));
        result
            .clauses
            .push(CnfClause::new(vec![-difference, -ob1, -ob2]));
        result
            .clauses
            .push(CnfClause::new(vec![-ob1, ob2, difference]));
        result
            .clauses
            .push(CnfClause::new(vec![ob1, -ob2, difference]));
    }
    let guard = *next as i32;
    *next += 1;
    for &difference in &differences {
        result
            .clauses
            .push(CnfClause::new(vec![-guard, -difference]));
    }
    let mut definition = differences.clone();
    definition.push(guard);
    result.clauses.push(CnfClause::new(definition));
    guard
}
