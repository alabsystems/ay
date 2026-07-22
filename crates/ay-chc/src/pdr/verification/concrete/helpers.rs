// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Helper functions for concrete transition checking: boundary sampling,
//! exhaustive enumeration, expression hashing, bounds extraction, and
//! constant extraction.

use super::ConcreteCheckRange;
use crate::expr::evaluate_expr;
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcOp};
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Sample boundary-value combinations up to a limit (odometer iteration).
pub(super) fn sample_boundary_combinations(
    ranges: &[ConcreteCheckRange],
    boundary_values: &[Vec<SmtValue>],
    assignment: &mut FxHashMap<String, SmtValue>,
    query: &ChcExpr,
    max_combos: usize,
    samples_checked: &mut usize,
) -> Option<FxHashMap<String, SmtValue>> {
    let n = ranges.len();
    let mut indices: Vec<usize> = vec![0; n];
    let sizes: Vec<usize> = boundary_values.iter().map(|v| v.len().max(1)).collect();

    for _ in 0..max_combos {
        assignment.clear();
        let mut all_assigned = true;
        for (i, r) in ranges.iter().enumerate() {
            let name = match r {
                ConcreteCheckRange::Int { name, .. } | ConcreteCheckRange::BitVec { name, .. } => {
                    name
                }
            };
            if let Some(val) = boundary_values[i].get(indices[i]) {
                assignment.insert(name.clone(), val.clone());
            } else {
                all_assigned = false;
            }
        }
        *samples_checked += 1;

        if all_assigned
            && assignment.len() == n
            && evaluate_expr(query, assignment) == Some(SmtValue::Bool(true))
        {
            return Some(assignment.clone());
        }

        // Odometer increment
        let carry = increment_odometer(&mut indices, &sizes);
        if carry {
            break;
        }
    }

    None
}

/// Increment an odometer-style index vector. Returns true if overflow (all done).
fn increment_odometer(indices: &mut [usize], sizes: &[usize]) -> bool {
    let mut carry = true;
    for i in (0..indices.len()).rev() {
        if carry {
            indices[i] += 1;
            if indices[i] >= sizes[i] {
                indices[i] = 0;
            } else {
                carry = false;
            }
        }
    }
    carry
}

/// Extract integer lower/upper bounds from formula conjuncts.
pub(super) fn extract_int_bounds_from_conjuncts(expr: &ChcExpr) -> FxHashMap<String, (i64, i64)> {
    let mut result: FxHashMap<String, (i64, i64)> = FxHashMap::default();

    fn collect_bounds(expr: &ChcExpr, result: &mut FxHashMap<String, (i64, i64)>) {
        match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    collect_bounds(arg, result);
                }
            }
            // x >= k  →  lower bound
            ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                if let (ChcExpr::Var(v), ChcExpr::Int(k)) = (args[0].as_ref(), args[1].as_ref()) {
                    // i128-lockstep: the concrete-sampling lane is i64; skip
                    // bounds outside i64 range (samples are re-checked by full
                    // evaluation, so fewer bounds only weakens the heuristic).
                    if let Ok(k) = i64::try_from(*k) {
                        let entry = result.entry(v.name.clone()).or_insert((k, i64::MAX));
                        entry.0 = entry.0.max(k);
                    }
                }
            }
            // x <= k  →  upper bound
            ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                if let (ChcExpr::Var(v), ChcExpr::Int(k)) = (args[0].as_ref(), args[1].as_ref()) {
                    // i128-lockstep: sampling lane is i64; skip out-of-range bounds.
                    if let Ok(k) = i64::try_from(*k) {
                        let entry = result.entry(v.name.clone()).or_insert((i64::MIN, k));
                        entry.1 = entry.1.min(k);
                    }
                }
            }
            // not (x >= k)  →  x < k  →  upper bound k-1
            ChcExpr::Op(ChcOp::Not, not_args) if not_args.len() == 1 => {
                if let ChcExpr::Op(ChcOp::Ge, args) = not_args[0].as_ref() {
                    if args.len() == 2 {
                        if let (ChcExpr::Var(v), ChcExpr::Int(k)) =
                            (args[0].as_ref(), args[1].as_ref())
                        {
                            // i128-lockstep: sampling lane is i64; skip
                            // out-of-range bounds.
                            if let Ok(k) = i64::try_from(*k) {
                                // Use saturating arithmetic to avoid overflow when
                                // k == i64::MIN (#5926).
                                let upper = k.saturating_sub(1);
                                let entry =
                                    result.entry(v.name.clone()).or_insert((i64::MIN, upper));
                                entry.1 = entry.1.min(upper);
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    collect_bounds(expr, &mut result);
    result
}

/// Compute a structural hash of an expression for PRNG seeding.
/// Not cryptographic — just needs to vary across different formulas.
pub(super) fn hash_expr_structure(expr: &ChcExpr) -> u64 {
    use std::hash::{Hash, Hasher};
    // Use a simple FNV-1a-like hasher for speed.
    struct FnvHasher(u64);
    impl Hasher for FnvHasher {
        fn finish(&self) -> u64 {
            self.0
        }
        fn write(&mut self, bytes: &[u8]) {
            for &b in bytes {
                self.0 = self
                    .0
                    .wrapping_mul(0x100000001b3)
                    .wrapping_add(u64::from(b));
            }
        }
    }

    fn hash_rec(expr: &ChcExpr, depth: usize) -> u64 {
        if depth > 50 {
            return 0xdeadbeef;
        }
        match expr {
            ChcExpr::Bool(b) => {
                if *b {
                    0x1
                } else {
                    0x2
                }
            }
            ChcExpr::Int(n) => (*n as u64).wrapping_mul(0x9e3779b97f4a7c15),
            ChcExpr::Real(n, d) => (*n as u64)
                .wrapping_mul(0x517cc1b727220a95)
                .wrapping_add(*d as u64),
            ChcExpr::BitVec(val, width) => {
                let folded = (*val as u64) ^ ((*val >> 64) as u64);
                folded
                    .wrapping_mul(0x6a09e667f3bcc908)
                    .wrapping_add(u64::from(*width))
            }
            ChcExpr::Var(v) => {
                let mut h: u64 = 0xcbf29ce484222325;
                for b in v.name.bytes() {
                    h = h.wrapping_mul(0x100000001b3).wrapping_add(u64::from(b));
                }
                h
            }
            ChcExpr::Op(op, args) => {
                let mut hasher = FnvHasher(0xcbf29ce484222325);
                op.hash(&mut hasher);
                let mut h = hasher.finish().wrapping_mul(0x9e3779b97f4a7c15);
                for arg in args {
                    h = h.wrapping_mul(31).wrapping_add(hash_rec(arg, depth + 1));
                }
                h
            }
            ChcExpr::PredicateApp(_, id, args) => {
                let mut h = (id.index() as u64).wrapping_mul(0x517cc1b727220a95);
                for arg in args {
                    h = h.wrapping_mul(31).wrapping_add(hash_rec(arg, depth + 1));
                }
                h
            }
            ChcExpr::FuncApp(name, _, args) => {
                let mut h: u64 = 0xcbf29ce484222325;
                for b in name.bytes() {
                    h = h.wrapping_mul(0x100000001b3).wrapping_add(u64::from(b));
                }
                for arg in args {
                    h = h.wrapping_mul(31).wrapping_add(hash_rec(arg, depth + 1));
                }
                h
            }
            ChcExpr::ConstArray(_ks, inner) => {
                0xa5a5a5a5a5a5a5a5_u64.wrapping_add(hash_rec(inner, depth + 1))
            }
            _ => 0x5a5a5a5a5a5a5a5a,
        }
    }
    hash_rec(expr, 0)
}

/// Extract integer constants from an expression tree.
/// Returns a deduplicated, sorted list of constants found in the formula.
/// Used to seed boundary values for Monte Carlo sampling (#5539).
pub(super) fn extract_int_constants(expr: &ChcExpr) -> Vec<i64> {
    let mut constants = Vec::new();
    fn collect(expr: &ChcExpr, out: &mut Vec<i64>, depth: usize) {
        if depth > 50 {
            return;
        }
        match expr {
            ChcExpr::Int(n) => {
                // Only collect small constants that fit in our sampling range.
                // Large constants outside [-100, 100] are still useful as they
                // inform us about the formula's value space.
                // i128-lockstep: sampling lane is i64; skip constants outside
                // i64 range (fewer boundary seeds, never wrong ones).
                if let Ok(n64) = i64::try_from(*n) {
                    if !out.contains(&n64) {
                        out.push(n64);
                    }
                }
            }
            ChcExpr::Op(_, args) => {
                for arg in args {
                    collect(arg, out, depth + 1);
                }
            }
            ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                for arg in args {
                    collect(arg, out, depth + 1);
                }
            }
            ChcExpr::ConstArray(_ks, inner) => {
                collect(inner, out, depth + 1);
            }
            _ => {}
        }
    }
    collect(expr, &mut constants, 0);
    constants.sort_unstable();
    constants.dedup();
    constants
}

/// Recursively enumerate Int and BV assignments and check the formula.
pub(super) fn enumerate_and_check_generic(
    ranges: &[ConcreteCheckRange],
    idx: usize,
    assignment: &mut FxHashMap<String, SmtValue>,
    query: &ChcExpr,
) -> Option<FxHashMap<String, SmtValue>> {
    if idx >= ranges.len() {
        // All variables assigned — evaluate the formula
        match evaluate_expr(query, assignment) {
            Some(SmtValue::Bool(true)) => Some(assignment.clone()),
            _ => None,
        }
    } else {
        match &ranges[idx] {
            ConcreteCheckRange::Int { name, lo, hi } => {
                for val in *lo..=*hi {
                    assignment.insert(name.clone(), SmtValue::Int(i128::from(val)));
                    if let Some(cex) =
                        enumerate_and_check_generic(ranges, idx + 1, assignment, query)
                    {
                        return Some(cex);
                    }
                }
                assignment.remove(name);
            }
            ConcreteCheckRange::BitVec {
                name, width, count, ..
            } => {
                for val in 0..*count {
                    assignment.insert(name.clone(), SmtValue::BitVec(val, *width));
                    if let Some(cex) =
                        enumerate_and_check_generic(ranges, idx + 1, assignment, query)
                    {
                        return Some(cex);
                    }
                }
                assignment.remove(name);
            }
        }
        None
    }
}
