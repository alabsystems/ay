// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_table_creation() {
    let vars = vec![IntVarId(0), IntVarId(1)];
    let tuples = vec![vec![1, 2], vec![3, 4]];
    let prop = Table::new(vars, tuples);
    assert_eq!(prop.variables().len(), 2);
    assert_eq!(prop.name(), "table");
}

#[test]
fn test_table_detects_conflict() {
    let mut trail = IntegerTrail::new();
    // x ∈ [5, 5], y ∈ [5, 5]
    let x = trail.register(5, 5);
    let y = trail.register(5, 5);

    let mut enc = IntegerEncoder::new();
    enc.register_var(5, 5);
    enc.register_var(5, 5);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    // Only tuple (1, 2) is allowed — but x=5, y=5 doesn't match
    let mut prop = Table::new(vec![x, y], vec![vec![1, 2], vec![3, 4]]);
    let result = prop.propagate(&trail, &enc);
    assert!(
        matches!(result, PropagationResult::Conflict(_)),
        "should detect no supported tuples"
    );
}

#[test]
fn test_table_propagates_bounds() {
    let mut trail = IntegerTrail::new();
    // x ∈ [1, 10], y ∈ [1, 10]
    let x = trail.register(1, 10);
    let y = trail.register(1, 10);

    let mut enc = IntegerEncoder::new();
    enc.register_var(1, 10);
    enc.register_var(1, 10);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    // Allowed tuples: (2, 3), (4, 5), (6, 7)
    // → x should be tightened to [2, 6], y to [3, 7]
    let mut prop = Table::new(vec![x, y], vec![vec![2, 3], vec![4, 5], vec![6, 7]]);
    let result = prop.propagate(&trail, &enc);
    assert!(
        matches!(result, PropagationResult::Propagated(ref clauses) if !clauses.is_empty()),
        "should propagate tighter bounds from table"
    );
}

/// Sparse-domain witness: interior holes must eliminate unsupported tuples.
///
/// x ∈ {1, 3} (interval [1,3] but 2 is absent)
/// y ∈ {1, 2}
/// Allowed tuples: {(1,1), (2,2)}
///
/// With exact domain membership, only (1,1) is supported (x cannot be 2).
/// The old interval-based check would wrongly keep (2,2) alive because
/// 2 ∈ [1,3]. With (1,1) as the sole support, x must be tightened to
/// ub=1 and y to ub=1.
#[test]
fn test_table_sparse_domain_hole_eliminates_tuple() {
    use crate::domain::Domain;

    let mut trail = IntegerTrail::new();
    // x ∈ {1, 3}: lb=1, ub=3, but 2 is absent
    let x = trail.register_domain(Domain::from_values(&[1, 3]));
    // y ∈ {1, 2}
    let y = trail.register(1, 2);

    let mut enc = IntegerEncoder::new();
    enc.register_var(1, 3);
    enc.register_var(1, 2);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    // Tuples: (1,1) and (2,2). Only (1,1) is truly supported.
    let mut prop = Table::new(vec![x, y], vec![vec![1, 1], vec![2, 2]]);
    let result = prop.propagate(&trail, &enc);

    // The propagator should tighten x's ub to 1 and y's ub to 1.
    match result {
        PropagationResult::Propagated(clauses) => {
            assert!(
                !clauses.is_empty(),
                "should propagate bounds from single supported tuple"
            );
        }
        PropagationResult::NoChange => {
            panic!("bug: interval-only check kept (2,2) alive despite x=2 being absent")
        }
        PropagationResult::Conflict(_) => {
            panic!("unexpected conflict — (1,1) is a valid supported tuple")
        }
    }
}

/// When ALL tuple values reference interior holes, the propagator must
/// detect a conflict (no supported tuples remain).
#[test]
fn test_table_sparse_domain_hole_causes_conflict() {
    use crate::domain::Domain;

    let mut trail = IntegerTrail::new();
    // x ∈ {1, 3}: 2 is absent
    let x = trail.register_domain(Domain::from_values(&[1, 3]));
    // y ∈ {1, 3}: 2 is absent
    let y = trail.register_domain(Domain::from_values(&[1, 3]));

    let mut enc = IntegerEncoder::new();
    enc.register_var(1, 3);
    enc.register_var(1, 3);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    // Only tuple is (2, 2), but both x=2 and y=2 are absent
    let mut prop = Table::new(vec![x, y], vec![vec![2, 2]]);
    let result = prop.propagate(&trail, &enc);
    assert!(
        matches!(result, PropagationResult::Conflict(_)),
        "should detect conflict when all tuples reference absent values"
    );
}

#[test]
fn test_table_no_change_when_bounds_tight() {
    let mut trail = IntegerTrail::new();
    // x ∈ [1, 3], y ∈ [1, 3]
    let x = trail.register(1, 3);
    let y = trail.register(1, 3);

    let mut enc = IntegerEncoder::new();
    enc.register_var(1, 3);
    enc.register_var(1, 3);
    let mut sat = ay_sat::Solver::new(0);
    enc.pre_allocate_all(&mut sat);

    // Tuples span the full domain range
    let mut prop = Table::new(vec![x, y], vec![vec![1, 1], vec![2, 2], vec![3, 3]]);
    let result = prop.propagate(&trail, &enc);
    assert!(
        matches!(result, PropagationResult::NoChange),
        "should not propagate when bounds already tight"
    );
}
