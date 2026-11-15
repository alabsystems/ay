// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn sat_unknown_reason_mapping_is_specific() {
    let mut reason = None;

    Executor::record_sat_unknown_reason(&mut reason, Some(SatUnknownReason::Interrupted));
    assert_eq!(reason, Some(UnknownReason::Interrupted));

    assert_eq!(
        Executor::map_sat_unknown_origin(SatUnknownReason::DeadlineExceeded),
        UnknownOrigin::SolveDeadline
    );
    Executor::record_sat_unknown_reason(&mut reason, Some(SatUnknownReason::DeadlineExceeded));
    assert_eq!(reason, Some(UnknownReason::Timeout));

    Executor::record_sat_unknown_reason(&mut reason, Some(SatUnknownReason::UnsupportedConfig));
    assert_eq!(reason, Some(UnknownReason::Unsupported));

    Executor::record_sat_unknown_reason(&mut reason, Some(SatUnknownReason::EmptyTheoryConflict));
    assert_eq!(reason, Some(UnknownReason::Unknown));
}

#[test]
fn nia_boolean_leaf_transport_rejects_formula_numeric_and_unmapped_entries_atomically() {
    let mut terms = ay_core::TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let formula = terms.mk_or(vec![p, q]);
    let mut mapping = std::collections::BTreeMap::new();
    mapping.insert(p, 1);
    mapping.insert(q, 2);
    mapping.insert(x, 2);
    mapping.insert(formula, 2);
    for invalid in [x, formula, TermId(u32::MAX)] {
        let mut point = vec![false, false];
        assert!(!Executor::install_boolean_leaf_witness(
            &terms,
            &mut point,
            &mapping,
            &[(p, true), (invalid, true)]
        ));
        assert_eq!(point, vec![false, false]);
    }
    let mut point = vec![false, true];
    assert!(Executor::install_boolean_leaf_witness(
        &terms,
        &mut point,
        &mapping,
        &[(p, true), (q, false)]
    ));
    assert_eq!(point, vec![true, false]);
}
