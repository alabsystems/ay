// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `merge_array_completion_candidate` on an array of arrays: an inner array
//! spelled twice is one cell under every policy, two values stored at one
//! inner index conflict under every policy, and the inner else-values follow
//! the outer default policy.

use super::super::{ExistingArrayCellPolicy, ExistingArrayDefaultPolicy};
use crate::executor::model::datatype_cell_authority::ExactDatatypeCellCompletions;
use crate::executor::Executor;
use ay_arrays::ArrayInterpretation;
use ay_core::Sort;

const ROW_SORT: &str = "(Array (_ BitVec 4) (_ BitVec 3))";

fn row(default: &str, stores: &[(&str, &str)]) -> String {
    let mut text = format!("((as const {ROW_SORT}) {default})");
    for (index, value) in stores {
        text = format!("(store {text} {index} {value})");
    }
    text
}

fn memory() -> ay_core::ArraySort {
    let row = Sort::array(Sort::bitvec(4), Sort::bitvec(3));
    ay_core::ArraySort {
        index_sort: Sort::bitvec(4),
        element_sort: row,
    }
}

fn interp(cell: String) -> ArrayInterpretation {
    ArrayInterpretation {
        default: Some(row("#b000", &[])),
        stores: vec![("#x1".to_string(), cell)],
        index_sort: Some(Sort::bitvec(4)),
        element_sort: Some(Sort::array(Sort::bitvec(4), Sort::bitvec(3))),
    }
}

fn merge(
    existing: String,
    candidate: String,
    policy: ExistingArrayDefaultPolicy,
) -> Option<String> {
    let exec = Executor::new();
    exec.merge_array_completion_candidate(
        &ExactDatatypeCellCompletions::default(),
        Some(&interp(existing)),
        interp(candidate),
        &memory(),
        policy,
        ExistingArrayCellPolicy::Authoritative,
    )
    .ok()
    .map(|merged| merged.stores[0].1.clone())
}

const POLICIES: [ExistingArrayDefaultPolicy; 3] = [
    ExistingArrayDefaultPolicy::Preserve,
    ExistingArrayDefaultPolicy::Require,
    ExistingArrayDefaultPolicy::Ignore,
];

#[test]
fn one_inner_array_spelled_twice_is_one_cell_under_every_policy() {
    let existing = row("#b000", &[("#x5", "#b100"), ("#x2", "#b001")]);
    let reordered = row("#b000", &[("#x2", "#b001"), ("#x5", "#b100")]);
    for policy in POLICIES {
        assert!(
            merge(existing.clone(), reordered.clone(), policy).is_some(),
            "{policy:?}"
        );
    }
}

#[test]
fn an_inner_store_at_one_index_with_two_values_conflicts_under_every_policy() {
    let existing = row("#b000", &[("#x5", "#b100")]);
    let candidate = row("#b000", &[("#x5", "#b101")]);
    for policy in POLICIES {
        assert_eq!(
            merge(existing.clone(), candidate.clone(), policy),
            None,
            "{policy:?}"
        );
    }
}

/// The candidate folds the read into its inner else-value. The reads-derived
/// pass keeps the extracted row; a target with a semantic `(default ..)` value
/// keeps the strict conflict -> taint path; any other defined target inherits
/// the definition's inner else-value under the extracted stores.
#[test]
fn a_disagreeing_inner_else_value_follows_the_outer_policy() {
    let existing = row("#b000", &[("#x5", "#b100")]);
    let fold = row("#b100", &[]);
    assert_eq!(
        merge(
            existing.clone(),
            fold.clone(),
            ExistingArrayDefaultPolicy::Preserve
        ),
        Some(existing.clone())
    );
    assert_eq!(
        merge(
            existing.clone(),
            fold.clone(),
            ExistingArrayDefaultPolicy::Require
        ),
        None
    );
    assert_eq!(
        merge(existing, fold, ExistingArrayDefaultPolicy::Ignore),
        Some(row("#b100", &[("#x5", "#b100")]))
    );
}

/// With agreeing inner else-values, the extracted inner stores stand over the
/// candidate's else-value, as the extracted outer stores do.
#[test]
fn agreeing_inner_else_values_keep_the_extracted_inner_stores() {
    let existing = row("#b000", &[("#x5", "#b100")]);
    let candidate = row("#b000", &[("#x7", "#b011")]);
    for policy in POLICIES {
        assert_eq!(
            merge(existing.clone(), candidate.clone(), policy),
            Some(row("#b000", &[("#x5", "#b100"), ("#x7", "#b011")])),
            "{policy:?}"
        );
    }
}
