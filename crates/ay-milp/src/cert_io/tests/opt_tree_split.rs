// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The streaming `opttree` verifier's `split` record, refusal by refusal.
//!
//! The record's parse, its coverage licence and its `lo` tightening live in
//! one helper of `verify_opt_tree_body`. This pins WHICH refusal each bad split
//! earns and what it names (the record's one-based line for a malformed field,
//! the split's index and column for an unlicensed cut), so that an edit to the
//! helper cannot move a split from one refusal to another, or name the wrong
//! record, without a test saying so.

use super::*;

/// Column 0 is INTEGRAL, column 1 is CONTINUOUS.
fn split_model() -> Model {
    let mut m = Model::new();
    let x = m.add_int_col(0.0, 10.0);
    let _y = m.add_col(0.0, 10.0);
    m.set_objective(&[(x, 1.0)], Sense::Minimize);
    m
}

fn malformed_at<T: fmt::Debug>(result: Result<T, OptTreeStreamError>) -> (usize, String) {
    match result {
        Err(OptTreeStreamError::Malformed { line, msg }) => (line, msg),
        other => panic!("expected Malformed, got {other:?}"),
    }
}

fn invalid_split<T: fmt::Debug>(result: Result<T, OptTreeStreamError>) -> (usize, usize) {
    match result {
        Err(OptTreeStreamError::InvalidSplit { index, col }) => (index, col),
        other => panic!("expected InvalidSplit, got {other:?}"),
    }
}

pub(super) fn every_split_refusal_names_its_record() {
    let m = split_model();
    let zero = BigRational::zero();
    let verify = |body: &str| verify_opt_tree_body(&m, &zero, body);

    // A malformed field is Malformed at the record's own line; the blank line
    // in front of it is counted.
    assert_eq!(
        malformed_at(verify("\nsplit x 5\n")),
        (2, "malformed split column".to_string())
    );
    assert_eq!(
        malformed_at(verify("split -1 5\n")),
        (1, "malformed split column".to_string())
    );
    assert_eq!(
        malformed_at(verify("split 0 five\n")),
        (1, "malformed split cut".to_string())
    );

    // THE COVERAGE LICENCE: a continuous column, a column the model does not
    // have, and a non-integer cut on an integral column are each refused as
    // the split they are, never as a malformed record.
    assert_eq!(invalid_split(verify("split 1 5\n")), (0, 1));
    assert_eq!(invalid_split(verify("split 7 5\n")), (0, 7));
    assert_eq!(invalid_split(verify("split 0 5/2\n")), (0, 0));

    // The index counts the splits before this one, licensed or not.
    assert_eq!(invalid_split(verify("split 0 5\nsplit 1 3\n")), (1, 1));

    // A licensed split is no refusal at all: the body below is refused only
    // because it ends with that split still open.
    assert!(matches!(
        verify("split 0 5\n"),
        Err(OptTreeStreamError::Incomplete)
    ));
}
