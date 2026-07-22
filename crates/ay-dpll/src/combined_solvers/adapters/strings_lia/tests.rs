// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::equality_propagation_conflict_result;
use ay_core::{TermId, TheoryLit, TheoryResult};

#[test]
fn strings_lia_empty_equality_conflict_returns_unknown() {
    let result = equality_propagation_conflict_result(Vec::new(), "test");
    assert!(
        matches!(result, TheoryResult::Unknown),
        "empty-reason SLIA equality conflict must degrade to Unknown; got {result:?}",
    );
}

#[test]
fn strings_lia_nonempty_equality_conflict_returns_unsat() {
    let result =
        equality_propagation_conflict_result(vec![TheoryLit::new(TermId(1), true)], "test");
    match result {
        TheoryResult::Unsat(conflict) => {
            assert_eq!(conflict, vec![TheoryLit::new(TermId(1), true)]);
        }
        other => panic!("non-empty SLIA equality conflict must stay Unsat; got {other:?}"),
    }
}
