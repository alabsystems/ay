// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use crate::{ChcDtConstructor, ChcDtSelector};

#[test]
fn array_cell_metadata_is_charged_at_every_source_copy_depth() {
    let cell = ChcSort::Datatype {
        name: "Cell".into(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: "mkCell".into(),
            selectors: vec![ChcDtSelector {
                name: "payload".into(),
                sort: ChcSort::Bool,
            }],
        }]),
    };
    let mut declarations = ChcProblem::new();
    declarations.add_datatype_def(
        "Cell".into(),
        vec![("mkCell".into(), vec![("payload".into(), ChcSort::Bool)])],
    );
    let registry = Registry::new(&declarations).unwrap();
    let array = ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(cell));
    let metadata = sort_bytes(&array).unwrap();
    for depth in [0, 1, MAX_DEPTH] {
        let charge = metadata * (depth + 1);
        let mut exact = Budget {
            nodes: 0,
            bytes: MAX_BYTES - charge,
        };
        assert!(exact.sort(&array, &registry, depth).is_ok());
        assert_eq!((exact.nodes, exact.bytes), (1, MAX_BYTES));
        assert!(exact.sort(&array, &registry, depth).is_err());
        let mut short = Budget {
            nodes: 0,
            bytes: MAX_BYTES - charge + 1,
        };
        assert!(short.sort(&array, &registry, depth).is_err());
        let mut fresh = Budget::default();
        assert!(fresh.sort(&array, &registry, depth).is_ok());
        assert_eq!(fresh.bytes, charge);
    }
    let legacy = ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::Bool));
    let mut unchanged = Budget::default();
    assert!(unchanged.sort(&legacy, &registry, MAX_DEPTH).is_ok());
    assert_eq!((unchanged.nodes, unchanged.bytes), (0, 0));
}
