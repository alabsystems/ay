// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn periodic_integer_native_producer_preserves_signed_cells_and_exact_index_sort() {
    for values in [
        vec![ModelValue::Int((-7).into()), ModelValue::Int(5.into())],
        vec![ModelValue::Bool(true), ModelValue::Bool(false)],
    ] {
        let element = match &values[0] {
            ModelValue::Bool(_) => Sort::Bool,
            _ => Sort::Int,
        };
        let sort = Sort::array(Sort::Int, element.clone());
        let snapshot = ArraySnapshot::periodic(&values, &sort, &mut 100_000).unwrap();
        let mut terms = TermStore::new();
        let term = convert(&snapshot, &mut terms, &mut Sink::new());
        assert_eq!(terms.sort(term), &sort);
        let rebuilt = captured(&terms, term);
        assert!(snapshot.same_function(&rebuilt, &mut 100_000).unwrap());
        for (index, expected) in [(-3, 1usize), (-2, 0), (1000, 0), (1001, 1)] {
            let index = ModelValue::Int(index.into());
            assert!(crate::value_eq(
                &rebuilt.read(&index, &mut 100_000).unwrap(),
                &values[expected]
            )
            .unwrap());
        }
    }
}

#[test]
fn periodic_integer_late_invalid_data_refuses_before_any_native_term_is_minted() {
    let values = [ModelValue::Int(1.into()), ModelValue::Bool(false)];
    let sort = Sort::array(Sort::Int, Sort::Int);
    let topology = SnapshotTopology {
        nodes: vec![SnapshotNode {
            sort: &sort,
            kind: SnapshotKind::Periodic(&values),
        }],
        root: 0,
    };
    let mut terms = TermStore::new();
    let original = terms.snapshot_stamp();
    let length = terms.len();
    assert!(matches!(
        topology.try_to_term_with_progress(&mut terms, &mut |_, _| true),
        Err(SnapshotTermError::InvalidTopology)
    ));
    assert_eq!(terms.len(), length);
    assert_eq!(terms.snapshot_stamp(), original);
}

#[test]
fn periodic_integer_large_payload_obeys_one_original_storage_and_cancel_owner() {
    let value = ModelValue::Int(BigInt::from(1u8) << 100_000usize);
    let snapshot =
        ArraySnapshot::periodic(&[value], &Sort::array(Sort::Int, Sort::Int), &mut 1_000_000)
            .unwrap();
    let topology = snapshot.topology(&mut 1_000_000, &mut || false).unwrap();
    let mut terms = TermStore::new();
    let length = terms.len();
    let mut remaining = 4096usize;
    let mut refused = false;
    let mut sink = |_, bytes| {
        if refused {
            return false;
        }
        match remaining.checked_sub(bytes) {
            Some(next) => {
                remaining = next;
                true
            }
            None => {
                refused = true;
                false
            }
        }
    };
    assert_eq!(
        topology.try_to_term_with_progress(&mut terms, &mut sink),
        Err(SnapshotTermError::ResourceLimit)
    );
    assert_eq!(terms.len(), length);
    assert_eq!(
        topology.try_to_term_with_progress(&mut terms, &mut sink),
        Err(SnapshotTermError::ResourceLimit)
    );
    assert_eq!(terms.len(), length);
    assert!(refused);
    assert_eq!(
        topology.try_to_term_with_progress(&mut terms, &mut |_, _| false),
        Err(SnapshotTermError::ResourceLimit)
    );
    assert_eq!(terms.len(), length);
}
