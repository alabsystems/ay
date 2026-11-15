// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn wide_array_fields_keep_complete_registry_identity() {
    for width in [72, 128, 136, crate::MAX_BITVECTOR_WIDTH] {
        let table = ChcSort::Array(Box::new(bv(width)), Box::new(bv(136)));
        let mut problem = ChcProblem::new();
        problem.add_datatype_def(
            "Wide".into(),
            vec![("mkWide".into(), vec![("table".into(), table.clone())])],
        );
        let registry = Registry::new(&problem).unwrap();
        let sort = registry.lookup("Wide").unwrap();
        assert_eq!(
            registry
                .application("table", std::slice::from_ref(sort))
                .unwrap(),
            table
        );
        assert_eq!(
            registry.application("mkWide", &[table.clone()]).unwrap(),
            *sort
        );
        let wrong_key = ChcSort::Array(Box::new(bv(width - 1)), Box::new(bv(136)));
        assert!(registry.application("mkWide", &[wrong_key]).is_err());
        assert!(sort_bytes(&table).unwrap() > 192);
        assert!(!small_copy_sort(&table));
    }
}

#[test]
fn repeated_wide_payloads_have_limb_sized_cost_even_in_record_cells() {
    for width in [72, 128, 136, crate::MAX_BITVECTOR_WIDTH] {
        let payload = usize::try_from(width.div_ceil(8)).unwrap();
        assert_eq!(sort_bytes(&bv(width)), Some(64 + payload));
        let table = ChcSort::Array(Box::new(bv(width)), Box::new(bv(width)));
        assert_eq!(sort_bytes(&table), Some(192 + 2 * payload));
        let nested = ChcSort::Array(Box::new(bv(width)), Box::new(table));
        assert_eq!(sort_bytes(&nested), Some(320 + 3 * payload));
    }
    let mut problem = ChcProblem::new();
    problem.add_datatype_def(
        "TooWide".into(),
        vec![(
            "mkTooWide".into(),
            (0..64)
                .map(|i| (format!("field{i}"), bv(crate::MAX_BITVECTOR_WIDTH)))
                .collect(),
        )],
    );
    assert!(registry_bytes(&problem).is_none());
    assert!(Registry::new(&problem).is_err());
}

#[test]
fn wide_sort_admission_keeps_zero_oversize_and_rank_refusals() {
    let registry = Registry::new(&ChcProblem::new()).unwrap();
    for width in [0, crate::MAX_BITVECTOR_WIDTH + 1, u32::MAX] {
        assert!(registry.validate_sort(&bv(width)).is_err());
        let table = ChcSort::Array(Box::new(bv(width)), Box::new(bv(8)));
        assert!(registry.validate_sort(&table).is_err());
    }
    let mut rank_three = bv(136);
    for _ in 0..3 {
        rank_three = ChcSort::Array(Box::new(bv(136)), Box::new(rank_three));
    }
    assert!(registry.validate_sort(&rank_three).is_err());
    assert!(small_copy_sort(&ChcSort::Array(
        Box::new(bv(64)),
        Box::new(bv(64))
    )));
}
