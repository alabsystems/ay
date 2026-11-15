// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exact_signed_namespace_frontiers_require_no_allocation() {
    let maximum = i32::MAX as u32;
    for (tseitin, next_fp, total) in [
        (0, 1, 0),
        (maximum, 1, maximum),
        (maximum - 1, 2, maximum),
        (0, maximum + 1, maximum),
        (11, 8, 18),
    ] {
        let namespace = FpNamespace::new(tseitin, next_fp).unwrap();
        assert_eq!(namespace.offset(), tseitin as i32);
        assert_eq!(namespace.total_vars(), total);
    }
}

#[test]
fn individually_valid_namespaces_can_overflow_the_combined_signed_range() {
    let maximum = i32::MAX as u32;
    for (tseitin, next_fp) in [
        (maximum, 2),
        (1, maximum + 1),
        (maximum / 2 + 1, maximum / 2 + 2),
    ] {
        assert!(validate_tseitin_namespace(tseitin).is_ok());
        assert!(next_fp - 1 <= maximum);
        assert_eq!(
            FpNamespace::new(tseitin, next_fp),
            Err(UnknownOrigin::DeterministicResourceBudget)
        );
    }
}

#[test]
fn invalid_frontiers_and_unsigned_overflow_refuse_without_wrapping() {
    let maximum = i32::MAX as u32;
    for (tseitin, next_fp) in [
        (0, 0),
        (1, 0),
        (maximum + 1, 1),
        (0, maximum + 2),
        (maximum, u32::MAX),
        (u32::MAX, u32::MAX),
    ] {
        assert_eq!(
            FpNamespace::new(tseitin, next_fp),
            Err(UnknownOrigin::DeterministicResourceBudget)
        );
    }
    assert_eq!(validate_tseitin_namespace(maximum), Ok(()));
    assert_eq!(
        validate_tseitin_namespace(maximum + 1),
        Err(UnknownOrigin::DeterministicResourceBudget)
    );
}

#[test]
fn both_polarities_preserve_the_exact_combined_namespace() {
    let namespace = FpNamespace::new(3, 5).unwrap();
    for (local, combined) in [(1, 4), (4, 7)] {
        assert_eq!(namespace.offset_lit(local), combined);
        assert_eq!(namespace.offset_lit(-local), -combined);
    }
    let maximum = i32::MAX;
    let last_variable = FpNamespace::new(maximum as u32 - 1, 2).unwrap();
    assert_eq!(last_variable.offset_lit(1), maximum);
    assert_eq!(last_variable.offset_lit(-1), -maximum);
    let no_offset = FpNamespace::new(0, maximum as u32 + 1).unwrap();
    assert_eq!(no_offset.offset_lit(maximum), maximum);
    assert_eq!(no_offset.offset_lit(-maximum), -maximum);
}
