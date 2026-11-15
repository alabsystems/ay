// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn linux_valid_units_zero_and_addressable_boundary() {
    assert_eq!(
        linux_available_bytes("MemTotal: 99999 kB\nMemAvailable:\t1234 kB\n"),
        Some(1234 * 1024)
    );
    assert_eq!(linux_available_bytes("MemAvailable: 0 kB\n"), Some(0));
    let maximum = usize::MAX / 1024;
    assert_eq!(
        linux_available_bytes(&format!("MemAvailable: {maximum} kB\n")),
        Some(maximum * 1024)
    );
    assert_eq!(
        linux_available_bytes(&format!("MemAvailable: {} kB\n", maximum + 1)),
        None
    );
}

#[test]
fn linux_malformed_ambiguous_and_overflow_samples_are_unavailable() {
    for sample in [
        "",
        "MemTotal: 100 kB",
        "MemAvailable:",
        "MemAvailable: nope kB",
        "MemAvailable: -1 kB",
        "MemAvailable: +1 kB",
        "MemAvailable: 1",
        "MemAvailable: 1 MB",
        "MemAvailable: 1 kB extra",
        "MemAvailable: 1 kB\nMemAvailable: 2 kB",
        "MemAvailable: broken\nMemAvailable: 1 kB",
        "MemAvailable: 18446744073709551615 kB",
        "MemAvailable: 18446744073709551616 kB",
    ] {
        assert_eq!(linux_available_bytes(sample), None, "{sample:?}");
    }
}

#[test]
fn mac_counts_are_validated_before_fields_and_page_fallback_is_preserved() {
    let words = [2, 777, 3, 999];
    for count in [0, 1, 2, 5, u32::MAX] {
        assert_eq!(mac_available_bytes(&words, count, Some(16384)), None);
    }
    assert_eq!(mac_available_bytes(&[], 3, Some(16384)), None);
    assert_eq!(mac_available_bytes(&words, 3, Some(16384)), Some(5 * 16384));
    assert_eq!(mac_available_bytes(&words, 4, None), Some(5 * 4096));
    assert_eq!(mac_available_bytes(&words, 3, Some(0)), None);
    assert_eq!(mac_available_bytes(&[0, 777, 0], 3, Some(16384)), Some(0));
}

#[test]
fn mac_arithmetic_overflow_is_not_a_saturated_available_sample() {
    let words = [u32::MAX, 0, u32::MAX];
    assert_eq!(mac_available_bytes(&words, 3, Some(u64::MAX)), None);
    let expected = (2 * u64::from(u32::MAX))
        .checked_mul(4096)
        .expect("u64 boundary");
    assert_eq!(
        mac_available_bytes(&words, 3, Some(4096)),
        usize::try_from(expected).ok()
    );
}
