// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::Sort;

#[test]
fn reglan_helper_and_display_match_smt_name() {
    let sort = Sort::RegLan;
    assert!(sort.is_reglan());
    assert_eq!(sort.to_string(), "RegLan");
}

#[test]
fn reglan_passthrough_in_term_sort_conversion() {
    assert_eq!(Sort::RegLan.as_term_sort(), Sort::RegLan);
}
