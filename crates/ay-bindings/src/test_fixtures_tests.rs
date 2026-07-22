// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_point_sort_structure() {
    let point = point_sort();
    assert!(point.is_datatype());
    assert_eq!(point.datatype_name(), Some("Point"));
}

#[test]
fn test_option_sort_structure() {
    let opt = option_i32_sort();
    assert!(opt.is_datatype());
    assert_eq!(opt.datatype_name(), Some("Option"));
}

#[test]
fn test_option_like_sort_structure() {
    let opt = option_like_i32_sort();
    assert!(opt.is_datatype());
    assert_eq!(opt.datatype_name(), Some("OptionLike"));
}

#[test]
fn test_tuple2_sort_naming() {
    let tuple = tuple2_sort(Sort::bv32(), Sort::bv64());
    assert!(tuple.is_datatype());
    assert_eq!(tuple.datatype_name(), Some("Tuple_bv32_bv64"));
}

#[test]
fn test_sort_suffix_coverage() {
    // Test all branches of sort_suffix for tuple naming
    assert_eq!(sort_suffix(&Sort::bv32()), "bv32");
    assert_eq!(sort_suffix(&Sort::bool()), "bool");
    assert_eq!(sort_suffix(&Sort::int()), "int");
    assert_eq!(sort_suffix(&Sort::real()), "real");
    assert_eq!(sort_suffix(&Sort::array(Sort::bv64(), Sort::bv32())), "arr");
    assert_eq!(sort_suffix(&point_sort()), "Point");
}
