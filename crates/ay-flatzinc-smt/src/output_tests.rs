// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_format_value_positive_int() {
    assert_eq!(format_value("42", false), "42");
}

#[test]
fn test_format_value_negative_smt() {
    assert_eq!(format_value("(- 7)", false), "-7");
}

#[test]
fn test_format_value_bool() {
    assert_eq!(format_value("true", true), "true");
    assert_eq!(format_value("false", true), "false");
}

#[test]
fn test_format_set_var_some_elements() {
    let var = OutputVarInfo {
        fzn_name: "S".into(),
        smt_names: vec!["S__bit__0".into(), "S__bit__1".into(), "S__bit__2".into()],
        is_array: false,
        array_range: None,
        is_bool: false,
        is_set: true,
        set_range: Some((1, 3)),
    };
    let mut values = HashMap::default();
    values.insert("S__bit__0".into(), "true".into());
    values.insert("S__bit__1".into(), "false".into());
    values.insert("S__bit__2".into(), "true".into());
    let dzn = format_dzn_solution(&values, &[var]);
    assert_eq!(dzn, "S = {1, 3};\n");
}

#[test]
fn test_format_set_var_empty() {
    let var = OutputVarInfo {
        fzn_name: "S".into(),
        smt_names: vec!["S__bit__0".into(), "S__bit__1".into()],
        is_array: false,
        array_range: None,
        is_bool: false,
        is_set: true,
        set_range: Some((5, 6)),
    };
    let mut values = HashMap::default();
    values.insert("S__bit__0".into(), "false".into());
    values.insert("S__bit__1".into(), "false".into());
    let dzn = format_dzn_solution(&values, &[var]);
    assert_eq!(dzn, "S = {};\n");
}

#[test]
fn test_format_set_var_all_elements() {
    let var = OutputVarInfo {
        fzn_name: "T".into(),
        smt_names: vec!["T__bit__0".into(), "T__bit__1".into(), "T__bit__2".into()],
        is_array: false,
        array_range: None,
        is_bool: false,
        is_set: true,
        set_range: Some((10, 12)),
    };
    let mut values = HashMap::default();
    values.insert("T__bit__0".into(), "true".into());
    values.insert("T__bit__1".into(), "true".into());
    values.insert("T__bit__2".into(), "true".into());
    let dzn = format_dzn_solution(&values, &[var]);
    assert_eq!(dzn, "T = {10, 11, 12};\n");
}
