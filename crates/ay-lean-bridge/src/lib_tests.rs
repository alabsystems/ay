// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;
use ay_core::{Constant, TermStore};

#[test]
fn test_sanitize_lean_name() {
    assert_eq!(sanitize_lean_name("x"), "x");
    assert_eq!(sanitize_lean_name("my_var"), "my_var");
    assert_eq!(sanitize_lean_name("x'"), "x'");
    assert_eq!(sanitize_lean_name("123"), "_123");
    assert_eq!(sanitize_lean_name("a-b"), "a_b");
    assert_eq!(sanitize_lean_name("def"), "def_");
    assert_eq!(sanitize_lean_name(""), "_unnamed");
}

#[test]
fn test_escape_lean_string() {
    assert_eq!(escape_lean_string("hello"), "hello");
    assert_eq!(escape_lean_string("hello\"world"), "hello\\\"world");
    assert_eq!(escape_lean_string("a\nb"), "a\\nb");
}

/// Regression test for #8852: `LeanError::Unsupported` is the documented
/// fallback for non-exhaustive `ay_core::Sort` / `TermData` / `Constant`
/// enums. Exercising the `Display` impl ensures the variant survives future
/// refactors and is surfaced with the `kind` tag for debugging.
#[test]
fn test_lean_error_unsupported_display() {
    let err = LeanError::Unsupported {
        kind: "Sort::NewVariant",
    };
    let rendered = format!("{err}");
    assert!(rendered.contains("unsupported"), "got: {rendered}");
    assert!(rendered.contains("Sort::NewVariant"), "got: {rendered}");
}

#[test]
fn test_export_constant() {
    assert_eq!(
        LeanExporter::export_constant(&Constant::Bool(true)).unwrap(),
        "true"
    );
    assert_eq!(
        LeanExporter::export_constant(&Constant::Bool(false)).unwrap(),
        "false"
    );
    assert_eq!(
        LeanExporter::export_constant(&Constant::Int(num_bigint::BigInt::from(42))).unwrap(),
        "42"
    );
    assert_eq!(
        LeanExporter::export_constant(&Constant::Int(num_bigint::BigInt::from(-42))).unwrap(),
        "(-42)"
    );
}

#[test]
fn test_export_sort() {
    let store = TermStore::new();
    let exporter = LeanExporter::new(&store);

    assert_eq!(exporter.export_sort(&Sort::Bool).unwrap(), "Bool");
    assert_eq!(exporter.export_sort(&Sort::Int).unwrap(), "Int");
    assert_eq!(exporter.export_sort(&Sort::Real).unwrap(), "Real");
    assert_eq!(
        exporter.export_sort(&Sort::bitvec(32)).unwrap(),
        "BitVec 32"
    );
    assert_eq!(
        exporter
            .export_sort(&Sort::array(Sort::Int, Sort::Bool))
            .unwrap(),
        "Array Int Bool"
    );
}

#[test]
fn test_export_simple_formula() {
    let mut store = TermStore::new();

    // Create: x && y
    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let formula = store.mk_and(vec![x, y]);

    let exporter = LeanExporter::new(&store);
    let result = exporter.export_term(formula).unwrap();
    assert!(result.contains("&&"));
}

#[test]
fn test_export_arithmetic() {
    use num_bigint::BigInt;
    let mut store = TermStore::new();

    // Create: x + 1 < 10
    let x = store.mk_var("x", Sort::Int);
    let one = store.mk_int(BigInt::from(1));
    let ten = store.mk_int(BigInt::from(10));
    let sum = store.mk_add(vec![x, one]);
    let lt = store.mk_lt(sum, ten);

    let exporter = LeanExporter::new(&store);
    let result = exporter.export_term(lt).unwrap();
    assert!(result.contains('+'));
    assert!(result.contains('<'));
}

#[test]
fn test_sat_verification_generation() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let y = store.mk_var("y", Sort::Bool);
    let formula = store.mk_and(vec![x, y]);

    let exporter = LeanExporter::new(&store);
    let code = exporter
        .generate_sat_verification(formula, &[("x".to_string(), true), ("y".to_string(), true)])
        .unwrap();

    assert!(code.contains("def x : Bool := true"));
    assert!(code.contains("def y : Bool := true"));
    assert!(code.contains("theorem sat_verification"));
}
