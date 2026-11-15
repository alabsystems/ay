// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn literal(text: &str) -> FrontendTerm {
    FrontendTerm::Const(if text.starts_with("#x") {
        FrontendConstant::Hexadecimal(text.to_string())
    } else {
        FrontendConstant::Binary(text.to_string())
    })
}

fn equality(constant: &str) -> FrontendTerm {
    FrontendTerm::App(
        "=".to_string(),
        vec![FrontendTerm::Symbol("x".to_string()), literal(constant)],
    )
}

#[test]
fn a_hexadecimal_literal_matches_its_binary_spelling() {
    assert!(same_modulo_bv_literal_spelling(
        &equality("#b11111111"),
        &equality("#xff")
    ));
    assert!(same_modulo_bv_literal_spelling(
        &equality("#b00001010"),
        &equality("#x0A")
    ));
}

#[test]
fn a_different_value_or_width_still_differs() {
    assert!(!same_modulo_bv_literal_spelling(
        &equality("#b11111110"),
        &equality("#xff")
    ));
    assert!(!same_modulo_bv_literal_spelling(
        &equality("#b011111111"),
        &equality("#xff")
    ));
    assert!(!same_modulo_bv_literal_spelling(
        &equality("#b1111"),
        &equality("#xff")
    ));
}

fn indexed(value: &str, width: &str) -> FrontendTerm {
    FrontendTerm::IndexedApp(
        format!("bv{value}"),
        vec![FrontendIndex::Numeral(width.to_string())],
        Vec::new(),
    )
}

#[test]
fn an_indexed_constant_matches_its_binary_spelling_and_nothing_else() {
    let x = FrontendTerm::Symbol("x".to_string());
    let with =
        |constant: FrontendTerm| FrontendTerm::App("=".to_string(), vec![x.clone(), constant]);
    assert!(same_modulo_bv_literal_spelling(
        &with(literal("#b00000111")),
        &with(indexed("7", "8"))
    ));
    assert!(same_modulo_bv_literal_spelling(
        &with(literal("#b00000000")),
        &with(indexed("0", "8"))
    ));
    assert!(!same_modulo_bv_literal_spelling(
        &with(literal("#b00000110")),
        &with(indexed("7", "8"))
    ));
    assert!(!same_modulo_bv_literal_spelling(
        &with(literal("#b0000111")),
        &with(indexed("7", "8"))
    ));
    // A value that does not fit its width keeps its spelling.
    assert!(!same_modulo_bv_literal_spelling(
        &with(literal("#b00")),
        &with(indexed("4", "2"))
    ));
}

#[test]
fn indexed_numeral_normalization_bounds_significant_digits_before_arithmetic() {
    assert_eq!(
        indexed_constant_in_binary(
            &format!("bv{}1", "0".repeat(16_384)),
            &[FrontendIndex::Numeral("2".into())]
        )
        .as_deref(),
        Some("#b01")
    );
    assert!(indexed_constant_in_binary(
        &format!("bv{}", "9".repeat(4097)),
        &[FrontendIndex::Numeral("4096".into())]
    )
    .is_none());
}
