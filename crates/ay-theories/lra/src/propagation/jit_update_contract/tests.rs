// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn small(num: i64, den: i64) -> Rational {
    Rational::Small(num, den)
}

/// A `Rational::Big` whose numerator exceeds i64, built via the public
/// overflow path (the pure-Rust `BigRational` backing).
fn big_over_i64() -> Rational {
    let r = Rational::from(i64::MAX) * Rational::from(2i64);
    assert!(!r.is_small(), "expected Big variant for 2*i64::MAX");
    r
}

fn inf(num: i64) -> InfRational {
    InfRational::from_rat(small(num, 1))
}

fn inf_eps(x_num: i64, y_num: i64) -> InfRational {
    InfRational::new_rat(small(x_num, 1), small(y_num, 1))
}

fn var(value: InfRational) -> VarInfo {
    VarInfo {
        value,
        lower: None,
        upper: None,
        status: None,
    }
}

fn vars_with(values: &[(u32, InfRational)]) -> Vec<VarInfo> {
    let len = values
        .iter()
        .map(|(idx, _)| *idx as usize)
        .max()
        .unwrap_or(0)
        + 1;
    let mut vars = vec![var(InfRational::default()); len];
    for (idx, value) in values {
        vars[*idx as usize] = var(value.clone());
    }
    vars
}

fn row(basic_var: u32, coeffs: Vec<(u32, Rational)>) -> TableauRow {
    TableauRow::new_rat(basic_var, coeffs, Rational::zero())
}

fn first_bignum_reason(contract: &LraJitUpdateContract) -> LraJitUpdateBignumReason {
    match contract.rows.first() {
        Some(LraJitUpdateRow::BignumRequired(row)) => row.reason,
        other => panic!("expected first row to require bignum, got {other:?}"),
    }
}

#[test]
fn extracts_column_entries_in_deterministic_order() {
    let rows = vec![
        row(4, vec![(1, small(2, 1)), (3, small(7, 1))]),
        row(5, vec![(1, small(-3, 2))]),
    ];
    let vars = vars_with(&[(4, inf(10)), (5, inf(20))]);
    let col_entries = vec![ColEntry::new(1, 0), ColEntry::new(0, 0)];

    let contract = extract_update_nonbasic_jit_contract(1, &inf(2), &rows, &vars, &col_entries)
        .expect("contract extraction should succeed");

    assert_eq!(contract.i64_rows, 2);
    assert_eq!(contract.bignum_rows, 0);
    assert!(!contract.requires_bignum());
    match contract.rows.as_slice() {
        [LraJitUpdateRow::I64FastPath(first), LraJitUpdateRow::I64FastPath(second)] => {
            assert_eq!(first.row_idx, 1);
            assert_eq!(first.basic_var, 5);
            assert_eq!(first.coeff, LraJitI64Rational { num: -3, den: 2 });
            assert_eq!(first.result_x, LraJitI64Rational { num: 17, den: 1 });
            assert_eq!(second.row_idx, 0);
            assert_eq!(second.basic_var, 4);
            assert_eq!(second.coeff, LraJitI64Rational { num: 2, den: 1 });
            assert_eq!(second.result_x, LraJitI64Rational { num: 14, den: 1 });
        }
        other => panic!("unexpected contract rows: {other:?}"),
    }
}

#[test]
fn classifies_big_coefficients_as_bignum_required() {
    let big_coeff = big_over_i64();
    let rows = vec![row(2, vec![(1, big_coeff)])];
    let vars = vars_with(&[(2, inf(0))]);
    let col_entries = vec![ColEntry::new(0, 0)];

    let contract = extract_update_nonbasic_jit_contract(1, &inf(1), &rows, &vars, &col_entries)
        .expect("contract extraction should succeed");

    assert_eq!(contract.i64_rows, 0);
    assert_eq!(contract.bignum_rows, 1);
    assert!(contract.requires_bignum());
    assert_eq!(
        first_bignum_reason(&contract),
        LraJitUpdateBignumReason::BigCoefficient
    );
}

#[test]
fn classifies_product_overflow_as_bignum_required() {
    let rows = vec![row(2, vec![(1, small(i64::MAX, 1))])];
    let vars = vars_with(&[(2, inf(0))]);
    let col_entries = vec![ColEntry::new(0, 0)];

    let contract =
        extract_update_nonbasic_jit_contract(1, &inf(i64::MAX), &rows, &vars, &col_entries)
            .expect("contract extraction should succeed");

    assert_eq!(
        first_bignum_reason(&contract),
        LraJitUpdateBignumReason::ProductOverflow
    );
}

#[test]
fn classifies_result_addition_overflow_as_bignum_required() {
    let rows = vec![row(2, vec![(1, small(1, 1))])];
    let vars = vars_with(&[(2, inf(i64::MAX))]);
    let col_entries = vec![ColEntry::new(0, 0)];

    let contract = extract_update_nonbasic_jit_contract(1, &inf(1), &rows, &vars, &col_entries)
        .expect("contract extraction should succeed");

    assert_eq!(
        first_bignum_reason(&contract),
        LraJitUpdateBignumReason::AdditionOverflow
    );
}

#[test]
fn classifies_non_small_delta_as_bignum_required() {
    let big_delta = InfRational::from_rat(big_over_i64());
    let rows = vec![row(2, vec![(1, small(1, 1))])];
    let vars = vars_with(&[(2, inf(0))]);
    let col_entries = vec![ColEntry::new(0, 0)];

    let contract = extract_update_nonbasic_jit_contract(1, &big_delta, &rows, &vars, &col_entries)
        .expect("contract extraction should succeed");

    assert_eq!(
        first_bignum_reason(&contract),
        LraJitUpdateBignumReason::NonSmallDelta
    );
}

#[test]
fn epsilon_component_must_also_fit_i64_result() {
    let rows = vec![row(2, vec![(1, small(3, 1))])];
    let vars = vars_with(&[(2, inf_eps(0, 4))]);
    let col_entries = vec![ColEntry::new(0, 0)];

    let contract =
        extract_update_nonbasic_jit_contract(1, &inf_eps(2, -1), &rows, &vars, &col_entries)
            .expect("contract extraction should succeed");

    match contract.rows.as_slice() {
        [LraJitUpdateRow::I64FastPath(row)] => {
            assert_eq!(row.result_x, LraJitI64Rational { num: 6, den: 1 });
            assert_eq!(row.result_y, LraJitI64Rational { num: 1, den: 1 });
        }
        other => panic!("unexpected contract rows: {other:?}"),
    }
}

#[test]
fn stale_column_entry_fails_closed_before_lowering() {
    let rows = vec![row(2, vec![(1, small(1, 1)), (3, small(5, 1))])];
    let vars = vars_with(&[(2, inf(0))]);
    let col_entries = vec![ColEntry::new(0, 1)];

    let err = extract_update_nonbasic_jit_contract(1, &inf(1), &rows, &vars, &col_entries)
        .expect_err("stale row_pos must block JIT lowering");

    assert_eq!(
        err,
        LraJitUpdateExtractionError::StaleColumnEntry {
            row_idx: 0,
            row_pos: 1,
            expected_var: 1,
            actual_var: Some(3),
        }
    );
}
