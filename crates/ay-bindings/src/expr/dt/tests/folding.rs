// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn valid_struct_fields_retain_exact_wide_array_and_nested_values() {
    let nested_sort = Sort::struct_type("Nested", [("bit", Sort::bool())]);
    let nested =
        Expr::datatype_constructor("Nested", "Nested_mk", vec![Expr::true_()], nested_sort);
    let fields = [
        ("flag", Expr::false_()),
        (
            "word",
            Expr::bitvec_const((BigInt::from(1u8) << 128usize) + 5, 129),
        ),
        (
            "integer",
            Expr::int_const((BigInt::from(1u8) << 256usize) + 11),
        ),
        (
            "array",
            Expr::var("cells", Sort::array(Sort::bitvec(64), Sort::bitvec(129))),
        ),
        ("nested", nested),
    ];
    let sort = Sort::struct_type(
        "Record",
        fields
            .iter()
            .map(|(name, value)| (*name, value.sort().clone())),
    );
    let record = Expr::try_datatype_constructor(
        "Record",
        "Record_mk",
        fields.iter().map(|(_, value)| value.clone()).collect(),
        sort,
    )
    .expect("well-typed record");
    for (name, expected) in &fields {
        let selected = record
            .clone()
            .try_field_select("Record", *name, expected.sort().clone())
            .expect("declared field");
        assert_eq!(selected.sort(), expected.sort());
        assert!(Arc::ptr_eq(&selected.value, &expected.value));
    }
}

#[test]
fn equal_field_reads_collapse_but_distinct_fields_keep_conditional_values() {
    let cond = Expr::var("choose", Sort::bool());
    let flag = Expr::true_();
    let low = Expr::bitvec_const(7u8, 8);
    let high = Expr::bitvec_const(19u8, 8);
    let state = Expr::ite(
        cond.clone(),
        pair(flag.clone(), low.clone()),
        pair(flag.clone(), high.clone()),
    );
    let selected_flag = state
        .clone()
        .try_field_select("Pair", "flag", Sort::bool())
        .expect("flag");
    assert!(Arc::ptr_eq(&selected_flag.value, &flag.value));
    let selected_word = state
        .try_field_select("Pair", "word", Sort::bitvec(8))
        .expect("word");
    let ExprValue::Ite {
        cond: actual_cond,
        then_expr,
        else_expr,
    } = selected_word.value()
    else {
        panic!("different field values must remain conditional")
    };
    assert!(Arc::ptr_eq(&actual_cond.value, &cond.value));
    assert!(Arc::ptr_eq(&then_expr.value, &low.value));
    assert!(Arc::ptr_eq(&else_expr.value, &high.value));
    for choose in [false, true] {
        let actual = if choose { then_expr } else { else_expr };
        assert_eq!(actual, if choose { &low } else { &high });
    }
}

#[test]
fn invalid_ite_condition_cannot_disappear_behind_equal_selected_fields() {
    let flag = Expr::true_();
    let left = pair(flag.clone(), Expr::bitvec_const(1, 8));
    let right = pair(flag, Expr::bitvec_const(2, 8));
    for cond in [Expr::var("bad", Sort::bitvec(1)), Expr::int_const(0)] {
        let malformed = raw_ite(cond, left.clone(), right.clone(), pair_sort(8));
        assert_error(malformed.try_field_select("Pair", "flag", Sort::bool()));
    }
}

#[test]
fn both_ite_branches_must_match_outer_schema_even_when_requested_field_agrees() {
    let flag = Expr::true_();
    let valid = pair(flag.clone(), Expr::bitvec_const(1, 8));
    let other_schema = pair(flag, Expr::bitvec_const(2, 16));
    for (left, right) in [
        (valid.clone(), other_schema.clone()),
        (other_schema.clone(), valid),
        (other_schema.clone(), other_schema),
    ] {
        let malformed = raw_ite(Expr::var("choose", Sort::bool()), left, right, pair_sort(8));
        assert_error(malformed.try_field_select("Pair", "flag", Sort::bool()));
    }
}

#[test]
fn malformed_unused_constructor_field_is_checked_in_both_ite_branches() {
    let flag = Expr::true_();
    let valid = pair(flag.clone(), Expr::bitvec_const(1, 8));
    let malformed = raw_constructor("Pair", "Pair_mk", vec![flag, Expr::false_()], pair_sort(8));
    for (left, right) in [(valid.clone(), malformed.clone()), (malformed, valid)] {
        let state = raw_ite(Expr::var("choose", Sort::bool()), left, right, pair_sort(8));
        assert_error(state.try_field_select("Pair", "flag", Sort::bool()));
    }
}

#[test]
fn symbolic_datatype_field_retains_its_source_and_declared_result_sort() {
    let source = Expr::var("state", pair_sort(129));
    let selected = source
        .clone()
        .try_field_select("Pair", "word", Sort::bitvec(129))
        .expect("field");
    let ExprValue::DatatypeSelector {
        datatype_name,
        selector_name,
        expr,
    } = selected.value()
    else {
        panic!("symbolic source must retain its selector")
    };
    assert_eq!(datatype_name, "Pair");
    assert_eq!(selector_name, "word");
    assert_eq!(selected.sort(), &Sort::bitvec(129));
    assert!(Arc::ptr_eq(&expr.value, &source.value));
}

#[test]
fn empty_vector_length_survives_nested_struct_state_reconstruction() {
    let vector_sort = Sort::struct_type(
        "Vec",
        [
            ("fld_ptr", Sort::bitvec(64)),
            ("fld_len", Sort::bitvec(64)),
            ("fld_cap", Sort::bitvec(64)),
        ],
    );
    let zero = Expr::bitvec_const(0, 64);
    let vector = Expr::datatype_constructor(
        "Vec",
        "Vec_mk",
        vec![zero.clone(), zero.clone(), zero.clone()],
        vector_sort.clone(),
    );
    let state_sort = Sort::struct_type(
        "State",
        [("data", vector_sort.clone()), ("tick", Sort::bitvec(8))],
    );
    let state = |tick| {
        Expr::datatype_constructor(
            "State",
            "State_mk",
            vec![vector.clone(), Expr::bitvec_const(tick, 8)],
            state_sort.clone(),
        )
    };
    let branches = Expr::ite(Expr::var("advance", Sort::bool()), state(1), state(2));
    let selected = branches
        .try_field_select("State", "data", vector_sort)
        .expect("data")
        .try_field_select("Vec", "fld_len", Sort::bitvec(64))
        .expect("length");
    assert!(Arc::ptr_eq(&selected.value, &zero.value));
}
