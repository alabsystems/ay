// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

//! Actual fallible array-store boundary, including its legacy collection bridge.
//! These are synthetic descriptor controls, not retained consumer verdicts.

use crate::memory::POINTER_WIDTH;
use crate::{Expr, ExprValue, Sort, SortError};
use std::sync::Arc;

fn pointer_sort() -> Sort {
    Sort::bitvec(POINTER_WIDTH)
}

fn fields() -> Vec<(&'static str, Sort)> {
    vec![
        ("fld_ptr", pointer_sort()),
        ("fld_len", pointer_sort()),
        ("fld_cap", pointer_sort()),
    ]
}

fn store(element: &Sort, value: Expr) -> Result<Expr, SortError> {
    Expr::var("memory", Sort::array(pointer_sort(), element.clone()))
        .try_store(Expr::bitvec_const(7, POINTER_WIDTH), value)
}

fn stored_value<'a>(stored: &'a Expr, element: &Sort) -> &'a Expr {
    assert_eq!(stored.sort(), &Sort::array(pointer_sort(), element.clone()));
    let ExprValue::Store {
        array,
        index,
        value,
    } = stored.value()
    else {
        panic!("expected the real Store node")
    };
    assert_eq!(array.sort(), stored.sort());
    assert_eq!(index, &Expr::bitvec_const(7, POINTER_WIDTH));
    assert_eq!(value.sort(), element);
    value
}

fn assert_collection(stored: &Expr, sort: &Sort, pointer: &Expr) {
    let value = stored_value(stored, sort);
    let ExprValue::DatatypeConstructor {
        datatype_name,
        constructor_name,
        args,
    } = value.value()
    else {
        panic!("the bridge must construct the collection")
    };
    let datatype = sort.datatype_sort().unwrap();
    let constructor = &datatype.constructors[0];
    assert_eq!(datatype_name, &datatype.name);
    assert_eq!(constructor_name, &constructor.name);
    assert_eq!(args.len(), constructor.fields.len());
    for (field, argument) in constructor.fields.iter().zip(args) {
        assert_eq!(argument.sort(), &field.sort);
        match field.name.as_str() {
            "fld_ptr" => assert!(Arc::ptr_eq(&argument.value, &pointer.value)),
            "fld_len" | "fld_cap" => {
                let zero = if field.sort.is_int() {
                    Expr::int_const(0)
                } else {
                    Expr::bitvec_const(0, field.sort.bitvec_width().unwrap())
                };
                assert_eq!(argument, &zero);
            }
            other => panic!("unrequested field fabricated: {other}"),
        }
    }
}

#[test]
fn three_field_vec_and_string_preserve_pointer_and_typed_zero_lengths() {
    for name in ["Vec", "String"] {
        for len in [pointer_sort(), Sort::int()] {
            for cap in [Sort::bitvec(32), Sort::int()] {
                let sort = Sort::struct_type(
                    name,
                    [
                        ("fld_ptr", pointer_sort()),
                        ("fld_len", len.clone()),
                        ("fld_cap", cap),
                    ],
                );
                let pointer = Expr::bitvec_const(19, POINTER_WIDTH);
                let result = store(&sort, pointer.clone()).expect("ordinary collection bridge");
                assert_collection(&result, &sort, &pointer);
            }
        }
    }
}

#[test]
fn maximum_width_lengths_use_canonical_constant_size_zero_payloads() {
    for name in ["Vec", "String"] {
        let sort = Sort::struct_type(
            name,
            [
                ("fld_ptr", pointer_sort()),
                ("fld_len", Sort::bitvec(u32::MAX)),
                ("fld_cap", Sort::bitvec(u32::MAX)),
            ],
        );
        let pointer = Expr::bitvec_const(19, POINTER_WIDTH);
        let result = store(&sort, pointer.clone()).expect("zero needs no width-sized modulus");
        let ExprValue::DatatypeConstructor { args, .. } = stored_value(&result, &sort).value()
        else {
            panic!("collection constructor")
        };
        assert_eq!(args.len(), 3);
        assert!(Arc::ptr_eq(&args[0].value, &pointer.value));
        for argument in &args[1..] {
            assert_eq!(argument.sort().bitvec_width(), Some(u32::MAX));
            let ExprValue::BitVecConst { value, width } = argument.value() else {
                panic!("already canonical zero, without bitvec_const normalization")
            };
            assert_eq!(*width, u32::MAX);
            assert_eq!(value, &num_bigint::BigInt::from(0));
            assert_eq!(value.bits(), 0);
        }
    }
}

#[test]
fn field_permutations_never_move_the_pointer_into_a_length_or_capacity_slot() {
    for name in ["Vec", "String"] {
        for order in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            let original = fields();
            let sort = Sort::struct_type(name, order.map(|index| original[index].clone()));
            let pointer = Expr::bitvec_const(29, POINTER_WIDTH);
            let result = store(&sort, pointer.clone()).expect("valid named three-field layout");
            assert_collection(&result, &sort, &pointer);
        }
    }
}

#[test]
fn four_field_collections_refuse_pointer_only_construction_without_inventing_data() {
    for name in ["Vec", "String"] {
        for data in [Sort::array(pointer_sort(), Sort::bv8()), Sort::bool()] {
            let mut with_data = fields();
            with_data.push(("fld_data", data));
            let sort = Sort::struct_type(name, with_data);
            assert!(store(&sort, Expr::bitvec_const(19, POINTER_WIDTH)).is_err());
            // A value already carrying that exact datatype is not a request for fabrication.
            let actual = Expr::var("complete_collection", sort.clone());
            let result = store(&sort, actual.clone()).expect("already typed value");
            assert!(Arc::ptr_eq(
                &stored_value(&result, &sort).value,
                &actual.value
            ));
            // Reading its declared pointer does not invent or discard any data constraint.
            let result = store(&pointer_sort(), actual.clone()).expect("four-field pointer read");
            let ExprValue::DatatypeSelector {
                selector_name,
                expr,
                ..
            } = stored_value(&result, &pointer_sort()).value()
            else {
                panic!("declared symbolic pointer selector")
            };
            assert_eq!(selector_name, "fld_ptr");
            assert!(Arc::ptr_eq(&expr.value, &actual.value));
        }
    }
}

#[test]
fn missing_duplicate_unknown_or_non_numeric_fields_refuse_coercion() {
    for name in ["Vec", "String"] {
        for removed in 0..3 {
            let mut missing = fields();
            missing.remove(removed);
            assert!(store(
                &Sort::struct_type(name, missing),
                Expr::var("ptr", pointer_sort())
            )
            .is_err());
        }
        for (position, replacement) in [
            (0, ("fld_ptr", Sort::bv32())),
            (0, ("fld_ptr", Sort::int())),
            (1, ("fld_len", Sort::bool())),
            (2, ("fld_cap", Sort::real())),
            (1, ("not_len", pointer_sort())),
            (2, ("fld_len", pointer_sort())),
        ] {
            let mut malformed = fields();
            malformed[position] = replacement;
            let sort = Sort::struct_type(name, malformed);
            assert!(store(&sort, Expr::var("ptr", pointer_sort())).is_err());
        }
        let sort = Sort::struct_type(name, fields());
        assert!(store(&sort, Expr::var("narrow_pointer", Sort::bv32())).is_err());
    }
}

#[test]
fn enum_pointer_fields_cannot_authorize_ambiguous_collection_coercion() {
    for name in ["Vec", "String"] {
        let sort = Sort::enum_type(
            name,
            [
                (format!("{name}_mk"), fields()),
                ("Other".to_owned(), vec![("fld_ptr", Sort::bv32())]),
            ],
        );
        assert!(store(&sort, Expr::var("ptr", pointer_sort())).is_err());
        assert!(store(&pointer_sort(), Expr::var("ambiguous", sort)).is_err());
    }
}

#[test]
fn datatype_to_pointer_uses_the_declared_selector_or_exact_constructor_argument() {
    for name in ["Vec", "String"] {
        let sort = Sort::struct_type(name, fields());
        let symbolic = Expr::var("collection", sort.clone());
        let result = store(&pointer_sort(), symbolic.clone()).expect("symbolic pointer projection");
        let ExprValue::DatatypeSelector {
            datatype_name,
            selector_name,
            expr,
        } = stored_value(&result, &pointer_sort()).value()
        else {
            panic!("symbolic selector")
        };
        assert_eq!(datatype_name, name);
        assert_eq!(selector_name, "fld_ptr");
        assert!(Arc::ptr_eq(&expr.value, &symbolic.value));

        let pointer = Expr::bitvec_const(41, POINTER_WIDTH);
        let collection = Expr::try_datatype_constructor(
            name,
            format!("{name}_mk"),
            vec![
                pointer.clone(),
                Expr::bitvec_const(5, POINTER_WIDTH),
                Expr::bitvec_const(9, POINTER_WIDTH),
            ],
            sort,
        )
        .expect("valid source constructor");
        let result = store(&pointer_sort(), collection).expect("constructor pointer projection");
        assert!(Arc::ptr_eq(
            &stored_value(&result, &pointer_sort()).value,
            &pointer.value
        ));
    }
}

#[test]
fn malformed_datatype_to_pointer_returns_error_instead_of_panicking_or_retyping() {
    let sort = Sort::struct_type("Vec", fields());
    for (datatype_name, constructor_name, args) in [
        (
            "Foreign",
            "Vec_mk",
            vec![Expr::bitvec_const(41, POINTER_WIDTH); 3],
        ),
        (
            "Vec",
            "Missing",
            vec![Expr::bitvec_const(41, POINTER_WIDTH); 3],
        ),
        ("Vec", "Vec_mk", Vec::new()),
        (
            "Vec",
            "Vec_mk",
            vec![
                Expr::true_(),
                Expr::bitvec_const(0, POINTER_WIDTH),
                Expr::bitvec_const(0, POINTER_WIDTH),
            ],
        ),
    ] {
        // Expr is the crate-owned AST; deliberately corrupt only descriptor metadata/args.
        let malformed = Expr {
            sort: sort.clone(),
            value: Arc::new(ExprValue::DatatypeConstructor {
                datatype_name: datatype_name.to_owned(),
                constructor_name: constructor_name.to_owned(),
                args,
            }),
        };
        assert!(store(&pointer_sort(), malformed).is_err());
    }
    for shape in [
        Sort::struct_type(
            "Vec",
            [("fld_len", pointer_sort()), ("fld_cap", pointer_sort())],
        ),
        Sort::struct_type("Vec", [("fld_ptr", Sort::bv32())]),
    ] {
        assert!(store(&pointer_sort(), Expr::var("bad_collection", shape)).is_err());
    }
}

#[test]
fn ordinary_integer_bitvector_coercions_keep_the_original_value_and_width() {
    let bits = Expr::bitvec_const(255u16, 8);
    let result = store(&Sort::int(), bits.clone()).expect("BV to Int");
    let ExprValue::Bv2Int(source) = stored_value(&result, &Sort::int()).value() else {
        panic!("unsigned conversion")
    };
    assert!(Arc::ptr_eq(&source.value, &bits.value));
    let integer = Expr::int_const(-1);
    let result = store(&Sort::bv8(), integer.clone()).expect("Int to BV");
    let ExprValue::Int2Bv(source, width) = stored_value(&result, &Sort::bv8()).value() else {
        panic!("modular conversion")
    };
    assert_eq!(*width, 8);
    assert!(Arc::ptr_eq(&source.value, &integer.value));
}

#[test]
fn already_typed_array_elements_are_preserved_without_coercion() {
    for sort in [
        Sort::bool(),
        Sort::int(),
        Sort::bv8(),
        Sort::array(pointer_sort(), Sort::bv8()),
    ] {
        let original = Expr::var("original", sort.clone());
        let result = store(&sort, original.clone()).expect("matching element sort");
        assert!(Arc::ptr_eq(
            &stored_value(&result, &sort).value,
            &original.value
        ));
    }
}
