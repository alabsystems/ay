// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for ay-core Sort conversions (requires "direct" feature).

use super::*;

/// Test roundtrip conversion for primitive sorts.
#[test]
fn test_primitive_sort_roundtrip() {
    // Bool
    let bindings_bool = Sort::bool();
    let core_bool: ay_core::Sort = (&bindings_bool).into();
    let back_bool: Sort = (&core_bool).into();
    assert_eq!(bindings_bool, back_bool);

    // Int
    let bindings_int = Sort::int();
    let core_int: ay_core::Sort = (&bindings_int).into();
    let back_int: Sort = (&core_int).into();
    assert_eq!(bindings_int, back_int);

    // Real
    let bindings_real = Sort::real();
    let core_real: ay_core::Sort = (&bindings_real).into();
    let back_real: Sort = (&core_real).into();
    assert_eq!(bindings_real, back_real);
}

/// Test roundtrip conversion for bitvector sorts.
#[test]
fn test_bitvec_sort_roundtrip() {
    for width in [8, 16, 32, 64, 128] {
        let bindings_bv = Sort::bitvec(width);
        let core_bv: ay_core::Sort = (&bindings_bv).into();
        let back_bv: Sort = (&core_bv).into();
        assert_eq!(bindings_bv, back_bv, "Bitvec({}) roundtrip failed", width);
    }
}

/// Test roundtrip conversion for array sorts.
#[test]
fn test_array_sort_roundtrip() {
    // Simple array: Int -> Bool
    let bindings_arr = Sort::array(Sort::int(), Sort::bool());
    let core_arr: ay_core::Sort = (&bindings_arr).into();
    let back_arr: Sort = (&core_arr).into();
    assert_eq!(bindings_arr, back_arr);

    // Memory array: BitVec(64) -> BitVec(8)
    let bindings_mem = Sort::memory();
    let core_mem: ay_core::Sort = (&bindings_mem).into();
    let back_mem: Sort = (&core_mem).into();
    assert_eq!(bindings_mem, back_mem);

    // Nested array: Int -> (Bool -> BitVec(32))
    let bindings_nested = Sort::array(Sort::int(), Sort::array(Sort::bool(), Sort::bv32()));
    let core_nested: ay_core::Sort = (&bindings_nested).into();
    let back_nested: Sort = (&core_nested).into();
    assert_eq!(bindings_nested, back_nested);
}

/// Test roundtrip conversion for struct datatype sorts.
#[test]
fn test_struct_datatype_roundtrip() {
    let bindings_struct = Sort::struct_type("Point", [("x", Sort::int()), ("y", Sort::int())]);
    let core_struct: ay_core::Sort = (&bindings_struct).into();
    let back_struct: Sort = (&core_struct).into();
    assert_eq!(bindings_struct, back_struct);
}

/// Test roundtrip conversion for enum datatype sorts.
#[test]
fn test_enum_datatype_roundtrip() {
    let bindings_enum = Sort::enum_type(
        "Option_i32",
        vec![("None", vec![]), ("Some", vec![("value", Sort::bv32())])],
    );
    let core_enum: ay_core::Sort = (&bindings_enum).into();
    let back_enum: Sort = (&core_enum).into();
    assert_eq!(bindings_enum, back_enum);
}

/// Test conversion from ay-core to ay-bindings for primitive sorts.
#[test]
fn test_from_core_primitives() {
    assert_eq!(Sort::from(&ay_core::Sort::Bool), Sort::bool());
    assert_eq!(Sort::from(&ay_core::Sort::Int), Sort::int());
    assert_eq!(Sort::from(&ay_core::Sort::Real), Sort::real());
}

/// Test conversion from ay-core to ay-bindings for bitvector sorts.
#[test]
fn test_from_core_bitvec() {
    let core_bv32 = ay_core::Sort::bitvec(32);
    assert_eq!(Sort::from(&core_bv32), Sort::bv32());

    let core_bv64 = ay_core::Sort::bitvec(64);
    assert_eq!(Sort::from(&core_bv64), Sort::bv64());
}

/// Test that previously-panicking ay-core sorts now convert successfully (#5426).
#[test]
fn test_string_sort_roundtrip() {
    let s = Sort::from(&ay_core::Sort::String);
    assert!(matches!(s.inner(), SortInner::String));
    assert_eq!(format!("{}", s), "String");
    assert_eq!(ay_core::Sort::from(&s), ay_core::Sort::String);
}

#[test]
fn test_fp_sort_roundtrip() {
    let s = Sort::from(&ay_core::Sort::FloatingPoint(8, 24));
    assert!(matches!(s.inner(), SortInner::FloatingPoint(8, 24)));
    assert_eq!(format!("{}", s), "(_ FloatingPoint 8 24)");
    assert_eq!(ay_core::Sort::from(&s), ay_core::Sort::FloatingPoint(8, 24));
}

#[test]
fn test_uninterpreted_sort_roundtrip() {
    let s = Sort::from(&ay_core::Sort::Uninterpreted("CustomSort".into()));
    assert!(matches!(s.inner(), SortInner::Uninterpreted(_)));
    assert_eq!(format!("{}", s), "CustomSort");
    assert_eq!(
        ay_core::Sort::from(&s),
        ay_core::Sort::Uninterpreted("CustomSort".into())
    );
}

#[test]
fn test_reglan_sort_roundtrip() {
    let s = Sort::from(&ay_core::Sort::RegLan);
    assert!(matches!(s.inner(), SortInner::RegLan));
    assert_eq!(format!("{}", s), "RegLan");
    assert_eq!(ay_core::Sort::from(&s), ay_core::Sort::RegLan);
}

/// Test as_term_sort() converts datatypes to uninterpreted sorts.
#[test]
fn test_as_term_sort_datatype() {
    let color = Sort::simple_enum_type("Color", ["Red", "Green", "Blue"]);
    let term_sort = color.as_term_sort();
    assert!(matches!(term_sort, ay_core::Sort::Uninterpreted(name) if name == "Color"));
}

/// Test as_term_sort() preserves primitive sorts.
#[test]
fn test_as_term_sort_primitives() {
    assert_eq!(Sort::bool().as_term_sort(), ay_core::Sort::Bool);
    assert_eq!(Sort::int().as_term_sort(), ay_core::Sort::Int);
    assert_eq!(Sort::real().as_term_sort(), ay_core::Sort::Real);
    assert_eq!(Sort::bv32().as_term_sort(), ay_core::Sort::bitvec(32));
}

/// Test as_term_sort() recursively converts arrays with datatype elements.
#[test]
fn test_as_term_sort_array_with_datatype() {
    let color = Sort::simple_enum_type("Color", ["Red", "Green", "Blue"]);
    let arr = Sort::array(Sort::int(), color);
    let term_arr = arr.as_term_sort();

    match term_arr {
        ay_core::Sort::Array(arr_inner) => {
            assert_eq!(arr_inner.index_sort, ay_core::Sort::Int);
            assert!(matches!(&arr_inner.element_sort,
                ay_core::Sort::Uninterpreted(name) if name == "Color"));
        }
        _ => panic!("Expected Array sort"),
    }
}
