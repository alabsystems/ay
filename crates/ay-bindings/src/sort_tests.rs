// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_sort_constructors() {
    assert!(Sort::bool().is_bool());
    assert!(Sort::bitvec(32).is_bitvec());
    assert!(Sort::int().is_int());
    assert!(Sort::real().is_real());
    assert!(Sort::memory().is_array());
}

#[test]
fn test_bitvec_width() {
    assert_eq!(Sort::bv8().bitvec_width(), Some(8));
    assert_eq!(Sort::bv16().bitvec_width(), Some(16));
    assert_eq!(Sort::bv32().bitvec_width(), Some(32));
    assert_eq!(Sort::bv64().bitvec_width(), Some(64));
    assert_eq!(Sort::bv128().bitvec_width(), Some(128));
    assert_eq!(Sort::bool().bitvec_width(), None);
}

#[test]
fn test_sort_display() {
    assert_eq!(Sort::bool().to_string(), "Bool");
    assert_eq!(Sort::bv32().to_string(), "(_ BitVec 32)");
    assert_eq!(Sort::int().to_string(), "Int");
    assert_eq!(Sort::real().to_string(), "Real");
    assert_eq!(
        Sort::memory().to_string(),
        "(Array (_ BitVec 64) (_ BitVec 8))"
    );
}

#[test]
fn test_datatype_helpers() {
    let point = Sort::struct_type("Point", [("x", Sort::bv32()), ("y", Sort::bv32())]);

    assert_eq!(point.datatype_name(), Some("Point"));
    // Constructor name is now prefixed with datatype name for uniqueness (#948)
    assert!(point.datatype_has_constructor("Point_mk"));
    assert!(!point.datatype_has_constructor("mk")); // Old generic name no longer used
    assert!(!point.datatype_has_constructor("Missing"));
    assert!(point.datatype_has_field("x"));
    assert!(!point.datatype_has_field("missing"));
    assert_eq!(Sort::bool().datatype_name(), None);
    assert!(!Sort::bool().datatype_has_constructor("Point_mk"));
    assert!(!Sort::bool().datatype_has_field("x"));
}

#[test]
fn test_struct_type() {
    let point = Sort::struct_type("Point", [("x", Sort::bv32()), ("y", Sort::bv32())]);
    assert!(point.is_datatype());
    assert_eq!(point.to_string(), "Point");
}

#[test]
fn test_enum_type() {
    let option_i32 = Sort::enum_type(
        "Option_i32",
        vec![("None", vec![]), ("Some", vec![("value", Sort::bv32())])],
    );
    assert!(option_i32.is_datatype());
}

#[test]
fn test_simple_enum_type() {
    // Simple enum with nullary constructors - matches ay-core signature
    let color = Sort::simple_enum_type("Color", ["Red", "Green", "Blue"]);
    assert!(color.is_datatype());

    let dt = color.datatype_sort().unwrap();
    assert_eq!(dt.name, "Color");
    assert_eq!(dt.constructors.len(), 3);
    assert_eq!(dt.constructors[0].name, "Red");
    assert_eq!(dt.constructors[1].name, "Green");
    assert_eq!(dt.constructors[2].name, "Blue");

    // All constructors should be nullary
    for ctor in &dt.constructors {
        assert!(ctor.fields.is_empty());
    }
}

#[test]
#[should_panic(expected = "BitVec width must be > 0")]
fn test_zero_width_panics() {
    let _ = Sort::bitvec(0);
}

#[test]
fn test_arc_sharing() {
    // Verify that cloning Sort shares the underlying Arc, not deep copying
    let sort1 = Sort::struct_type(
        "BigStruct",
        [
            ("field1", Sort::bv32()),
            ("field2", Sort::bv64()),
            ("field3", Sort::int()),
        ],
    );
    let sort2 = sort1.clone();

    // Both should be equal
    assert_eq!(sort1, sort2);

    // They should share the same underlying SortInner (pointer equality)
    assert!(std::ptr::eq(sort1.inner(), sort2.inner()));
}

#[test]
fn test_bitvec_sort_helper() {
    // Test bitvec_sort() returns Some for bitvector sorts
    let bv = Sort::bv32();
    let bv_sort = bv.bitvec_sort();
    assert!(bv_sort.is_some());
    assert_eq!(bv_sort.unwrap().width, 32);

    // Test bitvec_sort() returns None for non-bitvector sorts
    assert!(Sort::bool().bitvec_sort().is_none());
    assert!(Sort::int().bitvec_sort().is_none());
    assert!(Sort::memory().bitvec_sort().is_none());
}

#[test]
fn test_array_sort_accessor() {
    // Test array_sort() returns Some for array sorts
    let arr = Sort::array(Sort::int(), Sort::bool());
    let arr_sort = arr.array_sort().expect("should be array");
    assert!(arr_sort.index_sort.is_int());
    assert!(arr_sort.element_sort.is_bool());

    // Test with memory sort (Array (_ BitVec 64) (_ BitVec 8))
    let mem = Sort::memory();
    let mem_sort = mem.array_sort().expect("memory should be array");
    assert_eq!(mem_sort.index_sort.bitvec_width(), Some(64));
    assert_eq!(mem_sort.element_sort.bitvec_width(), Some(8));

    // Test array_sort() returns None for non-array sorts
    assert!(Sort::int().array_sort().is_none());
    assert!(Sort::bool().array_sort().is_none());
    assert!(Sort::bv32().array_sort().is_none());

    // Test nested array (array of arrays)
    let nested = Sort::array(Sort::int(), Sort::array(Sort::bool(), Sort::bv8()));
    let outer_arr = nested.array_sort().expect("outer should be array");
    assert!(outer_arr.index_sort.is_int());
    assert!(outer_arr.element_sort.is_array());
    let inner_arr = outer_arr
        .element_sort
        .array_sort()
        .expect("inner should be array");
    assert!(inner_arr.index_sort.is_bool());
    assert_eq!(inner_arr.element_sort.bitvec_width(), Some(8));
}

#[test]
fn test_datatype_sort_accessor() {
    // Test datatype_sort() returns Some for datatype sorts
    let point = Sort::struct_type("Point", [("x", Sort::int()), ("y", Sort::int())]);
    let dt_sort = point.datatype_sort().expect("should be datatype");
    assert_eq!(dt_sort.name, "Point");
    assert_eq!(dt_sort.constructors.len(), 1);
    assert_eq!(dt_sort.constructors[0].name, "Point_mk");
    assert_eq!(dt_sort.constructors[0].fields.len(), 2);

    // Test datatype_sort() returns None for non-datatype sorts
    assert!(Sort::bool().datatype_sort().is_none());
    assert!(Sort::int().datatype_sort().is_none());
    assert!(Sort::bv64().datatype_sort().is_none());
    assert!(Sort::memory().datatype_sort().is_none());
}

#[test]
fn test_datatype_default_constructor() {
    // Test struct type returns the "_mk" constructor
    let point = Sort::struct_type("Point", [("x", Sort::int()), ("y", Sort::int())]);
    assert_eq!(point.datatype_default_constructor(), Some("Point_mk"));

    // Test enum type returns the first variant's constructor
    let option = Sort::enum_type(
        "Option_i32",
        vec![("None", vec![]), ("Some", vec![("value", Sort::bv32())])],
    );
    assert_eq!(option.datatype_default_constructor(), Some("None"));

    // Test non-datatype sorts return None
    assert!(Sort::bool().datatype_default_constructor().is_none());
    assert!(Sort::int().datatype_default_constructor().is_none());
    assert!(Sort::memory().datatype_default_constructor().is_none());
}

#[test]
fn test_tuple_type() {
    // Test tuple with two elements
    let pair = Sort::tuple(vec![Sort::int(), Sort::bool()]);
    assert!(pair.is_datatype());
    assert_eq!(pair.datatype_name(), Some("Tuple2"));
    assert!(pair.datatype_has_field("_0"));
    assert!(pair.datatype_has_field("_1"));
    assert!(!pair.datatype_has_field("_2"));
    assert_eq!(pair.datatype_default_constructor(), Some("Tuple2_mk"));

    // Test tuple with three elements
    let triple = Sort::tuple(vec![Sort::bv32(), Sort::int(), Sort::real()]);
    assert!(triple.is_datatype());
    assert_eq!(triple.datatype_name(), Some("Tuple3"));
    assert!(triple.datatype_has_field("_0"));
    assert!(triple.datatype_has_field("_1"));
    assert!(triple.datatype_has_field("_2"));

    // Test single-element tuple
    let single = Sort::tuple(vec![Sort::bool()]);
    assert!(single.is_datatype());
    assert_eq!(single.datatype_name(), Some("Tuple1"));
    assert!(single.datatype_has_field("_0"));
}

#[test]
#[should_panic(expected = "Tuple must have at least one element")]
fn test_empty_tuple_panics() {
    let _ = Sort::tuple(vec![]);
}
