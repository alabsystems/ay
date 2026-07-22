// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use crate::constraint::Constraint;
use crate::sort::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

#[test]
fn test_declare_datatype_struct() {
    let dt = DatatypeSort {
        name: "Point".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Point_mk".to_string(),
            fields: vec![
                DatatypeField {
                    name: "x".to_string(),
                    sort: Sort::bv32(),
                },
                DatatypeField {
                    name: "y".to_string(),
                    sort: Sort::bv32(),
                },
            ],
        }],
    };
    let c = Constraint::declare_datatype(dt);
    assert_eq!(
        c.to_string(),
        "(declare-datatype Point ((Point_mk (x (_ BitVec 32)) (y (_ BitVec 32)))))"
    );
}

#[test]
fn test_declare_datatype_tuple() {
    let dt = DatatypeSort {
        name: "Tuple_bv32_bv32".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Tuple_bv32_bv32_mk".to_string(),
            fields: vec![
                DatatypeField {
                    name: "fld_0".to_string(),
                    sort: Sort::bv32(),
                },
                DatatypeField {
                    name: "fld_1".to_string(),
                    sort: Sort::bv32(),
                },
            ],
        }],
    };
    let c = Constraint::declare_datatype(dt);
    assert_eq!(
        c.to_string(),
        "(declare-datatype Tuple_bv32_bv32 ((Tuple_bv32_bv32_mk (fld_0 (_ BitVec 32)) (fld_1 (_ BitVec 32)))))"
    );
}

#[test]
fn test_declare_datatype_enum() {
    let dt = DatatypeSort {
        name: "Option_i32".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "value".to_string(),
                    sort: Sort::bv32(),
                }],
            },
        ],
    };
    let c = Constraint::declare_datatype(dt);
    assert_eq!(
        c.to_string(),
        "(declare-datatype Option_i32 ((None) (Some (value (_ BitVec 32)))))"
    );
}
