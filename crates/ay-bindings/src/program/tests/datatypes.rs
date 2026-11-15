// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use crate::program::AYProgram;
use crate::sort::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
use crate::SortError;

#[test]
fn test_declare_datatype() {
    let mut program = AYProgram::new();
    assert!(!program.has_datatypes());

    let dt = DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Pair_mk".to_string(),
            fields: vec![
                DatatypeField {
                    name: "fst".to_string(),
                    sort: Sort::bv32(),
                },
                DatatypeField {
                    name: "snd".to_string(),
                    sort: Sort::bv32(),
                },
            ],
        }],
    };

    // First declaration succeeds
    assert!(program.declare_datatype(dt.clone()));
    assert!(program.has_datatypes());
    assert!(program.is_datatype_declared("Pair"));

    // Second declaration is idempotent (returns false)
    assert!(!program.declare_datatype(dt));
}

/// `(declare-datatype Level ((zero) (succ (pred <pred>))))`
fn level_with_pred(pred: Sort) -> DatatypeSort {
    Sort::enum_type(
        "Level",
        vec![("zero", vec![]), ("succ", vec![("pred", pred)])],
    )
    .datatype_sort()
    .unwrap()
    .clone()
}

fn refusal(result: Result<bool, SortError>) -> String {
    match result {
        Err(error) => error.to_string(),
        Ok(admitted) => panic!("expected a refusal, got Ok({admitted})"),
    }
}

#[test]
fn declaring_a_conflicting_same_name_datatype_is_refused() {
    let mut program = AYProgram::new();
    let level = level_with_pred(Sort::datatype_ref("Level"));
    assert!(program.try_declare_datatype(level.clone()).unwrap());
    // An equal declaration from a separate allocation is a repeat, not a
    // conflict, and adds no second command.
    let commands = program.commands.len();
    assert!(!program
        .try_declare_datatype(level_with_pred(Sort::datatype_ref("Level")))
        .unwrap());
    assert_eq!(program.commands.len(), commands);

    // A different datatype under the name is refused, not silently dropped.
    let impostor = Sort::enum_type("Level", vec![("zero", Vec::<(&str, Sort)>::new())])
        .datatype_sort()
        .unwrap()
        .clone();
    let message = refusal(program.try_declare_datatype(impostor));
    assert!(
        message.contains("conflicting datatype definitions under one name"),
        "{message}"
    );
    // So is the same shape with the recursive field spelled as a bare name.
    let message =
        refusal(program.try_declare_datatype(level_with_pred(Sort::uninterpreted("Level"))));
    assert!(
        message.contains("conflicting datatype definitions under one name"),
        "{message}"
    );
    assert_eq!(program.commands.len(), commands);
    assert_eq!(
        program.declared_datatypes["Level"].datatype_sort(),
        Some(&level)
    );
}

#[test]
#[should_panic(expected = "one well-formed datatype definition per name")]
fn the_panicking_wrapper_refuses_a_conflict_too() {
    let mut program = AYProgram::new();
    assert!(program.declare_datatype(level_with_pred(Sort::datatype_ref("Level"))));
    let _ = program.declare_datatype(level_with_pred(Sort::int()));
}

#[test]
fn declaring_a_datatype_with_a_dangling_field_ref_is_refused_at_declaration() {
    let mut program = AYProgram::new();
    let message =
        refusal(program.try_declare_datatype(level_with_pred(Sort::datatype_ref("Ghost"))));
    assert!(
        message.contains("`Ghost` in the declaration of `Level` names no enclosing datatype"),
        "{message}"
    );
    assert!(!program.has_datatypes());

    // A reference nested under an array still resolves to the declaration;
    // a reference to a sibling that is inlined resolves to that inline
    // declaration; a bare sibling reference does not.
    let tree = Sort::enum_type(
        "Tree",
        vec![
            ("leaf", vec![]),
            (
                "node",
                vec![("kids", Sort::array(Sort::int(), Sort::datatype_ref("Tree")))],
            ),
        ],
    );
    assert!(program
        .try_declare_datatype(tree.datatype_sort().unwrap().clone())
        .unwrap());
    let block = Sort::enum_type("Block", vec![("leaf", Vec::<(&str, Sort)>::new())]);
    let tower = |top: Sort| {
        Sort::enum_type(
            "Tower",
            vec![
                ("empty", vec![]),
                (
                    "stack",
                    vec![("top", top), ("rest", Sort::datatype_ref("Tower"))],
                ),
            ],
        )
        .datatype_sort()
        .unwrap()
        .clone()
    };
    assert!(program
        .try_declare_datatype(tower(Sort::datatype_ref("Block")))
        .is_err());
    assert!(!program.is_datatype_declared("Tower"));
    assert!(program.try_declare_datatype(tower(block)).unwrap());
}

#[test]
fn declaring_a_malformed_datatype_is_refused() {
    let mut program = AYProgram::new();
    let empty = DatatypeSort {
        name: "Empty".to_string(),
        constructors: vec![],
    };
    assert!(program.try_declare_datatype(empty).is_err());
    let duplicate = DatatypeSort {
        name: "Dup".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "a".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "a".to_string(),
                fields: vec![],
            },
        ],
    };
    assert!(program.try_declare_datatype(duplicate).is_err());
    assert!(!program.has_datatypes());
}

#[test]
fn test_upgrade_logic_for_datatypes() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFBV");

    // No datatypes, no upgrade
    program.upgrade_logic_for_datatypes();
    assert!(program.to_string().contains("QF_AUFBV"));

    // Add a datatype
    let dt = DatatypeSort {
        name: "Unit".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Unit_mk".to_string(),
            fields: vec![],
        }],
    };
    program.declare_datatype(dt);

    // Now should upgrade to ALL
    program.upgrade_logic_for_datatypes();
    assert!(program.to_string().contains("(set-logic ALL)"));
}

#[test]
fn test_upgrade_logic_skips_horn() {
    let mut program = AYProgram::horn();

    let dt = DatatypeSort {
        name: "Unit".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Unit_mk".to_string(),
            fields: vec![],
        }],
    };
    program.declare_datatype(dt);

    // HORN should not be upgraded
    program.upgrade_logic_for_datatypes();
    assert!(program.to_string().contains("(set-logic HORN)"));
}

#[test]
fn test_upgrade_logic_skips_all() {
    let mut program = AYProgram::new();
    program.set_logic("ALL");

    let dt = DatatypeSort {
        name: "Unit".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Unit_mk".to_string(),
            fields: vec![],
        }],
    };
    program.declare_datatype(dt);

    // ALL should not be changed
    program.upgrade_logic_for_datatypes();
    assert!(program.to_string().contains("(set-logic ALL)"));
}

#[test]
fn test_upgrade_logic_none_becomes_all() {
    // Create program with NO logic set
    let mut program = AYProgram::new();
    assert!(program.get_logic().is_none());

    let dt = DatatypeSort {
        name: "Unit".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Unit_mk".to_string(),
            fields: vec![],
        }],
    };
    program.declare_datatype(dt);

    // Rule 1: None should become ALL when datatypes present
    program.upgrade_logic_for_datatypes();
    assert_eq!(program.get_logic(), Some("ALL"));
    assert!(program.to_string().contains("(set-logic ALL)"));
}

#[test]
fn test_upgrade_logic_skips_all_supported() {
    let mut program = AYProgram::new();
    program.set_logic("ALL_SUPPORTED");

    let dt = DatatypeSort {
        name: "Unit".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Unit_mk".to_string(),
            fields: vec![],
        }],
    };
    program.declare_datatype(dt);

    // ALL_SUPPORTED should not be changed (already datatype-capable)
    program.upgrade_logic_for_datatypes();
    assert_eq!(program.get_logic(), Some("ALL_SUPPORTED"));
    assert!(program.to_string().contains("(set-logic ALL_SUPPORTED)"));
}

#[test]
fn test_upgrade_logic_skips_dt_logics() {
    let mut program = AYProgram::new();
    program.set_logic("QF_DT");

    let dt = DatatypeSort {
        name: "Unit".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Unit_mk".to_string(),
            fields: vec![],
        }],
    };
    program.declare_datatype(dt);

    // QF_DT should not be changed (contains "DT")
    program.upgrade_logic_for_datatypes();
    assert_eq!(program.get_logic(), Some("QF_DT"));
    assert!(program.to_string().contains("(set-logic QF_DT)"));
}
