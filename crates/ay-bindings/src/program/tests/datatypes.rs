// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use crate::program::AYProgram;
use crate::sort::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

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
