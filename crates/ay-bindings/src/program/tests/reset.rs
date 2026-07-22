// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use crate::expr::Expr;
use crate::program::AYProgram;
use crate::sort::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

#[test]
fn test_clear_commands_preserves_consts() {
    let mut program = AYProgram::qf_bv();
    let x = program.declare_const("x", Sort::bv32());
    program.assert(x.eq(Expr::bitvec_const(1i32, 32)));
    program.check_sat();

    program.clear_commands();

    let output = program.to_string();
    assert!(
        output.contains("declare-const x"),
        "const declaration should survive clear_commands"
    );
    assert!(
        !output.contains("(assert"),
        "assertions should be removed by clear_commands"
    );
    assert!(
        !output.contains("(check-sat)"),
        "check-sat should be removed by clear_commands"
    );
}

#[test]
fn test_clear_commands_preserves_datatypes() {
    let mut program = AYProgram::new();
    program.set_logic("ALL");

    let dt = DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "mkPair".to_string(),
            fields: vec![
                DatatypeField {
                    name: "fst".to_string(),
                    sort: Sort::int(),
                },
                DatatypeField {
                    name: "snd".to_string(),
                    sort: Sort::int(),
                },
            ],
        }],
    };
    program.declare_datatype(dt);
    let pair_sort = Sort::struct_type("Pair", [("fst", Sort::int()), ("snd", Sort::int())]);
    let _p = program.declare_const("p", pair_sort);
    program.check_sat();

    program.clear_commands();

    let output = program.to_string();
    assert!(
        output.contains("declare-datatype"),
        "datatype declaration should survive clear_commands"
    );
    assert!(
        output.contains("Pair"),
        "datatype name should survive clear_commands"
    );
    assert!(
        output.contains("mkPair"),
        "constructor name should survive clear_commands"
    );
    assert!(!output.contains("(assert"), "assertions should be removed");
}

#[test]
fn test_clear_commands_preserves_functions() {
    let mut program = AYProgram::new();
    program.set_logic("QF_UF");
    program.declare_fun("f", vec![Sort::int()], Sort::int());
    let x = program.declare_const("x", Sort::int());
    program.assert(x.eq(Expr::int_const(0)));
    program.check_sat();

    program.clear_commands();

    let output = program.to_string();
    assert!(
        output.contains("declare-fun f"),
        "function declaration should survive clear_commands"
    );
    assert!(
        output.contains("declare-const x"),
        "const declaration should survive clear_commands"
    );
    assert!(!output.contains("(assert"), "assertions should be removed");
}

#[test]
fn test_clear_commands_preserves_chc_declarations() {
    let mut program = AYProgram::horn();
    program.declare_rel("Inv", vec![Sort::int()]);
    program.declare_var("x", Sort::int());

    let inv = Expr::var("Inv_x", Sort::bool());
    program.fact(inv.clone());
    program.query(inv);

    program.clear_commands();

    let output = program.to_string();
    assert!(
        output.contains("declare-rel Inv"),
        "CHC relation should survive clear_commands"
    );
    assert!(
        output.contains("declare-var x"),
        "CHC variable should survive clear_commands"
    );
    assert!(
        !output.contains("(rule"),
        "rules should be removed by clear_commands"
    );
    assert!(
        !output.contains("(query"),
        "queries should be removed by clear_commands"
    );
    assert_eq!(program.context_level(), 0);
}

#[test]
fn test_clear_commands_resets_context_level() {
    let mut program = AYProgram::qf_bv();
    let _ = program.declare_const("x", Sort::bv32());
    program.push();
    program.push();
    assert_eq!(program.context_level(), 2);

    program.clear_commands();
    assert_eq!(program.context_level(), 0);
}
