// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Basic execution, sort translation, boolean operations, ITE, and datatype tests.

use super::*;

use crate::constraint::logic;
use ay_dpll::api::Logic;

#[test]
fn test_named_bv_lia_logics_parse_for_direct_execution() {
    for (name, expected) in [
        (logic::QF_UFBVLIA, Logic::QfUfbvlia),
        (logic::QF_AUFBVLIA, Logic::QfAufbvlia),
    ] {
        let mut program = AYProgram::new();
        program.set_logic(name);
        assert_eq!(
            super::super::logic::parse_logic(&program).expect("public logic must parse"),
            expected
        );
    }
}

#[test]
fn test_execute_bool_sat() {
    // Use QF_UF (simpler logic) to avoid ay-dpll LIA model validation bugs
    let mut program = AYProgram::new();
    program.set_logic("QF_UF");
    let x = program.declare_const("x", Sort::bool());
    // x is satisfiable (x = true)
    program.assert(x);
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Counterexample { .. }));
}

#[test]
fn test_execute_bool_unsat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_UF");
    let x = program.declare_const("x", Sort::bool());
    // x AND NOT x is unsatisfiable
    program.assert(x.clone());
    program.assert(x.not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_datatype_direct_execution() {
    // DT programs should execute directly, not fall back (#5404)
    use crate::sort::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut program = AYProgram::new();
    let dt = DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "mk-Pair".to_string(),
            fields: vec![
                DatatypeField {
                    name: "fst".to_string(),
                    sort: Sort::bitvec(32),
                },
                DatatypeField {
                    name: "snd".to_string(),
                    sort: Sort::bitvec(32),
                },
            ],
        }],
    };
    let pair_sort = Sort::struct_type("Pair", [("fst", Sort::bv32()), ("snd", Sort::bv32())]);
    program.declare_datatype(dt);

    // Declare a variable of Pair sort
    let p = program.declare_const("p", pair_sort.clone());

    // Assert fst(p) = 42
    let fst_p = p.clone().field_select("Pair", "fst", Sort::bv32());
    let forty_two = Expr::bitvec_const(42i64, 32);
    program.assert(fst_p.eq(forty_two));

    // Assert snd(p) != 0
    let snd_p = p.field_select("Pair", "snd", Sort::bv32());
    let zero = Expr::bitvec_const(0i64, 32);
    program.assert(snd_p.eq(zero).not());

    program.check_sat();

    let result = execute(&program).unwrap();
    // Should get Counterexample (SAT) via direct path, not NeedsFallback
    assert!(
        matches!(result, ExecuteResult::Counterexample { .. }),
        "expected Counterexample, got {:?}",
        result
    );
}

#[test]
fn test_sort_translation() {
    assert!(matches!(translate_sort(&Sort::bool()), Ok(ApiSort::Bool)));
    assert!(matches!(translate_sort(&Sort::int()), Ok(ApiSort::Int)));
    assert!(matches!(translate_sort(&Sort::real()), Ok(ApiSort::Real)));

    // BitVec sort uses BitVecSort wrapper
    let bv_sort = translate_sort(&Sort::bv32()).unwrap();
    assert!(matches!(bv_sort, ApiSort::BitVec(bv) if bv.width == 32));

    // Array sort uses ArraySort wrapper in Box
    let arr = Sort::array(Sort::bv64(), Sort::bv8());
    let translated = translate_sort(&arr).unwrap();
    assert!(matches!(translated, ApiSort::Array(_)));
}

#[test]
fn test_bool_operations() {
    let mut program = AYProgram::new();
    program.set_logic("QF_UF");
    let a = program.declare_const("a", Sort::bool());
    let b = program.declare_const("b", Sort::bool());

    // (a AND b) AND NOT(a AND b) is UNSAT
    let ab = a.and(b);
    let not_ab = ab.clone().not();
    program.assert(ab.and(not_ab));
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_ite_operations() {
    let mut program = AYProgram::new();
    program.set_logic("QF_UF");
    let c = program.declare_const("c", Sort::bool());
    let t = program.declare_const("t", Sort::bool());
    let e = program.declare_const("e", Sort::bool());

    // ite(c, t, e) AND NOT(ite(c, t, e)) is UNSAT
    let ite_expr = Expr::ite(c.clone(), t, e);
    program.assert(ite_expr.clone());
    program.assert(ite_expr.not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(matches!(result, ExecuteResult::Verified));
}

#[test]
fn test_translate_bridge_array_uf_int_roundtrip() {
    let mut program = AYProgram::new();
    program.set_logic("QF_AUFLIA");
    let arr = program.declare_const("arr", Sort::array(Sort::int(), Sort::int()));
    let x = program.declare_const("x", Sort::int());
    program.declare_fun("f", vec![Sort::int()], Sort::int());

    let x_plus_one = x.clone().int_add(Expr::int(1));
    let fx = Expr::func_app_with_sort("f", vec![x_plus_one], Sort::int());
    let read_back = arr.store(x.clone(), fx.clone()).select(x);

    program.assert(read_back.eq(fx).not());
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        matches!(result, ExecuteResult::Verified),
        "store/select over shared UF result should stay on the direct bridge path, got {:?}",
        result
    );
}
