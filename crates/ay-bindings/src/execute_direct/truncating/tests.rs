// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_dpll::api::{Logic, Sort};
use ay_frontend::{Command, Context};

#[test]
fn truncating_private_name_is_undeclarable_on_native_and_both_source_spellings() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    assert!(solver
        .try_declare_const("__ay_fp_truncating_rem", Sort::FloatingPoint(8, 24))
        .is_err());
    assert!(solver
        .try_declare_fun(
            "__ay_fp_truncating_rem",
            &[Sort::FloatingPoint(8, 24)],
            Sort::FloatingPoint(8, 24)
        )
        .is_err());
    for text in [
        "(declare-const __ay_fp_truncating_rem (_ FloatingPoint 8 24))",
        "(declare-const |__ay_fp_truncating_rem| (_ FloatingPoint 8 24))",
    ] {
        let parsed = ay_frontend::parse(text).unwrap();
        let mut context = Context::new();
        assert!(matches!(parsed.as_slice(), [Command::DeclareConst(..)]));
        assert!(context.process_command(&parsed[0]).is_err());
    }
}

#[test]
fn direct_truncating_lowering_uses_checked_standard_operators_only() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver
        .try_declare_const("x", Sort::FloatingPoint(8, 24))
        .unwrap();
    let y = solver
        .try_declare_const("y", Sort::FloatingPoint(8, 24))
        .unwrap();
    let result = lower(&mut solver, x, y).unwrap();
    let zero = solver.try_fp_plus_zero(8, 24).unwrap();
    assert!(solver.try_fp_eq(result, zero).is_ok());
    let boolean = solver.bool_const(false);
    assert!(lower(&mut solver, x, boolean).is_err());
}
