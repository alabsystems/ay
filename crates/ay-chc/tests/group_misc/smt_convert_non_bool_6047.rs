// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used)]

use ay_chc::{ChcExpr, ChcSort, ChcVar, SmtContext, SmtResult};

#[test]
fn convert_or_with_non_bool_arg_returns_unknown_sentinel_issue_6047() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::BitVec(64));
    let b = ChcVar::new("b", ChcSort::Bool);
    let expr = ChcExpr::or(ChcExpr::var(x), ChcExpr::var(b));

    assert!(
        matches!(ctx.check_sat(&expr), SmtResult::Unknown),
        "ill-typed boolean connective should surface as Unknown through check_sat"
    );
}

#[test]
fn convert_and_with_non_bool_arg_returns_unknown_sentinel_issue_6047() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::BitVec(64));
    let b = ChcVar::new("b", ChcSort::Bool);
    let expr = ChcExpr::and(ChcExpr::var(x), ChcExpr::var(b));

    assert!(
        matches!(ctx.check_sat(&expr), SmtResult::Unknown),
        "ill-typed boolean connective should surface as Unknown through check_sat"
    );
}

#[test]
fn convert_implies_with_non_bool_arg_returns_unknown_sentinel_issue_6047() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::BitVec(64));
    let b = ChcVar::new("b", ChcSort::Bool);
    let expr = ChcExpr::implies(ChcExpr::var(x), ChcExpr::var(b));

    assert!(
        matches!(ctx.check_sat(&expr), SmtResult::Unknown),
        "ill-typed boolean connective should surface as Unknown through check_sat"
    );
}
