// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_chc::{ChcExpr, ChcOp, ChcSort, ChcVar, Mbp};
use ay_core::kani_compat::DetHashMap as FxHashMap;

fn is_var_after_even_negs(expr: &ChcExpr, var: &ChcVar) -> bool {
    match expr {
        ChcExpr::Var(v) => v == var,
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => match args[0].as_ref() {
            ChcExpr::Op(ChcOp::Neg, inner) if inner.len() == 1 => {
                is_var_after_even_negs(inner[0].as_ref(), var)
            }
            _ => false,
        },
        _ => false,
    }
}

#[test]
fn mbp_project_real_equality_negative_coeff_keeps_positive_guard() {
    let mbp = Mbp::new();
    let x = ChcVar::new("x", ChcSort::Real);
    let z = ChcVar::new("z", ChcSort::Real);

    // x = z isolates z with a negative coefficient internally. Replacing z in
    // (z > 0) must preserve the positive direction (x > 0), not invert it.
    let formula = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::var(z.clone())),
        ChcExpr::gt(ChcExpr::var(z.clone()), ChcExpr::Real(0, 1)),
    );

    let model = FxHashMap::default();
    let result = mbp.project(&formula, std::slice::from_ref(&z), &model);

    assert!(
        !result.vars().iter().any(|v| v.name == z.name),
        "projected formula must eliminate z"
    );

    let gt_guard = result
        .collect_conjuncts()
        .into_iter()
        .find(|c| matches!(c, ChcExpr::Op(ChcOp::Gt, _)))
        .expect("projection should retain a strict positivity guard");

    let ChcExpr::Op(ChcOp::Gt, ref args) = gt_guard else {
        unreachable!("guard is filtered to Gt");
    };
    assert_eq!(
        args[1].as_ref(),
        &ChcExpr::Real(0, 1),
        "guard threshold should remain zero"
    );
    assert!(
        is_var_after_even_negs(args[0].as_ref(), &x),
        "guard must normalize to x > 0 (not -x > 0); got {result:?}"
    );
}
