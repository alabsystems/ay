// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::expr::fold::{fold_expr, rebuild_with_children, ExprFold};
use crate::{Expr, ExprValue, Sort};

#[test]
fn checked_truncating_constructor_is_distinct_and_rejects_wrong_sorts() {
    let x = Expr::var("x", Sort::fp(8, 24));
    let y = Expr::var("y", Sort::fp(8, 24));
    assert!(matches!(
        x.clone().try_fp_truncating_rem(y.clone()).unwrap().value(),
        ExprValue::FpTruncatingRem(..)
    ));
    assert!(matches!(x.clone().fp_rem(y).value(), ExprValue::FpRem(..)));
    assert!(x.clone().try_fp_truncating_rem(Expr::true_()).is_err());
    assert!(x
        .try_fp_truncating_rem(Expr::var("wide", Sort::fp(11, 53)))
        .is_err());
}

#[test]
fn truncating_walk_rebuild_and_fold_keep_both_ordered_children() {
    let x = Expr::var("x", Sort::fp(11, 53));
    let y = Expr::var("y", Sort::fp(11, 53));
    let expr = x.clone().fp_truncating_rem(y.clone());
    assert!(expr.value().is_known_variant());
    let children = expr.value().children().cloned().collect::<Vec<_>>();
    assert_eq!(children, [x.clone(), y.clone()]);
    let rebuilt = rebuild_with_children(&expr, vec![y.clone(), x.clone()]);
    assert!(matches!(rebuilt.value(),ExprValue::FpTruncatingRem(a,b) if a==&y && b==&x));
    struct Swap;
    impl ExprFold for Swap {
        fn fold_var(&mut self, name: &str, sort: &Sort) -> Expr {
            Expr::var(
                if name == "x" {
                    "renamed_x"
                } else {
                    "renamed_y"
                },
                sort.clone(),
            )
        }
    }
    let folded = fold_expr(&mut Swap, &expr);
    assert!(matches!(folded.value(),ExprValue::FpTruncatingRem(a,b)
        if matches!(a.value(),ExprValue::Var { name } if name=="renamed_x")
        && matches!(b.value(),ExprValue::Var { name } if name=="renamed_y")));
}

#[test]
fn portable_lets_do_not_capture_adversarial_free_or_nested_operand_names() {
    let sort = Sort::fp(8, 24);
    let a = Expr::var("ay_fp_fmod_x", sort.clone());
    let b = Expr::var("ay_fp_fmod_r", sort.clone());
    let left = a.clone().fp_truncating_rem(b.clone());
    let right = Expr::var("ay_fp_fmod_y", sort).fp_neg();
    let rendered = left.clone().fp_truncating_rem(right.clone()).to_string();
    assert!(rendered.starts_with(&format!(
        "(let ((ay_fp_fmod_x {left}) (ay_fp_fmod_y {right})) "
    )));
    assert!(rendered.contains("(fp.rem ay_fp_fmod_x ay_fp_fmod_y)"));
    assert!(rendered.contains("(not (fp.isNaN ay_fp_fmod_r))"));
    assert!(rendered.contains("(not (fp.isZero ay_fp_fmod_r))"));
    assert!(!rendered.contains("__ay_fp_truncating_rem"));
    assert_eq!(rendered.matches("(let ((ay_fp_fmod_x ").count(), 2);
    assert_eq!(
        a.fp_rem(b).to_string(),
        "(fp.rem ay_fp_fmod_x ay_fp_fmod_r)"
    );
}

#[test]
fn deeply_owned_truncating_nodes_use_the_existing_iterative_drop_walk() {
    let sort = Sort::fp(8, 24);
    let y = Expr::var("y", sort.clone());
    let mut value = Expr::var("x", sort);
    for _ in 0..4096 {
        value = value.fp_truncating_rem(y.clone());
    }
    drop(value);
}
