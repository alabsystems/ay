// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;
use crate::sort::Sort;

/// Identity fold: folding with default implementations returns the
/// same expression.
struct IdentityFold;
impl ExprFold for IdentityFold {}

#[test]
fn test_fold_identity_var() {
    let x = Expr::var("x", Sort::int());
    let mut f = IdentityFold;
    let result = fold_expr(&mut f, &x);
    assert_eq!(result, x);
}

#[test]
fn test_fold_identity_const() {
    let c = Expr::int_const(42);
    let mut f = IdentityFold;
    let result = fold_expr(&mut f, &c);
    assert_eq!(result, c);
}

#[test]
fn test_fold_identity_compound() {
    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());
    let sum = x.int_add(y);
    let mut f = IdentityFold;
    let result = fold_expr(&mut f, &sum);
    assert_eq!(result, sum);
}

#[test]
fn test_fold_identity_nested() {
    let a = Expr::var("a", Sort::bool());
    let b = Expr::var("b", Sort::bool());
    let c = Expr::var("c", Sort::bool());
    let expr = a.and(b).or(c);
    let mut f = IdentityFold;
    let result = fold_expr(&mut f, &expr);
    assert_eq!(result, expr);
}

#[test]
fn test_fold_identity_ite() {
    let cond = Expr::var("c", Sort::bool());
    let t = Expr::int_const(1);
    let e = Expr::int_const(0);
    let ite = Expr::ite(cond, t, e);
    let mut f = IdentityFold;
    let result = fold_expr(&mut f, &ite);
    assert_eq!(result, ite);
}

/// Substitution fold: replaces variable "x" with constant 42.
struct SubstFold;
impl ExprFold for SubstFold {
    fn fold_var(&mut self, name: &str, sort: &Sort) -> Expr {
        if name == "x" && sort.is_int() {
            Expr::int_const(42)
        } else {
            Expr::var(name.to_string(), sort.clone())
        }
    }
}

#[test]
fn test_fold_substitute_var() {
    let x = Expr::var("x", Sort::int());
    let mut f = SubstFold;
    let result = fold_expr(&mut f, &x);
    assert_eq!(result, Expr::int_const(42));
}

#[test]
fn test_fold_substitute_in_compound() {
    let x = Expr::var("x", Sort::int());
    let one = Expr::int_const(1);
    let sum = x.int_add(one.clone());
    let mut f = SubstFold;
    let result = fold_expr(&mut f, &sum);
    let expected = Expr::int_const(42).int_add(one);
    assert_eq!(result, expected);
}

#[test]
fn test_fold_substitute_preserves_other_vars() {
    let y = Expr::var("y", Sort::int());
    let mut f = SubstFold;
    let result = fold_expr(&mut f, &y);
    assert_eq!(result, y);
}

/// Counting fold: counts the number of nodes visited.
struct CountFold {
    count: usize,
}
impl ExprFold for CountFold {
    fn fold_var(&mut self, name: &str, sort: &Sort) -> Expr {
        self.count += 1;
        Expr::var(name.to_string(), sort.clone())
    }
    fn fold_const(&mut self, expr: &Expr) -> Expr {
        self.count += 1;
        expr.clone()
    }
    fn fold_post(&mut self, original: &Expr, children: Vec<Expr>) -> Expr {
        self.count += 1;
        rebuild_with_children(original, children)
    }
}

#[test]
fn test_fold_count_nodes() {
    // (+ x 1) has 3 nodes: Var("x"), IntConst(1), IntAdd
    let x = Expr::var("x", Sort::int());
    let one = Expr::int_const(1);
    let sum = x.int_add(one);
    let mut f = CountFold { count: 0 };
    let _ = fold_expr(&mut f, &sum);
    assert_eq!(f.count, 3);
}

#[test]
fn test_fold_count_nary() {
    // (and a b c) has 4 nodes: Var("a"), Var("b"), Var("c"), And
    let a = Expr::var("a", Sort::bool());
    let b = Expr::var("b", Sort::bool());
    let c = Expr::var("c", Sort::bool());
    let expr = Expr {
        sort: Sort::bool(),
        value: Arc::new(ExprValue::And(vec![a, b, c])),
    };
    let mut f = CountFold { count: 0 };
    let _ = fold_expr(&mut f, &expr);
    assert_eq!(f.count, 4);
}

#[test]
fn test_fold_identity_forall() {
    let body = Expr::var("x", Sort::int()).int_ge(Expr::int_const(0));
    let q = Expr::forall(vec![("x".into(), Sort::int())], body);
    let mut f = IdentityFold;
    let result = fold_expr(&mut f, &q);
    assert_eq!(result, q);
}

#[test]
fn test_fold_identity_select_store() {
    let arr = Expr::var("arr", Sort::array(Sort::int(), Sort::int()));
    let idx = Expr::var("idx", Sort::int());
    let val = Expr::var("val", Sort::int());
    let sel = arr.clone().select(idx.clone());
    let sto = arr.store(idx, val);
    let mut f = IdentityFold;
    assert_eq!(fold_expr(&mut f, &sel), sel);
    assert_eq!(fold_expr(&mut f, &sto), sto);
}

#[test]
fn test_fold_identity_func_app() {
    let x = Expr::var("x", Sort::int());
    let app = Expr::func_app("f", vec![x]);
    let mut f = IdentityFold;
    let result = fold_expr(&mut f, &app);
    assert_eq!(result, app);
}

#[test]
fn test_fold_identity_bv_ops() {
    let x = Expr::var("x", Sort::bv32());
    let y = Expr::var("y", Sort::bv32());
    let add = x.clone().bvadd(y);
    let ext = x.clone().extract(15, 0);
    let zext = x.zero_extend(32);
    let mut f = IdentityFold;
    assert_eq!(fold_expr(&mut f, &add), add);
    assert_eq!(fold_expr(&mut f, &ext), ext);
    assert_eq!(fold_expr(&mut f, &zext), zext);
}

#[test]
fn test_children_leaf_empty() {
    assert_eq!(ExprValue::BoolConst(true).children().count(), 0);
    assert_eq!(
        ExprValue::BitVecConst {
            value: 0.into(),
            width: 32
        }
        .children()
        .count(),
        0
    );
    assert_eq!(ExprValue::IntConst(42.into()).children().count(), 0);
    assert_eq!(
        ExprValue::Var {
            name: "x".to_string()
        }
        .children()
        .count(),
        0
    );
}

#[test]
fn test_children_unary() {
    let inner = Expr::var("x", Sort::bool());
    let not_val = ExprValue::Not(inner.clone());
    let children: Vec<_> = not_val.children().collect();
    assert_eq!(children.len(), 1);
    assert_eq!(children[0], &inner);
}

#[test]
fn test_children_binary() {
    let a = Expr::var("a", Sort::int());
    let b = Expr::var("b", Sort::int());
    let add_val = ExprValue::IntAdd(a.clone(), b.clone());
    let children: Vec<_> = add_val.children().collect();
    assert_eq!(children.len(), 2);
    assert_eq!(children[0], &a);
    assert_eq!(children[1], &b);
}

#[test]
fn test_children_nary() {
    let a = Expr::var("a", Sort::bool());
    let b = Expr::var("b", Sort::bool());
    let c = Expr::var("c", Sort::bool());
    let and_val = ExprValue::And(vec![a.clone(), b.clone(), c.clone()]);
    let children: Vec<_> = and_val.children().collect();
    assert_eq!(children.len(), 3);
    assert_eq!(children[0], &a);
    assert_eq!(children[1], &b);
    assert_eq!(children[2], &c);
}

#[test]
fn test_is_known_variant() {
    assert!(ExprValue::BoolConst(true).is_known_variant());
    assert!(ExprValue::IntConst(0.into()).is_known_variant());
    assert!(ExprValue::Var {
        name: "x".to_string()
    }
    .is_known_variant());
    let a = Expr::var("a", Sort::bool());
    assert!(ExprValue::Not(a).is_known_variant());
}

#[test]
fn test_expr_children_delegate() {
    let a = Expr::var("a", Sort::int());
    let b = Expr::var("b", Sort::int());
    let sum = a.clone().int_add(b.clone());
    let children: Vec<_> = sum.children().collect();
    assert_eq!(children.len(), 2);
    assert_eq!(children[0], &a);
    assert_eq!(children[1], &b);
}
