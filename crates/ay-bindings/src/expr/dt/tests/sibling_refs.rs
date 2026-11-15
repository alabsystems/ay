// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Sibling and mutually recursive declarations under `Sort::datatype_ref`:
//! a non-enclosing datatype is inlined in the field, a bare reference to it
//! is dangling, and inlined spellings compare coinductively.

#![cfg(test)]

use super::super::check::{Check, CHECK_LIMIT};
use super::recursive_refs::{level, level_with_pred};
use crate::expr::Expr;
use crate::sort::Sort;

/// `(declare-datatype Block ((leaf)))`
fn block() -> Sort {
    Sort::enum_type("Block", vec![("leaf", Vec::<(&str, Sort)>::new())])
}

/// `(declare-datatype Tower ((empty) (stack (top <top>) (rest Tower))))`
fn tower_with_top(top: Sort) -> Sort {
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
}

#[test]
fn sibling_declaration_inlined_in_a_field_is_admitted() {
    let tower = tower_with_top(block());
    let b = Expr::var("b", block());
    let t = Expr::var("t", tower.clone());
    let stack = Expr::try_datatype_constructor("Tower", "stack", vec![b, t], tower.clone())
        .expect("an inlined sibling definition is that sibling");
    assert!(stack
        .clone()
        .try_field_select("Tower", "top", block())
        .is_ok());
    assert!(stack
        .clone()
        .try_field_select("Tower", "rest", tower)
        .is_ok());
    assert!(stack
        .try_field_select("Tower", "top", Sort::uninterpreted("Block"))
        .is_err());
}

#[test]
fn a_bare_sibling_reference_is_dangling_and_refused() {
    // No cross-declaration resolution: `Block` does not enclose the field.
    let tower = tower_with_top(Sort::datatype_ref("Block"));
    let b = Expr::var("b", block());
    let t = Expr::var("t", tower.clone());
    assert!(Expr::try_datatype_constructor("Tower", "stack", vec![b, t], tower.clone()).is_err());
    assert!(Expr::var("t", tower)
        .try_field_select("Tower", "top", block())
        .is_err());
}

#[test]
fn a_forged_inlined_sibling_is_refused() {
    // The inlined `Block` has an extra constructor: an argument of the real
    // `Block` sort does not match it, and neither does a selector result.
    let forged_block = Sort::enum_type(
        "Block",
        vec![("leaf", vec![]), ("extra", vec![("bit", Sort::bool())])],
    );
    let tower = tower_with_top(forged_block);
    let b = Expr::var("b", block());
    let t = Expr::var("t", tower.clone());
    assert!(Expr::try_datatype_constructor("Tower", "stack", vec![b, t], tower.clone()).is_err());
    assert!(Expr::var("t", tower)
        .try_field_select("Tower", "top", block())
        .is_err());
}

/// `Block { leaf | cell (owner: <owner>) }`
fn block_with_owner(owner: Sort) -> Sort {
    Sort::enum_type(
        "Block",
        vec![("leaf", vec![]), ("cell", vec![("owner", owner)])],
    )
}

/// `Tower` as a term sort: the mutual `Block` is inlined, and inside it the
/// reference back to `Tower` is a ref.
fn tower_top() -> Sort {
    tower_with_top(block_with_owner(Sort::datatype_ref("Tower")))
}

/// `Block` as a term sort, spelled from the other side of the pair.
fn block_top() -> Sort {
    block_with_owner(tower_with_top(Sort::datatype_ref("Block")))
}

fn field_sort(declaration: &Sort, constructor: usize, field: usize) -> Sort {
    declaration.datatype_sort().unwrap().constructors[constructor].fields[field]
        .sort
        .clone()
}

#[test]
fn mutually_recursive_declarations_inlined_one_level_compare_equal() {
    // Through a declaration both spellings denote one datatype, in both
    // directions, and the coinductive walk terminates well inside the budget.
    let t = Expr::var("t", tower_top());
    let b = Expr::var("b", block_top());
    let cell = Expr::try_datatype_constructor("Block", "cell", vec![t.clone()], block_top())
        .expect("Tower spelled at top level is the Tower nested inside Block");
    assert!(cell
        .clone()
        .try_field_select("Block", "owner", tower_top())
        .is_ok());
    let stack = Expr::try_datatype_constructor("Tower", "stack", vec![b, t], tower_top())
        .expect("Block spelled at top level is the Block nested inside Tower");
    assert!(stack.try_field_select("Tower", "top", block_top()).is_ok());

    let mut check = Check::new("mutual_recursion_budget");
    check
        .constructor(
            &block_top(),
            "Block",
            "cell",
            &[Expr::var("t", tower_top())],
        )
        .unwrap();
    assert!(check.remaining() > CHECK_LIMIT / 2, "{}", check.remaining());

    // A nested spelling is a field sort, not a term sort: pulled out of its
    // declaration its reference to the sibling is dangling.
    let tower_inside_block = field_sort(&block_top(), 1, 0);
    let mut check = Check::new("nested_spelling_is_not_a_term_sort");
    assert!(!check.same_sort(&tower_top(), &tower_inside_block).unwrap());
    assert!(cell.try_eq(Expr::var("t", tower_inside_block)).is_err());
}

#[test]
fn equal_declarations_unfolded_to_different_depths_are_one_sort() {
    // Both spellings are closed (every ref enclosed) and denote `Tower`, but
    // derived `Sort` equality distinguishes them. The checked API does not:
    // `eq`, `distinct`, `ite` and the datatype signatures all agree.
    let shallow = tower_top();
    let deep = tower_with_top(block_with_owner(tower_with_top(block_with_owner(
        Sort::datatype_ref("Tower"),
    ))));
    assert_ne!(shallow, deep);
    let mut check = Check::new("unfolding_depth");
    assert!(check.same_sort(&shallow, &deep).unwrap());
    assert!(check.same_sort(&deep, &shallow).unwrap());
    let s = Expr::var("s", shallow.clone());
    let d = Expr::var("d", deep.clone());
    assert!(s.clone().try_eq(d.clone()).is_ok());
    assert!(Expr::try_distinct(vec![s.clone(), d.clone(), s.clone()]).is_ok());
    let ite = Expr::try_ite(Expr::bool_const(true), s.clone(), d.clone()).unwrap();
    assert!(ite.try_eq(s.clone()).is_ok());
    assert!(Expr::try_datatype_constructor(
        "Tower",
        "stack",
        vec![Expr::var("b", block_top()), d],
        shallow
    )
    .is_ok());
    assert!(s.try_field_select("Tower", "rest", deep).is_ok());
}

#[test]
fn scalar_and_uninterpreted_sort_agreement_is_unchanged() {
    let x = Expr::var("x", Sort::bv32());
    assert!(x.clone().try_eq(Expr::var("y", Sort::bv64())).is_err());
    assert!(x.clone().try_eq(Expr::var("y", Sort::bv32())).is_ok());
    let u = Expr::var("u", Sort::uninterpreted("U"));
    assert!(u
        .clone()
        .try_eq(Expr::var("v", Sort::uninterpreted("U")))
        .is_ok());
    assert!(u
        .clone()
        .try_eq(Expr::var("v", Sort::uninterpreted("V")))
        .is_err());
    assert!(u.try_eq(x).is_err());
    assert!(Expr::var("l", level())
        .try_eq(Expr::var("u", Sort::uninterpreted("Level")))
        .is_err());
}

/// A tower of the shape and name length a Trust `downstream proof consumer` proof lowers:
/// `expr::Expr { mk (kind: ExprKind, meta: BV64) }` with a ten-constructor
/// `expr::ExprKind` referring back to `Expr` and down to `level::Level`.
fn proof_kernel_expr(kind: Sort) -> Sort {
    Sort::enum_type(
        "proof_kernel::expr::Expr",
        vec![("mk", vec![("kind", kind), ("meta", Sort::bv64())])],
    )
}

fn proof_kernel_expr_kind(level: Sort, expr: Sort) -> Sort {
    Sort::enum_type(
        "proof_kernel::expr::ExprKind",
        vec![
            ("BVar", vec![("index", Sort::bv64())]),
            ("FVar", vec![("name", Sort::bv64())]),
            ("MVar", vec![("name", Sort::bv64())]),
            ("Sort", vec![("level", level)]),
            (
                "Const",
                vec![("name", Sort::bv64()), ("levels", Sort::bv32())],
            ),
            ("App", vec![("f", expr.clone()), ("x", expr.clone())]),
            ("Lam", vec![("ty", expr.clone()), ("body", expr.clone())]),
            ("Pi", vec![("ty", expr.clone()), ("body", expr.clone())]),
            (
                "Let",
                vec![
                    ("ty", expr.clone()),
                    ("val", expr.clone()),
                    ("body", expr.clone()),
                ],
            ),
            ("Proj", vec![("index", Sort::bv64()), ("s", expr)]),
        ],
    )
}

#[test]
fn a_proof_kernel_sized_inlined_tower_stays_well_inside_the_budget() {
    let level = level_with_pred(Sort::datatype_ref("Level"));
    let level = Sort::enum_type(
        "proof_kernel::level::Level",
        level
            .datatype_sort()
            .unwrap()
            .constructors
            .iter()
            .map(|ctor| {
                (
                    ctor.name.clone(),
                    ctor.fields
                        .iter()
                        .map(|_| {
                            (
                                "pred".to_owned(),
                                Sort::datatype_ref("proof_kernel::level::Level"),
                            )
                        })
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<_>>(),
    );
    // Term sorts: `Expr` inlines `ExprKind` (which refs `Expr`), `ExprKind`
    // inlines `Expr` (which refs `ExprKind`), both inline `Level`.
    let expr = proof_kernel_expr(proof_kernel_expr_kind(
        level.clone(),
        Sort::datatype_ref("proof_kernel::expr::Expr"),
    ));
    let kind = proof_kernel_expr_kind(
        level.clone(),
        proof_kernel_expr(Sort::datatype_ref("proof_kernel::expr::ExprKind")),
    );

    let mut check = Check::new("proof_kernel_budget");
    let args = [Expr::var("k", kind.clone()), Expr::var("m", Sort::bv64())];
    check
        .constructor(&expr, "proof_kernel::expr::Expr", "mk", &args)
        .expect("ExprKind spelled at top level is the ExprKind nested inside Expr");
    let spent = CHECK_LIMIT - check.remaining();
    assert!(spent < CHECK_LIMIT / 4, "constructor spent {spent}");

    let mut check = Check::new("proof_kernel_budget");
    check
        .selector(&expr, "proof_kernel::expr::Expr", "kind", &kind)
        .unwrap();
    let spent = CHECK_LIMIT - check.remaining();
    assert!(spent < CHECK_LIMIT / 4, "selector spent {spent}");

    let app = Expr::try_datatype_constructor(
        "proof_kernel::expr::ExprKind",
        "App",
        vec![Expr::var("f", expr.clone()), Expr::var("x", expr.clone())],
        kind.clone(),
    )
    .unwrap();
    let mk = Expr::try_datatype_constructor(
        "proof_kernel::expr::Expr",
        "mk",
        vec![app, Expr::var("m", Sort::bv64())],
        expr.clone(),
    )
    .unwrap();
    let l = Expr::var("l", level);
    let sort_kind = Expr::try_datatype_constructor(
        "proof_kernel::expr::ExprKind",
        "Sort",
        vec![l],
        kind.clone(),
    )
    .unwrap();
    assert!(mk
        .try_field_select("proof_kernel::expr::Expr", "kind", kind)
        .unwrap()
        .try_eq(sort_kind)
        .is_ok());
    let _ = expr;
}
