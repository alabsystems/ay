// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! `Sort::datatype_ref`: recursive datatype fields resolve only to an
//! enclosing declaration of the same name, never to a bare uninterpreted sort.

#![cfg(test)]

use super::super::check::Check;
use crate::expr::{Expr, ExprValue};
use crate::sort::Sort;

/// `(declare-datatype Level ((zero) (succ (pred Level))))`
pub(super) fn level_with_pred(pred: Sort) -> Sort {
    Sort::enum_type(
        "Level",
        vec![("zero", vec![]), ("succ", vec![("pred", pred)])],
    )
}

pub(super) fn level() -> Sort {
    level_with_pred(Sort::datatype_ref("Level"))
}

#[test]
fn recursive_constructor_and_selector_build() {
    let level = level();
    let l = Expr::var("l", level.clone());
    let succ = Expr::try_datatype_constructor("Level", "succ", vec![l.clone()], level.clone())
        .expect("a recursive field accepts its own declaration");
    let pred = succ
        .try_field_select("Level", "pred", level.clone())
        .expect("a recursive selector returns its own declaration");
    // Struct-style folding does not apply to a two-constructor enum.
    assert!(matches!(pred.value(), ExprValue::DatatypeSelector { .. }));
    let symbolic = l
        .try_field_select("Level", "pred", level.clone())
        .expect("selector over a symbolic recursive value");
    assert_eq!(symbolic.sort(), &level);
}

#[test]
fn recursive_tester_and_fidelity_equation_build() {
    // The shapes a Trust fidelity proof lowers: `((_ is succ) (succ l))`,
    // `(= (succ l) l)` between a constructed term and a datatype-sorted
    // variable, `(= (succ l) (succ l))` between separately built terms over
    // separately allocated declarations, and `(= (pred (succ l)) l)`.
    let l = Expr::var("l", level());
    let succ = Expr::try_datatype_constructor("Level", "succ", vec![l.clone()], level()).unwrap();
    let tester = succ.clone().try_is_constructor("Level", "succ").unwrap();
    assert!(tester.sort().is_bool());
    assert!(matches!(tester.value(), ExprValue::DatatypeTester { .. }));
    assert!(succ.clone().try_eq(l.clone()).is_ok());
    let again =
        Expr::try_datatype_constructor("Level", "succ", vec![Expr::var("l", level())], level())
            .unwrap();
    assert!(succ.clone().try_eq(again).is_ok());
    let pred = succ.try_field_select("Level", "pred", level()).unwrap();
    assert!(pred.try_eq(l).is_ok());
}

#[test]
fn separately_built_equal_declarations_still_match() {
    // The receiver and the argument are separate allocations of the same
    // declaration; the reference is compared structurally, coinductively.
    let receiver = level();
    let argument = Expr::var("l", level());
    assert!(Expr::try_datatype_constructor(
        "Level",
        "succ",
        vec![argument.clone()],
        receiver.clone()
    )
    .is_ok());
    assert!(argument.try_field_select("Level", "pred", receiver).is_ok());
}

#[test]
fn datatype_and_uninterpreted_of_the_same_name_stay_distinct() {
    // Declared field is a bare uninterpreted `Level`: a Datatype argument is
    // refused (the type confusion ad07c5cc6 closed).
    let opaque = level_with_pred(Sort::uninterpreted("Level"));
    let argument = Expr::var("l", level());
    assert!(
        Expr::try_datatype_constructor("Level", "succ", vec![argument], opaque.clone()).is_err()
    );
    assert!(Expr::var("l", opaque.clone())
        .try_field_select("Level", "pred", level())
        .is_err());

    // Declared field is a datatype ref: an uninterpreted argument is refused.
    let uninterpreted = Expr::var("u", Sort::uninterpreted("Level"));
    assert!(Expr::try_datatype_constructor("Level", "succ", vec![uninterpreted], level()).is_err());
    assert!(Expr::var("l", level())
        .try_field_select("Level", "pred", Sort::uninterpreted("Level"))
        .is_err());
}

#[test]
fn a_reference_to_a_different_datatype_name_is_refused() {
    let other = Sort::enum_type("Other", vec![("leaf", Vec::<(&str, Sort)>::new())]);
    let mislabelled = level_with_pred(Sort::datatype_ref("Other"));
    let argument = Expr::var("o", other.clone());
    assert!(
        Expr::try_datatype_constructor("Level", "succ", vec![argument], mislabelled.clone())
            .is_err()
    );
    assert!(Expr::var("l", mislabelled)
        .try_field_select("Level", "pred", other)
        .is_err());
}

#[test]
fn a_same_named_but_different_declaration_is_refused() {
    // Another datatype also called `Level` does not satisfy the reference:
    // it resolves to the enclosing declaration, which has other constructors.
    let impostor = Sort::enum_type("Level", vec![("zero", Vec::<(&str, Sort)>::new())]);
    let argument = Expr::var("l", impostor.clone());
    assert!(Expr::try_datatype_constructor("Level", "succ", vec![argument], level()).is_err());
    assert!(Expr::var("l", level())
        .try_field_select("Level", "pred", impostor)
        .is_err());
}

#[test]
fn a_forged_descriptor_with_a_renamed_or_retyped_field_is_refused() {
    // A descriptor whose recursive selector is `prev` does not declare `pred`,
    // and a descriptor whose `pred` is Bool does not accept a Level argument,
    // whichever side of the check carries the forgery.
    let renamed = Sort::enum_type(
        "Level",
        vec![
            ("zero", vec![]),
            ("succ", vec![("prev", Sort::datatype_ref("Level"))]),
        ],
    );
    assert!(Expr::var("l", renamed.clone())
        .try_field_select("Level", "pred", level())
        .is_err());
    assert!(Expr::var("l", renamed.clone())
        .try_field_select("Level", "prev", level())
        .is_err());
    assert!(Expr::try_datatype_constructor(
        "Level",
        "succ",
        vec![Expr::var("l", level())],
        renamed
    )
    .is_err());

    let retyped = level_with_pred(Sort::bool());
    assert!(Expr::try_datatype_constructor(
        "Level",
        "succ",
        vec![Expr::var("l", level())],
        retyped.clone()
    )
    .is_err());
    assert!(Expr::try_datatype_constructor(
        "Level",
        "succ",
        vec![Expr::var("b", Sort::bool())],
        level()
    )
    .is_err());
    assert!(Expr::var("l", level())
        .try_field_select("Level", "pred", Sort::bool())
        .is_err());
    assert!(Expr::var("l", retyped)
        .try_field_select("Level", "pred", level())
        .is_err());
}

#[test]
fn a_dangling_reference_is_never_a_sort_of_its_own() {
    // Outside any declaration a reference is unequal to everything,
    // including an identical reference and the datatype it names.
    let reference = Sort::datatype_ref("Level");
    assert!(Expr::var("l", level())
        .try_field_select("Level", "pred", reference.clone())
        .is_err());
    let dangling = Expr::var("r", reference.clone());
    assert!(
        Expr::try_datatype_constructor("Level", "succ", vec![dangling.clone()], level()).is_err()
    );
    let mut check = Check::new("dangling_ref_test");
    assert!(!check.same_sort(&reference, &reference).unwrap());
    assert!(!check.same_sort(&reference, &level()).unwrap());
    // `try_eq` follows the same rule: the reference is not the datatype.
    assert!(dangling.clone().try_eq(Expr::var("l", level())).is_err());
    assert!(Expr::var("l", level()).try_eq(dangling).is_err());
}

#[test]
fn a_reference_nested_inside_a_field_resolves_to_the_enclosing_declaration() {
    // (declare-datatype Tree ((leaf) (node (kids (Array Int Tree)))))
    let tree = |kids: Sort| {
        Sort::enum_type(
            "Tree",
            vec![
                ("leaf", vec![]),
                ("node", vec![("kids", Sort::array(Sort::int(), kids))]),
            ],
        )
    };
    let declared = tree(Sort::datatype_ref("Tree"));
    let kids = Expr::var("kids", Sort::array(Sort::int(), declared.clone()));
    assert!(Expr::try_datatype_constructor("Tree", "node", vec![kids], declared.clone()).is_ok());
    let opaque_kids = Expr::var(
        "kids",
        Sort::array(Sort::int(), Sort::uninterpreted("Tree")),
    );
    assert!(Expr::try_datatype_constructor("Tree", "node", vec![opaque_kids], declared).is_err());
}
