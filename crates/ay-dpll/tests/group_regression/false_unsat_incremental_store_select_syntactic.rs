// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! In-crate regression for the incremental ArrayEUF pre-solve shortcut
//! `active_store_select_value_contradiction`
//! (`executor/theories/euf/array_fixpoint.rs`), which declared UNSAT — before
//! any search, producing no proof object — whenever an asserted
//! `(= a (store k i v))` coexisted with a positive `(= (select a i) w)` whose
//! value `w` merely FAILED TO MATCH `v` SYNTACTICALLY. Syntactic mismatch is
//! not semantic disequality: with `v = y`, `w = 3`, and `y = 3` asserted
//! beside them, the conjunction is satisfiable, yet the shortcut refuted it.
//! The consumer shape that surfaced the hazard (the model-checker consumer's sequence encoder) puts a
//! `select` term in value position, which can never syntactically equal the
//! stored value.
//!
//! The sound arms are kept: distinct concrete `Const` values on a
//! syntactically matched index ARE contradictory (the control test), and a
//! NEGATIVE select-equality against the syntactically identical stored value
//! remains a genuine conflict.

#![allow(clippy::panic)]

use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

fn arr_sort() -> Sort {
    Sort::array(Sort::Int, Sort::Int)
}

/// a = store(k, 1, y)  /\  select(a, 1) = 3  /\  y = 3   — satisfiable.
/// Pre-fix the shortcut answered Unsat (no proof) in incremental mode.
#[test]
fn incremental_store_select_var_value_semantically_equal_is_not_unsat() {
    let mut s = Solver::try_new(Logic::QfAx).expect("solver");
    s.push();
    let k = s.declare_const("k", arr_sort());
    let a = s.declare_const("a", arr_sort());
    let y = s.declare_const("y", Sort::Int);
    let one = s.int_const(1);
    let three = s.int_const(3);
    let st = s.try_store(k, one, y).expect("store");
    let eq_a = s.try_eq(a, st).expect("eq a");
    s.try_assert_term(eq_a).expect("assert a");
    let sel = s.try_select(a, one).expect("select");
    let eq_sel = s.try_eq(sel, three).expect("eq sel");
    s.try_assert_term(eq_sel).expect("assert sel");
    let eq_y = s.try_eq(y, three).expect("eq y");
    s.try_assert_term(eq_y).expect("assert y");
    let result = s.check_sat().into_inner();
    assert!(
        !matches!(result, SolveResult::Unsat(_)),
        "satisfiable-by-construction conjunction refuted: {result:?}"
    );
}

/// The consumer shape: the stored value is a SELECT term, the probed value a
/// numeral, and the two are linked by an equality on the source array.
/// b = store(k, 1, select(t, 2))  /\  select(b, 1) = 3  /\  select(t, 2) = 3.
#[test]
fn incremental_store_select_select_value_semantically_equal_is_not_unsat() {
    let mut s = Solver::try_new(Logic::QfAx).expect("solver");
    s.push();
    let k = s.declare_const("k", arr_sort());
    let b = s.declare_const("b", arr_sort());
    let t = s.declare_const("t", arr_sort());
    let one = s.int_const(1);
    let two = s.int_const(2);
    let three = s.int_const(3);
    let sel_t = s.try_select(t, two).expect("select t");
    let st = s.try_store(k, one, sel_t).expect("store");
    let eq_b = s.try_eq(b, st).expect("eq b");
    s.try_assert_term(eq_b).expect("assert b");
    let sel_b = s.try_select(b, one).expect("select b");
    let eq_sel = s.try_eq(sel_b, three).expect("eq sel");
    s.try_assert_term(eq_sel).expect("assert sel");
    let eq_src = s.try_eq(sel_t, three).expect("eq src");
    s.try_assert_term(eq_src).expect("assert src");
    let result = s.check_sat().into_inner();
    assert!(
        !matches!(result, SolveResult::Unsat(_)),
        "satisfiable-by-construction conjunction refuted: {result:?}"
    );
}

/// Control: distinct concrete constants on the matched index remain UNSAT —
/// the shortcut's legitimate catch (and, post-fix, the only positive-arm
/// conclusion it may draw).
#[test]
fn incremental_store_select_distinct_const_values_still_unsat() {
    let mut s = Solver::try_new(Logic::QfAx).expect("solver");
    s.push();
    let k = s.declare_const("k", arr_sort());
    let a = s.declare_const("a", arr_sort());
    let one = s.int_const(1);
    let three = s.int_const(3);
    let four = s.int_const(4);
    let st = s.try_store(k, one, four).expect("store");
    let eq_a = s.try_eq(a, st).expect("eq a");
    s.try_assert_term(eq_a).expect("assert a");
    let sel = s.try_select(a, one).expect("select");
    let eq_sel = s.try_eq(sel, three).expect("eq sel");
    s.try_assert_term(eq_sel).expect("assert sel");
    let result = s.check_sat().into_inner();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "genuinely contradictory conjunction not refuted: {result:?}"
    );
}
