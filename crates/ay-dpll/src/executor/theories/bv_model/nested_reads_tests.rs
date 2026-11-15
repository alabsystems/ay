// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An array of arrays takes its interpretation from its nested reads
//! (`nested_reads.rs`), and a nested-only definition no longer withholds it
//! (`live_definitions.rs`), whether that interpretation refutes the definition
//! the SAT assignment refused or holds it.

use super::tests::{array_of, bv, cell, define, extract, model};
use super::*;

const SMALL_ROW: &str = "(Array (_ BitVec 4) (_ BitVec 3))";

fn small_memory() -> Sort {
    array_of(4, array_of(4, Sort::bitvec(3)))
}

/// `(select (select m0 i) j)` with both indices constants.
fn nested_read(terms: &mut TermStore, m0: TermId, i: u64, j: u64) -> TermId {
    let i = bv(terms, i, 4);
    let j = bv(terms, j, 4);
    let row = terms.mk_select(m0, i);
    terms.mk_select(row, j)
}

#[test]
fn nested_reads_give_an_array_of_arrays_its_cells() {
    let mut terms = TermStore::new();
    let m0 = terms.mk_var("m0", small_memory());
    let x = terms.mk_var("x", Sort::bitvec(4));
    let five = bv(&mut terms, 5, 4);
    let row_x = terms.mk_select(m0, x);
    let at_x_five = terms.mk_select(row_x, five);
    let at_one_two = nested_read(&mut terms, m0, 1, 2);
    let at_one_six = nested_read(&mut terms, m0, 1, 6);

    let values = [(x, 0), (at_x_five, 4), (at_one_two, 7), (at_one_six, 1)];
    let arrays = extract(&terms, &model(&values, &[]), &[]);

    assert_eq!(
        cell(&arrays, m0, "#x0"),
        format!("(store ((as const {SMALL_ROW}) #b000) #x5 #b100)")
    );
    assert_eq!(
        cell(&arrays, m0, "#x1"),
        format!("(store (store ((as const {SMALL_ROW}) #b000) #x2 #b111) #x6 #b001)")
    );
    assert_eq!(
        cell(&arrays, m0, "#x9"),
        format!("((as const {SMALL_ROW}) #b000)"),
        "no read reaches row 9"
    );
}

#[test]
fn disagreeing_nested_reads_pin_nothing() {
    let mut terms = TermStore::new();
    let m0 = terms.mk_var("m0", small_memory());
    let x = terms.mk_var("x", Sort::bitvec(4));
    let two = bv(&mut terms, 2, 4);
    let row_x = terms.mk_select(m0, x);
    let at_x_two = terms.mk_select(row_x, two);
    let at_one_two = nested_read(&mut terms, m0, 1, 2);
    let at_one_three = nested_read(&mut terms, m0, 1, 3);

    // x = 1: two reads of m0[1][2] disagree; m0[1][3] stands.
    let values = [(x, 1), (at_x_two, 4), (at_one_two, 7), (at_one_three, 2)];
    let arrays = extract(&terms, &model(&values, &[]), &[]);

    assert_eq!(
        cell(&arrays, m0, "#x1"),
        format!("(store ((as const {SMALL_ROW}) #b000) #x3 #b010)")
    );
}

#[test]
fn inner_default_term_sets_the_inner_else_value() {
    let mut terms = TermStore::new();
    let m0 = terms.mk_var("m0", small_memory());
    let one = bv(&mut terms, 1, 4);
    let row_one = terms.mk_select(m0, one);
    let default_row_one = terms.mk_array_default(row_one);
    let at_one_two = nested_read(&mut terms, m0, 1, 2);

    let values = [(at_one_two, 7), (default_row_one, 3)];
    let arrays = extract(&terms, &model(&values, &[]), &[]);

    assert_eq!(
        cell(&arrays, m0, "#x1"),
        format!("(store ((as const {SMALL_ROW}) #b011) #x2 #b111)")
    );
}

#[test]
fn nested_read_whose_index_was_eliminated_is_skipped() {
    let mut terms = TermStore::new();
    let m0 = terms.mk_var("m0", small_memory());
    let gone = terms.mk_var("gone", Sort::bitvec(4));
    let two = bv(&mut terms, 2, 4);
    let row = terms.mk_select(m0, gone);
    let read = terms.mk_select(row, two);
    let kept = nested_read(&mut terms, m0, 3, 3);
    let substituted: HashSet<TermId> = [gone].into_iter().collect();

    let values = [(gone, 1), (read, 7), (kept, 5)];
    let arrays = Executor::extract_array_model_from_bv_model(
        &terms,
        &model(&values, &[]),
        &[],
        &substituted,
    );

    assert_eq!(
        cell(&arrays, m0, "#x1"),
        format!("((as const {SMALL_ROW}) #b000)"),
        "the decoupled read plants nothing"
    );
    assert_eq!(
        cell(&arrays, m0, "#x3"),
        format!("(store ((as const {SMALL_ROW}) #b000) #x3 #b101)")
    );
}

/// `(or (= n (store n0 #x1 (const #b000))) q)` with the definition atom set
/// false, `n0[1][2] = 0` read, and `n[1][2]` read as `n_at`.
fn refused_nested_definition(n_at: u64) -> (TermStore, ArrayModel, TermId) {
    let mut terms = TermStore::new();
    let n = terms.mk_var("n", small_memory());
    let n0 = terms.mk_var("n0", small_memory());
    let one = bv(&mut terms, 1, 4);
    let zero = bv(&mut terms, 0, 3);
    let zero_row = terms.mk_const_array(Sort::bitvec(4), zero);
    let rows = terms.mk_store(n0, one, zero_row);
    let n_def = define(&mut terms, n, rows);
    let q = terms.mk_var("q", Sort::Bool);
    let assertion = terms.mk_or(vec![n_def, q]);
    let n_read = nested_read(&mut terms, n, 1, 2);
    let n0_read = nested_read(&mut terms, n0, 1, 2);

    let values = [(n_read, n_at), (n0_read, 0)];
    let arrays = extract(
        &terms,
        &model(&values, &[(n_def, false), (q, true)]),
        &[assertion],
    );
    (terms, arrays, n)
}

/// `n[1][2] = 5` where the definition stores a zero row at 1: the published
/// interpretations refute the definition the atom refused, so `n` is an
/// ordinary array of arrays with its own value.
#[test]
fn array_of_arrays_whose_refused_definition_its_reads_refute_is_released() {
    let (_, arrays, n) = refused_nested_definition(5);
    assert!(!arrays.read_conflicted.contains(&n));
    assert_eq!(
        cell(&arrays, n, "#x1"),
        format!("(store ((as const {SMALL_ROW}) #b000) #x2 #b101)")
    );
}

/// `n[1][2] = 0`: built from the reads, `n` equals the definition the atom
/// refused. Its release once confirmed models z3 rejects, while acceptance
/// still counted bit-blast coverage as evidence; since #bv-array-delegation
/// the gate judges the printed `n` on its values, so `n` is published with
/// the interpretation its reads give it (`live_definitions.rs`). A model that
/// relied on the refusal fails closed (`model/tests/bv_array_delegation.rs`,
/// `released_array_of_arrays_holding_its_refused_definition_fails_closed`).
#[test]
fn array_of_arrays_whose_reads_hold_its_refused_definition_keeps_its_reads() {
    let (_, arrays, n) = refused_nested_definition(0);
    assert!(!arrays.read_conflicted.contains(&n));
    assert_eq!(
        crate::executor_format::array_cell::array_cells_equal(
            cell(&arrays, n, "#x1"),
            &format!("((as const {SMALL_ROW}) #b000)")
        ),
        Some(true),
        "{}",
        cell(&arrays, n, "#x1")
    );
}

/// A definition under a false conjunct cannot matter: an array of arrays a
/// read reaches is released like a flat one.
#[test]
fn array_of_arrays_definition_under_a_false_conjunct_is_released_once_read() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let seven = bv(&mut terms, 7, 8);
    let guard = terms.mk_bvuge(x, seven);
    let n = terms.mk_var("n", small_memory());
    let n0 = terms.mk_var("n0", small_memory());
    let one = bv(&mut terms, 1, 4);
    let zero = bv(&mut terms, 0, 3);
    let zero_row = terms.mk_const_array(Sort::bitvec(4), zero);
    let rows = terms.mk_store(n0, one, zero_row);
    let n_def = define(&mut terms, n, rows);
    let dead_arm = terms.mk_and(vec![guard, n_def]);
    let q = terms.mk_var("q", Sort::Bool);
    let assertion = terms.mk_or(vec![dead_arm, q]);
    let n_read = nested_read(&mut terms, n, 3, 3);

    let values = [(x, 1), (n_read, 6)];
    let arrays = extract(&terms, &model(&values, &[(q, true)]), &[assertion]);

    assert!(!arrays.read_conflicted.contains(&n));
    assert_eq!(
        cell(&arrays, n, "#x3"),
        format!("(store ((as const {SMALL_ROW}) #b000) #x3 #b110)")
    );
}

/// `(or (= n (store n0 #x1 (store (select n0 #x1) #x2 #b111))) q)`, the write
/// of one cell into row 1 of `n0`, with its atom set false, `n0[1][2] = 4`
/// read, and `n[1][2]` read as `n_at`. The store over the read
/// `(select n0 #x1)` builds from `n0`'s row parsed back from its cell
/// (`nested_cells.rs`); before, it did not build and `n` stayed withheld
/// whatever its reads.
fn refused_row_write(n_at: u64) -> (ArrayModel, TermId) {
    let mut terms = TermStore::new();
    let n = terms.mk_var("n", small_memory());
    let n0 = terms.mk_var("n0", small_memory());
    let one = bv(&mut terms, 1, 4);
    let two = bv(&mut terms, 2, 4);
    let seven = bv(&mut terms, 7, 3);
    let row = terms.mk_select(n0, one);
    let written = terms.mk_store(row, two, seven);
    let rows = terms.mk_store(n0, one, written);
    let n_def = define(&mut terms, n, rows);
    let q = terms.mk_var("q", Sort::Bool);
    let assertion = terms.mk_or(vec![n_def, q]);
    let n_read = nested_read(&mut terms, n, 1, 2);
    let n0_read = nested_read(&mut terms, n0, 1, 2);

    let values = [(n_read, n_at), (n0_read, 4)];
    let arrays = extract(
        &terms,
        &model(&values, &[(n_def, false), (q, true)]),
        &[assertion],
    );
    (arrays, n)
}

/// `n[1][2] = 3` where the refused write puts 7: the published
/// interpretations refute it, so `n` is released with its own cells.
#[test]
fn refused_write_into_a_row_its_reads_refute_is_released() {
    let (arrays, n) = refused_row_write(3);
    assert!(!arrays.read_conflicted.contains(&n));
    assert_eq!(
        cell(&arrays, n, "#x1"),
        format!("(store ((as const {SMALL_ROW}) #b000) #x2 #b011)")
    );
}

/// `n[1][2] = 7`: built from the reads, `n` is the array the refused write
/// denotes; it is published with its own cells all the same.
#[test]
fn refused_write_into_a_row_its_reads_hold_keeps_its_reads() {
    let (arrays, n) = refused_row_write(7);
    assert!(!arrays.read_conflicted.contains(&n));
    assert_eq!(
        cell(&arrays, n, "#x1"),
        format!("(store ((as const {SMALL_ROW}) #b000) #x2 #b111)")
    );
}

/// The same write asserted at the top level publishes `n` as `n0` with row 1
/// rewritten, the row read back from `n0`'s cell.
#[test]
fn unconditional_write_into_a_row_publishes_the_written_row() {
    let mut terms = TermStore::new();
    let n = terms.mk_var("n", small_memory());
    let n0 = terms.mk_var("n0", small_memory());
    let one = bv(&mut terms, 1, 4);
    let two = bv(&mut terms, 2, 4);
    let seven = bv(&mut terms, 7, 3);
    let row = terms.mk_select(n0, one);
    let written = terms.mk_store(row, two, seven);
    let rows = terms.mk_store(n0, one, written);
    let n_def = define(&mut terms, n, rows);
    let n0_read = nested_read(&mut terms, n0, 1, 5);

    let values = [(n0_read, 4)];
    let arrays = extract(&terms, &model(&values, &[]), &[n_def]);

    assert!(!arrays.read_conflicted.contains(&n));
    let expected = format!("(store (store ((as const {SMALL_ROW}) #b000) #x2 #b111) #x5 #b100)");
    assert_eq!(
        crate::executor_format::array_cell::array_cells_equal(cell(&arrays, n, "#x1"), &expected),
        Some(true),
        "{}",
        cell(&arrays, n, "#x1")
    );
}
