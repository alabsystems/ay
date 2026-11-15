// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Datatype-valued BitVec-indexed array cells of a datatype whose NAME needs
//! pipe-quoting (`executor/model/datatype_cell_authority.rs`,
//! `exact_datatype_carrier_token`; C-4 of the 2026-09-16 solver-fix round).
//!
//! deductive-checks encodes a Rust tuple as the native datatype `(u32, u32)`, so its
//! EUF carriers are spelled `@(u32, u32)!n`. The exact cell authority used to
//! decline every carrier of a quoted-name datatype, so when an arithmetic lane
//! made the array extractor keep the carrier spelling for a cell, neither the
//! completion pass nor the independent gate could normalize that cell to its
//! class's constructor tree, and the gate fail-closed a genuine `sat` with
//! "datatype sort requires a constructor-bearing value" (deductive-checks
//! `collection_tuple_element_capability::map_tuple_false_counterexamples`).
//! The same queries with a bare-safe datatype name were already `sat`. z3
//! answers `sat` on every satisfiable query below and `unsat` on every
//! control; the quoted-name and bare-name twins must agree.

use super::*;

fn verdict(input: &str) -> Vec<String> {
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap()
}

const QUOTED_PRELUDE: &str = r#"
    (set-logic ALL)
    (declare-datatypes ((|(u32, u32)| 0))
        (((mk (f0 (_ BitVec 32)) (f1 (_ BitVec 32))))))
    (declare-const seed |(u32, u32)|)
    (declare-const m (Array (_ BitVec 32) |(u32, u32)|))
    (declare-const l4 Int)
"#;

const BARE_PRELUDE: &str = r#"
    (set-logic ALL)
    (declare-datatypes ((T 0))
        (((mk (f0 (_ BitVec 32)) (f1 (_ BitVec 32))))))
    (declare-const seed T)
    (declare-const m (Array (_ BitVec 32) T))
    (declare-const l4 Int)
"#;

/// Run `body` under both preludes; `{SORT}` in `body` names the datatype.
fn twins(body: &str, expected: &[&str]) {
    for (prelude, sort) in [(QUOTED_PRELUDE, "|(u32, u32)|"), (BARE_PRELUDE, "T")] {
        let input = format!("{prelude}{}", body.replace("{SORT}", sort));
        assert_eq!(
            verdict(&input),
            expected,
            "verdict must not depend on whether the datatype name needs quoting:\n{input}"
        );
    }
}

/// The reduced C-4 trigger: one datatype-valued cell pinned to a free
/// datatype constant, plus an arithmetic lane. Without the Int atom the
/// query never took the failing route.
///
/// This and the two `_with_int_lane`/`_other_index` shapes below were a
/// known gap from 2026-09-17 to 2026-10-13: their `sat` depended on reading
/// the dtbv field variables from their EUF classes, and the read for every
/// evaluation was reverted (#bv-euf-class-literal-read: it answered ten other
/// queries, `sfz/q/dtn/dtn_0001_named.smt2` among them, with a literal
/// contradicting their own `bvult` atoms). Model completion now offers the
/// class value once, verified per variable against every atom that mentions
/// it (#uninterpreted-bitvec-class-values,
/// `executor/model/completion/bitvec_classes.rs`). z3 answers `sat` on each,
/// and the twins still agree.
#[test]
fn cell_equal_to_free_constant_with_int_lane_is_sat() {
    twins(
        r#"
        (assert (= (select m #x00000000) seed))
        (assert (<= l4 1))
        (check-sat)
    "#,
        &["sat"],
    );
}

/// Same shape without the arithmetic lane (control: was already `sat`).
#[test]
fn cell_equal_to_free_constant_without_int_lane_is_sat() {
    twins(
        r#"
        (assert (= (select m #x00000000) seed))
        (check-sat)
    "#,
        &["sat"],
    );
}

/// A selector read through the cell agrees with the pinned constant.
#[test]
fn selector_of_cell_agrees_with_pinned_constant_is_sat() {
    twins(
        r#"
        (assert (= (select m #x00000000) seed))
        (assert (= seed (mk #x00000001 #x00000002)))
        (assert (<= l4 1))
        (assert (= (f1 (select m #x00000000)) #x00000002))
        (check-sat)
    "#,
        &["sat"],
    );
}

/// Field constraints on both spellings of one class; the published values of
/// the cell and the constant must be the SAME constructor tree, never an
/// opaque carrier.
#[test]
fn cell_and_constant_publish_one_constructor_tree() {
    let input = format!(
        "{QUOTED_PRELUDE}
        (assert (= (select m #x00000000) seed))
        (assert (<= l4 1))
        (assert (= (f0 seed) #x00000005))
        (assert (= (f1 (select m #x00000000)) #x00000009))
        (check-sat)
        (get-value ((select m #x00000000) seed))
    "
    );
    let out = verdict(&input);
    // This shape reaches the publication only through the dtbv field
    // variables' EUF class values, offered and verified at model completion
    // (#uninterpreted-bitvec-class-values; a known gap from 2026-09-17 to
    // 2026-10-13). z3 answers `sat`.
    assert_eq!(out[0], "sat", "z3 answers `sat`: {out:?}");
    let values = &out[1];
    assert!(
        values.contains("(mk #x00000005 #x00000009)"),
        "expected the constructor tree in the published values: {values}"
    );
    assert!(
        !values.contains('@'),
        "no opaque carrier may be published for a datatype-sorted read: {values}"
    );
    assert_eq!(
        values.matches("(mk #x00000005 #x00000009)").count(),
        2,
        "cell and constant must agree: {values}"
    );
}

/// Two cells pinned to two distinct constants, one field constrained.
#[test]
fn two_distinct_cells_with_int_lane_is_sat() {
    twins(
        r#"
        (declare-const seed2 {SORT})
        (assert (= (select m #x00000000) seed))
        (assert (= (select m #x00000001) seed2))
        (assert (not (= seed seed2)))
        (assert (<= l4 1))
        (assert (= (f0 (select m #x00000001)) #x00000005))
        (check-sat)
    "#,
        &["sat"],
    );
}

/// A read through a store at another index still reaches the base cell.
#[test]
fn read_through_store_at_other_index_is_sat() {
    twins(
        r#"
        (assert (= (select m #x00000000) seed))
        (assert (= (select (store m #x00000001 (mk #x00000003 #x00000004)) #x00000000) seed))
        (assert (<= l4 1))
        (assert (not (= (f1 seed) #x00000004)))
        (check-sat)
    "#,
        &["sat"],
    );
}

/// The faithful reconstruction of the deductive-checks `map_tuple_false` query
/// (`Map<u32,(u32,u32)>::empty().insert(1,(7,8)).get(1).1 == 999`), with
/// deductive-checks's own symbol names and the unsat-core route it uses.
#[test]
fn deductive_checks_map_tuple_false_reconstruction_is_sat() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic ALL)
        (declare-datatypes ((|(u32, u32)| 0))
            (((u32_u32_Tuple (u32_u32_Tuple_0 (_ BitVec 32))
                             (u32_u32_Tuple_1 (_ BitVec 32))))))
        (declare-const dom (Array (_ BitVec 32) Bool))
        (declare-const seed |(u32, u32)|)
        (declare-const m (Array (_ BitVec 32) |(u32, u32)|))
        (declare-const l3 Int)
        (declare-const l4 Int)
        (assert (! (= dom ((as const (Array (_ BitVec 32) Bool)) false)) :named dn0))
        (assert (! (= (select m #x00000000) seed) :named dn1))
        (assert (! (<= 0 l3) :named dn2))
        (assert (! (<= l3 1) :named dn3))
        (assert (! (<= 0 l4) :named dn4))
        (assert (! (<= l4 1) :named dn5))
        (assert (! (not (= (u32_u32_Tuple_1 (u32_u32_Tuple #x00000007 #x00000008))
                           #x000003e7))
                   :named dn6))
        (check-sat)
    "#;
    assert_eq!(verdict(input), vec!["sat"]);
}

/// UNSAT controls: the cell IS the pinned constant, so a selector read that
/// contradicts the pinned field is refuted on both spellings.
#[test]
fn selector_of_cell_contradicting_pinned_constant_is_unsat() {
    twins(
        r#"
        (assert (= (select m #x00000000) seed))
        (assert (= seed (mk #x00000001 #x00000002)))
        (assert (<= l4 1))
        (assert (not (= (f1 (select m #x00000000)) #x00000002)))
        (check-sat)
    "#,
        &["unsat"],
    );
    twins(
        r#"
        (assert (= (select m #x00000000) seed))
        (assert (= seed (mk #x00000001 #x00000002)))
        (assert (<= l4 1))
        (assert (= (f1 (select m #x00000000)) #x00000003))
        (check-sat)
    "#,
        &["unsat"],
    );
    twins(
        r#"
        (assert (= (select m #x00000000) seed))
        (assert (<= l4 1))
        (assert (= (f0 seed) #x00000005))
        (assert (not (= (f0 (select m #x00000000)) #x00000005)))
        (check-sat)
    "#,
        &["unsat"],
    );
}
