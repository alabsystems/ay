// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The read-over-write link of the broken-chain repair, and the same planner
//! offered to the printed-resolution pivot bridge.
//!
//! The positive fixtures are the steps two measured documents shipped as
//! `hole` before `--proof` refused them outright
//! (`conformance/QF_AX/unsat_store_mismatch.smt2`,
//! `regression/soundness_sat_chokepoint/qf_alia_read_over_store_via_maximize`).
//! Pinned carcara 1.1.0 checks the exact derivations asserted here as `valid`
//! (`carcara_external_check/read_over_write_chain.rs` runs them end to end).

use super::{bridged_eq_transitive, bridged_printed_equality};

const READ: &str = "(select (store a i v1) i)";

#[test]
fn a_same_index_read_over_write_link_is_proved_by_arrays_idx() {
    let clause = format!("(cl (not (= v1 v2)) (= {READ} v2))");
    let text = bridged_eq_transitive("t2", &clause).expect("broken only by a read over a write");
    let chain = format!(
        "(step t2.gb.et (cl (not (= {READ} v1)) (not (= v1 v2)) (= {READ} v2)) :rule eq_transitive)"
    );
    let close = format!("(step t2 {clause} :rule resolution :premises (t2.gb.et t2.gb0))");
    assert_eq!(
        text.lines().collect::<Vec<_>>(),
        vec![
            format!("(step t2.gb0 (cl (= {READ} v1)) :rule arrays_idx)").as_str(),
            chain.as_str(),
            close.as_str(),
        ]
    );
}

#[test]
fn a_read_on_the_goal_side_closes_the_chain() {
    let read = "(select (store a i 5) i)";
    let clause = format!("(cl (not (= x 5)) (= x {read}))");
    let text = bridged_eq_transitive("t2", &clause).expect("the read is the last link");
    let chain = format!(
        "(step t2.gb.et (cl (not (= x 5)) (not (= {read} 5)) (= x {read})) :rule eq_transitive)"
    );
    assert_eq!(
        text.lines().collect::<Vec<_>>(),
        vec![
            format!("(step t2.gb0 (cl (= {read} 5)) :rule arrays_idx)").as_str(),
            chain.as_str(),
            format!("(step t2 {clause} :rule resolution :premises (t2.gb.et t2.gb0))").as_str(),
        ]
    );
}

#[test]
fn a_respelled_written_element_adds_its_own_link() {
    let read = "(select (store m #x00 (bvadd #x01 #x01)) #x00)";
    let clause = format!("(cl (not (= y #x02)) (= {read} y))");
    let text = bridged_eq_transitive("t7", &clause).expect("read over write, then evaluate");
    assert!(
        text.starts_with(&format!(
            "(step t7.gb0 (cl (= {read} (bvadd #x01 #x01))) :rule arrays_idx)\n\
             (step t7.gb1 (cl (= (bvadd #x01 #x01) #x02)) :rule evaluate)\n\
             (step t7.gb2 (cl (= {read} #x02)) :rule trans :premises (t7.gb0 t7.gb1))\n"
        )),
        "{text}"
    );
    assert!(text.ends_with(":premises (t7.gb.et t7.gb2))"), "{text}");
}

#[test]
fn a_read_arrays_idx_cannot_prove_keeps_the_hole() {
    for clause in [
        // A different read index needs `arrays_row` and an index disequality.
        "(cl (not (= v1 v2)) (= (select (store a i v1) j) v2))".to_string(),
        // The written element is a different term.
        "(cl (not (= v1 v2)) (= (select (store a i v3) i) v2))".to_string(),
        // Not a read: the outer head is an uninterpreted function.
        "(cl (not (= v1 v2)) (= (f (store a i v1) i) v2))".to_string(),
        // A read of the bare array, no write under it.
        "(cl (not (= v1 v2)) (= (select a i) v2))".to_string(),
    ] {
        assert!(bridged_eq_transitive("t0", &clause).is_none(), "{clause}");
    }
}

#[test]
fn a_printed_equality_between_two_spellings_reports_its_orientation() {
    let positive = format!("(= {READ} v2)");
    let bridged =
        bridged_printed_equality("t4.rw", &positive, "(= v1 v2)").expect("cong over arrays_idx");
    assert_eq!(
        bridged.steps,
        format!(
            "(step t4.rw.gb0 (cl (= {READ} v1)) :rule arrays_idx)\n\
             (step t4.rw.gb1 (cl (= {positive} (= v1 v2))) :rule cong :premises (t4.rw.gb0))\n"
        )
    );
    assert_eq!(bridged.step, "t4.rw.gb1");
    assert!(!bridged.mirrored);

    // `arrays_idx` concludes the read on the LEFT, so asked the other way
    // round the proved equality is the mirror of the request.
    let mirrored = bridged_printed_equality("t9", "v1", READ).expect("arrays_idx");
    assert_eq!(
        mirrored.steps,
        format!("(step t9.gb0 (cl (= {READ} v1)) :rule arrays_idx)\n")
    );
    assert!(mirrored.mirrored);

    for (left, right) in [
        ("(= v1 v2)", "(= v1 v2)"),
        ("(= (select (store a i v1) j) v2)", "(= v1 v2)"),
        ("(= v1 v2)", "(= v2 v1)"),
        // Swapped operands are retried only for `=`, and still need a link.
        ("(= v2 (select (store a i v3) i))", "(= v1 v2)"),
        ("(f v2 (select (store a i v1) i))", "(f v1 v2)"),
    ] {
        assert!(
            bridged_printed_equality("t0", left, right).is_none(),
            "{left} / {right}"
        );
    }
}

#[test]
fn an_authored_equality_with_swapped_operands_still_meets_its_canonical_atom() {
    // `(assert (= v2 (select (store a i v1) i)))` + `(assert (distinct v1 v2))`:
    // the respelled pivot pairs `v2` with `v1` in order, so the planner
    // retries the operands of `(= v1 v2)` swapped; carcara's `cong` checks a
    // binary `=` in every orientation.
    let positive = format!("(= v2 {READ})");
    let bridged = bridged_printed_equality("t4.rw", &positive, "(= v1 v2)")
        .expect("cong over arrays_idx, operands swapped");
    assert_eq!(
        bridged.steps,
        format!(
            "(step t4.rw.gb0 (cl (= {READ} v1)) :rule arrays_idx)\n\
             (step t4.rw.gb1 (cl (= {positive} (= v1 v2))) :rule cong :premises (t4.rw.gb0))\n"
        )
    );
    assert!(!bridged.mirrored);
}
