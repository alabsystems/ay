// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::literal::Variable;

fn pos(v: u32) -> Literal {
    Literal::positive(Variable(v))
}

fn neg(v: u32) -> Literal {
    Literal::negative(Variable(v))
}

/// A writer over a 3-clause formula on x1..x3 (all below the anchor floor, so
/// no anchoring), collecting every `every` fresh occurrences.
fn writer(every: u64) -> VeripbWriter<Vec<u8>> {
    let mut w = VeripbWriter::with_original_constraints(Vec::new(), 3);
    w.note_original(&[pos(0), pos(1)], 1);
    w.note_original(&[neg(1), pos(2)], 2);
    w.note_original(&[neg(0), neg(2)], 3);
    w.fresh.every = every;
    w
}

fn text(w: VeripbWriter<Vec<u8>>) -> String {
    String::from_utf8(w.into_inner().expect("no io error")).expect("utf8")
}

#[test]
fn test_a_collection_names_every_fresh_variable_written_and_is_deleted() {
    let mut w = writer(4);
    w.add_rup(&[pos(10), pos(0)], &[1]).expect("write");
    w.add_rup(&[neg(11), pos(10), pos(1)], &[2]).expect("write");
    assert_eq!(w.fresh_collections(), 0);
    w.add_rup(&[pos(11), pos(2)], &[3]).expect("write");
    assert_eq!(w.fresh_collections(), 1);
    // The step took id 7: the next derived constraint is 8.
    w.add_rup(&[pos(0), pos(1), pos(2)], &[1]).expect("write");
    assert_eq!(w.constraint_id(&[pos(0), pos(1), pos(2)]), Some(8));
    assert_eq!(
        text(w),
        "pseudo-Boolean proof version 3.0\n\
         rup 1 x11 1 x1 >= 1 : 1 ;\n\
         rup 1 ~x12 1 x11 1 x2 >= 1 : 2 ;\n\
         rup 1 x12 1 x3 >= 1 : 3 ;\n\
         red >= 0 : x11 -> x11 x12 -> x12 ;\n\
         del id 7 ;\n\
         rup 1 x1 1 x2 1 x3 >= 1 : 1 ;\n"
    );
}

#[test]
fn test_formula_variables_never_count_and_a_later_collection_names_all_seen() {
    let mut w = writer(2);
    for _ in 0..5 {
        w.add_rup(&[pos(0), pos(1), pos(2)], &[1]).expect("write");
    }
    assert_eq!(w.fresh_collections(), 0);
    w.add_rup(&[pos(20), pos(21)], &[1]).expect("write");
    w.add_rup(&[pos(22), pos(0)], &[1]).expect("write");
    w.add_rup(&[pos(20), pos(1)], &[1]).expect("write");
    assert_eq!(w.fresh_collections(), 2);
    let out = text(w);
    assert!(
        out.contains("red >= 0 : x21 -> x21 x22 -> x22 ;\n"),
        "{out}"
    );
    assert!(
        out.contains("red >= 0 : x21 -> x21 x22 -> x22 x23 -> x23 ;\n"),
        "{out}"
    );
}

#[test]
fn test_no_collection_without_formula_clauses_or_line_numbers() {
    // Hints off: no formula clause noted, so nothing is known to be fresh.
    let mut w = VeripbWriter::with_original_constraints(Vec::new(), 3);
    w.fresh.every = 1;
    w.add_rup(&[pos(10), pos(11)], &[1]).expect("write");
    assert_eq!(w.fresh_collections(), 0);
    // No line count: the step could not be deleted by id, so none is written.
    let mut w = VeripbWriter::new(Vec::new());
    w.note_original(&[pos(0), pos(1)], 1);
    w.fresh.every = 1;
    w.add_rup(&[pos(10), pos(0)], &[1]).expect("write");
    assert_eq!(w.fresh_collections(), 0);
    assert!(!text(w).contains("red >= 0"));
}
