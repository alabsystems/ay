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

/// A writer over 14 formula clauses (x1 ∨ x2 ∨ x<3+i>): x1 and x2 occur 14
/// times each, so they are the anchors; every other variable occurs once.
fn anchored_writer() -> VeripbWriter<Vec<u8>> {
    let mut w = VeripbWriter::with_original_constraints(Vec::new(), 14);
    for i in 0..14 {
        w.note_original(&[pos(0), pos(1), pos(2 + i)], u64::from(i) + 1);
    }
    w
}

fn text(w: VeripbWriter<Vec<u8>>) -> String {
    String::from_utf8(w.into_inner().expect("no io error")).expect("utf8")
}

#[test]
fn test_the_first_formula_witness_anchors_and_takes_an_identity() {
    let mut w = anchored_writer();
    w.add(&[pos(5), pos(6)]).expect("write");
    assert_eq!(w.constraint_id(&[pos(5), pos(6)]), Some(16));
    w.add(&[pos(7), pos(8)]).expect("write");
    assert_eq!(w.anchored_reds(), 2);
    assert_eq!(
        text(w),
        "pseudo-Boolean proof version 3.0\n\
         red 1 x1 1 x2 1 ay_anchor >= 1 : ay_anchor -> 1 ;\n\
         del id 15 ;\n\
         red 1 x6 1 x7 >= 1 : x6 -> 1 x1 -> x1 ;\n\
         red 1 x8 1 x9 >= 1 : x8 -> 1 x1 -> x1 ;\n"
    );
}

#[test]
fn test_a_witness_on_one_anchor_takes_the_other() {
    let mut w = anchored_writer();
    w.add(&[neg(0), pos(5)]).expect("write");
    w.add(&[neg(1), pos(5)]).expect("write");
    assert!(text(w).ends_with(
        "red 1 ~x1 1 x6 >= 1 : x1 -> 0 x2 -> x2 ;\n\
         red 1 ~x2 1 x6 >= 1 : x2 -> 0 x1 -> x1 ;\n"
    ));
}

#[test]
fn test_a_symmetry_witness_takes_an_identity_unless_it_moves_an_anchor() {
    let mut w = anchored_writer();
    // σ = (x4 x5): pivot, divider, then (l m) pairs.
    w.add_sr(
        &[pos(3), neg(4)],
        &[pos(3), pos(3), pos(3), pos(4), pos(4), pos(3)],
    )
    .expect("write");
    // σ = (x1 x3) moves the anchor x1, which is dropped: nothing to add.
    w.add_sr(
        &[pos(0), neg(2)],
        &[pos(0), pos(0), pos(0), pos(2), pos(2), pos(0)],
    )
    .expect("write");
    assert_eq!(w.anchored_reds(), 1);
    assert!(text(w).ends_with(
        "red 1 x4 1 ~x5 >= 1 : x4 -> x5 x5 -> x4 x1 -> x1 ;\n\
         red 1 x1 1 ~x3 >= 1 : x1 -> x3 x3 -> x1 ;\n"
    ));
}

#[test]
fn test_fresh_witnesses_neither_anchor_nor_take_an_identity() {
    let mut w = anchored_writer();
    // x41 occurs in no formula clause (a factoring variable).
    w.add(&[neg(40), neg(5), neg(6)]).expect("write");
    assert!(w
        .add_conjunction_dividers(pos(40), &[pos(5), pos(6)])
        .expect("write"));
    assert_eq!(w.anchored_reds(), 0);
    let out = text(w);
    assert!(!out.contains("ay_anchor"), "{out}");
    assert!(
        out.contains("red 1 ~x41 1 ~x6 1 ~x7 >= 1 : x41 -> 0 ;\n"),
        "{out}"
    );
}

#[test]
fn test_no_anchor_below_the_occurrence_floor_or_without_line_numbers() {
    // Eleven occurrences each: below the floor.
    let mut w = VeripbWriter::with_original_constraints(Vec::new(), 11);
    for i in 0..11 {
        w.note_original(&[pos(0), pos(1), pos(2 + i)], u64::from(i) + 1);
    }
    w.add(&[pos(5), pos(6)]).expect("write");
    assert_eq!(
        text(w),
        "pseudo-Boolean proof version 3.0\nred 1 x6 1 x7 >= 1 : x6 -> 1 ;\n"
    );
    // No line count when the first witness comes: no anchors for this proof,
    // even once the count is known.
    let mut w = VeripbWriter::new(Vec::new());
    for i in 0..14 {
        w.note_original(&[pos(0), pos(1), pos(2 + i)], u64::from(i) + 1);
    }
    w.add(&[pos(5), pos(6)]).expect("write");
    w.set_original_constraints(14);
    w.add(&[pos(7), pos(8)]).expect("write");
    assert_eq!(w.anchored_reds(), 0);
    assert!(!text(w).contains("ay_anchor"));
}

#[test]
fn test_occurrences_skip_tautologies_and_count_a_variable_once_per_clause() {
    let mut anchor = CakepbAnchor::default();
    anchor.note_clause(&[pos(0), pos(0), pos(1)]);
    anchor.note_clause(&[pos(0), neg(0), pos(2)]);
    anchor.note_clause(&[neg(1), pos(3)]);
    assert_eq!(anchor.occurrences, vec![1, 2, 0, 1]);
    assert!(!anchor.is_formula_variable(2));
    assert!(!anchor.is_formula_variable(9));
}

#[test]
fn test_the_rarest_qualifying_variables_anchor() {
    let mut anchor = CakepbAnchor {
        occurrences: vec![30, 12, 11, 15, 12, 40],
        ..Default::default()
    };
    assert_eq!(anchor.pick(), Some([1, 4]));
    anchor.occurrences = vec![30, 11];
    assert_eq!(anchor.pick(), None);
}
