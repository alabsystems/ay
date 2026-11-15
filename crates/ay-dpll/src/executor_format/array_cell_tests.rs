// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{array_cell_parts, array_cells_equal, merge_array_cells, CellDefaultPolicy};

const ROW: &str = "(as const (Array (_ BitVec 4) (_ BitVec 3)))";

/// The reads-derived pass: the existing else-value stands.
fn preserve(existing: &str, candidate: &str) -> Option<String> {
    merge_array_cells(existing, candidate, CellDefaultPolicy::Preserve)
}

/// A target with a semantic `(default ..)` value: the else-values must agree.
fn require(existing: &str, candidate: &str) -> Option<String> {
    merge_array_cells(existing, candidate, CellDefaultPolicy::Require)
}

/// Any other defined target: the candidate's else-value replaces the existing.
fn ignore(existing: &str, candidate: &str) -> Option<String> {
    merge_array_cells(existing, candidate, CellDefaultPolicy::Ignore)
}

fn row(default: &str, stores: &[(&str, &str)]) -> String {
    let mut text = format!("({ROW} {default})");
    for (index, value) in stores {
        text = format!("(store {text} {index} {value})");
    }
    text
}

#[test]
fn single_read_fold_keeps_the_extracted_row() {
    // The extractor's row stores the read; the candidate folded it into its
    // else-value. The extracted else-value stands.
    let existing = row("#b000", &[("#x5", "#b100")]);
    let candidate = row("#b100", &[]);
    assert_eq!(preserve(&existing, &candidate), Some(existing));
}

#[test]
fn store_order_does_not_matter() {
    let existing = row("#b000", &[("#x5", "#b100"), ("#x1", "#b010")]);
    let candidate = row("#b000", &[("#x1", "#b010"), ("#x5", "#b100")]);
    assert_eq!(
        preserve(&existing, &candidate),
        Some(row("#b000", &[("#x1", "#b010"), ("#x5", "#b100")]))
    );
}

#[test]
fn a_candidate_store_at_a_new_index_is_added() {
    let existing = row("#b000", &[("#x5", "#b100")]);
    let candidate = row("#b111", &[("#x7", "#b001")]);
    assert_eq!(
        preserve(&existing, &candidate),
        Some(row("#b000", &[("#x5", "#b100"), ("#x7", "#b001")]))
    );
}

#[test]
fn the_outermost_store_of_an_index_wins() {
    let existing = row("#b000", &[("#x5", "#b001"), ("#x5", "#b100")]);
    let candidate = row("#b000", &[("#x5", "#b100")]);
    assert_eq!(
        preserve(&existing, &candidate),
        Some(row("#b000", &[("#x5", "#b100")]))
    );
}

#[test]
fn two_values_at_one_index_conflict() {
    let existing = row("#b000", &[("#x5", "#b100")]);
    let candidate = row("#b000", &[("#x5", "#b101")]);
    assert_eq!(preserve(&existing, &candidate), None);
}

#[test]
fn nested_rows_merge_recursively_and_conflict_on_a_leaf() {
    let outer = "(as const (Array (_ BitVec 4) (Array (_ BitVec 4) (_ BitVec 3))))";
    let zero = row("#b000", &[]);
    let existing = format!(
        "(store ({outer} {zero}) #x1 {})",
        row("#b000", &[("#x5", "#b100")])
    );
    let agreeing = format!(
        "(store ({outer} {zero}) #x1 {})",
        row("#b000", &[("#x6", "#b011")])
    );
    assert_eq!(
        preserve(&existing, &agreeing),
        Some(format!(
            "(store ({outer} {zero}) #x1 {})",
            row("#b000", &[("#x5", "#b100"), ("#x6", "#b011")])
        ))
    );
    let disagreeing = format!(
        "(store ({outer} {zero}) #x1 {})",
        row("#b000", &[("#x5", "#b001")])
    );
    assert_eq!(preserve(&existing, &disagreeing), None);
}

#[test]
fn unparsed_or_scalar_text_conflicts() {
    let existing = row("#b000", &[("#x5", "#b100")]);
    assert_eq!(preserve(&existing, "(store"), None);
    assert_eq!(preserve("#b000", "#b001"), None);
    assert_eq!(preserve("#b000", "#b000"), None);
    assert_eq!(preserve(&existing, "@Arr!3"), None);
    let other_sort = "((as const (Array (_ BitVec 4) (_ BitVec 2))) #b00)";
    assert_eq!(preserve(&existing, other_sort), None);
}

#[test]
fn equal_cells_are_the_same_array_however_spelled() {
    let stored = row("#b000", &[("#x5", "#b100"), ("#x1", "#b010")]);
    let reordered = row(
        "#b000",
        &[("#x1", "#b010"), ("#x5", "#b100"), ("#x7", "#b000")],
    );
    assert_eq!(array_cells_equal(&stored, &reordered), Some(true));
    // A single read folded into the else-value is a different array.
    let read = row("#b000", &[("#x5", "#b100")]);
    let fold = row("#b100", &[]);
    assert_eq!(array_cells_equal(&read, &fold), Some(false));
    // Defaults may differ only under a fully stored domain.
    let all: Vec<(String, &str)> = (0..16).map(|i| (format!("#x{i:x}"), "#b001")).collect();
    let all: Vec<(&str, &str)> = all.iter().map(|(k, v)| (k.as_str(), *v)).collect();
    assert_eq!(
        array_cells_equal(&row("#b000", &all), &row("#b001", &[])),
        Some(true)
    );
    assert_eq!(
        array_cells_equal(&row("#b000", &all[1..]), &row("#b001", &[])),
        Some(false)
    );
    assert_eq!(array_cells_equal(&stored, "#b000"), None);
}

#[test]
fn require_needs_agreeing_else_values() {
    let existing = row("#b000", &[("#x5", "#b100")]);
    // The fold puts the read in the else-value: a definition's else-value is
    // not a fallback, so the disagreement is a conflict.
    assert_eq!(require(&existing, &row("#b100", &[])), None);
    assert_eq!(
        require(&existing, &row("#b000", &[("#x7", "#b001")])),
        Some(row("#b000", &[("#x5", "#b100"), ("#x7", "#b001")]))
    );
    assert_eq!(require(&existing, &row("#b000", &[("#x5", "#b101")])), None);
    // A fully stored domain leaves no index to read either else-value.
    let all: Vec<(String, &str)> = (0..16).map(|i| (format!("#x{i:x}"), "#b001")).collect();
    let all: Vec<(&str, &str)> = all.iter().map(|(k, v)| (k.as_str(), *v)).collect();
    assert_eq!(
        require(&row("#b000", &all), &row("#b001", &[])),
        Some(row("#b000", &all))
    );
    assert_eq!(require(&row("#b000", &all[1..]), &row("#b001", &[])), None);
}

#[test]
fn require_compares_else_values_at_every_level() {
    let outer = "(as const (Array (_ BitVec 4) (Array (_ BitVec 4) (_ BitVec 3))))";
    let zero = row("#b000", &[]);
    let respelled = row("#b000", &[("#x3", "#b000")]);
    let one = row("#b001", &[]);
    let cell = |default: &str| format!("(store ({outer} {default}) #x1 {})", row("#b000", &[]));
    // One inner else-value spelled twice agrees; a different one does not,
    // also when it is an array itself.
    assert_eq!(require(&cell(&zero), &cell(&respelled)), Some(cell(&zero)));
    assert_eq!(require(&cell(&zero), &cell(&one)), None);
    assert_eq!(preserve(&cell(&zero), &cell(&one)), Some(cell(&zero)));
}

#[test]
fn ignore_takes_the_candidates_else_value_under_the_existing_stores() {
    let existing = row("#b000", &[("#x5", "#b100")]);
    assert_eq!(
        ignore(&existing, &row("#b011", &[("#x7", "#b001")])),
        Some(row("#b011", &[("#x5", "#b100"), ("#x7", "#b001")]))
    );
    assert_eq!(ignore(&existing, &row("#b011", &[("#x5", "#b101")])), None);
}

#[test]
fn parts_read_back_the_else_value_and_one_store_per_index() {
    assert_eq!(
        array_cell_parts(&row("#b010", &[("#x2", "#b001"), ("#x2", "#b111")])),
        Some((
            "#b010".to_string(),
            vec![("#x2".to_string(), "#b111".to_string())]
        )),
        "the outermost store of an index wins"
    );
    let outer = "(as const (Array (_ BitVec 4) (Array (_ BitVec 4) (_ BitVec 3))))";
    let inner = row("#b000", &[("#x5", "#b100")]);
    let cell = format!("(store ({outer} {}) #x1 {inner})", row("#b001", &[]));
    assert_eq!(
        array_cell_parts(&cell),
        Some((row("#b001", &[]), vec![("#x1".to_string(), inner)]))
    );
    assert_eq!(array_cell_parts("#b000"), None);
    assert_eq!(array_cell_parts("(store"), None);
    assert_eq!(array_cell_parts("@Arr!3"), None);
}
