// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ROW1 under a problem file's own bit-vector literal spelling.
//!
//! Measured defect (`benchmarks/smt/QF_ABV/csplit_repro_unsat.smt2`): the
//! file writes `(store a #x00000000 #xFF)`, AY's canonical rendering of the
//! same 32-bit index is `#b0…0`, and the ROW1 printer compared the two
//! spellings BYTE-FOR-BYTE. It therefore declared its own correct proof
//! invalid — `ROW1 select/store surface override changes the certified array
//! or index` — and, correctly refusing a `:rule trust` fallback, published no
//! Alethe at all.
//!
//! The guard now asks carcara's question instead: do the two texts PARSE to
//! one term? Value AND width must agree and the application shapes must be
//! identical, so every genuine mismatch below is still refused.

use super::*;
use ay_core::kani_compat::DetHashMap;

/// `(= (select (store a #b0…0 #b11111111) #b0…0) #b11111111)` over a
/// 32-bit index and an 8-bit element, the csplit shape.
fn fixture() -> (TermStore, TermId, TermId, TermId) {
    let mut terms = TermStore::new();
    let index_sort = Sort::bitvec(32);
    let element_sort = Sort::bitvec(8);
    let array = Sort::array(index_sort.clone(), element_sort.clone());
    let a = terms.mk_var("a", array.clone());
    let index = terms.mk_bitvec(0.into(), 32);
    let value = terms.mk_bitvec(255.into(), 8);
    let store = terms.mk_app(Symbol::named("store"), [a, index, value], array);
    let select = terms.mk_app(Symbol::named("select"), [store, index], element_sort);
    let row = terms.mk_app(Symbol::named("="), [select, value], Sort::Bool);
    (terms, store, select, row)
}

const CANONICAL_INDEX: &str = "#b00000000000000000000000000000000";
const CANONICAL_VALUE: &str = "#b11111111";

fn printed(store_surface: &str, read_surface: &str) -> (String, String) {
    let stored = store_surface.to_string();
    let selected = format!("(select {stored} {read_surface})");
    (stored, selected)
}

/// Every alternate spelling SMT-LIB admits for the csplit index and value is
/// one term to carcara, so ROW1 must print its `arrays_idx` step for each.
#[test]
fn row1_accepts_the_problem_files_own_bitvector_literal_spellings() {
    let (terms, store, select, row) = fixture();
    for (store_index, stored_value, read_index) in [
        // The measured csplit surface: hex store index, canonical read index.
        ("#x00000000", "#xFF", CANONICAL_INDEX),
        // Both indices hex.
        ("#x00000000", "#xFF", "#x00000000"),
        // `(_ bvN W)` is the third legal spelling.
        ("(_ bv0 32)", "(_ bv255 8)", "#x00000000"),
        // Nothing re-spelled at all: the byte-identical path still works.
        (CANONICAL_INDEX, CANONICAL_VALUE, CANONICAL_INDEX),
    ] {
        let (stored, selected) = printed(
            &format!("(store a {store_index} {stored_value})"),
            read_index,
        );
        for reversed in [false, true] {
            let equality = if reversed {
                format!("(= {stored_value} {selected})")
            } else {
                format!("(= {selected} {stored_value})")
            };
            let overrides: DetHashMap<TermId, String> = [
                (store, stored.clone()),
                (select, selected.clone()),
                (row, equality.clone()),
            ]
            .into_iter()
            .collect();
            let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
            let proof = printer
                .format_array_select_store(ProofId(4), &[row], true)
                .unwrap_or_else(|error| {
                    panic!("{store_index}/{stored_value}/{read_index} reversed={reversed}: {error}")
                });
            assert!(proof.contains(":rule arrays_idx"), "{proof}");
            assert!(!proof.contains(":rule hole"), "{proof}");
            assert!(!proof.contains(":rule trust"), "{proof}");
            assert!(!proof.contains(":rule poly_simp"), "{proof}");
            // The reversed surface must be re-oriented, never silently
            // published as the forward row.
            assert_eq!(proof.contains(":rule symm"), reversed, "{proof}");
        }
    }
}

/// THE NEGATIVE CONTROL. Reading values instead of spellings must not make a
/// genuinely different array, index, width or stored value compare equal —
/// that is the unsound direction, and every row here stays refused.
#[test]
fn row1_still_refuses_a_changed_array_index_width_or_value() {
    let (terms, store, select, row) = fixture();
    for (case, base, store_index, stored_value, read_index) in [
        ("different array", "b", "#x00000000", "#xFF", "#x00000000"),
        (
            "different store index",
            "a",
            "#x00000001",
            "#xFF",
            "#x00000000",
        ),
        (
            "different read index",
            "a",
            "#x00000000",
            "#xFF",
            "#x00000001",
        ),
        (
            "different stored value",
            "a",
            "#x00000000",
            "#xFE",
            "#x00000000",
        ),
        // Same VALUE, narrower index: `#x0000` is a 16-bit zero, a different
        // term to carcara and a different sort to the array.
        ("narrower store index", "a", "#x0000", "#xFF", "#x00000000"),
        (
            "wider store index",
            "a",
            "#x000000000",
            "#xFF",
            "#x00000000",
        ),
        // Same value, wider element: `#x00FF` is a 16-bit 255.
        (
            "wider stored value",
            "a",
            "#x00000000",
            "#x00FF",
            "#x00000000",
        ),
        // `(_ bv0 16)` is the same trap in the third spelling.
        (
            "narrower indexed spelling",
            "a",
            "(_ bv0 16)",
            "#xFF",
            "#x00000000",
        ),
        // A non-literal index text is not a re-spelling of a constant.
        ("symbolic store index", "a", "p", "#xFF", "#x00000000"),
    ] {
        let (stored, selected) = printed(
            &format!("(store {base} {store_index} {stored_value})"),
            read_index,
        );
        let equality = format!("(= {selected} {stored_value})");
        let overrides: DetHashMap<TermId, String> =
            [(store, stored), (select, selected), (row, equality)]
                .into_iter()
                .collect();
        let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
        assert!(
            matches!(
                printer.format_array_select_store(ProofId(4), &[row], true),
                Err(AlethePrintError::InvalidArrayStep { .. })
            ),
            "{case}: a changed ROW1 surface must stay refused"
        );
    }
}

/// A conclusion that is neither orientation of the certified row is refused
/// however its literals are spelled.
#[test]
fn row1_still_refuses_a_conclusion_that_is_not_the_certified_row() {
    let (terms, store, select, row) = fixture();
    let (stored, selected) = printed("(store a #x00000000 #xFF)", "#x00000000");
    for conclusion in [
        "(= #xFF #xFF)",
        "(= #xFE #xFF)",
        format!("(= {selected} #xFE)").as_str(),
        "(= a #xFF)",
    ] {
        let overrides: DetHashMap<TermId, String> = [
            (store, stored.clone()),
            (select, selected.clone()),
            (row, conclusion.to_string()),
        ]
        .into_iter()
        .collect();
        let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
        assert!(
            matches!(
                printer.format_array_select_store(ProofId(4), &[row], true),
                Err(AlethePrintError::InvalidArrayStep { .. })
            ),
            "{conclusion}: a conclusion off the certified row must stay refused"
        );
    }
}
