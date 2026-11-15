// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Proof, Symbol};

fn int_fixture(base: &str, count: usize) -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::Int, Sort::Int);
    let mut array = terms.mk_var(base, sort.clone());
    for n in 1..=count {
        let key = terms.mk_int(n.into());
        let value = terms.mk_var(format!("v{n}"), Sort::Int);
        array = terms.mk_app(Symbol::named("store"), [array, key, value], sort.clone());
    }
    (terms, array)
}

fn render(printer: &AlethePrinter<'_>, term: TermId, source: &str) -> Option<String> {
    let canonical = crate::render_term_canonical(printer.terms, term);
    printer.literal_store_permutation_equivalence("case", source, term, &canonical, &mut 256, 64)
}

#[test]
fn typed_literal_permutation_uses_the_existing_transposition_rules() {
    for count in [2, 3, MAX_STORE_PERMUTATION_CHAIN] {
        let mut source = "a".to_string();
        for n in (1..=count).rev() {
            source = format!("(store {source} {n} v{n})");
        }
        let (terms, term) = int_fixture("a", count);
        let printer = AlethePrinter::new(&terms);
        let proof = render(&printer, term, &source).expect("an exact typed permutation");
        assert!(proof.contains(":rule arrays_ext"));
        assert!(proof.contains(":rule arrays_row"));
        assert!(proof.contains(":rule arrays_idx"));
        assert!(proof.contains(":rule evaluate"));
        assert!(!proof.contains(":rule hole") && !proof.contains(":rule trust"));
        assert!(proof.contains(&format!("(step case (cl (= {source} ")));
    }
}

#[test]
fn nonliteral_repeated_or_foreign_typed_native_indices_refuse() {
    for index in ["symbolic", "repeated", "foreign"] {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::Int, Sort::Int);
        let base = terms.mk_var("a", sort.clone());
        let v1 = terms.mk_var("v1", Sort::Int);
        let v2 = terms.mk_var("v2", Sort::Int);
        let one = terms.mk_int(1.into());
        let other = match index {
            "symbolic" => terms.mk_var("i", Sort::Int),
            "repeated" => one,
            "foreign" => terms.mk_bitvec(2.into(), 8),
            _ => unreachable!(),
        };
        let inner = terms.mk_app(Symbol::named("store"), [base, one, v1], sort.clone());
        let term = terms.mk_app(Symbol::named("store"), [inner, other, v2], sort);
        assert!(
            render(
                &AlethePrinter::new(&terms),
                term,
                "(store (store a 2 v2) 1 v1)"
            )
            .is_none(),
            "{index}"
        );
    }
}

#[test]
fn altered_or_unproved_store_spines_refuse() {
    let (terms, term) = int_fixture("a", 2);
    for source in [
        "(store (store other 2 v2) 1 v1)",
        "(store (store a 2 v1) 1 v1)",
        "(store (store a 2 v2) 2 v1)",
        "(store (store a 2 v2) i v1)",
        "(store (store a 2.0 v2) 1 v1)",
        "(store a 1 v1)",
        "(store (store (store a 3 v3) 2 v2) 1 v1)",
    ] {
        let printer = AlethePrinter::new(&terms);
        assert!(render(&printer, term, source).is_none(), "{source}");
    }
    let (terms, term) = int_fixture("x", 2);
    assert!(render(
        &AlethePrinter::new(&terms),
        term,
        "(store (store x 2 v2) 1 v1)"
    )
    .is_none());
    let (terms, term) = int_fixture("a", 9);
    let mut reversed = "a".to_string();
    for n in (1..=9).rev() {
        reversed = format!("(store {reversed} {n} v{n})");
    }
    assert!(render(&AlethePrinter::new(&terms), term, &reversed).is_none());
}

#[test]
fn typed_bv_and_real_literals_keep_their_actual_index_sorts() {
    for (sort, first, second, one, two, bad) in [
        (
            Sort::bitvec(8),
            "#b00000001",
            "#b00000010",
            "#x01",
            "#x02",
            "#x0002",
        ),
        (Sort::Real, "1.0", "2.0", "1.0", "2.0", "2"),
    ] {
        let mut terms = TermStore::new();
        let array_sort = Sort::array(sort.clone(), Sort::Int);
        let base = terms.mk_var("a", array_sort.clone());
        let v1 = terms.mk_var("v1", Sort::Int);
        let v2 = terms.mk_var("v2", Sort::Int);
        let make = |terms: &mut TermStore, text: &str| match &sort {
            Sort::BitVec(_) => {
                let (value, width) = parse_printed_bitvec_literal(text).unwrap();
                terms.mk_bitvec(value.into(), width)
            }
            Sort::Real => {
                terms.mk_rational(crate::la_generic_signs::parse_numeric_constant(text).unwrap())
            }
            _ => unreachable!(),
        };
        let i = make(&mut terms, first);
        let j = make(&mut terms, second);
        let inner = terms.mk_app(Symbol::named("store"), [base, i, v1], array_sort.clone());
        let term = terms.mk_app(Symbol::named("store"), [inner, j, v2], array_sort);
        let source = format!("(store (store a {two} v2) {one} v1)");
        assert!(render(&AlethePrinter::new(&terms), term, &source).is_some());
        let source = format!("(store (store a {bad} v2) {one} v1)");
        assert!(render(&AlethePrinter::new(&terms), term, &source).is_none());
    }
}

#[test]
fn authored_assume_planner_confines_the_actual_reordered_source() {
    let (mut terms, array) = int_fixture("a", 2);
    let rhs = terms.mk_var("rhs", terms.sort(array).clone());
    let binding = terms.mk_app(Symbol::named("="), [rhs, array], Sort::Bool);
    let denied = terms.mk_not_raw(binding);
    let mut proof = Proof::new();
    let yes = proof.add_assume(binding, None);
    let no = proof.add_assume(denied, None);
    proof.add_resolution(Vec::new(), binding, yes, no);
    let source = "(= rhs (store (store a 2 v2) 1 v1))";
    let mut overrides = HashMap::default();
    overrides.insert(binding, source.to_string());
    overrides.insert(
        denied,
        format!("(not {})", crate::render_term_canonical(&terms, binding)),
    );
    let document = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[binding, denied],
        Some(&overrides),
    )
    .expect("the original assume is bridged, not replaced");
    assert!(
        document.contains(&format!("(assume t0.a {source})")),
        "{document}"
    );
    assert!(
        !document.contains(":rule hole") && !document.contains(":rule trust"),
        "{document}"
    );
}

#[test]
fn permutation_planning_and_output_keep_the_borrowed_limits() {
    let (terms, term) = int_fixture("a", 3);
    let source = "(store (store (store a 3 v3) 1 v1) 2 v2)";
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(1));
    assert!(render(&printer, term, source).is_none());
    assert!(printer.work_budget_exhausted());
    assert!(render(&printer, term, source).is_none());
    let printer = AlethePrinter::new(&terms);
    let canonical = crate::render_term_canonical(&terms, term);
    let mut nodes = 1;
    assert!(printer
        .literal_store_permutation_equivalence("case", source, term, &canonical, &mut nodes, 64)
        .is_none());
    assert_eq!(nodes, 0);
    assert!(printer
        .literal_store_permutation_equivalence("case", source, term, &canonical, &mut 256, 1)
        .is_none());
}
