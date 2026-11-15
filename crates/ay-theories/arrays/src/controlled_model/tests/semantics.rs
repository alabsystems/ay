// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn full_owned_copy_preserves_candidate_conflicts_and_duplicate_order() {
    let source = model();
    let result = healthy(|work| source.try_clone_with_budget(work)).unwrap();
    assert_eq!(result.array_values, source.array_values);
    assert_eq!(result.read_conflicted, source.read_conflicted);
    assert_eq!(
        result.store_chain_class_candidate,
        source.store_chain_class_candidate
    );
    assert_eq!(result.array_values[&TermId(7)].stores[0].1, "new");
    assert_eq!(result.array_values[&TermId(7)].stores[1].1, "old");
}

#[test]
fn absent_empty_and_empty_spelling_options_remain_distinct() {
    let mut source = ArrayModel::default();
    source.array_values.insert(
        TermId(2),
        ArrayInterpretation {
            default: Some(String::new()),
            ..Default::default()
        },
    );
    source.store_chain_class_candidate = Some(HashMap::default());
    let first = healthy(|work| source.try_clone_with_budget(work)).unwrap();
    assert_eq!(first.array_values[&TermId(2)].default.as_deref(), Some(""));
    assert_eq!(first.store_chain_class_candidate, Some(HashMap::default()));
    source.store_chain_class_candidate = None;
    source.array_values.get_mut(&TermId(2)).unwrap().default = None;
    let second = healthy(|work| source.try_clone_with_budget(work)).unwrap();
    assert!(second.array_values[&TermId(2)].default.is_none());
    assert!(second.store_chain_class_candidate.is_none());
}

#[test]
fn concrete_duplicates_remain_authoritative_and_in_original_order() {
    let original = [
        (row("i", "new"), CellAuthority::Concrete),
        (row("i", "old"), CellAuthority::Concrete),
    ];
    let observations = [row("i", "different")];
    let result =
        healthy(|work| ArrayModel::try_from_indexed_rows(input(&original, &observations), work))
            .unwrap();
    assert_eq!(
        result.array_values[&TermId(7)].stores,
        vec![("i".into(), "new".into()), ("i".into(), "old".into())]
    );
    assert!(result.read_conflicted.is_empty());
}

#[test]
fn soft_flag_is_key_wide_and_second_disagreement_poison_is_first_only() {
    let original = [
        (row("i", "first"), CellAuthority::Concrete),
        (row("i", "older"), CellAuthority::Soft),
    ];
    let observations = [row("i", "one"), row("i", "two"), row("i", "repair")];
    let result =
        healthy(|work| ArrayModel::try_from_indexed_rows(input(&original, &observations), work))
            .unwrap();
    assert_eq!(
        result.array_values[&TermId(7)].stores,
        vec![("i".into(), "older".into())]
    );
    assert!(result.read_conflicted.contains(&TermId(7)));
    assert!(result.array_values[&TermId(7)].default.is_none());
}

#[test]
fn existing_default_is_copied_without_class_completion_or_inference() {
    let original = [(row("0", "one"), CellAuthority::Concrete)];
    let mut request = input(&original, &[]);
    request.default = Some("constant");
    let result = healthy(|work| ArrayModel::try_from_indexed_rows(request, work)).unwrap();
    assert_eq!(
        result.array_values[&TermId(7)].default.as_deref(),
        Some("constant")
    );
    assert!(result.store_chain_class_candidate.is_none());
}

#[test]
fn complete_utf8_names_values_and_boundary_windows_are_owned_exactly() {
    for length in [127, 128, 129] {
        let key = format!("{}é🙂", "k".repeat(length));
        let value = format!("{}🙂é", "v".repeat(length));
        let original = [(row(&key, &value), CellAuthority::Concrete)];
        let result =
            healthy(|work| ArrayModel::try_from_indexed_rows(input(&original, &[]), work)).unwrap();
        assert_eq!(result.array_values[&TermId(7)].stores, vec![(key, value)]);
    }
}

#[test]
fn recursive_sort_datatype_names_fields_and_all_scalar_variants_are_exact() {
    use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let named = Sort::Datatype(DatatypeSort {
        name: "D🙂".into(),
        constructors: vec![DatatypeConstructor {
            name: "C".into(),
            fields: vec![
                DatatypeField {
                    name: "f".into(),
                    sort: Sort::Seq(Box::new(Sort::FiniteDomain("F".into(), 9))),
                },
                DatatypeField {
                    name: "g".into(),
                    sort: Sort::TypeVar("T".into()),
                },
            ],
        }],
    });
    let scalar = [
        Sort::Bool,
        Sort::Int,
        Sort::Real,
        Sort::bitvec(1024),
        Sort::String,
        Sort::RegLan,
        Sort::Char,
        Sort::FloatingPoint(15, 113),
        Sort::Uninterpreted("U".into()),
        named,
    ];
    for element in scalar {
        let source = ArrayInterpretation {
            index_sort: Some(Sort::array(Sort::Int, element)),
            ..Default::default()
        };
        let result = healthy(|work| source.try_clone_with_budget(work)).unwrap();
        assert_eq!(result, source);
    }
}

#[test]
fn every_duplicate_and_both_candidate_maps_pay_separate_payload_copies() {
    let source = model();
    let (full_work, full_bytes, _) = costs(&source);
    let mut smaller = source.clone();
    smaller.store_chain_class_candidate = None;
    let (less_work, less_bytes, _) = costs(&smaller);
    assert!(full_work > less_work && full_bytes > less_bytes);
    smaller
        .array_values
        .get_mut(&TermId(7))
        .unwrap()
        .stores
        .pop();
    let (_, single_bytes, _) = costs(&smaller);
    assert!(less_bytes > single_bytes);
}

#[test]
fn native_legacy_agreeing_read_interpretation_is_copied_exactly() {
    use crate::{ArraySolver, BigInt, TermStore};
    let mut terms = TermStore::new();
    let array = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let one = terms.mk_int(BigInt::from(1));
    let index = terms.mk_var("i", Sort::Int);
    let first = terms.mk_select(array, one);
    let second = terms.mk_select(array, index);
    let mut solver = ArraySolver::new(&terms);
    let mut values = HashMap::default();
    for (term, text) in [(one, "1"), (index, "1"), (first, "10"), (second, "10")] {
        values.insert(term, text.to_string());
    }
    // This is the independent legacy oracle, NOT a controlled preparation claim.
    let legacy = solver.extract_model(&values);
    let rows: Vec<_> = solver
        .select_cache
        .iter()
        .map(|(&select, &(_, index))| row(values[&index].as_str(), values[&select].as_str()))
        .collect();
    let scalar = Sort::Int;
    let request = ArrayModelConstruction {
        array,
        default: None,
        index_sort: Some(&scalar),
        element_sort: Some(&scalar),
        original: &[],
        observations: &rows,
    };
    let result = healthy(|work| ArrayModel::try_from_indexed_rows(request, work)).unwrap();
    assert_eq!(
        result.array_values.get(&array),
        legacy.array_values.get(&array)
    );
    assert_eq!(result.read_conflicted, legacy.read_conflicted);
}

#[test]
fn native_legacy_conflicting_reads_remain_partial_and_conflicted() {
    use crate::{ArraySolver, BigInt, TermStore};
    let mut terms = TermStore::new();
    let array = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let one = terms.mk_int(BigInt::from(1));
    let index = terms.mk_var("i", Sort::Int);
    let first = terms.mk_select(array, one);
    let second = terms.mk_select(array, index);
    let mut solver = ArraySolver::new(&terms);
    let mut values = HashMap::default();
    for (term, text) in [(one, "1"), (index, "1"), (first, "10"), (second, "0")] {
        values.insert(term, text.to_string());
    }
    let legacy = solver.extract_model(&values);
    let rows: Vec<_> = solver
        .select_cache
        .iter()
        .map(|(&select, &(_, index))| row(values[&index].as_str(), values[&select].as_str()))
        .collect();
    let scalar = Sort::Int;
    let request = ArrayModelConstruction {
        array,
        default: None,
        index_sort: Some(&scalar),
        element_sort: Some(&scalar),
        original: &[],
        observations: &rows,
    };
    let result = healthy(|work| ArrayModel::try_from_indexed_rows(request, work)).unwrap();
    assert_eq!(
        result.array_values.get(&array),
        legacy.array_values.get(&array)
    );
    assert_eq!(result.read_conflicted, legacy.read_conflicted);
    assert!(result.array_values[&array].default.is_none());
}
