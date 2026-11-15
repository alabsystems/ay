// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn prepared_array_bv_values_tables_and_tracked_maps_match_legacy_all_widths() {
    let end = Instant::now() + Duration::from_secs(20);
    let flag = Arc::new(AtomicBool::new(false));
    let original = owner(100_000_000, 256_000_000, end, &flag);
    for width in [1, 7, 8, 64, 128] {
        let (terms, roots, assignments) = fixture(width, false);
        let mut source = prepare(&terms, &assignments);
        source.scope_model_to_roots(&roots);
        let expected = source.extract_model();
        let before = source.uf.parent.clone();
        let actual = original
            .with_work(|work| {
                source.try_extract_prepared_bv_model_from_roots_with_budget(&roots, work)
            })
            .unwrap();
        compare(&actual, &expected);
        assert!(!actual.function_tables.is_empty());
        assert!(!actual.func_app_const_terms.is_empty());
        assert_eq!(source.uf.parent, before);
        assert_eq!(
            actual.term_values.get(&roots[2]),
            expected.term_values.get(&roots[2])
        );
        assert!(Instant::now() < end);
    }
}

#[test]
fn boolean_select_predicates_and_placeholder_arguments_match_legacy() {
    let (terms, roots, assignments) = fixture(8, true);
    let mut source = prepare(&terms, &assignments);
    source.scope_model_to_roots(&roots);
    let expected = source.extract_model();
    let actual = measured(&source, &roots, u64::MAX, usize::MAX).0.unwrap();
    compare(&actual, &expected);
    assert!(actual.function_tables["select"]
        .iter()
        .all(|(_, result)| result == "true"));
    assert!(actual.function_tables["const-array"]
        .iter()
        .any(|(args, _)| args.iter().any(|v| v.starts_with("@?"))));
}

#[test]
fn out_of_scope_hard_class_constant_remains_authoritative() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("value", Sort::bitvec(8));
    let constant = terms.mk_bitvec(171u8.into(), 8);
    let equal = terms.mk_app(Symbol::named("="), [value, constant], Sort::Bool);
    let mut source = prepare(&terms, &[(equal, true)]);
    source.scope_model_to_roots(&[value]);
    let expected = source.extract_model();
    let actual = measured(&source, &[value], u64::MAX, usize::MAX).0.unwrap();
    compare(&actual, &expected);
    assert_eq!(actual.term_values[&value], "#xab");
    assert!(!actual.term_values.contains_key(&constant));
}

#[test]
fn tiny_domain_completion_preserves_disequal_reuse_and_class_order() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(1));
    let b = terms.mk_var("b", Sort::bitvec(1));
    let c = terms.mk_var("c", Sort::bitvec(1));
    let unequal = terms.mk_app(Symbol::named("="), [a, c], Sort::Bool);
    let mut source = prepare(&terms, &[(unequal, false)]);
    let roots = [a, b, c, unequal];
    source.scope_model_to_roots(&roots);
    let expected = source.extract_model();
    let actual = measured(&source, &roots, u64::MAX, usize::MAX).0.unwrap();
    compare(&actual, &expected);
    assert_ne!(actual.term_values[&a], actual.term_values[&c]);
    assert_eq!(actual.term_values[&b], actual.term_values[&c]);
}

#[test]
fn duplicate_roots_and_table_argument_rows_keep_exact_first_origins() {
    let (terms, roots, assignments) = fixture(8, false);
    let mut source = prepare(&terms, &assignments);
    let mut repeated = roots.clone();
    repeated.extend_from_slice(&roots);
    source.scope_model_to_roots(&repeated);
    let expected = source.extract_model();
    let once = measured(&source, &roots, u64::MAX, usize::MAX);
    let twice = measured(&source, &repeated, u64::MAX, usize::MAX);
    compare(&twice.0.unwrap(), &expected);
    assert!(twice.1 > once.1);
    assert_eq!(twice.2, once.2);
    assert_eq!(expected.function_table_terms["select"], vec![roots[2]]);
}
