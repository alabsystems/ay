// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn flat_store_bool_bv_endpoints_preserve_all_legacy_fields() {
    let end = Instant::now() + Duration::from_secs(20);
    let flag = Arc::new(AtomicBool::new(false));
    let original = owner(100_000_000, 256_000_000, end, &flag);
    for (index, cell) in [
        (Sort::Bool, Sort::Bool),
        (Sort::bitvec(64), Sort::Bool),
        (Sort::Bool, Sort::bitvec(1)),
        (Sort::bitvec(64), Sort::bitvec(8)),
        (Sort::bitvec(128), Sort::bitvec(128)),
    ] {
        let fixture = store_fixture(index, cell);
        let mut source = prepare(&fixture.terms, &fixture.assignments);
        let expected = legacy(&mut source, &fixture.roots);
        let parents = source.uf.parent.clone();
        let actual = original
            .with_work(|work| {
                source.try_extract_prepared_bv_model_from_roots_with_budget(&fixture.roots, work)
            })
            .unwrap();
        compare(&actual, &expected);
        assert!(!actual.function_tables["store"].is_empty());
        assert_eq!(source.uf.parent, parents);
        assert!(Instant::now() < end);
    }
}

#[test]
fn store_table_first_equal_arguments_keep_exact_legacy_origin() {
    let fixture = store_fixture(Sort::bitvec(64), Sort::bitvec(8));
    let mut source = prepare(&fixture.terms, &fixture.assignments);
    let expected = legacy(&mut source, &fixture.roots);
    let actual = measured(&source, &fixture.roots, u64::MAX, usize::MAX)
        .0
        .unwrap();
    compare(&actual, &expected);
    let origins = &actual.function_table_terms["store"];
    assert!(origins.contains(&fixture.stores[0]));
    assert!(!origins.contains(&fixture.stores[1]));
    assert!(origins.contains(&fixture.stores[2]));
    assert!(actual.function_tables["store"]
        .iter()
        .all(|(args, _)| args.len() == 3));
}

#[test]
fn newest_store_and_array_alias_keep_full_literal_read_pins() {
    let fixture = store_fixture(Sort::bitvec(64), Sort::bitvec(128));
    let mut source = prepare(&fixture.terms, &fixture.assignments);
    let expected = legacy(&mut source, &fixture.roots);
    let actual = measured(&source, &fixture.roots, u64::MAX, usize::MAX)
        .0
        .unwrap();
    compare(&actual, &expected);
    assert_eq!(
        actual.term_values[&fixture.reads[0]],
        "#xffffffffffffffffffffffffffffffff"
    );
    assert_eq!(
        actual.term_values[&fixture.reads[1]],
        "#x00000000000000000000000000000000"
    );
    assert_eq!(
        actual.term_values[&fixture.reads[2]],
        actual.term_values[&fixture.reads[1]]
    );
    assert_eq!(actual.func_app_const_terms, expected.func_app_const_terms);
}

#[test]
fn scoped_store_uses_whole_class_literals_and_global_tracked_metadata() {
    let fixture = store_fixture(Sort::bitvec(64), Sort::bitvec(8));
    let mut source = prepare(&fixture.terms, &fixture.assignments);
    let roots = [fixture.stores[1]];
    let expected = legacy(&mut source, &roots);
    let actual = measured(&source, &roots, u64::MAX, usize::MAX).0.unwrap();
    compare(&actual, &expected);
    assert_eq!(actual.term_values[&fixture.index], "#xffffffffffffffff");
    assert_eq!(actual.term_values[&fixture.written], "#xff");
    assert_eq!(
        actual.function_table_terms["store"],
        vec![fixture.stores[1]]
    );
    assert!(!actual.term_values.contains_key(&fixture.reads[0]));
    assert!(actual.func_app_const_terms.contains_key(&fixture.reads[0]));
}

#[test]
fn repeated_store_roots_preserve_tables_and_pay_each_inventory_occurrence() {
    let fixture = store_fixture(Sort::bitvec(64), Sort::bitvec(8));
    let source = prepare(&fixture.terms, &fixture.assignments);
    let mut roots = fixture.roots.clone();
    roots.extend_from_slice(&fixture.roots);
    let once = measured(&source, &fixture.roots, u64::MAX, usize::MAX);
    let repeated = measured(&source, &roots, u64::MAX, usize::MAX);
    compare(&once.0.unwrap(), &repeated.0.unwrap());
    assert!(repeated.1 > once.1);
    assert_eq!(repeated.2, once.2);
}
