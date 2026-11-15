// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn actual_bv_read_and_default_pins_keep_cached_and_rebuilt_whole_model_data() {
    let end = Instant::now() + Duration::from_secs(20);
    for width in [8, 64, 128] {
        let fixture = Pinned::new(Sort::bitvec(width));
        let values = fixture.values();
        for cached in [false, true] {
            let mut source = fixture.solver();
            if cached {
                source.build_equiv_class_cache();
            }
            let before = (source.eq_adj_version, source.equiv_class_cache_version);
            let original = owner(end, 1_000_000, 128 << 20);
            let output = run(&source, &values, &original);
            assert_eq!(
                (source.eq_adj_version, source.equiv_class_cache_version),
                before
            );
            let expected = source.extract_model(&values);
            same(&output, &expected);
            assert_eq!(
                output.array_values[&fixture.base].default.as_deref(),
                Some("9")
            );
            assert_eq!(
                output.array_values[&fixture.constant].default.as_deref(),
                Some("9")
            );
            assert_eq!(
                output.array_values.keys().copied().collect::<Vec<_>>(),
                expected.array_values.keys().copied().collect::<Vec<_>>()
            );
            assert!(fixture
                .reads
                .iter()
                .chain(&fixture.defaults)
                .all(|t| { !output.array_values.contains_key(t) }));
            drop(output);
            original.check().unwrap();
        }
    }
}

#[test]
fn registered_boolean_pins_preserve_original_defaults_stores_and_conflicts() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Pinned::new(Sort::Bool);
    let values = fixture.values();
    for cached in [false, true] {
        let mut source = fixture.solver();
        if cached {
            source.build_equiv_class_cache();
        }
        let original = owner(end, 1_000_000, 128 << 20);
        let output = run(&source, &values, &original);
        same(&output, &source.extract_model(&values));
        assert_eq!(
            output.array_values[&fixture.alias].default.as_deref(),
            Some("true")
        );
        assert_eq!(
            output.array_values[&fixture.chain].stores[0],
            ("0".into(), "true".into())
        );
        assert!(output.read_conflicted.is_empty());
        drop(output);
        original.check().unwrap();
    }
}

#[test]
fn complete_class_plan_retains_every_scalar_and_exact_legacy_lifo_member_order() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Pinned::new(Sort::bitvec(8));
    for cached in [false, true] {
        let mut source = fixture.solver();
        if cached {
            source.build_equiv_class_cache();
        }
        let original = owner(end, 1_000_000, 128 << 20);
        let plan = original
            .with_work(|work| {
                shape::prepared(&source, work)?;
                classes::prepare_reconciled(&source, work)
            })
            .unwrap();
        source.build_equiv_class_cache();
        let mut start = 0;
        assert_eq!(plan.ends.len(), source.equiv_classes.len());
        for (class, &end) in source.equiv_classes.iter().zip(&plan.ends) {
            assert_eq!(&plan.members[start..end], class.as_slice());
            start = end;
        }
        assert_eq!(start, plan.members.len());
        assert!(fixture
            .reads
            .iter()
            .chain(&fixture.defaults)
            .all(|t| { plan.members.contains(t) }));
        original.with_work(|work| plan.finish(work)).unwrap();
        original.check().unwrap();
    }
}

#[test]
fn scalar_only_true_components_never_invent_array_interpretations() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let a = terms.mk_var("scalar-only-a", Sort::bitvec(8));
    let b = terms.mk_var("scalar-only-b", Sort::bitvec(8));
    let equality = terms.mk_app(Symbol::named("="), [a, b], Sort::Bool);
    let mut source = ArraySolver::new(&terms);
    source.register_atom(equality);
    source.assert_literal(equality, true);
    source.populate_caches();
    source.rebuild_assign_indices();
    let values = HashMap::default();
    let original = owner(end, 1_000_000, 128 << 20);
    let output = run(&source, &values, &original);
    same(&output, &source.extract_model(&values));
    assert!(output.array_values.is_empty());
    assert!(output.read_conflicted.is_empty());
    assert!(output.store_chain_class_candidate.is_none());
    drop(output);
    original.check().unwrap();
}

#[test]
fn original_store_free_api_still_refuses_genuine_scalar_components() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let base = terms.mk_var(
        "old-api-array",
        Sort::array(Sort::bitvec(64), Sort::bitvec(8)),
    );
    let index = terms.mk_var("old-api-index", Sort::bitvec(64));
    let selected = read(&mut terms, base, index, &Sort::bitvec(8));
    let value = terms.mk_bitvec(9u8.into(), 8);
    let equality = terms.mk_app(Symbol::named("="), [selected, value], Sort::Bool);
    let mut source = ArraySolver::new(&terms);
    source.register_atom(equality);
    source.assert_literal(equality, true);
    source.populate_caches();
    source.rebuild_assign_indices();
    let mut values = HashMap::default();
    for (term, text) in [(index, "0"), (selected, "9"), (value, "9")] {
        values.insert(term, text.into());
    }
    let original = owner(end, 1_000_000, 128 << 20);
    let output = run(&source, &values, &original);
    same(&output, &source.extract_model(&values));
    drop(output);
    original.check().unwrap();
    let separate = owner(end, 1_000_000, 128 << 20);
    assert!(matches!(
        separate.with_work(|work| { source.try_extract_prepared_model_with_budget(&values, work) }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
}

#[test]
fn genuinely_registered_scalar_scope_keeps_cached_and_rebuilt_whole_model_parity() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Pinned::new(Sort::bitvec(8));
    let values = fixture.values();
    for cached in [false, true] {
        let mut source = ArraySolver::new(&fixture.terms);
        source.enable_registered_atom_scope(true);
        for &root in &fixture.roots {
            source.register_atom(root);
            source.assert_literal(root, true);
        }
        source.populate_caches();
        source.rebuild_assign_indices();
        if cached {
            source.build_equiv_class_cache();
        }
        let original = owner(end, 1_000_000, 128 << 20);
        let output = run(&source, &values, &original);
        same(&output, &source.extract_model(&values));
        assert!(output.array_values.contains_key(&fixture.constant));
        drop(output);
        original.check().unwrap();
    }
}
