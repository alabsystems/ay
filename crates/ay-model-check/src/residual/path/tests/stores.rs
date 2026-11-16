// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact parser coordinates and budgets only; no SAT evidence is constructed.

use super::*;
use num_bigint::BigInt;

struct Fixture {
    root: TermId,
    index: TermId,
    miss: TermId,
    value: TermId,
    array_sort: Sort,
    element_sort: Sort,
}

impl Fixture {
    fn new(terms: &mut TermStore) -> Self {
        let element_sort = record("Cell", "flag", Sort::Bool);
        let array_sort = Sort::array(Sort::Int, element_sort.clone());
        Self {
            root: terms.mk_var("root", array_sort.clone()),
            index: terms.mk_int(BigInt::from(0)),
            miss: terms.mk_int(BigInt::from(1)),
            value: terms.mk_var("uncommitted_cell", element_sort.clone()),
            array_sort,
            element_sort,
        }
    }

    fn store(&self, terms: &mut TermStore, base: TermId, key: TermId) -> TermId {
        terms.mk_app(
            Symbol::named("store"),
            [base, key, self.value],
            self.array_sort.clone(),
        )
    }

    fn read(&self, terms: &mut TermStore, array: TermId) -> [TermId; 2] {
        let select = terms.mk_app(
            Symbol::named("select"),
            [array, self.index],
            self.element_sort.clone(),
        );
        let flag = terms.mk_app(Symbol::named("flag"), [select], Sort::Bool);
        [select, flag]
    }
}

#[test]
fn outer_misses_preserve_original_read_index_and_exact_receiver_edges() {
    let mut terms = TermStore::new();
    let fixture = Fixture::new(&mut terms);
    let first = fixture.store(&mut terms, fixture.root, fixture.miss);
    let second_key = terms.mk_int(BigInt::from(2));
    let second = fixture.store(&mut terms, first, second_key);
    let [select, flag] = fixture.read(&mut terms, second);
    let size = terms.len();
    let model = Empty;
    let evaluator = Evaluator::new(&terms, &model);
    let resolve = |_: &str| None;
    let parsed = classifier(&terms, &model, &evaluator, &resolve)
        .parse_read_with_stores(flag)
        .expect("two independently proved misses");
    assert_eq!(parsed.array, fixture.root);
    assert_eq!(parsed.index, fixture.index);
    assert!(matches!(parsed.slot, Slot::Field(name) if name == "flag"));
    assert_eq!(
        parsed.store_edges,
        [(select, second), (second, first), (first, fixture.root)]
    );
    assert_eq!(terms.len(), size);
    assert!(matches!(
        evaluator.evaluate(fixture.value),
        EvalOutcome::Unevaluable(_)
    ));
}

#[test]
fn inner_miss_preserves_field_index_path_without_resolving_stored_value() {
    let mut terms = TermStore::new();
    let inner_sort = Sort::array(Sort::Int, Sort::Bool);
    let element = record("WithArray", "data", inner_sort.clone());
    let root = terms.mk_var("root", Sort::array(Sort::Int, element.clone()));
    let outer_index = terms.mk_int(BigInt::from(9));
    let outer = terms.mk_app(Symbol::named("select"), [root, outer_index], element);
    let data = terms.mk_app(Symbol::named("data"), [outer], inner_sort.clone());
    let stored_key = terms.mk_int(BigInt::from(1));
    let stored_value = terms.mk_var("uncommitted_bool", Sort::Bool);
    let store = terms.mk_app(
        Symbol::named("store"),
        [data, stored_key, stored_value],
        inner_sort,
    );
    let key = terms.mk_int(BigInt::from(-3));
    let select = terms.mk_app(Symbol::named("select"), [store, key], Sort::Bool);
    let model = Empty;
    let evaluator = Evaluator::new(&terms, &model);
    let resolve = |_: &str| None;
    let parsed = classifier(&terms, &model, &evaluator, &resolve)
        .parse_read_with_stores(select)
        .expect("typed inner miss");
    assert_eq!(parsed.array, root);
    assert_eq!(parsed.index, outer_index);
    assert_eq!(parsed.store_edges, [(select, store), (store, data)]);
    let Slot::Access(path) = parsed.slot else {
        panic!("inner index retained")
    };
    assert!(matches!(&path[0], AccessStep::Field(name) if name == "data"));
    assert!(
        matches!(&path[1], AccessStep::Index(ModelValue::Int(value)) if *value == BigInt::from(-3))
    );
}

#[test]
fn equal_or_unresolved_store_keys_and_unresolved_read_keys_do_not_peel() {
    let mut terms = TermStore::new();
    let fixture = Fixture::new(&mut terms);
    let unknown = terms.mk_var("unknown_index", Sort::Int);
    let hit = fixture.store(&mut terms, fixture.root, fixture.index);
    let unresolved = fixture.store(&mut terms, fixture.root, unknown);
    let missed = fixture.store(&mut terms, fixture.root, fixture.miss);
    let hit = fixture.read(&mut terms, hit)[0];
    let unresolved = fixture.read(&mut terms, unresolved)[0];
    let unknown_read = terms.mk_app(
        Symbol::named("select"),
        [missed, unknown],
        fixture.element_sort.clone(),
    );
    let model = Empty;
    let evaluator = Evaluator::new(&terms, &model);
    let resolve = |_: &str| None;
    for read in [hit, unresolved, unknown_read] {
        assert!(classifier(&terms, &model, &evaluator, &resolve)
            .parse_free_read(read)
            .is_none());
    }
}

#[test]
fn malformed_store_metadata_and_indexed_builtin_spellings_refuse() {
    let mut terms = TermStore::new();
    let fixture = Fixture::new(&mut terms);
    let wrong = terms.mk_bool(false);
    let variants = [
        terms.mk_app(
            Symbol::named("store"),
            [fixture.root, wrong, fixture.value],
            fixture.array_sort.clone(),
        ),
        terms.mk_app(
            Symbol::named("store"),
            [fixture.root, fixture.miss, wrong],
            fixture.array_sort.clone(),
        ),
        terms.mk_app(
            Symbol::named("store"),
            [wrong, fixture.miss, fixture.value],
            fixture.array_sort.clone(),
        ),
        terms.mk_app(
            Symbol::indexed("store", vec![0]),
            [fixture.root, fixture.miss, fixture.value],
            fixture.array_sort.clone(),
        ),
        terms.mk_app(
            Symbol::named("store"),
            [fixture.root, fixture.miss],
            fixture.array_sort.clone(),
        ),
        terms.mk_app(
            Symbol::named("store"),
            [fixture.root, fixture.miss, fixture.value],
            Sort::Bool,
        ),
    ];
    let reads = variants.map(|store| fixture.read(&mut terms, store)[0]);
    let valid_store = fixture.store(&mut terms, fixture.root, fixture.miss);
    let indexed_read = terms.mk_app(
        Symbol::indexed("select", vec![0]),
        [valid_store, fixture.index],
        fixture.element_sort.clone(),
    );
    let model = Empty;
    let evaluator = Evaluator::new(&terms, &model);
    let resolve = |_: &str| None;
    for read in reads.into_iter().chain([indexed_read]) {
        assert!(classifier(&terms, &model, &evaluator, &resolve)
            .parse_free_read(read)
            .is_none());
    }
}

#[test]
fn projection_on_any_peeled_store_is_terminal_before_syntax_localization() {
    struct Projected(TermId);
    impl ModelView for Projected {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            None
        }
        fn projection_argument(
            &self,
            term: TermId,
        ) -> Result<Option<usize>, crate::ProjectionLookupError> {
            Ok((term == self.0).then_some(0))
        }
    }
    let mut terms = TermStore::new();
    let fixture = Fixture::new(&mut terms);
    let first = fixture.store(&mut terms, fixture.root, fixture.miss);
    let second = fixture.store(&mut terms, first, fixture.miss);
    let read = fixture.read(&mut terms, second)[0];
    let resolve = |_: &str| None;
    for projected in [read, second, first] {
        let model = Projected(projected);
        let evaluator = Evaluator::new(&terms, &model);
        assert!(classifier(&terms, &model, &evaluator, &resolve)
            .parse_free_read(read)
            .is_none());
    }
}

#[test]
fn store_steps_and_field_steps_share_the_existing_complete_path_depth() {
    for count in [MAX_CLASSIFY_DEPTH - 1, MAX_CLASSIFY_DEPTH] {
        let mut terms = TermStore::new();
        let fixture = Fixture::new(&mut terms);
        let mut array = fixture.root;
        for _ in 0..count {
            array = fixture.store(&mut terms, array, fixture.miss);
        }
        let flag = fixture.read(&mut terms, array)[1];
        let model = Empty;
        let evaluator = Evaluator::new(&terms, &model);
        let resolve = |_: &str| None;
        let mut classifier = classifier(&terms, &model, &evaluator, &resolve);
        let parsed = classifier.parse_read_with_stores(flag);
        assert_eq!(parsed.is_some(), count == MAX_CLASSIFY_DEPTH - 1);
        if let Some(parsed) = parsed {
            assert_eq!(parsed.store_edges.len(), count + 1);
        }
    }
}

#[test]
fn parser_and_edge_union_have_exact_shared_work_boundaries_and_no_global_node_blessing() {
    let mut terms = TermStore::new();
    let fixture = Fixture::new(&mut terms);
    let store = fixture.store(&mut terms, fixture.root, fixture.miss);
    let [select, flag] = fixture.read(&mut terms, store);
    let model = Empty;
    let evaluator = Evaluator::new(&terms, &model);
    let resolve = |_: &str| None;
    let mut measured = classifier(&terms, &model, &evaluator, &resolve);
    let parsed = measured.parse_read_with_stores(flag).unwrap();
    let cost = measured.classify_work;
    let payload = measured.witness_value_work;
    for extra in [0, 1] {
        let mut limited = classifier(&terms, &model, &evaluator, &resolve);
        limited.classify_work = MAX_CLASSIFY_WORK - cost + extra;
        limited.witness_value_work = MAX_WITNESS_VALUE_WORK - payload;
        assert_eq!(limited.parse_free_read(flag).is_some(), extra == 0);
        if extra == 1 {
            assert!(limited.classify_work > MAX_CLASSIFY_WORK);
            assert!(limited.parse_free_read(flag).is_none());
        }
    }
    let union_cost = parsed.store_edges.len() * size_of::<(TermId, TermId)>() * 2;
    let mut exact = classifier(&terms, &model, &evaluator, &resolve);
    exact.classify_work = MAX_CLASSIFY_WORK - union_cost;
    let mut edges = StoreEdges::default();
    edges.admit(parsed.store_edges, &mut exact).unwrap();
    assert_eq!(exact.classify_work, MAX_CLASSIFY_WORK);
    assert!(edges.permits(select, store, 0));
    assert!(edges.permits(store, fixture.root, 0));
    assert!(!edges.permits(flag, store, 0));
    assert!(!edges.permits(select, store, 1));
    let mut short = classifier(&terms, &model, &evaluator, &resolve);
    short.classify_work = MAX_CLASSIFY_WORK - union_cost + 1;
    assert!(StoreEdges::default()
        .admit(vec![(select, store), (store, fixture.root)], &mut short)
        .is_none());
    assert!(short.classify_work > MAX_CLASSIFY_WORK);
}

#[test]
fn undecidable_compound_key_equality_is_not_a_store_miss() {
    struct Keys([(TermId, ModelValue); 2]);
    impl ModelView for Keys {
        fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
            self.0
                .iter()
                .find(|(candidate, _)| *candidate == term)
                .map(|(_, value)| value.clone())
        }
    }
    let mut terms = TermStore::new();
    let key_sort = Sort::array(Sort::Bool, Sort::Bool);
    let cell_sort = record("Cell", "flag", Sort::Bool);
    let array_sort = Sort::array(key_sort.clone(), cell_sort.clone());
    let root = terms.mk_var("root", array_sort.clone());
    let keys = [
        terms.mk_var("left", key_sort.clone()),
        terms.mk_var("right", key_sort),
    ];
    let value = terms.mk_var("uncommitted", cell_sort.clone());
    let store = terms.mk_app(Symbol::named("store"), [root, keys[0], value], array_sort);
    let read = terms.mk_app(Symbol::named("select"), [store, keys[1]], cell_sort);
    let array = |default| {
        ModelValue::Array(Box::new(crate::ArrayValue {
            default: ModelValue::Bool(default),
            store: Vec::new(),
        }))
    };
    let model = Keys([(keys[0], array(false)), (keys[1], array(true))]);
    assert!(crate::value_eq(&model.0[0].1, &model.0[1].1).is_err());
    let evaluator = Evaluator::new(&terms, &model);
    let resolve = |_: &str| None;
    assert!(classifier(&terms, &model, &evaluator, &resolve)
        .parse_free_read(read)
        .is_none());
}
