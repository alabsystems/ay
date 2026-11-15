// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parser-only tests. These do not construct or assert SAT authority.

use super::*;
use num_bigint::BigInt;

struct Fixture {
    root: TermId,
    outer_index: TermId,
    data: TermId,
    key: TermId,
    read: TermId,
}

impl Fixture {
    fn new(terms: &mut TermStore) -> Self {
        let data_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(40));
        let vector = record("Vector", "data", data_sort.clone());
        let outer = record("Outer", "lits", vector.clone());
        let root = terms.mk_var("array", Sort::array(Sort::bitvec(64), outer.clone()));
        let outer_index = terms.mk_bitvec(BigInt::from(9), 64);
        let row = terms.mk_app(Symbol::named("select"), [root, outer_index], outer);
        let vector = terms.mk_app(Symbol::named("lits"), [row], vector);
        let data = terms.mk_app(Symbol::named("data"), [vector], data_sort);
        let left = terms.mk_bitvec(BigInt::from(63), 64);
        let right = terms.mk_bitvec(BigInt::from(1), 64);
        let key = terms.mk_app(Symbol::named("bvadd"), [left, right], Sort::bitvec(64));
        let read = terms.mk_app(Symbol::named("select"), [data, key], Sort::bitvec(40));
        Self {
            root,
            outer_index,
            data,
            key,
            read,
        }
    }
}

#[test]
fn mixed_path_keeps_outer_index_and_evaluated_inner_index_independent() {
    let mut terms = TermStore::new();
    let fixture = Fixture::new(&mut terms);
    let model = Empty;
    let evaluator = Evaluator::new(&terms, &model);
    let resolve = |_: &str| None;
    let mut classifier = classifier(&terms, &model, &evaluator, &resolve);
    let (root, index, slot) = classifier
        .parse_free_read(fixture.read)
        .expect("typed mixed path");
    assert_eq!(root, fixture.root);
    assert_eq!(index, fixture.outer_index);
    let Slot::Access(path) = slot else {
        panic!("inner index needs mixed storage")
    };
    assert_eq!(path.len(), 3);
    assert!(matches!(&path[0], AccessStep::Field(name) if name == "lits"));
    assert!(matches!(&path[1], AccessStep::Field(name) if name == "data"));
    assert!(
        matches!(&path[2], AccessStep::Index(ModelValue::BitVec { width: 64, value }) if *value == BigInt::from(64))
    );
    assert_eq!(classifier.witness_value_work, 9); // one value plus eight payload bytes
}

#[test]
fn selectors_after_inner_select_and_multiple_inner_indices_keep_path_order() {
    let mut terms = TermStore::new();
    let terminal = record("Terminal", "flag", Sort::Bool);
    let inner_array = Sort::array(Sort::Int, terminal.clone());
    let middle = record("Middle", "inner", inner_array.clone());
    let array = Sort::array(Sort::Bool, middle.clone());
    let outer = record("Outer", "data", array.clone());
    let root = terms.mk_var("root", Sort::array(Sort::Int, outer.clone()));
    let zero = terms.mk_int(BigInt::from(0));
    let row = terms.mk_app(Symbol::named("select"), [root, zero], outer);
    let data = terms.mk_app(Symbol::named("data"), [row], array);
    let yes = terms.mk_bool(true);
    let middle = terms.mk_app(Symbol::named("select"), [data, yes], middle);
    let inner = terms.mk_app(Symbol::named("inner"), [middle], inner_array);
    let negative = terms.mk_int(BigInt::from(-7));
    let terminal = terms.mk_app(Symbol::named("select"), [inner, negative], terminal);
    let flag = terms.mk_app(Symbol::named("flag"), [terminal], Sort::Bool);
    let model = Empty;
    let evaluator = Evaluator::new(&terms, &model);
    let resolve = |_: &str| None;
    let (_, _, Slot::Access(path)) = classifier(&terms, &model, &evaluator, &resolve)
        .parse_free_read(flag)
        .expect("alternating exact selectors and indices")
    else {
        panic!("mixed path expected")
    };
    assert_eq!(path.len(), 5);
    assert!(matches!(&path[0], AccessStep::Field(name) if name == "data"));
    assert!(matches!(
        &path[1],
        AccessStep::Index(ModelValue::Bool(true))
    ));
    assert!(matches!(&path[2], AccessStep::Field(name) if name == "inner"));
    assert!(
        matches!(&path[3], AccessStep::Index(ModelValue::Int(value)) if *value == BigInt::from(-7))
    );
    assert!(matches!(&path[4], AccessStep::Field(name) if name == "flag"));
}

#[test]
fn mixed_path_rejects_mistyped_or_unresolved_indices_and_results() {
    let mut terms = TermStore::new();
    let fixture = Fixture::new(&mut terms);
    let wrong_key = terms.mk_bool(true);
    let unknown_key = terms.mk_var("unknown", Sort::bitvec(64));
    let wrong_array = terms.mk_var("not_array", Sort::Bool);
    let invalid = [
        terms.mk_app(
            Symbol::named("select"),
            [fixture.data, wrong_key],
            Sort::bitvec(40),
        ),
        terms.mk_app(
            Symbol::named("select"),
            [fixture.data, unknown_key],
            Sort::bitvec(40),
        ),
        terms.mk_app(
            Symbol::named("select"),
            [fixture.data, fixture.key],
            Sort::bitvec(39),
        ),
        terms.mk_app(
            Symbol::named("select"),
            [wrong_array, fixture.key],
            Sort::bitvec(40),
        ),
    ];
    let model = Empty;
    let evaluator = Evaluator::new(&terms, &model);
    let resolve = |_: &str| None;
    for invalid in invalid {
        assert!(classifier(&terms, &model, &evaluator, &resolve)
            .parse_free_read(invalid)
            .is_none());
    }
    assert!(classifier(&terms, &model, &evaluator, &resolve)
        .parse_free_read(fixture.read)
        .is_some());
}

#[test]
fn mixed_path_does_not_rewrite_store_constant_or_opaque_array_receivers() {
    let mut terms = TermStore::new();
    let fixture = Fixture::new(&mut terms);
    let array_sort = terms.sort(fixture.data).clone();
    let value = terms.mk_bitvec(BigInt::from(7), 40);
    let store = terms.mk_app(
        Symbol::named("store"),
        [fixture.data, fixture.key, value],
        array_sort.clone(),
    );
    let constant = terms.mk_app(Symbol::named("const-array"), [value], array_sort.clone());
    let opaque = terms.mk_app(Symbol::named("unknown_array"), [fixture.data], array_sort);
    let reads = [store, constant, opaque].map(|array| {
        terms.mk_app(
            Symbol::named("select"),
            [array, fixture.key],
            Sort::bitvec(40),
        )
    });
    let model = Empty;
    let evaluator = Evaluator::new(&terms, &model);
    let resolve = |_: &str| None;
    for read in reads {
        assert!(classifier(&terms, &model, &evaluator, &resolve)
            .parse_free_read(read)
            .is_none());
    }
}

#[test]
fn mixed_parser_shares_exact_work_and_payload_limits_with_sticky_refusal() {
    let mut terms = TermStore::new();
    let fixture = Fixture::new(&mut terms);
    let model = Empty;
    let evaluator = Evaluator::new(&terms, &model);
    let resolve = |_: &str| None;
    let mut measured = classifier(&terms, &model, &evaluator, &resolve);
    assert!(measured.parse_free_read(fixture.read).is_some());
    let cost = measured.classify_work;
    let payload = measured.witness_value_work;
    assert!((1..MAX_CLASSIFY_WORK).contains(&cost));
    assert_eq!(payload, 9);
    let mut exact = classifier(&terms, &model, &evaluator, &resolve);
    exact.classify_work = MAX_CLASSIFY_WORK - cost;
    exact.witness_value_work = MAX_WITNESS_VALUE_WORK - payload;
    assert!(exact.parse_free_read(fixture.read).is_some());
    assert_eq!(exact.classify_work, MAX_CLASSIFY_WORK);
    assert_eq!(exact.witness_value_work, MAX_WITNESS_VALUE_WORK);
    for (work, value) in [
        (MAX_CLASSIFY_WORK - cost + 1, 0),
        (0, MAX_WITNESS_VALUE_WORK - payload + 1),
    ] {
        let mut short = classifier(&terms, &model, &evaluator, &resolve);
        short.classify_work = work;
        short.witness_value_work = value;
        assert!(short.parse_free_read(fixture.read).is_none());
        assert!(short.classify_work > MAX_CLASSIFY_WORK);
        assert!(short.parse_free_read(fixture.read).is_none());
    }
    assert!(classifier(&terms, &model, &evaluator, &resolve)
        .parse_free_read(fixture.read)
        .is_some());
}

#[test]
fn promotion_moves_existing_field_payloads_and_preserves_legacy_variants() {
    let mut path = ReversePath::default();
    path.push_field("leaf", &mut |_| true)
        .expect("legacy field");
    let ReversePath::Fields(fields) = &path else {
        panic!("legacy storage")
    };
    let pointer = fields[0].as_ptr();
    path.push_index(ModelValue::Bool(true), &mut |_| true)
        .expect("promote");
    let Slot::Access(steps) = path.finish().expect("path") else {
        panic!("mixed storage")
    };
    assert!(matches!(
        &steps[0],
        AccessStep::Index(ModelValue::Bool(true))
    ));
    assert!(matches!(&steps[1], AccessStep::Field(name) if name.as_ptr() == pointer));
    assert!(matches!(ReversePath::default().finish(), Some(Slot::Whole)));
    let mut path = ReversePath::default();
    path.push_field("only", &mut |_| true).expect("field");
    assert!(matches!(path.finish(), Some(Slot::Field(name)) if name == "only"));
}

#[test]
fn captured_inner_key_stays_stable_after_a_congruent_conflicting_uf_pin() {
    struct Keys {
        arguments: [TermId; 2],
        applications: [TermId; 2],
    }
    impl ModelView for Keys {
        fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
            self.arguments
                .contains(&term)
                .then(|| ModelValue::bitvec(BigInt::from(3), 64))
        }

        fn uf_app_value(&self, term: TermId) -> Option<ModelValue> {
            let index = self
                .applications
                .iter()
                .position(|candidate| *candidate == term)?;
            Some(ModelValue::bitvec(BigInt::from(64 + index), 64))
        }
    }
    let mut terms = TermStore::new();
    let fixture = Fixture::new(&mut terms);
    let arguments = [
        terms.mk_var("x", Sort::bitvec(64)),
        terms.mk_var("y", Sort::bitvec(64)),
    ];
    let applications = arguments
        .map(|argument| terms.mk_app(Symbol::named("key_function"), [argument], Sort::bitvec(64)));
    let reads = applications.map(|key| {
        terms.mk_app(
            Symbol::named("select"),
            [fixture.data, key],
            Sort::bitvec(40),
        )
    });
    let model = Keys {
        arguments,
        applications,
    };
    assert!(
        matches!(model.uf_app_value(applications[1]), Some(ModelValue::BitVec { value, .. }) if value == BigInt::from(65))
    );
    let evaluator = Evaluator::new(&terms, &model);
    let resolve = |_: &str| None;
    let mut classifier = classifier(&terms, &model, &evaluator, &resolve);
    for read in [reads[0], reads[1], reads[0]] {
        let (_, _, Slot::Access(path)) = classifier.parse_free_read(read).expect("stable key")
        else {
            panic!("mixed path expected")
        };
        assert!(
            matches!(path.last(), Some(AccessStep::Index(ModelValue::BitVec { width: 64, value })) if *value == BigInt::from(64))
        );
    }
    // The second raw pin cannot overwrite the first value-keyed interpretation.
    assert!(
        matches!(evaluator.evaluate(applications[1]), EvalOutcome::Value(ModelValue::BitVec { value, .. }) if value == BigInt::from(64))
    );
}

#[test]
fn failed_or_trial_rolls_back_entries_but_not_inner_key_acquisition_work() {
    let mut terms = TermStore::new();
    let fixture = Fixture::new(&mut terms);
    let value = terms.mk_bitvec(BigInt::from(7), 40);
    let requirement = terms.mk_app(Symbol::named("="), [fixture.read, value], Sort::Bool);
    let unsupported = terms.mk_var("unknown_condition", Sort::Bool);
    let failed = terms.mk_app(Symbol::named("and"), [requirement, unsupported], Sort::Bool);
    let disjunction = terms.mk_app(Symbol::named("or"), [failed, requirement], Sort::Bool);
    let model = Empty;
    let evaluator = Evaluator::new(&terms, &model);
    let resolve = |_: &str| None;
    let mut metadata_work = 0usize;
    for term in [fixture.data, fixture.key, fixture.read] {
        assert!(metadata::sort_work(terms.sort(term), 0, &mut |n| {
            metadata_work += n;
            true
        }));
    }
    let mut key_only = classifier(&terms, &model, &evaluator, &resolve);
    assert!(key_only
        .inner_index(fixture.read, fixture.data, fixture.key)
        .is_some());
    assert_eq!(key_only.witness_value_work, 9);
    assert_eq!(key_only.classify_work, metadata_work + 9);

    let mut rejected = classifier(&terms, &model, &evaluator, &resolve);
    assert!(!rejected.classify(failed, 0));
    assert_eq!(rejected.entries.len(), 1); // retained only inside the rejected trial
    let mut direct = classifier(&terms, &model, &evaluator, &resolve);
    assert!(direct.classify(requirement, 0));
    let mut retried = classifier(&terms, &model, &evaluator, &resolve);
    assert!(retried.classify(disjunction, 0));
    assert_eq!(retried.entries.len(), 1);
    assert_eq!(retried.witness_value_work, direct.witness_value_work);
    assert!(retried.classify_work >= rejected.classify_work + direct.classify_work);
}
