// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ArrayValue, ProjectionLookupError};
use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort};

mod resources;

fn bv(value: u64) -> ModelValue {
    ModelValue::bitvec(BigInt::from(value), 64)
}

fn row(length: u64) -> ModelValue {
    ModelValue::Datatype {
        ctor: "Row".to_string(),
        args: vec![bv(length), ModelValue::Bool(true)],
    }
}

fn outer(array: ArrayValue) -> ModelValue {
    ModelValue::Datatype {
        ctor: "Outer".to_string(),
        args: vec![ModelValue::Array(Box::new(array))],
    }
}

fn rows() -> ArrayValue {
    ArrayValue {
        default: row(4),
        store: vec![
            (bv(1), row(2)),
            (bv(2), row(8)),
            (bv(2), row(7)),
            (bv(3), row(0)),
        ],
    }
}

struct Fixture {
    terms: TermStore,
    root: TermId,
    index: TermId,
    data: TermId,
    selected: TermId,
    length: TermId,
}

impl Fixture {
    fn new(selector: &str) -> Self {
        let mut terms = TermStore::new();
        let row = Sort::Datatype(DatatypeSort::new(
            "RowSort",
            vec![DatatypeConstructor::new(
                "Row",
                vec![
                    DatatypeField::new(selector, Sort::bitvec(64)),
                    DatatypeField::new("payload", Sort::Bool),
                ],
            )],
        ));
        let array = Sort::array(Sort::bitvec(64), row.clone());
        let container = Sort::Datatype(DatatypeSort::new(
            "OuterSort",
            vec![DatatypeConstructor::new(
                "Outer",
                vec![DatatypeField::new("data", array.clone())],
            )],
        ));
        let root = terms.mk_var("outer", container);
        let index = terms.mk_var("r", Sort::bitvec(64));
        let data = terms.mk_app(Symbol::named("data"), &[root], array);
        let selected = terms.mk_app(Symbol::named("select"), &[data, index], row);
        let length = terms.mk_app(Symbol::named(selector), &[selected], Sort::bitvec(64));
        Self {
            terms,
            root,
            index,
            data,
            selected,
            length,
        }
    }

    fn model(&self, index: u64) -> Values {
        Values {
            leaves: vec![(self.root, outer(rows())), (self.index, bv(index))],
            pins: vec![(self.selected, row(0)), (self.length, bv(0))],
            projection: None,
            pin_calls: Cell::new(0),
        }
    }
}

struct Values {
    leaves: Vec<(TermId, ModelValue)>,
    pins: Vec<(TermId, ModelValue)>,
    projection: Option<TermId>,
    pin_calls: Cell<usize>,
}

impl ModelView for Values {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.leaves
            .iter()
            .find(|(key, _)| *key == term)
            .map(|(_, value)| value.clone())
    }

    fn uf_app_value(&self, term: TermId) -> Option<ModelValue> {
        self.pin_calls.set(self.pin_calls.get() + 1);
        self.pins
            .iter()
            .find(|(key, _)| *key == term)
            .map(|(_, value)| value.clone())
    }

    fn array_select_value(&self, term: TermId) -> Option<ModelValue> {
        self.uf_app_value(term)
    }

    fn projection_argument(&self, term: TermId) -> Result<Option<usize>, ProjectionLookupError> {
        Ok((self.projection == Some(term)).then_some(0))
    }
}

fn bound(
    fixture: &Fixture,
    model: &Values,
    term: TermId,
    unavailable: &[(String, Sort)],
) -> Result<Option<BigInt>, QuantifierRejection> {
    let evaluator = Evaluator::new(&fixture.terms, model);
    evaluator.quantifier_state.nesting.set(1);
    let sort = Sort::bitvec(64);
    let mut analysis = analysis(&evaluator, &sort);
    analysis.unavailable = unavailable;
    analysis.endpoint(term)
}

#[test]
fn nested_endpoint_reads_actual_rows_and_ignores_conflicting_application_pins() {
    let fixture = Fixture::new("len");
    for (index, length) in [(0, 4), (1, 2), (2, 7), (3, 0), (4, 4)] {
        let model = fixture.model(index);
        assert_eq!(
            bound(&fixture, &model, fixture.length, &[]),
            Ok(Some(BigInt::from(length)))
        );
        assert_eq!(model.pin_calls.get(), 0);
    }
}

#[test]
fn nested_endpoint_unavailable_names_cover_receiver_index_and_wrong_sort_aliases() {
    let fixture = Fixture::new("len");
    let model = fixture.model(2);
    for (name, sort) in [
        ("r", Sort::bitvec(64)),
        ("r", Sort::Bool),
        ("outer", Sort::bitvec(64)),
    ] {
        let unavailable = [
            ("i".to_string(), Sort::bitvec(64)),
            (name.to_string(), sort),
        ];
        assert_eq!(
            bound(&fixture, &model, fixture.length, &unavailable),
            Ok(None)
        );
    }
    let unrelated = [
        ("i".to_string(), Sort::bitvec(64)),
        ("future".to_string(), Sort::bitvec(64)),
    ];
    assert_eq!(
        bound(&fixture, &model, fixture.length, &unrelated),
        Ok(Some(BigInt::from(7)))
    );
}

#[test]
fn nested_endpoint_authenticates_unselected_rows_keys_and_siblings() {
    let fixture = Fixture::new("len");
    let invalid_rows = [
        ModelValue::Datatype {
            ctor: "Foreign".to_string(),
            args: vec![bv(1), ModelValue::Bool(true)],
        },
        ModelValue::Datatype {
            ctor: "Row".to_string(),
            args: vec![bv(1)],
        },
        ModelValue::Datatype {
            ctor: "Row".to_string(),
            args: vec![bv(1), bv(0)],
        },
        ModelValue::Datatype {
            ctor: "Row".to_string(),
            args: vec![
                ModelValue::bitvec(BigInt::from(1), 32),
                ModelValue::Bool(true),
            ],
        },
    ];
    for invalid in invalid_rows {
        let mut model = fixture.model(1);
        let mut array = rows();
        array.store.push((bv(99), invalid));
        model.leaves[0].1 = outer(array);
        assert!(bound(&fixture, &model, fixture.length, &[]).is_err());
    }
    let mut model = fixture.model(1);
    let mut array = rows();
    array
        .store
        .push((ModelValue::bitvec(BigInt::from(99), 32), row(0)));
    model.leaves[0].1 = outer(array);
    assert!(bound(&fixture, &model, fixture.length, &[]).is_err());
}

#[test]
fn nested_endpoint_refuses_wrong_term_metadata_before_it_can_supply_a_bound() {
    let mut fixture = Fixture::new("len");
    let wrong_index = fixture.terms.mk_var("wrong_index", Sort::bitvec(32));
    let row_sort = fixture.terms.sort(fixture.selected).clone();
    let wrong_read = fixture.terms.mk_app(
        Symbol::named("select"),
        &[fixture.data, wrong_index],
        row_sort,
    );
    let wrong_length = fixture
        .terms
        .mk_app(Symbol::named("len"), &[wrong_read], Sort::bitvec(64));
    let forged_result = fixture.terms.mk_app(
        Symbol::named("select"),
        &[fixture.data, fixture.index],
        Sort::bitvec(64),
    );
    let false_selector = fixture.terms.mk_app(
        Symbol::named("payload"),
        &[fixture.selected],
        Sort::bitvec(64),
    );
    let mut model = fixture.model(1);
    model
        .leaves
        .push((wrong_index, ModelValue::bitvec(BigInt::from(1), 32)));
    for term in [wrong_length, forged_result, false_selector] {
        assert!(!matches!(bound(&fixture, &model, term, &[]), Ok(Some(_))));
    }
    assert_eq!(model.pin_calls.get(), 0);
}

#[test]
fn nested_endpoint_declines_opaque_receivers_and_unmaterialized_read_pins() {
    let mut fixture = Fixture::new("len");
    let array_sort = fixture.terms.sort(fixture.data).clone();
    let opaque = fixture
        .terms
        .mk_app(Symbol::named("opaque"), &[fixture.root], array_sort);
    let row_sort = fixture.terms.sort(fixture.selected).clone();
    let read = fixture
        .terms
        .mk_app(Symbol::named("select"), &[opaque, fixture.index], row_sort);
    let length = fixture
        .terms
        .mk_app(Symbol::named("len"), &[read], Sort::bitvec(64));
    let mut model = fixture.model(1);
    model
        .pins
        .push((opaque, ModelValue::Array(Box::new(rows()))));
    assert_eq!(bound(&fixture, &model, length, &[]), Ok(None));
    model.leaves.retain(|(term, _)| *term != fixture.root);
    assert_eq!(bound(&fixture, &model, fixture.length, &[]), Ok(None));
    assert_eq!(model.pin_calls.get(), 0);
}

#[test]
fn nested_endpoint_retains_projection_and_builtin_precedence() {
    let fixture = Fixture::new("len");
    for projected in [fixture.data, fixture.selected, fixture.length] {
        let mut model = fixture.model(1);
        model.projection = Some(projected);
        assert_eq!(bound(&fixture, &model, fixture.length, &[]), Ok(None));
    }
    let fixture = Fixture::new("bvnot");
    let model = fixture.model(1);
    // A same-spelled field cannot bypass the ordinary bitvector operator:
    // its datatype operand is a hard error, not an unavailable endpoint.
    assert_eq!(
        bound(&fixture, &model, fixture.length, &[]),
        Err(QuantifierRejection::UnevaluableBody(EvalError::Refused(
            "expected a bitvector operand".to_string(),
        )))
    );
    assert_eq!(model.pin_calls.get(), 0);
}
