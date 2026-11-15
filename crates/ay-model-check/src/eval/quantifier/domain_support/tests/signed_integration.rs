// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exercise support derivation through the real lexical quantifier evaluator.
//! Concrete array cells, not another support implementation, determine truth.

use super::*;
use crate::{ArrayValue, ModelView};
use ay_core::TermStore;

#[derive(Default)]
struct Model(Vec<(TermId, ModelValue)>);

impl ModelView for Model {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.0
            .iter()
            .find(|(key, _)| *key == term)
            .map(|(_, value)| value.clone())
    }
}

fn unsigned(value: i64, width: u32) -> BigInt {
    let value = BigInt::from(value);
    if value < BigInt::zero() {
        (BigInt::one() << width) + value
    } else {
        value
    }
}

fn literal(terms: &mut TermStore, value: i64, width: u32) -> TermId {
    terms.mk_bitvec(unsigned(value, width), width)
}

fn boolean(terms: &mut TermStore, name: &str, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::Bool)
}

#[derive(Clone, Copy)]
enum Form {
    Direct,
    Reversed,
    Negated,
}

fn range(
    terms: &mut TermStore,
    variable: TermId,
    lower: TermId,
    upper: TermId,
    form: Form,
) -> TermId {
    let (lower, upper) = match form {
        Form::Direct => (
            boolean(terms, "bvsge", &[variable, lower]),
            boolean(terms, "bvslt", &[variable, upper]),
        ),
        Form::Reversed => (
            boolean(terms, "bvsle", &[lower, variable]),
            boolean(terms, "bvsgt", &[upper, variable]),
        ),
        Form::Negated => {
            let below = boolean(terms, "bvslt", &[variable, lower]);
            let above = boolean(terms, "bvsge", &[variable, upper]);
            (terms.mk_not_raw(below), boolean(terms, "not", &[above]))
        }
    };
    boolean(terms, "and", &[lower, upper])
}

fn array_model(array: TermId, width: u32, bad: Option<i64>) -> Model {
    let store = bad
        .into_iter()
        .map(|index| {
            (
                ModelValue::bitvec(unsigned(index, width), width),
                ModelValue::Bool(false),
            )
        })
        .collect();
    Model(vec![(
        array,
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Bool(true),
            store,
        })),
    )])
}

fn quantified_read(
    terms: &mut TermStore,
    variable: TermId,
    guard: TermId,
    width: u32,
) -> (TermId, TermId, TermId) {
    let array = terms.mk_var("cells", Sort::array(Sort::bitvec(width), Sort::Bool));
    let read = boolean(terms, "select", &[array, variable]);
    let all = boolean(terms, "=>", &[guard, read]);
    let missing = terms.mk_not_raw(read);
    let some = boolean(terms, "and", &[guard, missing]);
    let binders = vec![("i".to_owned(), Sort::bitvec(width))];
    (
        array,
        terms.mk_forall(binders.clone(), all),
        terms.mk_exists(binders, some),
    )
}

fn value(terms: &TermStore, model: &Model, term: TermId) -> Result<bool, String> {
    match Evaluator::new(terms, model)
        .eval(term, 0)
        .map_err(|error| error.to_string())?
    {
        ModelValue::Bool(value) => Ok(value),
        other => panic!("quantified result is not Boolean: {other:?}"),
    }
}

#[test]
fn signed_bv64_negative_and_cross_zero_ranges_visit_every_relevant_cell() {
    for (lower, upper) in [(-3, -1), (-2, 2)] {
        for form in [Form::Direct, Form::Reversed, Form::Negated] {
            let mut terms = TermStore::new();
            let i = terms.mk_var("i", Sort::bitvec(64));
            let lo = literal(&mut terms, lower, 64);
            let hi = literal(&mut terms, upper, 64);
            let guard = range(&mut terms, i, lo, hi, form);
            let (array, all, some) = quantified_read(&mut terms, i, guard, 64);
            let good = array_model(array, 64, None);
            assert_eq!(value(&terms, &good, all), Ok(true));
            assert_eq!(value(&terms, &good, some), Ok(false));
            // Each negative/positive member is independently the ONLY bad cell.
            // A dropped negative segment therefore changes both polarities.
            for missing in lower..upper {
                let bad = array_model(array, 64, Some(missing));
                assert_eq!(value(&terms, &bad, all), Ok(false));
                assert_eq!(value(&terms, &bad, some), Ok(true));
            }
            for excluded in [lower - 1, upper] {
                let outside = array_model(array, 64, Some(excluded));
                assert_eq!(value(&terms, &outside, all), Ok(true));
                assert_eq!(value(&terms, &outside, some), Ok(false));
            }
        }
    }
}

#[test]
fn signed_and_unsigned_guards_intersect_in_the_same_unsigned_carrier() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(64));
    let lower = literal(&mut terms, -2, 64);
    let upper = literal(&mut terms, 2, 64);
    let signed = range(&mut terms, i, lower, upper, Form::Direct);
    let sign_bit = terms.mk_bitvec(BigInt::one() << 63, 64);
    let negative = boolean(&mut terms, "bvuge", &[i, sign_bit]);
    let guard = boolean(&mut terms, "and", &[signed, negative]);
    let (array, all, some) = quantified_read(&mut terms, i, guard, 64);
    for bad in [-2, -1, 0, 1] {
        let model = array_model(array, 64, Some(bad));
        assert_eq!(value(&terms, &model, all), Ok(bad >= 0));
        assert_eq!(value(&terms, &model, some), Ok(bad < 0));
    }
}

#[test]
fn signed_bv128_keeps_negative_values_exact_and_bv129_stays_refused() {
    for width in [128, 129] {
        let mut terms = TermStore::new();
        let i = terms.mk_var("i", Sort::bitvec(width));
        let lower = literal(&mut terms, -2, width);
        let upper = literal(&mut terms, 0, width);
        let guard = range(&mut terms, i, lower, upper, Form::Reversed);
        let (array, all, some) = quantified_read(&mut terms, i, guard, width);
        let model = array_model(array, width, Some(-1));
        if width == 128 {
            assert_eq!(value(&terms, &model, all), Ok(false));
            assert_eq!(value(&terms, &model, some), Ok(true));
        } else {
            assert!(value(&terms, &model, all).is_err());
            assert!(value(&terms, &model, some).is_err());
        }
    }
}

#[test]
fn signed_endpoint_uses_live_outer_lexical_value_and_restores_it_afterward() {
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(64);
    let outer = terms.mk_var("outer", sort.clone());
    let i = terms.mk_var("i", sort.clone());
    let lower = literal(&mut terms, -3, 64);
    let zero = literal(&mut terms, 0, 64);
    let inner_guard = range(&mut terms, i, outer, zero, Form::Direct);
    let at_outer = boolean(&mut terms, "=", &[i, outer]);
    let inner = boolean(&mut terms, "and", &[inner_guard, at_outer]);
    let inner = terms.mk_exists(vec![("i".into(), sort.clone())], inner);
    let outer_guard = range(&mut terms, outer, lower, zero, Form::Direct);
    let body = boolean(&mut terms, "=>", &[outer_guard, inner]);
    let all = terms.mk_forall(vec![("outer".into(), sort)], body);
    let ambient = ModelValue::bitvec(BigInt::from(42), 64);
    let model = Model(vec![(outer, ambient.clone())]);
    let evaluator = Evaluator::new(&terms, &model);
    assert!(matches!(evaluator.eval(all, 0), Ok(ModelValue::Bool(true))));
    assert!(evaluator.local_bindings.borrow().is_empty());
    assert!(matches!(evaluator.eval(outer, 0),
        Ok(ModelValue::BitVec { width: 64, value }) if value == BigInt::from(42)));
}

#[test]
fn signed_ranges_do_not_adopt_current_future_unused_or_wrong_sort_bound_pins() {
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(64);
    let i = terms.mk_var("i", sort.clone());
    let alias = terms.mk_fresh_named_var("i", sort.clone());
    let future = terms.mk_var("j", sort.clone());
    let unknown = terms.mk_var("unknown", sort.clone());
    let zero = literal(&mut terms, 0, 64);
    let maximum = (BigInt::one() << 63) - BigInt::one();
    let pin = ModelValue::bitvec(maximum, 64);
    let alias_expr = terms.mk_app(Symbol::named("bvadd"), &[alias, zero], sort.clone());
    let no = terms.mk_bool(false);
    let mut cases = Vec::new();
    for endpoint in [alias_expr, future, unknown] {
        let guard = boolean(&mut terms, "bvsgt", &[i, endpoint]);
        let body = boolean(&mut terms, "=>", &[guard, no]);
        let binders = if endpoint == future {
            vec![("i".into(), sort.clone()), ("j".into(), sort.clone())]
        } else {
            vec![("i".into(), sort.clone())]
        };
        cases.push(terms.mk_forall(binders, body));
    }
    let guard = boolean(&mut terms, "bvsgt", &[i, zero]);
    let body = boolean(&mut terms, "=>", &[guard, no]);
    cases.push(terms.mk_forall(vec![("unused".into(), sort)], body));
    let model = Model(vec![
        (i, pin.clone()),
        (alias, pin.clone()),
        (future, pin.clone()),
        (unknown, ModelValue::Bool(false)),
    ]);
    for term in &cases {
        assert!(value(&terms, &model, *term).is_err());
    }
    // Even an existing outer term binding cannot authenticate an endpoint
    // shadowed by the inner quantifier's current lexical name.
    let evaluator = Evaluator::new(&terms, &model);
    assert!(evaluator
        .eval_with_binding(alias, pin, cases[0], 0)
        .is_err());
    assert!(evaluator.local_bindings.borrow().is_empty());
}

#[test]
fn signed_resource_refusal_never_becomes_an_empty_successful_domain() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(64));
    let lower = literal(&mut terms, -2, 64);
    let upper = literal(&mut terms, 0, 64);
    let guard = range(&mut terms, i, lower, upper, Form::Direct);
    let empty = range(&mut terms, i, lower, lower, Form::Direct);
    let (array, all, some) = quantified_read(&mut terms, i, guard, 64);
    let (_, vacuous, empty_exists) = quantified_read(&mut terms, i, empty, 64);
    let model = array_model(array, 64, None);
    for term in [all, some, vacuous, empty_exists] {
        let evaluator = Evaluator::new(&terms, &model);
        evaluator.quantifier_state.work_left.set(0);
        assert!(evaluator.eval(term, 0).is_err());
        assert!(evaluator.eval(term, 0).is_err());
        assert!(evaluator.local_bindings.borrow().is_empty());
    }
    let short = Evaluator::new(&terms, &model);
    short.quantifier_state.assignments_left.set(1);
    assert!(short.eval(all, 0).is_err());
    assert!(short.local_bindings.borrow().is_empty());
    assert_eq!(value(&terms, &model, all), Ok(true));
    assert_eq!(value(&terms, &model, some), Ok(false));
    assert_eq!(value(&terms, &model, vacuous), Ok(true));
    assert_eq!(value(&terms, &model, empty_exists), Ok(false));
}

#[test]
fn signed_joint_ranges_preserve_negative_tuples_and_share_plan_byte_budget() {
    let mut terms = TermStore::new();
    let sort = Sort::bitvec(64);
    let i = terms.mk_var("i", sort.clone());
    let j = terms.mk_var("j", sort.clone());
    let lower = literal(&mut terms, -1, 64);
    let zero = literal(&mut terms, 0, 64);
    let first = range(&mut terms, i, lower, zero, Form::Direct);
    let second = range(&mut terms, j, lower, zero, Form::Reversed);
    let guard = boolean(&mut terms, "and", &[first, second]);
    let array = terms.mk_var("cells", Sort::array(sort.clone(), Sort::Bool));
    let read = boolean(&mut terms, "select", &[array, j]);
    let body = boolean(&mut terms, "=>", &[guard, read]);
    let all = terms.mk_forall(vec![("i".into(), sort.clone()), ("j".into(), sort)], body);
    let model = array_model(array, 64, None);
    let fresh = Evaluator::new(&terms, &model);
    assert!(matches!(fresh.eval(all, 0), Ok(ModelValue::Bool(true))));
    assert_eq!(
        value(&terms, &array_model(array, 64, Some(-1)), all),
        Ok(false)
    );
    let exhausted = Evaluator::new(&terms, &model);
    exhausted.quantifier_state.plan_bytes_left.set(0);
    assert!(exhausted.eval(all, 0).is_err());
    assert!(exhausted.eval(all, 0).is_err());
    assert!(exhausted.local_bindings.borrow().is_empty());
    assert_eq!(value(&terms, &model, all), Ok(true));
}
