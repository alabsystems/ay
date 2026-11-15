// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A universal equality of two array reads outside one index.
//!
//! Over Int, two finite-store arrays agree off the exceptional index iff their
//! defaults and all remaining effective overrides agree. Compare the existing
//! array values after removing every write at that index, including shadowed
//! writes. No solver result or sampled index certifies the universal.

use super::{EvalError, EvalResource, EvalResult, Evaluator, ModelValue, Sort, TermId};
use ay_core::{TermData, TermStore};

struct Frame {
    left: TermId,
    right: TermId,
    exception: TermId,
}

fn app<'a>(terms: &'a TermStore, term: TermId, head: &str) -> Option<&'a [TermId]> {
    match terms.get(term) {
        TermData::App(ay_core::Symbol::Named(symbol), args)
            if symbol == head && !terms.is_declared_function(head) =>
        {
            Some(args)
        }
        _ => None,
    }
}

fn frame(terms: &TermStore, bindings: &[(String, Sort)], body: TermId) -> Option<Frame> {
    let [(binder, Sort::Int)] = bindings else {
        return None;
    };
    if terms.sort(body) != &Sort::Bool {
        return None;
    }
    let [first, second] = app(terms, body, "or")? else {
        return None;
    };
    let is_binder = |term| {
        terms.sort(term) == &Sort::Int
            && matches!(terms.get(term), TermData::Var(name, _) if name == binder)
    };
    let independent_leaf = |term| match terms.get(term) {
        TermData::Var(name, _) => name != binder,
        TermData::Const(_) => true,
        _ => false,
    };
    let read = |term| {
        let [array, index] = app(terms, term, "select")? else {
            return None;
        };
        let Sort::Array(sort) = terms.sort(*array) else {
            return None;
        };
        (is_binder(*index)
            && independent_leaf(*array)
            && sort.index_sort == Sort::Int
            && terms.sort(term) == &sort.element_sort)
            .then_some(*array)
    };
    for (guard, equality) in [(*first, *second), (*second, *first)] {
        if terms.sort(guard) != &Sort::Bool || terms.sort(equality) != &Sort::Bool {
            continue;
        }
        let (Some([i, k]), Some([lhs, rhs])) = (app(terms, guard, "="), app(terms, equality, "="))
        else {
            continue;
        };
        let exception = if is_binder(*i) {
            *k
        } else if is_binder(*k) {
            *i
        } else {
            continue;
        };
        if terms.sort(exception) != &Sort::Int || !independent_leaf(exception) {
            continue;
        }
        if let (Some(left), Some(right)) = (read(*lhs), read(*rhs)) {
            if terms.sort(left) == terms.sort(right) {
                return Some(Frame {
                    left,
                    right,
                    exception,
                });
            }
        }
    }
    None
}

/// Whether this exact root is a single-exception integer-index array frame.
#[must_use]
pub fn recognizes_int_array_frame(terms: &TermStore, root: TermId) -> bool {
    match terms.get(root) {
        TermData::Forall(bindings, body, _) => frame(terms, bindings, *body).is_some(),
        _ => false,
    }
}

pub(super) fn evaluate(
    evaluator: &Evaluator<'_>,
    bindings: &[(String, Sort)],
    body: TermId,
    depth: usize,
) -> EvalResult<Option<bool>> {
    let Some(Frame {
        left,
        right,
        exception,
    }) = frame(evaluator.terms, bindings, body)
    else {
        return Ok(None);
    };
    let Sort::Array(sort) = evaluator.terms.sort(left) else {
        return Err("array frame operand is not an array".into());
    };
    let ModelValue::Int(exception) = evaluator.eval(exception, depth + 1)? else {
        return Err("array frame exception is not an integer".into());
    };
    let mut left = evaluator.eval_array_value(left, depth + 1)?;
    let mut right = evaluator.eval_array_value(right, depth + 1)?;
    for array in [&mut left, &mut right] {
        for (key, _) in &array.store {
            let ModelValue::Int(key) = key else {
                return Err("array frame index is not an integer".into());
            };
            let work = usize::try_from(key.bits().max(exception.bits()).div_ceil(8))
                .ok()
                .and_then(|bytes| bytes.checked_add(1))
                .ok_or_else(|| {
                    EvalError::resource(EvalResource::Work, "array frame key work overflow")
                })?;
            evaluator.charge_quantifier_work(work)?;
            evaluator.admit_evaluation(work, 0)?;
        }
        array
            .store
            .retain(|(key, _)| !matches!(key, ModelValue::Int(key) if key == &exception));
    }
    let mut comparison_work = 0;
    evaluator
        .array_eq_at_sort(&left, &right, sort, &mut comparison_work)
        .map(Some)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{evaluate_term, ArrayValue, EvalOutcome, ModelView};
    use ay_core::Symbol;
    use num_rational::BigRational;

    struct FrameModel {
        left: (TermId, ModelValue),
        right: (TermId, ModelValue),
    }

    impl ModelView for FrameModel {
        fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
            [&self.left, &self.right]
                .into_iter()
                .find_map(|(id, value)| (*id == term).then(|| value.clone()))
        }

        fn uf_app_value(&self, _: TermId) -> Option<ModelValue> {
            Some(ModelValue::Bool(false))
        }
    }

    fn array(default: i64, writes: &[(i64, i64)]) -> ModelValue {
        let real = |value: i64| ModelValue::Real(BigRational::from_integer(value.into()));
        ModelValue::Array(Box::new(ArrayValue {
            default: real(default),
            store: writes
                .iter()
                .map(|&(i, v)| (ModelValue::Int(i.into()), real(v)))
                .collect(),
        }))
    }

    #[test]
    fn declared_connective_cannot_certify_an_integer_array_frame() {
        let mut terms = TermStore::new();
        let index = terms.mk_var("i", Sort::Int);
        let a = terms.mk_var("a", Sort::array(Sort::Int, Sort::Real));
        let b = terms.mk_var("b", Sort::array(Sort::Int, Sort::Real));
        let zero = terms.mk_int(0.into());
        let left = terms.mk_app_structural(Symbol::named("select"), &[a, index], Sort::Real);
        let right = terms.mk_app_structural(Symbol::named("select"), &[b, index], Sort::Real);
        let same = terms.mk_app_structural(Symbol::named("="), &[left, right], Sort::Bool);
        let guard = terms.mk_app_structural(Symbol::named("="), &[index, zero], Sort::Bool);
        let body = terms.mk_app_structural(Symbol::named("or"), &[guard, same], Sort::Bool);
        let root = terms.mk_forall(vec![("i".into(), Sort::Int)], body);
        let model = FrameModel {
            left: (a, array(0, &[])),
            right: (b, array(0, &[])),
        };
        terms.register_declared_function("or");
        assert!(!matches!(
            crate::confirm_model(&terms, &model, &[root]),
            crate::GateVerdict::ConfirmedSat
        ));
    }

    #[test]
    fn frame_checks_every_effective_write_and_the_uncovered_default() {
        let mut terms = TermStore::new();
        let index = terms.mk_var("i", Sort::Int);
        let array_sort = Sort::array(Sort::Int, Sort::Real);
        let a = terms.mk_var("a", array_sort.clone());
        let b = terms.mk_var("b", array_sort);
        let k = terms.mk_int(3.into());
        let a_read = terms.mk_app(Symbol::named("select"), [a, index], Sort::Real);
        let b_read = terms.mk_app(Symbol::named("select"), [b, index], Sort::Real);
        let same = terms.mk_app(Symbol::named("="), [a_read, b_read], Sort::Bool);
        let except = terms.mk_app(Symbol::named("="), [index, k], Sort::Bool);
        let body = terms.mk_app(Symbol::named("or"), [except, same], Sort::Bool);
        let root = terms.mk_forall(vec![("i".into(), Sort::Int)], body);
        let mut model = FrameModel {
            left: (a, array(0, &[(3, 4), (8, 1)])),
            right: (b, array(0, &[(3, 5), (3, 9), (8, 7), (8, 1)])),
        };
        assert!(matches!(
            evaluate_term(&terms, &model, root),
            EvalOutcome::Value(ModelValue::Bool(true))
        ));
        model.right.1 = array(0, &[(3, 9), (8, 2)]);
        assert!(matches!(
            evaluate_term(&terms, &model, root),
            EvalOutcome::Value(ModelValue::Bool(false))
        ));
        model.right.1 = array(1, &[(3, 9), (8, 1)]);
        assert!(matches!(
            evaluate_term(&terms, &model, root),
            EvalOutcome::Value(ModelValue::Bool(false))
        ));
    }
}
