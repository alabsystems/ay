// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Complete ArrayModel leaves used by exact constructor arguments.

use ay_core::{ArraySort, Sort, TermId};
use ay_model_check::{ArrayValue, ModelValue};

use super::super::{charge_work, Model, TypedArrayParseBudget};
use crate::executor::Executor;

impl Executor {
    pub(super) fn complete_array_model_leaf_shape(
        &self,
        model: &Model,
        source: TermId,
        sort: &Sort,
    ) -> bool {
        let Sort::Array(array_sort) = sort else {
            return false;
        };
        let Some(arrays) = model.array_model.as_ref() else {
            return false;
        };
        let Some(interp) = arrays.array_values.get(&source) else {
            return false;
        };
        !arrays.read_conflicted.contains(&source)
            && interp
                .index_sort
                .as_ref()
                .is_none_or(|found| found == &array_sort.index_sort)
            && interp
                .element_sort
                .as_ref()
                .is_none_or(|found| found == &array_sort.element_sort)
            && interp.default.is_some()
    }

    pub(super) fn exact_array_model_leaf_value(
        &self,
        model: &Model,
        source: TermId,
        sort: &ArraySort,
        work: &mut usize,
        parse_budget: &mut TypedArrayParseBudget,
    ) -> Option<ModelValue> {
        let arrays = model.array_model.as_ref()?;
        let interp = arrays.array_values.get(&source)?;
        if arrays.read_conflicted.contains(&source)
            || interp
                .index_sort
                .as_ref()
                .is_some_and(|found| found != &sort.index_sort)
            || interp
                .element_sort
                .as_ref()
                .is_some_and(|found| found != &sort.element_sort)
            || !charge_work(work, interp.stores.len().saturating_add(1))
        {
            return None;
        }
        let default =
            self.typed_scalar_text(interp.default.as_deref()?, &sort.element_sort, parse_budget)?;
        let mut stores = Vec::with_capacity(interp.stores.len());
        for (key, value) in interp.stores.iter().rev() {
            stores.push((
                self.typed_scalar_text(key, &sort.index_sort, parse_budget)?,
                self.typed_scalar_text(value, &sort.element_sort, parse_budget)?,
            ));
        }
        Some(ModelValue::Array(Box::new(ArrayValue {
            default,
            store: stores,
        })))
    }
}
