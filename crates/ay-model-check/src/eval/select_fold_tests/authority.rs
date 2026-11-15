// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn malformed_read_or_store_metadata_cannot_establish_a_known_miss() {
    for case in 0..7 {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::bitvec(64), Sort::Bool);
        let base = terms.mk_var("base", sort.clone());
        let key_sort = if case == 1 {
            Sort::Bool
        } else {
            Sort::bitvec(64)
        };
        let key = terms.mk_var("key", key_sort);
        let index_sort = if matches!(case, 3 | 4) {
            Sort::bitvec(32)
        } else {
            Sort::bitvec(64)
        };
        let index = terms.mk_var("index", index_sort);
        let value = if case == 2 {
            terms.mk_bitvec(BigInt::from(1), 64)
        } else {
            terms.mk_bool(true)
        };
        let store_sort = if case == 3 {
            Sort::array(Sort::bitvec(32), Sort::Bool)
        } else {
            sort
        };
        let updated = app(&mut terms, "store", &[base, key, value], store_sort);
        let result_sort = if case == 0 {
            Sort::bitvec(1)
        } else {
            Sort::Bool
        };
        let read = app(&mut terms, "select", &[updated, index], result_sort);
        let mut model = CountedModel::default();
        model.leaves.insert(
            key,
            if case == 1 {
                ModelValue::Bool(true)
            } else if case == 5 {
                ModelValue::bitvec(BigInt::from(1), 32)
            } else {
                bv(1)
            },
        );
        model.leaves.insert(
            index,
            if matches!(case, 3 | 4 | 6) {
                ModelValue::bitvec(BigInt::from(0), 32)
            } else {
                bv(0)
            },
        );
        model.reads.insert(read, ModelValue::Bool(true));
        let evaluator = Evaluator::new(&terms, &model);
        assert!(evaluator.eval(read, 0).is_err(), "malformed case {case}");
        assert!(evaluator.select_graph.borrow().is_empty());
        assert!(model.read_calls.borrow().is_empty());
    }
}

struct ProjectedModel {
    values: CountedModel,
    array: TermId,
    projection: Result<Option<usize>, crate::ProjectionLookupError>,
}

impl ModelView for ProjectedModel {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.values.leaf_value(term)
    }

    fn array_select_value(&self, term: TermId) -> Option<ModelValue> {
        self.values.array_select_value(term)
    }

    fn projection_argument(
        &self,
        term: TermId,
    ) -> Result<Option<usize>, crate::ProjectionLookupError> {
        if term == self.array {
            self.projection.clone()
        } else {
            Ok(None)
        }
    }
}

#[test]
fn checked_array_projection_precedes_syntactic_store_folding_and_read_pins() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::Bool);
    let base = terms.mk_var("base", sort.clone());
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let yes = terms.mk_bool(true);
    let updated = app(&mut terms, "store", &[base, zero, yes], sort);
    let read = app(&mut terms, "select", &[updated, zero], Sort::Bool);
    let mut values = CountedModel::default();
    values.leaves.insert(base, constant_array(false));
    values.reads.insert(read, ModelValue::Bool(true));
    let mut model = ProjectedModel {
        values,
        array: updated,
        projection: Ok(Some(0)),
    };
    assert_bool(Evaluator::new(&terms, &model).eval(read, 0), false);
    assert!(model.values.read_calls.borrow().is_empty());
    for projection in [
        Err(crate::ProjectionLookupError::inconsistent_model(
            "authored refusal",
        )),
        Ok(Some(99)),
        Ok(Some(1)),
    ] {
        model.projection = projection;
        let evaluator = Evaluator::new(&terms, &model);
        assert!(evaluator.eval(read, 0).is_err());
        assert!(evaluator.select_graph.borrow().is_empty());
        assert!(model.values.read_calls.borrow().is_empty());
    }
}
