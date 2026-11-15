// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::Evaluator;
use crate::{ModelValue, ModelView};
use ay_core::{Sort, Symbol, TermId, TermStore};

#[test]
fn fp_to_real_reuses_original_plan_storage_and_refusal_does_not_renew_it() {
    struct Values(ModelValue);
    impl ModelView for Values {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            Some(self.0.clone())
        }
    }
    let mut terms = TermStore::new();
    let sb = 1 << 20;
    let sort = Sort::FloatingPoint(8, sb);
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort);
    let a = terms.mk_app(Symbol::named("fp.to_real"), vec![x], Sort::Real);
    let b = terms.mk_app(Symbol::named("fp.to_real"), vec![y], Sort::Real);
    let model =
        Values(ModelValue::floating_point_exact(false, 127u8.into(), 0u8.into(), 8, sb).unwrap());
    let storage = crate::fp_exact::real_plan(&model.0).unwrap().storage;
    let evaluator = Evaluator::new(&terms, &model);
    // Narrow the actual existing cumulative plan ledger, as the previous
    // retained quantifier plans in this same evaluator would do.
    evaluator.quantifier_state.plan_bytes_left.set(storage);
    assert!(matches!(evaluator.eval(a, 0), Ok(ModelValue::Real(_))));
    assert!(matches!(
        evaluator.eval(b, 0),
        Err(crate::eval::EvalError::Resource {
            kind: crate::eval::EvalResource::Work,
            ..
        })
    ));
    assert!(
        evaluator.eval(b, 0).is_err(),
        "the original refusal cannot mint another plan allowance"
    );
    assert!(matches!(
        Evaluator::new(&terms, &model).eval(b, 0),
        Ok(ModelValue::Real(_))
    ));
}
