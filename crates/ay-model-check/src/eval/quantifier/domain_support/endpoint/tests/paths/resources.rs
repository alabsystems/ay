// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn nested_endpoint_spends_one_shared_work_budget_and_fresh_attempt_retries() {
    let fixture = Fixture::new("len");
    let model = fixture.model(2);
    let sort = Sort::bitvec(64);
    let evaluator = Evaluator::new(&fixture.terms, &model);
    evaluator.quantifier_state.nesting.set(1);
    let before = evaluator.quantifier_state.work_left.get();
    assert_eq!(
        analysis(&evaluator, &sort).endpoint(fixture.length),
        Ok(Some(BigInt::from(7)))
    );
    let used = before - evaluator.quantifier_state.work_left.get();
    assert!(used > 1 && used < 10_000);
    for budget in [0, used - 1, used] {
        let evaluator = Evaluator::new(&fixture.terms, &model);
        evaluator.quantifier_state.nesting.set(1);
        evaluator.quantifier_state.work_left.set(budget);
        let result = analysis(&evaluator, &sort).endpoint(fixture.length);
        if budget == used {
            assert_eq!(result, Ok(Some(BigInt::from(7))));
        } else {
            assert!(result.is_err());
        }
        assert_eq!(evaluator.quantifier_state.work_left.get(), 0);
        assert!(analysis(&evaluator, &sort)
            .endpoint(fixture.length)
            .is_err());
    }
    assert_eq!(
        bound(&fixture, &model, fixture.length, &[]),
        Ok(Some(BigInt::from(7)))
    );
}

#[test]
fn nested_endpoint_received_values_have_depth_limb_and_shared_copy_work_caps() {
    let terms = TermStore::new();
    let model = EmptyModel;
    let sort = Sort::bitvec(64);
    let evaluator = Evaluator::new(&terms, &model);
    evaluator.quantifier_state.nesting.set(1);
    let analysis = analysis(&evaluator, &sort);
    assert!(analysis
        .endpoint_value_work(&bv(0), MAX_SUPPORT_DEPTH)
        .is_ok());
    assert_eq!(
        analysis.endpoint_value_work(&bv(0), MAX_SUPPORT_DEPTH + 1),
        Err(QuantifierRejection::NestingLimit)
    );
    let huge = ModelValue::Int(BigInt::from(1) << 4096usize);
    assert_eq!(
        analysis.endpoint_value_work(&huge, 0),
        Err(QuantifierRejection::EvaluationBudget)
    );
    let wide = ModelValue::Array(Box::new(ArrayValue {
        default: bv(0),
        store: (0..64).map(|index| (bv(index), bv(index))).collect(),
    }));
    evaluator.quantifier_state.work_left.set(100);
    assert!(analysis.endpoint_value_work(&wide, 0).is_err());
    assert_eq!(evaluator.quantifier_state.work_left.get(), 0);
    assert!(analysis.endpoint_value_work(&bv(0), 0).is_err());
}
