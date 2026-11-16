// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn cancellation_and_exhausted_copy_budget_never_return_partial_obligations() {
    let source = source("fill");
    let token = CancellationToken::new();
    let model = model(&source, &control(&token));
    let stopped = control(&token);
    token.cancel();
    assert!(prepare(&source, &model, 0, &stopped).is_none());
    token.reset();
    assert!(prepare(&source, &model, 0, &stopped).is_none());
    let exhausted = control(&token);
    assert!(exhausted.bytes(usize::MAX).is_none());
    assert!(validate(&source, &model, &exhausted).is_none());
    assert!(prepare(&source, &model, 0, &exhausted).is_none());
    let fresh = control(&token);
    validate(&source, &model, &fresh).unwrap();
    assert!(prepare(&source, &model, 0, &fresh).is_some());
}

#[test]
fn original_deadline_is_checked_before_preparation_and_discharge() {
    let source = source("fill");
    let token = CancellationToken::new();
    let model = model(&source, &control(&token));
    let expired = SourceControl::new(
        Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("fixture instant supports a one-second offset"),
        &token,
    );
    assert!(prepare(&source, &model, 0, &expired).is_none());
    let prepared = prepare(&source, &model, 0, &control(&token)).unwrap();
    // This returns at its first control check; it cannot launch an SMT solve.
    assert!(!discharge(prepared, 2, &expired));
    assert!(prepare(&source, &model, 0, &control(&token)).is_some());
}

#[test]
fn repeated_formals_precharge_large_actual_name_fanout_before_substitution() {
    let source = source(&"fill".repeat(2_048));
    let token = CancellationToken::new();
    let live = control(&token);
    let mut model = model(&source, &live);
    let id = PredicateId::new(0);
    let mut interpretation = model.model.get(&id).unwrap().clone();
    let repeated = Arc::new(interpretation.formula);
    interpretation.formula = ChcExpr::Op(ChcOp::And, vec![repeated; 4_096]);
    model.model.set(id, interpretation);
    validate(&source, &model, &live).unwrap();
    let axes = [ChcExpr::BitVec(0, 1), ChcExpr::BitVec(1, 1)];
    assert!(pullback::instance(&model, id, original_args(&source), &axes, &live).is_none());
    assert!(live.poll().is_none());
    let fresh = control(&token);
    let ordinary = super::model(&source, &fresh);
    assert!(pullback::instance(&ordinary, id, original_args(&source), &axes, &fresh).is_some());
}
