// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Phase 0 (`resolve_ground_constrained_absent_atoms`) runs its nested
//! sub-solve inside the completion's live evaluation-memo session. These
//! tests pin that the sub-solve and the outer completion do not share
//! `TermId`-keyed memo entries.

use super::super::{EvalMemoSession, EvalValue, Model};
use crate::executor::Executor;
use crate::executor_types::SolveResult;
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Sort, TermId};
use ay_lia::LiaModel;
use num_bigint::BigInt;
use num_rational::BigRational;

fn int(v: i64) -> EvalValue {
    EvalValue::Rational(BigRational::from_integer(BigInt::from(v)))
}

/// `(= (+ x y) 5)` with `x = 2` decided and `y` absent from the LIA model.
/// `extra` adds one more assertion that does not mention `y`.
fn absent_y(extra: Option<i64>) -> (Executor, TermId, Model) {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("x", Sort::Int);
    let y = exec.ctx.terms.mk_var("y", Sort::Int);
    let five = exec.ctx.terms.mk_int(BigInt::from(5));
    let sum = exec.ctx.terms.mk_add(vec![x, y]);
    let eq = exec.ctx.terms.mk_eq(sum, five);
    exec.ctx.assertions.push(eq);
    if let Some(k) = extra {
        let k = exec.ctx.terms.mk_int(BigInt::from(k));
        let pin = exec.ctx.terms.mk_eq(x, k);
        exec.ctx.assertions.push(pin);
    }
    let mut values = HashMap::default();
    values.insert(x, BigInt::from(2));
    let mut model = Model::empty();
    model.lia_model = Some(LiaModel { values });
    exec.last_result = Some(SolveResult::Sat);
    (exec, y, model)
}

/// The sub-solve's witness `y = 3` reaches the outer model. Without memo
/// isolation the sub-solve reads the outer's cached `Unknown` entries (its
/// own validation cannot confirm), or plants its own values that make the
/// outer skip the target: either way nothing transfers.
#[test]
fn phase0_transfers_its_sub_witness_under_a_live_completion_memo() {
    let (mut exec, y, mut model) = absent_y(None);
    // Mirrors the session `complete_model_for_validation` holds around Phase 0.
    let _completion_memo = EvalMemoSession::new();
    let filled = exec.resolve_ground_constrained_absent_atoms(&mut model);
    assert_eq!(filled, 1, "the definitive sub-SAT witness must transfer");
    assert_eq!(exec.evaluate_term(&model, y), int(3));
    assert_eq!(
        exec.last_statistics
            .get_int("model_completion.ground_resolved"),
        Some(1)
    );
}

/// Negative twin: the transfer stays candidate-only. The outer model already
/// violates an assertion that does not mention `y`, so the completed-gap gate
/// rejects the fill and the pre-fill model is restored.
#[test]
fn phase0_transfer_rejected_by_the_gap_gate_restores_the_model() {
    let (mut exec, y, mut model) = absent_y(Some(7));
    let _completion_memo = EvalMemoSession::new();
    let filled = exec.resolve_ground_constrained_absent_atoms(&mut model);
    assert_eq!(filled, 0);
    assert!(!model.completed_values.contains_key(&y));
    assert_eq!(exec.evaluate_term(&model, y), EvalValue::Unknown);
}
