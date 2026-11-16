// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Real producer -> ordinary whole-pin caller DATA controls; no native verdict.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use crate::executor_types::UnknownOrigin;
use ay_core::resource::{check_stop_requested, enter_check_stop};
use ay_core::time::Instant;
use ay_core::Constant;
use ay_frontend::parse;
use ay_model_check::{recognize_range_lambda, ArraySnapshot};

use super::*;

mod support;
use support::*;

mod normalized_fixtures;

#[test]
fn whole_caller_finite_bv128_retains_complete_default_overrides_and_original_identity() {
    let end = Instant::now() + Duration::from_secs(20);
    let scope = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(FINITE, end);
    let leaf = variable(&exec, "a");
    let root = matrix(&exec);
    let source = exec.ctx.source_context_stamp();
    let birth = exec.ctx.terms.entry_stamp(leaf);
    let selected = snapshot(&exec, leaf);
    let result = pins(&mut exec, root, &HashSet::new());
    assert!(
        result.total,
        "actual caller must admit this bounded complete pin"
    );
    assert_eq!(result.equalities.len(), 1);
    let value = rhs(&exec, &result, leaf);
    let outer = args(&exec, value, "store");
    let inner = args(&exec, outer[0], "store");
    let base = args(&exec, inner[0], "const-array");
    let maximum = (num_bigint::BigInt::from(1u8) << 128u32) - 1u8;
    assert!(matches!(exec.ctx.terms.get(base[0]),
        TermData::Const(Constant::BitVec { value, width: 128 }) if value == &maximum));
    assert!(matches!(exec.ctx.terms.get(outer[2]),
        TermData::Const(Constant::BitVec { value, width: 128 }) if value == &maximum));
    assert_eq!(exec.ctx.source_context_stamp(), source);
    assert_eq!(exec.ctx.terms.entry_stamp(leaf), birth);
    assert!(Arc::ptr_eq(&selected, &snapshot(&exec, leaf)));
    whole(&exec, leaf, value);
    drop(result);
    drop(exec);
    drop(scope);
    assert!(
        Instant::now() < end,
        "cleanup stays inside the ONE original end"
    );
}

#[test]
fn whole_caller_overlapping_prewrite_range_retains_full_domain_and_modular_maximum() {
    let end = Instant::now() + Duration::from_secs(20);
    let scope = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(RANGE, end);
    let leaf = variable(&exec, "w");
    let root = matrix(&exec);
    let result = pins(&mut exec, root, &HashSet::new());
    assert!(result.total, "unchanged 1M owner, no enumerated huge range");
    assert_eq!(result.equalities.len(), 1);
    let value = rhs(&exec, &result, leaf);
    let recipe =
        recognize_range_lambda(&exec.ctx.terms, value).expect("exact closed range grammar");
    assert_eq!(
        recipe.source, recipe.destination,
        "one captured old aliased graph"
    );
    bv(&exec, recipe.lo, 1);
    bv(&exec, recipe.hi, u64::MAX);
    bv(
        &exec,
        recipe.source_lo.expect("MAX offset is retained"),
        u64::MAX,
    );
    let outer = args(&exec, recipe.source, "store");
    args(&exec, outer[0], "store");
    whole(&exec, leaf, value);
    drop(result);
    drop(exec);
    drop(scope);
    assert!(Instant::now() < end);
}

#[test]
fn whole_caller_rejects_equal_but_foreign_arc_and_then_changed_original_source() {
    let end = Instant::now() + Duration::from_secs(20);
    let scope = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(FINITE, end);
    let leaf = variable(&exec, "a");
    let root = matrix(&exec);
    let selected = snapshot(&exec, leaf);
    let foreign = Arc::new((*selected).clone());
    assert!(!Arc::ptr_eq(&foreign, &selected));
    let before = exec.ctx.terms.len();
    assert!(exec
        .complete_functional_array_model_pin(leaf, foreign)
        .is_none());
    assert_eq!(
        exec.ctx.terms.len(),
        before,
        "identity refusal precedes producer append"
    );
    let valid = pins(&mut exec, root, &HashSet::new());
    assert!(
        valid.total,
        "the original selected Arc still uses the actual caller"
    );
    drop(valid);
    assert_eq!(
        exec.execute_all(&parse("(assert false)").expect("source change"))
            .expect("source mutation only"),
        [] as [String; 0]
    );
    assert!(exec
        .complete_functional_array_model_pin(leaf, selected)
        .is_none());
    refused(&mut exec, root);
    drop(exec);
    drop(scope);
    assert!(Instant::now() < end);
}

#[test]
fn whole_caller_preserves_scalar_pins_binder_scope_and_explicit_gate_exclusions() {
    let end = Instant::now() + Duration::from_secs(20);
    let scope = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let source = "(declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-const x (_ BitVec 64))
        (assert (= a ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07)))
        (assert (= x (_ bv3 64)))
        (assert (forall ((i (_ BitVec 64)))
            (=> (bvult i x) (= (select a i) #x07))))";
    let mut exec = loaded(source, end);
    let x = variable(&exec, "x");
    exec.last_model
        .as_mut()
        .expect("same original model")
        .completed_values
        .insert(
            x,
            EvalValue::BitVec {
                value: 3u8.into(),
                width: 64,
            },
        );
    let original = matrix(&exec);
    // This fixture-created term is deliberately NOT an original source leaf.
    let created = exec
        .ctx
        .terms
        .mk_fresh_var("qmg!whole-pin-fixture", Sort::Bool);
    let combined = exec.ctx.terms.mk_and(vec![original, created]);
    let result = pins(&mut exec, combined, &HashSet::from([created]));
    assert!(result.total);
    assert_eq!(
        result.equalities.len(),
        2,
        "array and original x; no bound i or created leaf"
    );
    bv(&exec, rhs(&exec, &result, x), 3);
    let array = variable(&exec, "a");
    whole(&exec, array, rhs(&exec, &result, array));
    assert!(result
        .equalities
        .iter()
        .all(|&id| args(&exec, id, "=")[0] != created));
    drop(result);
    drop(exec);
    drop(scope);
    assert!(Instant::now() < end);
}

#[test]
fn whole_caller_exact_zero_then_refusal_is_sticky_across_a_distinct_read_frame() {
    let end = Instant::now() + Duration::from_secs(20);
    let scope = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(FINITE, end);
    let root = matrix(&exec);
    let model = exec.last_model.as_ref().expect("original model");
    let remaining = model.functional_work_left();
    model
        .charge_functional_array_work(&exec, remaining)
        .expect("exact original remainder");
    model
        .charge_functional_array_work(&exec, 0)
        .expect("exact-limit zero is not yet refused");
    assert_eq!(model.functional_work_left(), 0);
    refused(&mut exec, root);
    let read = exec.begin_external_evaluation_read();
    assert!(
        exec.evaluation_stop_origin().is_none(),
        "fresh frame is not a new MODEL allowance"
    );
    assert!(exec
        .last_model
        .as_ref()
        .expect("same MODEL")
        .charge_functional_array_work(&exec, 0)
        .is_err());
    refused(&mut exec, root);
    drop(read);
    refused(&mut exec, root);
    drop(exec);
    drop(scope);
    assert!(Instant::now() < end);
}

#[test]
fn whole_caller_original_callback_raw_and_end_refusals_survive_reset_and_scope_drop() {
    let end = Instant::now() + Duration::from_secs(20);
    for cause in 0..3 {
        let flag = Arc::new(AtomicBool::new(false));
        let callback = Arc::clone(&flag);
        let scope = enter_check_stop(Arc::new(move || {
            Instant::now() >= end || callback.load(Ordering::Acquire)
        }));
        let mut exec = loaded(FINITE, end);
        let raw = Arc::new(AtomicBool::new(false));
        exec.set_interrupt(Arc::clone(&raw));
        let root = matrix(&exec);
        match cause {
            0 => flag.store(true, Ordering::Release),
            1 => raw.store(true, Ordering::Release),
            _ => exec.set_deadline(Some(Instant::now())),
        }
        refused(&mut exec, root);
        let expected = match cause {
            0 => UnknownOrigin::IncompleteSolverLane,
            1 => UnknownOrigin::InterruptFlag,
            _ => UnknownOrigin::SolveDeadline,
        };
        assert_eq!(exec.evaluation_stop_origin(), Some(expected));
        flag.store(false, Ordering::Release);
        raw.store(false, Ordering::Release);
        exec.set_deadline(None);
        drop(scope);
        let read = exec.begin_external_evaluation_read();
        refused(&mut exec, root);
        drop(read);
        refused(&mut exec, root);
        drop(exec);
        assert!(
            Instant::now() < end,
            "independent negative fixtures share ONE absolute end"
        );
    }
}
