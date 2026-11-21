// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn source() -> (Executor, Vec<TermId>) {
    fixture(
        "(set-logic AUFLIA)(declare-fun weather (Int) Bool)",
        &["(forall ((x Int)) (= (weather x) (< x 5)))"],
    )
}

#[test]
fn symbolic_uf_binding_lease_retains_raw_core_operator_and_shadow_checks() {
    for change in 0..3 {
        let (mut executor, roots) = source();
        let (_scope, package) = candidate(&mut executor, &roots);
        let stamp = executor.ctx.source_context_stamp();
        let length = executor.ctx.terms.len();
        let generation = executor.ctx.terms.checker_visible_metadata_generation();
        match change {
            0 => executor.ctx.terms.register_declared_function("<"),
            1 => executor.ctx.terms.mark_to_real_shadowed(),
            _ => executor.ctx.terms.mark_is_int_shadowed(),
        }
        assert_eq!(stamp, executor.ctx.source_context_stamp());
        assert_eq!(length, executor.ctx.terms.len());
        assert_eq!(
            executor.ctx.terms.checker_visible_metadata_generation(),
            generation + 1
        );
        assert!(
            !package.is_current(&executor),
            "frontend stamp alone must not grant core operator meaning"
        );
    }
}

#[test]
fn symbolic_uf_binding_lease_keeps_append_prefix_and_full_original_roots() {
    let (mut executor, roots) = source();
    let (_scope, package) = candidate(&mut executor, &roots);
    let checkpoint = executor.ctx.terms.rollback_checkpoint();
    executor.ctx.terms.mk_int(987654.into());
    assert!(
        package.is_current(&executor),
        "an unrelated append does not alter checked source"
    );
    executor.ctx.terms.rollback_to(checkpoint);
    assert!(
        !package.is_current(&executor),
        "even restored row contents cannot restore arena currency"
    );

    drop(_scope);
    let (_scope, package) = candidate(&mut executor, &roots);
    executor
        .independent_gate_authored_assertions
        .as_mut()
        .unwrap()
        .push(roots[0]);
    assert!(
        !package.is_current(&executor),
        "ordered original roots and duplicates remain exact"
    );
}

#[test]
fn symbolic_uf_binding_lease_repeated_views_still_debit_one_retained_owner() {
    let (mut executor, roots) = source();
    let (scope, package) = candidate(&mut executor, &roots);
    let owner = scope.admission();
    let mut model = crate::executor::model::Model::empty();
    executor
        .install_model_check_symbolic_ufs(&mut model, package, &owner)
        .unwrap();
    drop(scope);
    let term = source_term(&mut executor, "(weather 4)");
    let mut before = owner.remaining();
    for _ in 0..4 {
        let result = executor.symbolic_residual_check(&model, &[term]);
        assert!(result.is_ok(), "{result:?}");
        let after = owner.remaining();
        assert!(
            after.0 < before.0 && after.1 < before.1,
            "a lease does not cache model values or renew budgets"
        );
        before = after;
    }
    assert!(owner.pay(before.0, 0));
    assert!(executor.symbolic_residual_check(&model, &[term]).is_err());
    assert!(!owner.pay(0, 0), "work refusal remains sticky across views");
}

#[test]
fn symbolic_uf_binding_lease_stop_between_views_is_sticky() {
    use std::sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    };
    let (mut executor, roots) = source();
    let running = Arc::new(AtomicBool::new(true));
    let callback = Arc::clone(&running);
    let scope = SymbolicRecoveryScope::enter(
        &executor,
        Box::new(move |_, _| callback.load(Ordering::SeqCst)),
    )
    .unwrap();
    let owner = scope.admission();
    let package = executor.qmc_symbolic_candidate(&roots, &owner).unwrap();
    let mut model = crate::executor::model::Model::empty();
    executor
        .install_model_check_symbolic_ufs(&mut model, package, &owner)
        .unwrap();
    drop(scope);
    let term = source_term(&mut executor, "(weather 4)");
    assert!(executor.symbolic_residual_check(&model, &[term]).is_ok());
    running.store(false, Ordering::SeqCst);
    assert!(executor.symbolic_residual_check(&model, &[term]).is_err());
    running.store(true, Ordering::SeqCst);
    assert!(executor.symbolic_residual_check(&model, &[term]).is_err());
    assert!(!owner.pay(0, 0));
}
