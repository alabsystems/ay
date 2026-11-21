// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn symbolic_uf_retained_custody_preserves_model_and_public_solver_send() {
    fn send<T: Send>() {}
    fn send_sync<T: Send + Sync>() {}
    send::<crate::executor::model::Model>();
    send::<crate::api::Solver>();
    send::<crate::executor::theories::FpStop>();
    send_sync::<crate::executor::model::SymbolicAdmission>();
}

fn installed() -> (
    Executor,
    crate::executor::model::Model,
    crate::executor::model::SymbolicAdmission,
) {
    let (mut executor, roots) = fixture(
        "(set-logic AUFLIA)(set-option :produce-models true)(declare-fun weather (Int) Bool)",
        &["(forall ((x Int)) (= (weather x) (< x 5)))"],
    );
    let (scope, package) = candidate(&mut executor, &roots);
    let owner = scope.admission();
    let mut model = crate::executor::model::Model::empty();
    executor
        .install_model_check_symbolic_ufs(&mut model, package, &owner)
        .unwrap();
    drop(scope);
    (executor, model, owner)
}

#[test]
fn symbolic_uf_retained_owner_debits_after_scope_and_model_clones_cannot_refill() {
    let (mut executor, model, owner) = installed();
    let term = source_term(&mut executor, "(weather 4)");
    let before = owner.remaining();
    let result = executor.symbolic_residual_check(&model, &[term]);
    assert!(result.is_ok(), "{result:?}");
    let after = owner.remaining();
    assert!(after.0 < before.0 && after.1 < before.1);

    let clone = model.clone();
    let result = executor.symbolic_residual_check(&clone, &[term]);
    assert!(result.is_ok(), "{result:?}");
    let after_clone = owner.remaining();
    assert!(after_clone.0 < after.0 && after_clone.1 < after.1);
    assert!(owner.pay(after_clone.0, 0));
    assert!(!executor.symbolic_residual_holds(&clone, &[term]));
    assert!(!owner.pay(0, 0), "refusal is shared and sticky");
    assert!(!executor.symbolic_residual_holds(&model, &[term]));
}

#[test]
fn symbolic_uf_retained_model_moves_with_its_original_account_to_another_thread() {
    let (mut executor, model, owner) = installed();
    let term = source_term(&mut executor, "(weather 4)");
    let before = owner.remaining();
    std::thread::spawn(move || {
        let result = executor.symbolic_residual_check(&model, &[term]);
        assert!(result.is_ok(), "{result:?}");
    })
    .join()
    .unwrap();
    let after = owner.remaining();
    assert!(after.0 < before.0 && after.1 < before.1);
}

#[test]
fn symbolic_uf_retained_output_copies_share_original_storage_allowance() {
    let (mut executor, model, owner) = installed();
    executor.last_result = Some(crate::executor_types::SolveResult::Sat);
    executor.last_model = Some(model);
    let before = owner.remaining();
    let output = executor.model();
    assert!(output.contains("(define-fun weather"), "{output}");
    let after = owner.remaining();
    assert!(after.0 < before.0 && after.1 < before.1);
    assert!(owner.pay(0, after.1));
    assert!(executor.model().starts_with("(error"));
    assert!(!owner.pay(0, 0));
}

#[test]
fn symbolic_uf_retained_refusal_keeps_first_exact_resource_or_source_reason() {
    for storage in [false, true] {
        let (mut executor, model, owner) = installed();
        let term = source_term(&mut executor, "(weather 4)");
        let remaining = owner.remaining();
        assert!(if storage {
            owner.pay(0, remaining.1)
        } else {
            owner.pay(remaining.0, 0)
        });
        let result = executor.symbolic_residual_check(&model, &[term]);
        assert!(result.is_err());
        let reason = format!("{:?}", owner.refusal());
        assert!(
            reason.starts_with(if storage {
                "Some(Storage {"
            } else {
                "Some(Work {"
            }),
            "{result:?} {reason}"
        );
        let first = owner.refusal();
        executor.advance_query_authority_epoch();
        assert!(!owner.pay_for(&executor, 0, 0));
        assert_eq!(
            owner.refusal(),
            first,
            "later failure cannot replace first cause"
        );
    }
    let (mut executor, model, owner) = installed();
    let term = source_term(&mut executor, "(weather 4)");
    executor.advance_query_authority_epoch();
    let result = executor.symbolic_residual_check(&model, &[term]);
    assert!(result.is_err());
    assert_eq!(format!("{:?}", owner.refusal()), "Some(Source)");
    assert!(result.unwrap_err().contains("Source"));
}

#[test]
fn symbolic_uf_retained_owner_rejects_foreign_reset_pop_and_changed_epoch() {
    for change in 0..4 {
        let (mut executor, model, owner) = installed();
        let term = source_term(&mut executor, "(weather 4)");
        match change {
            0 => {
                let foreign = Executor::new();
                assert!(!owner.pay_for(&foreign, 0, 0));
            }
            1 => executor.ctx.terms = ay_core::TermStore::new(),
            2 => {
                executor
                    .execute_all(&ay_frontend::parse("(push 1)(pop 1)").unwrap())
                    .unwrap();
            }
            _ => executor.advance_query_authority_epoch(),
        }
        assert!(!owner.pay_for(&executor, 0, 0));
        // Reset can make the old root invalid; the zero-copy admission fence
        // must reject before the evaluator could inspect it.
        if change != 1 {
            assert!(!executor.symbolic_residual_holds(&model, &[term]));
        }
        assert!(!owner.pay(0, 0));
    }
}

#[test]
fn symbolic_uf_retained_owner_never_adopts_a_different_active_transaction() {
    let (mut executor, model, owner) = installed();
    let term = source_term(&mut executor, "(weather 4)");
    let other = Executor::new();
    let scope = SymbolicRecoveryScope::enter(&other, Box::new(|_, _| true)).unwrap();
    let other_owner = scope.admission();
    let before = other_owner.remaining();
    assert!(!executor.symbolic_residual_holds(&model, &[term]));
    assert!(!owner.pay(0, 0));
    assert_eq!(other_owner.remaining(), before);
    assert!(other_owner.pay(1, 0));
}

#[test]
fn symbolic_uf_retained_owner_preserves_original_stop_after_scope_drop() {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    let (mut executor, roots) = fixture(
        "(set-logic AUFLIA)(declare-fun weather (Int) Bool)",
        &["(forall ((x Int)) (= (weather x) (< x 5)))"],
    );
    let stopped = Arc::new(AtomicBool::new(false));
    let stop = Arc::clone(&stopped);
    let scope = SymbolicRecoveryScope::enter(
        &executor,
        Box::new(move |_, _| !stop.load(Ordering::SeqCst)),
    )
    .unwrap();
    let owner = scope.admission();
    let package = executor.qmc_symbolic_candidate(&roots, &owner).unwrap();
    let mut model = crate::executor::model::Model::empty();
    executor
        .install_model_check_symbolic_ufs(&mut model, package, &owner)
        .unwrap();
    let term = source_term(&mut executor, "(weather 4)");
    drop(scope);
    stopped.store(true, Ordering::SeqCst);
    assert!(!executor.symbolic_residual_holds(&model, &[term]));
    stopped.store(false, Ordering::SeqCst);
    assert!(!owner.pay(0, 0));
    assert!(!executor.symbolic_residual_holds(&model, &[term]));
}

#[test]
fn symbolic_uf_retained_owner_also_honors_the_current_external_read_deadline() {
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;

    let (mut executor, model, owner) = installed();
    let term = source_term(&mut executor, "(weather 4)");
    let read = executor.begin_native_evaluation_read(
        Arc::new(AtomicBool::new(false)),
        Some(ay_core::time::Instant::now()),
        None,
        None,
    );
    assert!(!executor.symbolic_residual_holds(&model, &[term]));
    drop(read);
    assert!(!owner.pay(0, 0));
    assert!(!executor.symbolic_residual_holds(&model, &[term]));
}

#[test]
fn symbolic_uf_retained_package_cannot_be_installed_under_a_new_allowance() {
    let (mut executor, roots) = fixture(
        "(set-logic AUFLIA)(declare-fun weather (Int) Bool)",
        &["(forall ((x Int)) (= (weather x) (< x 5)))"],
    );
    let (scope, package) = candidate(&mut executor, &roots);
    let original = scope.admission();
    drop(scope);
    let replacement = SymbolicRecoveryScope::enter(&executor, Box::new(|_, _| true)).unwrap();
    let mut model = crate::executor::model::Model::empty();
    assert!(executor
        .install_model_check_symbolic_ufs(&mut model, package, &replacement.admission())
        .is_none());
    assert!(original.pay(0, 0));
    assert!(replacement.admission().pay(0, 0));
}
