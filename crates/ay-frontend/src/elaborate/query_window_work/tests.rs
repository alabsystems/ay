// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::parser::parse;
use ay_core::original_query::{FiniteAdmissionGrant, OriginalAdmission, OriginalAdmissionError};
use ay_core::time::Instant;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

fn fixture() -> Context {
    let commands = parse(
        "(declare-const p Bool) (push 1) (assert (! p :named keep)) \
         (maximize (ite p 1 0)) (assert-soft p :weight 3 :id soft-keep)",
    )
    .expect("bounded query fixture");
    let mut context = Context::new();
    for command in &commands {
        context
            .process_command(command)
            .expect("query fixture elaborates");
    }
    context.set_retain_parsed_assertions(true);
    context
}

fn owner(work: u64, bytes: usize) -> OriginalAdmission {
    OriginalAdmission::new(
        FiniteAdmissionGrant::new(work, bytes),
        Instant::now() + Duration::from_secs(20),
        Arc::new(|| false),
    )
}

fn exact_owner(rows: usize) -> OriginalAdmission {
    owner(
        256 + 128 * rows as u64,
        storage_bytes(rows).expect("small fixture size"),
    )
}

fn assert_probe_view(context: &Context, roots: &[TermId]) {
    assert_eq!(context.assertions, roots);
    assert_eq!(context.assertion_finite_set_metadata.len(), roots.len());
    assert!(context
        .assertion_finite_set_metadata
        .iter()
        .all(|row| { row == &PublicAssertionMetadata::default() }));
    assert_eq!(context.assertions_parsed.len(), 0);
    assert!(!context.retains_parsed_assertions());
    assert_eq!(context.definitional_pass.parsed.len(), 0);
    assert_eq!(context.objectives.len(), 0);
    assert_eq!(context.objective_finite_set_metadata.len(), 0);
    assert_eq!(context.soft_constraints.len(), 0);
    assert_eq!(context.soft_finite_set_metadata.len(), 0);
    assert_eq!(context.named_terms.len(), 0);
    assert_eq!(context.polymorphic_assertions.len(), 0);
    assert_eq!(context.authored_assertions.len(), 0);
    assert_eq!(context.materialized_polymorphic_assertions, 0);
    assert!(context.polymorphic_instantiation_complete);
}

#[test]
fn prepaid_window_matches_legacy_query_view_and_restores_original_fields() {
    let mut context = fixture();
    let roots = [
        context.terms.false_term(),
        context.terms.true_term(),
        context.terms.false_term(),
    ];
    let source = context.source_context_stamp();
    let assertions = context.assertions.clone();
    let metadata = context.assertion_finite_set_metadata.clone();
    let parsed = context.assertions_parsed.clone();
    let objectives = context.objectives.clone();
    let soft = context.soft_constraints.clone();
    let names = context.named_terms.clone();
    let scope_depth = context.scope_depth();
    let legacy = context
        .begin_internal_query_window(roots.to_vec())
        .expect("legacy view");
    assert_probe_view(&context, &roots);
    assert!(context.restore_internal_query_window(legacy));
    let original = exact_owner(roots.len());
    original
        .with_work(|work| {
            context.with_internal_query_window_with_work(&roots, work, |probe, _| {
                assert_probe_view(probe, &roots);
                Ok(())
            })
        })
        .expect("same finite original grant");
    assert_eq!(context.source_context_stamp(), source);
    assert_eq!(context.assertions, assertions);
    assert_eq!(context.assertion_finite_set_metadata, metadata);
    assert_eq!(context.assertions_parsed, parsed);
    assert_eq!(context.objectives, objectives);
    assert_eq!(context.soft_constraints, soft);
    assert_eq!(context.named_terms, names);
    assert_eq!(context.scope_depth(), scope_depth);
    assert!(context.retains_parsed_assertions());
    assert!(original.clone().with_work(|work| work.charge(1)).is_err());
}

#[test]
fn empty_window_is_an_exact_zero_row_transaction_not_a_fresh_grant() {
    let mut context = fixture();
    let before = context.assertions.clone();
    let original = exact_owner(0);
    original
        .with_work(|work| {
            context.with_internal_query_window_with_work(&[], work, |probe, _| {
                assert_probe_view(probe, &[]);
                Ok(())
            })
        })
        .expect("fixed empty-window admission");
    assert_eq!(context.assertions, before);
    assert!(original.with_work(|work| work.charge(1)).is_err());
}

#[test]
fn dead_root_is_refused_before_operation_or_query_mutation() {
    let mut context = fixture();
    let before = context.assertions.clone();
    let original = exact_owner(1);
    let mut entered = false;
    let result = original.with_work(|work| {
        context.with_internal_query_window_with_work(&[TermId::SENTINEL], work, |_, _| {
            entered = true;
            Ok(())
        })
    });
    assert_eq!(
        result,
        Err(OriginalAdmissionError::Query(QueryError::Invalid(
            "query window root is not live"
        )))
    );
    assert!(!entered);
    assert_eq!(context.assertions, before);
    assert!(original.clone().check().is_err());
}

#[test]
fn non_boolean_root_is_refused_without_recursive_sort_formatting() {
    let mut context = fixture();
    let wrong = context.terms.mk_int(1.into());
    let before = context.assertions.clone();
    let original = exact_owner(1);
    let result = original.with_work(|work| {
        context.with_internal_query_window_with_work(&[wrong], work, |_, _| Ok(()))
    });
    assert_eq!(
        result,
        Err(OriginalAdmissionError::Query(QueryError::Invalid(
            "query window root is not Boolean"
        )))
    );
    assert_eq!(context.assertions, before);
    assert!(original.check().is_err());
}

#[test]
fn one_short_work_refuses_before_install_and_stays_originally_sticky() {
    let mut context = fixture();
    let root = context.terms.true_term();
    let before = context.assertions.clone();
    let original = owner(383, storage_bytes(1).expect("fixture size"));
    assert_eq!(
        original.with_work(|work| {
            context.with_internal_query_window_with_work(&[root], work, |_, _| Ok(()))
        }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(context.assertions, before);
    assert_eq!(
        original.clone().with_work(|_| Ok(())),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}

#[test]
fn one_short_copy_refuses_before_install_and_stays_originally_sticky() {
    let mut context = fixture();
    let root = context.terms.true_term();
    let before = context.assertions.clone();
    let original = owner(384, storage_bytes(1).expect("fixture size") - 1);
    assert_eq!(
        original.with_work(|work| {
            context.with_internal_query_window_with_work(&[root], work, |_, _| Ok(()))
        }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(context.assertions, before);
    assert!(original.clone().check().is_err());
}

#[test]
fn expired_original_end_refuses_before_preparation_or_mutation() {
    let mut context = fixture();
    let root = context.terms.false_term();
    let before = context.assertions.clone();
    let original = OriginalAdmission::new(
        FiniteAdmissionGrant::new(384, storage_bytes(1).expect("fixture size")),
        Instant::now(),
        Arc::new(|| false),
    );
    assert_eq!(
        original.with_work(|work| {
            context.with_internal_query_window_with_work(&[root], work, |_, _| Ok(()))
        }),
        Err(OriginalAdmissionError::Query(QueryError::Interrupted(
            ay_core::original_query::StopReason::Deadline,
        )))
    );
    assert_eq!(context.assertions, before);
    assert!(original.clone().check().is_err());
}

#[test]
fn swallowed_operation_resource_refusal_restores_without_later_retry() {
    let mut context = fixture();
    let root = context.terms.false_term();
    let before = context.assertions.clone();
    let original = exact_owner(1);
    assert_eq!(
        original.with_work(|work| {
            context.with_internal_query_window_with_work(&[root], work, |_, work| {
                work.refuse_exhaustion();
                Ok(())
            })
        }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(context.assertions, before);
    assert_eq!(
        original.clone().with_work(|_| Ok(())),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}

#[test]
fn observed_stop_after_operation_restores_query_before_final_owner_refusal() {
    let mut context = fixture();
    let root = context.terms.false_term();
    let before = context.assertions.clone();
    let flag = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&flag);
    let original = OriginalAdmission::new(
        FiniteAdmissionGrant::new(384, storage_bytes(1).expect("fixture size")),
        Instant::now() + Duration::from_secs(20),
        Arc::new(move || observed.load(Ordering::SeqCst)),
    );
    let result = original.with_work(|work| {
        context.with_internal_query_window_with_work(&[root], work, |_, _| {
            flag.store(true, Ordering::SeqCst);
            Ok(())
        })
    });
    assert_eq!(result, Err(OriginalAdmissionError::ObserverStopped));
    assert_eq!(context.assertions, before);
    assert!(context.retains_parsed_assertions());
    flag.store(false, Ordering::SeqCst);
    assert_eq!(
        original.clone().check(),
        Err(OriginalAdmissionError::ObserverStopped)
    );
}

#[test]
fn outer_original_final_poll_refuses_only_after_closed_window_returned_unit() {
    let mut context = fixture();
    let root = context.terms.false_term();
    let before = context.assertions.clone();
    let closed = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&closed);
    let original = OriginalAdmission::new(
        FiniteAdmissionGrant::new(384, storage_bytes(1).expect("fixture size")),
        Instant::now() + Duration::from_secs(20),
        Arc::new(move || observed.load(Ordering::SeqCst)),
    );
    let result = original.with_work(|work| {
        context.with_internal_query_window_with_work(&[root], work, |_, _| Ok(()))?;
        assert_eq!(context.assertions, before);
        assert!(context.retains_parsed_assertions());
        // The frontend has returned ONLY unit, after restoring saved state.
        // This refusal is at with_work's own later final poll, not its callback.
        closed.store(true, Ordering::SeqCst);
        Ok(())
    });
    assert_eq!(result, Err(OriginalAdmissionError::ObserverStopped));
    assert_eq!(context.assertions, before);
    closed.store(false, Ordering::SeqCst);
    assert_eq!(
        original.check(),
        Err(OriginalAdmissionError::ObserverStopped)
    );
}

#[test]
fn operation_unwind_restores_query_then_latches_the_original_owner() {
    let mut context = fixture();
    let root = context.terms.false_term();
    let before = context.assertions.clone();
    let source = context.source_context_stamp();
    let original = exact_owner(1);
    let result = original.with_work(|work| {
        context.with_internal_query_window_with_work(&[root], work, |probe, _| {
            probe.set_retain_parsed_assertions(true);
            panic!("bounded fixture unwind")
        })
    });
    assert_eq!(result, Err(OriginalAdmissionError::OperationPanicked));
    assert_eq!(context.assertions, before);
    assert_eq!(context.source_context_stamp(), source);
    assert!(context.retains_parsed_assertions());
    assert_eq!(
        original.check(),
        Err(OriginalAdmissionError::OperationPanicked)
    );
}

#[test]
fn source_revision_change_restores_bytes_but_refuses_authority() {
    let mut context = fixture();
    let root = context.terms.false_term();
    let before = context.assertions.clone();
    let original = owner(512, storage_bytes(1).expect("fixture size") + 64);
    let result = original.with_work(|work| {
        context.with_internal_query_window_with_work(&[root], work, |probe, work| {
            // Separate prepaid operation cost, not a query-window fee or grant.
            work.admit(128, 64)?;
            probe.set_logic("QF_UF".to_string());
            Ok(())
        })
    });
    assert_eq!(
        result,
        Err(OriginalAdmissionError::Query(QueryError::Invalid(
            "query window source or term prefix changed"
        )))
    );
    assert_eq!(context.assertions, before);
    assert!(original.check().is_err());
}

#[test]
fn allocation_size_overflow_is_checked_before_any_prepare_or_install() {
    assert!(storage_bytes(usize::MAX).is_none());
    assert_eq!(
        storage_bytes(0),
        size_of::<InternalQueryWindow>()
            .checked_mul(4)
            .and_then(|n| n.checked_add(256))
    );
}
