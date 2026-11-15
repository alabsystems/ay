// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_chc::engines::{
    validate_external_invariant_model_typed, ExternalInvariantValidation as Kind,
};
use ay_chc::{ChcExpr, ChcSort, ChcVar, InvariantModel, PredicateInterpretation};

#[test]
fn all_original_prepared_rows_reject_free_binder_models_under_exact_row_caps() {
    let archive = super::super::tests::fixture();
    for case in R34Row::ALL {
        let row = &archive.capture.rows[case.index()];
        let config = preparation::config(&archive, row).unwrap();
        let original = super::super::tests::original();
        let mut validation = config.to_pdr_config();
        let owner = ExternalInvariantValidationOwner::capture(&original, &validation);
        let result = owner
            .with_resources(|| {
                // A negative current-source validation control, not approval of a
                // historical identity migration or permission to publish a proof.
                let prepared = preparation::prepare_with_progress(&archive, row, &mut || {
                    owner.check().is_none()
                })
                .map_err(chc_error)?
                .ok_or_else(|| {
                    ay_chc::ChcError::Internal(
                        "original validation control stopped during preparation".to_owned(),
                    )
                })?;
                let mut invalid = InvariantModel::new();
                assert!(!prepared.problem.predicates().is_empty());
                for predicate in prepared.problem.predicates() {
                    let binders = predicate
                        .arg_sorts
                        .iter()
                        .enumerate()
                        .map(|(i, sort)| ChcVar::new(format!("r34_bound_{i}"), sort.clone()))
                        .collect();
                    let outside = ChcExpr::var(ChcVar::new("r34_unbound", ChcSort::Bool));
                    invalid.set(predicate.id, PredicateInterpretation::new(binders, outside));
                }
                validation.solve_timeout =
                    Some(owner.deadline().saturating_duration_since(Instant::now()));
                validate_external_invariant_model_typed(&prepared.problem, &invalid, &validation)
            })
            .unwrap();
        assert_eq!(result, Ok(Kind::Rejected), "{case:?}");
        assert_eq!(owner.check(), None);
    }
}

#[test]
fn genuine_source_error_survives_a_later_retirement_stop() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
    let mut archive = super::super::tests::fixture();
    let path = format!("{}/source.smt2", archive.capture.sources["static"].base);
    archive.files.get_mut(&path).unwrap().push(b' ');
    let count = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&count);
    let scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::Relaxed);
        false
    }));
    let failed = archive
        .inspect_row(
            R34Row::StaticErrorP0,
            &super::super::tests::original(),
            &CancellationToken::new(),
        )
        .unwrap();
    assert!(matches!(failed.status, R34RowStatus::ExecutionError { .. }));
    drop(scope);
    let last = count.load(Ordering::Relaxed);
    assert!(last > 3);
    count.store(0, Ordering::Relaxed);
    let observed = Arc::clone(&count);
    let scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::Relaxed) + 1 >= last
    }));
    let failed = archive
        .inspect_row(
            R34Row::StaticErrorP0,
            &super::super::tests::original(),
            &CancellationToken::new(),
        )
        .unwrap();
    assert!(
        matches!(failed.status, R34RowStatus::ExecutionError { ref reason }
        if reason.contains("source bytes identity mismatch"))
    );
    assert_eq!(count.load(Ordering::Relaxed), last);
    drop(scope);
}
