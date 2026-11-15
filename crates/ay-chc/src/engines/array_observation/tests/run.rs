// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Simulated search/validator controls, not proof evidence.

use super::super::{run_observed, Phase};
use super::*;
use crate::engine_result::ValidationEvidence;
use crate::{ChcEngineResult, PdrConfig, PdrResult, VerifiedChcResult};
use ay_core::time::Instant;
use std::time::Duration;

pub(super) fn configured() -> PdrConfig {
    PdrConfig {
        strict_proofs: true,
        preserve_original_clauses: true,
        solve_timeout: Some(Duration::from_secs(20)),
        ..PdrConfig::production(false)
    }
}

pub(super) fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(20)
}

pub(super) fn fake_safe(model: InvariantModel) -> VerifiedChcResult {
    VerifiedChcResult::from_validated(
        ChcEngineResult::Safe(model),
        ValidationEvidence::FullVerification,
    )
}

pub(super) fn fake_unknown() -> VerifiedChcResult {
    VerifiedChcResult::from_validated(
        ChcEngineResult::Unknown,
        ValidationEvidence::FullVerification,
    )
}

pub(super) fn phases() -> [Phase; 9] {
    [
        Phase::HintAdmission,
        Phase::Projection,
        Phase::HintRebase,
        Phase::Search,
        Phase::Lift,
        Phase::Validation,
        Phase::Validated,
        Phase::Publication,
        Phase::Cleanup,
    ]
}

#[test]
fn only_original_validator_admission_publishes_a_fresh_complete_model() {
    let original = source(9, false);
    let before = original.clone();
    for accept in [false, true] {
        let until = deadline();
        let mut calls = 0;
        let mut observed = Vec::new();
        let result = run_observed(
            &original,
            &configured(),
            Some(until),
            &mut |reduced, config| {
                assert!(config.strict_proofs && config.preserve_original_clauses);
                assert!(config.disable_array_scalarization);
                PdrResult::Safe(candidate(reduced))
            },
            &mut |lifted, config, clock| {
                calls += 1;
                assert!(config.strict_proofs && config.preserve_original_clauses);
                assert_eq!(clock, Some(until));
                assert_eq!(lifted.len(), original.predicates().len());
                assert!(!lifted.convergence_proven && !lifted.individually_inductive);
                if accept {
                    fake_safe(lifted)
                } else {
                    fake_unknown()
                }
            },
            &mut |phase| observed.push(phase),
        );
        assert_eq!(calls, 1);
        if accept {
            assert!(result.unwrap().is_safe());
            assert_eq!(observed, phases());
        } else {
            assert!(result.is_none());
            assert!(!observed.contains(&Phase::Publication));
        }
    }
    same_source(&before, &original);
}

#[test]
fn unsafe_unknown_and_not_applicable_candidates_never_reach_validation() {
    let original = source(9, false);
    for raw in [
        PdrResult::Unsafe(crate::Counterexample::new(vec![])),
        PdrResult::Unknown,
        PdrResult::NotApplicable,
    ] {
        let mut raw = Some(raw);
        let result = run_observed(
            &original,
            &configured(),
            Some(deadline()),
            &mut |_, _| raw.take().unwrap(),
            &mut |_, _, _| panic!("only scalarized Safe is a candidate"),
            &mut |_| {},
        );
        assert!(raw.is_none());
        assert!(result.is_none());
    }
}

#[test]
fn partial_candidate_declines_without_repair_or_validation() {
    let original = source(9, false);
    let result = run_observed(
        &original,
        &configured(),
        Some(deadline()),
        &mut |reduced, _| {
            let mut model = candidate(reduced);
            model
                .interpretations
                .remove(&original.lookup_predicate("B").unwrap());
            PdrResult::Safe(model)
        },
        &mut |_, _, _| panic!("partial model cannot reach validator"),
        &mut |_| {},
    );
    assert!(result.is_none());
}

#[test]
fn source_bound_hints_tracing_and_extra_keys_decline_without_clearing_inputs() {
    let original = source(9, false);
    for kind in 0..4 {
        let mut config = configured();
        match kind {
            0 => config.user_hints.push(crate::LemmaHint::new(
                original.lookup_predicate("H").unwrap(),
                ChcExpr::eq(
                    ChcExpr::select(
                        variable(
                            &crate::canonical_var_name(original.lookup_predicate("H").unwrap(), 0),
                            original.predicates()[0].arg_sorts[0].clone(),
                        ),
                        bv(1, 64),
                    ),
                    bv(9, 32),
                ),
                0,
                "native-auto-hint",
            )),
            1 => config.enable_tla_trace = true,
            2 => config
                .array_scalarization_extra_indices
                .push((ChcSort::BitVec(64), bv(1, 64))),
            _ => config.bv_to_int_relaxed = true,
        }
        let result = run_observed(
            &original,
            &config,
            Some(deadline()),
            &mut |_, _| panic!("source channels are not translated"),
            &mut |_, _, _| panic!("no candidate"),
            &mut |_| {},
        );
        assert!(result.is_none());
        if kind == 0 {
            assert_eq!(config.user_hints.len(), 1);
        }
    }
}

#[test]
fn the_existing_disable_scalarization_request_is_not_silently_overridden() {
    let original = source(9, false);
    let mut config = configured();
    config.disable_array_scalarization = true;
    assert!(run_observed(
        &original,
        &config,
        Some(deadline()),
        &mut |_, _| panic!("caller disabled the candidate transform"),
        &mut |_, _, _| panic!("no candidate"),
        &mut |_| {}
    )
    .is_none());
    assert!(config.disable_array_scalarization);
}

#[test]
fn absent_finite_clock_or_inapplicable_source_retains_ordinary_fallback() {
    let original = source(9, false);
    assert!(run_observed(
        &original,
        &configured(),
        None,
        &mut |_, _| panic!("no finite slice"),
        &mut |_, _, _| panic!("no candidate"),
        &mut |_| {}
    )
    .is_none());
    let scalar = ChcParser::parse("(declare-fun p (Int) Bool) (assert (p 0)) (check-sat)").unwrap();
    assert!(run_observed(
        &scalar,
        &configured(),
        Some(deadline()),
        &mut |_, _| panic!("not an observation source"),
        &mut |_, _, _| panic!("no candidate"),
        &mut |_| {}
    )
    .is_none());
}
