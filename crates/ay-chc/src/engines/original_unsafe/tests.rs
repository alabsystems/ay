// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Injected tests exercise control flow, not proof authority. The separate
//! `authority` module calls the real original-source search and validator.

use super::*;
use crate::{CancellationToken, ChcParser};

mod ambient;
mod authority;
mod controls;
mod ground;

const SCALAR: &str = include_str!(
    "../../../tests/group_bv/model_checker_consumer_cyclic_arrays/loop_repro_array_false.smt2"
);
const ARRAY: &str = include_str!(
    "../../../tests/group_bv/model_checker_consumer_cyclic_arrays/loop_repro_array_true.smt2"
);
const SAFE_GUARD: &str = "(not (bvult i #x0000000000000004))";
const UNSAFE_GUARD: &str = "(bvult i #x0000000000000004)";

fn source() -> ChcProblem {
    ChcParser::parse(SCALAR).unwrap()
}

fn configured() -> PdrConfig {
    PdrConfig {
        strict_proofs: true,
        preserve_original_clauses: true,
        solve_timeout: Some(Duration::from_secs(60)),
        ..PdrConfig::production(false)
    }
}

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn candidate() -> Counterexample {
    Counterexample::new(Vec::new())
}

// A deliberately simulated validator return, never an assertion that an empty
// trace proves reachability. Production run() always uses the real validator.
fn fake_unsafe(candidate: Counterexample) -> VerifiedChcResult {
    VerifiedChcResult::from_validated(
        ChcEngineResult::Unsafe(candidate),
        ValidationEvidence::CounterexampleVerification,
    )
}

fn phases() -> [Phase; 6] {
    [
        Phase::Eligibility,
        Phase::Search,
        Phase::Validation,
        Phase::Validated,
        Phase::Publication,
        Phase::Cleanup,
    ]
}

#[test]
fn simulated_candidate_requires_original_validation_before_publication() {
    let original = source();
    let before = format!("{original:?}");
    for accepted in [None, Some(candidate())] {
        let until = deadline();
        let mut searched = 0;
        let mut validated = 0;
        let mut observed = Vec::new();
        let mut accepted = accepted;
        let expected = accepted.is_some();
        let result = run_observed(
            &original,
            &configured(),
            Some(until),
            &mut |input, budget, config| {
                searched += 1;
                assert!(std::ptr::eq(input, &original));
                assert!(budget >= Duration::from_millis(250));
                assert!(budget <= Duration::from_secs(4));
                assert!(config.strict_proofs && config.preserve_original_clauses);
                Some(candidate())
            },
            &mut |_, config, clock| {
                validated += 1;
                assert!(config.strict_proofs && config.preserve_original_clauses);
                assert_eq!(clock, Some(until));
                accepted.take().map(fake_unsafe).unwrap_or_else(unknown)
            },
            &mut |phase| observed.push(phase),
        );
        assert_eq!((searched, validated), (1, 1));
        if expected {
            assert!(result.unwrap().is_unsafe());
            assert_eq!(observed, phases());
        } else {
            assert!(result.is_none());
            assert!(!observed.contains(&Phase::Publication));
        }
        assert_eq!(format!("{original:?}"), before);
    }
}

#[test]
fn absent_clock_or_unconfirmed_search_preserves_ordinary_fallback() {
    let original = source();
    for clock in [None, Some(deadline())] {
        let mut searched = 0;
        let result = run_observed(
            &original,
            &configured(),
            clock,
            &mut |input, _, _| {
                assert!(std::ptr::eq(input, &original));
                searched += 1;
                None
            },
            &mut |_, _, _| panic!("no confirmed original candidate"),
            &mut |_| {},
        );
        assert!(result.is_none());
        assert_eq!(searched, usize::from(clock.is_some()));
    }
}

#[test]
fn ineligible_sources_and_source_bound_configuration_never_search() {
    for case in 0..7 {
        let mut original = source();
        let mut config = configured();
        match case {
            0 => original.mark_stripped_body_forall(),
            1 => config.disable_cex_replay = true,
            2 => config.enable_tla_trace = true,
            3 => config.bv_bit_groups.push((0, 64)),
            4 => original = ChcProblem::new(),
            5 => {
                // Duplicate a genuine body atom: the source is now nonlinear.
                let clause = original
                    .clauses_mut()
                    .iter_mut()
                    .find(|clause| !clause.body.predicates.is_empty())
                    .unwrap();
                clause
                    .body
                    .predicates
                    .push(clause.body.predicates[0].clone());
            }
            _ => {
                original =
                    ChcParser::parse("(set-logic HORN) (declare-rel p ()) (rule p) (query p)")
                        .unwrap();
            }
        }
        assert!(run_observed(
            &original,
            &config,
            Some(deadline()),
            &mut |_, _, _| panic!("ineligible case {case} must not search"),
            &mut |_, _, _| panic!("ineligible case {case} must not validate"),
            &mut |_| {},
        )
        .is_none());
    }
}

#[test]
fn subminimum_probe_budget_does_not_start_or_renew_search() {
    let original = source();
    assert!(run_observed(
        &original,
        &configured(),
        Some(Instant::now() + Duration::from_millis(500)),
        &mut |_, _, _| panic!("remaining quarter is below the helper minimum"),
        &mut |_, _, _| panic!("no candidate"),
        &mut |_| {},
    )
    .is_none());
}
