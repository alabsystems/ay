// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Every route that admits an empty-model acyclic SAFE, pinned on the §4-A1
//! repros and on a fabricated engine claim.
//!
//! The fabricated claims stand in for an engine that lies, so these pins keep
//! discriminating after the head-only-variable fix made BMC honest on `H3`
//! (on current code they fail when any one re-check is removed):
//! - a `ScalarAcyclicBmcExhaustive` or `CheckedQueryOnlyDischarge` label on an
//!   UNSAFE problem, which the finalize gate admitted on label and signature
//!   alone;
//! - an acyclic-certificate cache entry saying BMC proved an UNSAFE problem,
//!   which `validate_external_invariant_model` returned as `Ok(true)` because
//!   it re-ran (or recalled) that same engine, and which the proof-grade PDR
//!   prepass accepted as proof;
//! - a BMC re-proof verdict of `Safe` handed to Fix V1's admission.

use super::{parse, H3, H3Y, H3_SAFE, H8, H8M};
use crate::engine_result::ValidationEvidence;
use crate::portfolio::PortfolioResult;
use crate::{
    AdaptiveConfig, AdaptivePortfolio, ChcProblem, InvariantModel, PdrConfig, VerifiedChcResult,
};
use ay_core::time::Instant;
use ntest::timeout;
use std::time::Duration;

fn empty() -> InvariantModel {
    InvariantModel::default()
}

/// `H3Y` (UNSAFE) under a predicate name no other test uses, so a cache
/// entry recorded for it cannot reach another test's problem.
fn unsafe_with_private_names(prefix: &str) -> ChcProblem {
    parse(
        &H3Y.replace("(declare-fun P ", &format!("(declare-fun {prefix}P "))
            .replace("(P ", &format!("({prefix}P ")),
    )
}

/// `validate_external_invariant_model` / `external_invariant_model_excludes_error`
/// with an empty model: the repros are refused, the safe twin admitted.
#[test]
#[timeout(120_000)]
fn external_empty_model_validators_refuse_the_repros() {
    for (name, input) in [("h3", H3), ("h8", H8), ("h3y", H3Y), ("h8m", H8M)] {
        let problem = parse(input);
        let config = PdrConfig::default();
        assert_eq!(
            crate::engines::validate_external_invariant_model(&problem, &empty(), &config).ok(),
            Some(false),
            "{name}: an empty model must not validate an UNSAFE problem"
        );
        assert_eq!(
            crate::engines::external_invariant_model_excludes_error(&problem, &empty(), &config)
                .ok(),
            Some(false),
            "{name}: an empty model must not discharge an UNSAFE problem's query"
        );
    }
    let safe = parse(H3_SAFE);
    assert_eq!(
        crate::engines::validate_external_invariant_model(&safe, &empty(), &PdrConfig::default())
            .ok(),
        Some(true),
        "the independent check must still admit a genuinely safe empty model"
    );
}

/// Counterfactual: record that acyclic BMC "proved" an UNSAFE problem, as a
/// lying engine would. The pre-fix validator consulted that record (or re-ran
/// the engine that wrote it) and returned `Ok(true)`.
#[test]
#[timeout(120_000)]
fn a_lying_bmc_proof_does_not_validate_an_empty_model() {
    let unsafe_problem = unsafe_with_private_names("LyingBmc");
    crate::acyclic_cert_cache::record_acyclic_bmc_safe(&unsafe_problem, usize::MAX);
    assert_eq!(
        crate::acyclic_cert_cache::lookup_acyclic_bmc_safe(&unsafe_problem),
        Some(usize::MAX)
    );
    assert_eq!(
        crate::engines::validate_external_invariant_model(
            &unsafe_problem,
            &empty(),
            &PdrConfig::default()
        )
        .ok(),
        Some(false),
        "the empty-model validator must not take the engine's word for it"
    );
    assert_eq!(
        crate::engines::chc_safe_replay_obligations(&unsafe_problem, &empty())
            .ok()
            .map(|obligations| obligations.is_empty()),
        None,
        "certificate export must not treat the engine's claim as a discharged proof"
    );
}

/// Counterfactual: a fabricated empty-model acyclic label on an UNSAFE
/// problem is demoted at the finalize gate; the same label on the safe twin
/// is admitted. The datatype pair is the finalize test's fixture before and
/// after its reachable `o = none` query was corrected.
#[test]
#[timeout(240_000)]
fn the_finalize_gate_rechecks_empty_model_acyclic_evidence() {
    let option = |query: &str| {
        format!(
            "(set-logic HORN)
(declare-datatypes ((Opt 0)) (((none) (some (val Int)))))
(declare-fun P (Opt) Bool)
(declare-fun Q (Opt) Bool)
(assert (forall ((o Opt)) (=> (= o none) (P o))))
(assert (forall ((o Opt)) (=> (P o) (Q o))))
(assert (forall ((o Opt)) (=> (and (Q o) (= o {query})) false)))
(check-sat)
"
        )
    };
    let (option_unsafe, option_safe) = (option("none"), option("(some 0)"));
    for evidence in [
        ValidationEvidence::ScalarAcyclicBmcExhaustive { max_depth: 3 },
        ValidationEvidence::CheckedQueryOnlyDischarge { query_count: 1 },
    ] {
        for (input, admitted) in [
            (H3Y, false),
            (H3_SAFE, true),
            (option_unsafe.as_str(), false),
            (option_safe.as_str(), true),
        ] {
            let adaptive = AdaptivePortfolio::new(parse(input), AdaptiveConfig::test_default());
            let result =
                adaptive.finalize_verified_result(PortfolioResult::Safe(empty()), evidence.clone());
            assert_eq!(
                matches!(result, VerifiedChcResult::Safe(_)),
                admitted,
                "{evidence:?} on {input}: got {result:?}"
            );
        }
    }
}

/// Counterfactual for Fix V1 (`final_safe_verdict_reproved_on_original`): a
/// BMC re-proof that says `Safe` is admitted only when the engine-free check
/// agrees, inside the re-proof's own deadline. The end-to-end re-proof never
/// accepts the repros either.
#[test]
#[timeout(240_000)]
fn fix_v1_admits_a_bmc_reproof_only_with_the_independent_check() {
    for (name, input, admitted) in [
        ("h3y", H3Y, false),
        ("h8m", H8M, false),
        ("h3-safe", H3_SAFE, true),
    ] {
        let adaptive = AdaptivePortfolio::new(parse(input), AdaptiveConfig::test_default());
        let deadline = Instant::now() + Duration::from_secs(20);
        assert_eq!(
            adaptive.final_safe_reproof_admitted(&PortfolioResult::Safe(empty()), deadline, None),
            admitted,
            "{name}: a BMC `Safe` re-proof must be admitted iff the problem is safe"
        );
        assert!(
            !adaptive.final_safe_reproof_admitted(&PortfolioResult::Unknown, deadline, None),
            "{name}: nothing is admitted without the BMC re-proof"
        );
        assert!(
            !adaptive.final_safe_reproof_admitted(
                &PortfolioResult::Safe(empty()),
                Instant::now(),
                None
            ),
            "{name}: a spent re-proof budget leaves nothing for the check"
        );
    }
    for (name, input) in [("h3", H3), ("h8", H8)] {
        let adaptive = AdaptivePortfolio::new(parse(input), AdaptiveConfig::test_default());
        assert!(
            !adaptive.final_safe_verdict_reproved_on_original(Some(Duration::from_secs(10))),
            "{name}: Fix V1 re-proved an UNSAFE problem"
        );
    }
}

/// The route MODEL_CHECKER_CONSUMER calls (`AdaptiveConfig::with_budget`, `strict_proofs =
/// true`, `solve_proof_run_with_budget_report`): on 938ec0327 `H3`/`H8` came
/// back `Safe` with `accepted_as_proof = true`.
#[test]
#[timeout(300_000)]
fn the_in_process_strict_route_never_accepts_the_repros_as_safe() {
    for (name, input, unsafe_expected) in [
        ("h3", H3, false),
        ("h8", H8, false),
        ("h3y", H3Y, true),
        ("h8m", H8M, true),
    ] {
        let mut problem = parse(input);
        problem.expand_nullary_fail_queries(false);
        let mut config = AdaptiveConfig::with_budget(Duration::from_secs(30), false);
        config.strict_proofs = true;
        let report = AdaptivePortfolio::new(problem, config).solve_proof_run_with_budget_report();
        let run = report.proof_run();
        assert!(
            !matches!(run.result(), VerifiedChcResult::Safe(_)),
            "{name}: UNSAFE problem accepted as SAFE (accepted_as_proof={})",
            run.accepted_as_proof()
        );
        if unsafe_expected {
            assert!(
                matches!(run.result(), VerifiedChcResult::Unsafe(_)),
                "{name}: control must stay UNSAFE, got {}",
                run.result()
            );
        }
    }
}

/// The proof-grade PDR entry's acyclic prepass admits BMC's certificate only
/// after the independent check. A recorded "BMC proved it" for an UNSAFE
/// problem makes the prepass certificate say `Safe` without running BMC; it
/// is not accepted as proof, whatever order the tests run in. The safe twin
/// keeps its SAFE.
#[test]
#[timeout(300_000)]
fn the_pdr_proof_prepass_rechecks_the_acyclic_certificate() {
    let config = || PdrConfig {
        solve_timeout: Some(Duration::from_secs(20)),
        ..PdrConfig::default()
    };
    let lying = unsafe_with_private_names("LyingPdr");
    crate::acyclic_cert_cache::record_acyclic_bmc_safe(&lying, usize::MAX);
    let run = crate::engines::solve_pdr_proof(lying, config()).unwrap();
    assert!(
        !matches!(run.result(), VerifiedChcResult::Safe(_)),
        "proof-grade PDR accepted a recorded BMC claim for an UNSAFE problem: {}",
        run.result()
    );
    for (name, input) in [("h3", H3), ("h8", H8)] {
        let run = crate::engines::solve_pdr_proof(parse(input), config()).unwrap();
        assert!(
            !matches!(run.result(), VerifiedChcResult::Safe(_)),
            "{name}: proof-grade PDR accepted an UNSAFE problem as SAFE"
        );
    }
    let run = crate::engines::solve_pdr_proof(parse(H3_SAFE), config()).unwrap();
    assert!(
        matches!(run.result(), VerifiedChcResult::Safe(_)),
        "safe twin lost its SAFE: {}",
        run.result()
    );
}
