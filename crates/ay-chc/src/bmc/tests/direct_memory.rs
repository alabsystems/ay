// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Direct public BMC memory-boundary controls. Positive runs perform native
//! search and original-source replay; the runner still supplies its RSS guard.

use super::*;
use crate::smt::SmtContext;
use crate::{AdaptiveConfig, AdaptivePortfolio, VerifiedChcResult};
use std::time::Duration;

const SOURCE: &str = r#"(set-logic HORN)
(declare-fun P ((_ BitVec 8)) Bool)
(assert (P #x07))
(assert (forall ((x (_ BitVec 8))) (=> (and (P x) (= x #x07)) false)))
(check-sat)
"#;
const MEMORY: usize = 64 * 1024 * 1024;

fn problem() -> ChcProblem {
    let problem = ChcParser::parse(SOURCE).unwrap();
    problem.validate().unwrap();
    assert_eq!(problem.clauses().len(), 2);
    problem
}

fn config() -> BmcConfig {
    BmcConfig {
        prefer_exact_acyclic_first: true,
        ..BmcConfig::default()
            .with_memory_budget(MEMORY)
            .with_max_depth(2)
            .with_time_budget(Duration::from_secs(10))
            .with_per_depth_timeout(Duration::from_secs(10))
            .with_acyclic_safe(true)
    }
}

#[test]
fn memory_setting_is_optional_cloned_and_preserved_by_config_builders() {
    for config in [
        BmcConfig::default(),
        BmcConfig::cross_check(),
        BmcConfig::with_engine_config(2, false, None),
    ] {
        assert_eq!(config.memory_budget, None);
        for limit in [0, 1, MEMORY] {
            let configured = config.clone().with_memory_budget(limit);
            assert_eq!(configured.clone().memory_budget, Some(limit));
            assert_eq!(configured.with_max_depth(3).memory_budget, Some(limit));
        }
    }
}

#[test]
fn zero_explicit_adaptive_and_inherited_caps_refuse_public_direct_entries() {
    let _outer = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let explicit = config().with_memory_budget(0);
    assert!(matches!(
        BmcSolver::new(problem(), explicit.clone()).solve(),
        ChcEngineResult::Unknown
    ));
    assert!(crate::engines::solve_bmc_only(problem(), explicit.clone()).is_unknown());
    assert!(
        crate::engines::solve_bmc_only_from_str(SOURCE, explicit.clone())
            .unwrap()
            .is_unknown()
    );
    assert!(
        crate::engines::solve_bmc_only_from_str("(invalid unmatched", explicit.clone())
            .unwrap()
            .is_unknown(),
        "zero refuses before parsing"
    );
    assert!(
        matches!(
            crate::engines::solve_bmc_proof_from_str("(invalid unmatched", explicit.clone()),
            Err(crate::ChcError::TermMemoryBudgetExhausted)
        ),
        "a stopped source parser cannot fabricate an empty source-bound proof run"
    );
    let proof = crate::engines::solve_bmc_proof(problem(), explicit.clone()).unwrap();
    assert!(proof.result().is_unknown());
    assert!(!proof.accepted_as_proof());
    assert!(!proof.metadata().trust_full_verifier_admissible());
    let replay = crate::engines::solve_bmc_proof_with_checked_replay(
        problem(),
        explicit,
        Duration::from_secs(10),
    )
    .unwrap();
    assert!(replay.result().is_unknown());
    assert!(!replay.metadata().trust_full_verifier_admissible());
    let adaptive =
        AdaptivePortfolio::new(problem(), AdaptiveConfig::default().with_memory_budget(0));
    assert!(adaptive.solve_bmc_only(config()).is_unknown());
    {
        let _inner = SmtContext::scoped_thread_term_memory_budget(Some(0));
        assert!(crate::engines::solve_bmc_only(problem(), config()).is_unknown());
        let proof = crate::engines::solve_bmc_proof(problem(), config()).unwrap();
        assert!(proof.result().is_unknown());
        assert_eq!(SmtContext::new().term_memory_budget, Some(0));
    }
    assert_eq!(SmtContext::new().term_memory_budget, Some(MEMORY));
}

#[test]
fn cancelled_direct_run_refuses_but_fresh_native_replay_preserves_originals() {
    let _outer = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY * 2));
    let cancelled = CancellationToken::new();
    cancelled.cancel();
    let refused = crate::engines::solve_bmc_proof_with_checked_replay(
        problem(),
        config().with_cancellation(cancelled),
        Duration::from_secs(10),
    )
    .unwrap();
    assert!(refused.result().is_unknown());
    assert!(!refused.metadata().trust_full_verifier_admissible());

    let live = CancellationToken::new();
    let original = problem();
    let run = crate::engines::solve_bmc_proof_with_checked_replay(
        original.clone(),
        config().with_cancellation(live.clone()),
        Duration::from_secs(10),
    )
    .expect("genuine bounded BMC plus checked replay");
    let VerifiedChcResult::Unsafe(counterexample) = run.result() else {
        panic!(
            "the reachable original query must have verified evidence: {}",
            run.result()
        );
    };
    let derivation = counterexample
        .counterexample()
        .ground_derivation
        .as_ref()
        .expect("exact acyclic BMC must retain original ground evidence");
    crate::ground_derivation::validate_ground_derivation(&original, derivation).unwrap();
    crate::ground_derivation::validate_ground_derivation(run.problem(), derivation).unwrap();
    assert!(run.metadata().trust_full_verifier_admissible());
    assert!(
        !live.is_cancelled(),
        "the route may not cancel its embedding caller"
    );
    assert_eq!(SmtContext::new().term_memory_budget, Some(MEMORY * 2));

    let unreachable = ChcParser::parse(&SOURCE.replace("(= x #x07)", "(= x #x08)")).unwrap();
    assert!(
        crate::ground_derivation::validate_ground_derivation(&unreachable, derivation).is_err()
    );
    assert!(
        !crate::engines::solve_bmc_only(unreachable, config()).is_unsafe(),
        "a completed memory scope cannot certify a false original trace"
    );
}

#[test]
fn captured_owner_reaches_raw_and_strict_replay_adapters_without_being_loosened() {
    use crate::bmc::memory::Budget;
    use crate::smt::executor_adapter::{
        smtlib_first_verdict_via_executor_until, smtlib_strict_unsat_cert_via_executor_until,
    };

    const SAT: &str = "(set-logic QF_BV) (declare-const x (_ BitVec 8)) \
        (assert (= x #x07)) (check-sat)";
    const UNSAT: &str = "(set-logic QF_BV) (declare-const x (_ BitVec 8)) \
        (assert (= x #x07)) (assert (not (= x #x07))) (check-sat)";
    let deadline = || ay_core::time::Instant::now() + Duration::from_secs(10);
    let _caller = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY * 2));
    for limit in [0, 1] {
        let captured = Budget::capture(Some(limit), None);
        let _scope = captured.install();
        assert!(
            smtlib_first_verdict_via_executor_until(SAT, deadline(), Some(usize::MAX)).is_none(),
            "an explicit looser replay limit cannot bypass the inherited owner"
        );
        assert!(
            smtlib_strict_unsat_cert_via_executor_until(UNSAT, deadline()).is_none(),
            "strict proof production must obey the same term-memory scope"
        );
    }
    assert_eq!(
        SmtContext::current_thread_term_memory_budget(),
        Some(MEMORY * 2)
    );
    let captured = Budget::capture(Some(MEMORY), None);
    captured
        .run(|| {
            assert_eq!(
                smtlib_first_verdict_via_executor_until(SAT, deadline(), None).as_deref(),
                Some("sat")
            );
            let certificate = smtlib_strict_unsat_cert_via_executor_until(UNSAT, deadline())
                .expect("fresh bounded exact UNSAT replay");
            assert!(matches!(certificate.strict_verdict,
            ay_dpll::api::StrictProofVerdict::Verified(ref quality) if quality.is_complete()));
            assert!(ay_dpll::api::re_check_bundle_strict(&certificate.bundle)
                .unwrap()
                .quality
                .is_complete());
            assert!(smtlib_strict_unsat_cert_via_executor_until(SAT, deadline()).is_none());
        })
        .expect("the captured owner stays live through both real replay paths");
    assert_eq!(
        SmtContext::current_thread_term_memory_budget(),
        Some(MEMORY * 2)
    );
}
