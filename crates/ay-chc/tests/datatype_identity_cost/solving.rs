// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! R26 original-source solving, separate from the parent module's identity tests.
//!
//! Source: model-checker-consumer/docs/ay-asks/2026-10-01-datatype-sort-cost-follows-leaf-count,
//! unchanged at model-checker-consumer c7aa0bef2511571fe41b24a8e2aca184ec3b1431. The original
//! k10 file must be Unsafe, with a witness independently replayed on ORIGINAL
//! datatype clauses. Unknown is failure, not a successful bounded refusal.
//!
//! The ask records historical 20s runs but grants no current whole-run budget.
//! These tests choose a 20s DIAGNOSTIC envelope per case, including source
//! identity, parsing, solving, native ground replay and cleanup. They do not
//! establish complete O(k) work accounting or consumer acceptance. The compact
//! evidence route must preserve complete shared datatype values, publish a
//! source-bound artifact and freshly replay it without expanding a value tree.
//!
//! A fixed GuardTree node and explicit stop callback retain the original owner;
//! public duration APIs get only its remainder, and the linked cancellation
//! timer is never renewed. Native `ground_checks_unsafe` has no progress
//! parameter: opaque validation can overrun between checks, so this is NOT a
//! hard in-process return-time/RSS guarantee. Run the compiled tests serially
//! under the shared external process guard with a 4GiB envelope. The 1GiB
//! portfolio setting below bounds term stores, not total process memory.

use ay_chc::{
    AdaptiveConfig, AdaptivePortfolio, CancellationGuard, CancellationToken, ChcParser, ChcProblem,
    ChcSort, Counterexample, VerifiedChcResult,
};
use ay_core::resource::{
    current_check_stop, current_guard, enter_check_stop, CheckStop, ChildSpec, DeadlineSource,
    Guard, NodeLabel,
};
use ay_core::time::Instant;
use sha2::{Digest, Sha256};
use std::sync::{Arc, Mutex};
use std::time::Duration;

const ORIGINAL_K10: &str =
    include_str!("../fixtures/model_checker_consumer_struct_dag_datatype_k10.smt2");
const K10_SHA256: &str = "555712d96a47f700d3621b3a8fbe725904fb3e71bfc4362d8f5dd4018bf1cc24";
const K4_SHA256: &str = "98f8545336437e9563153417ffee503dc2351e197789486ed927c181e585aa93";
const DIAGNOSTIC_BUDGET: Duration = Duration::from_secs(20);
const TERM_MEMORY_BYTES: usize = 1024 * 1024 * 1024;
static SERIAL: Mutex<()> = Mutex::new(());

#[path = "solving/portable.rs"]
mod portable;

struct Owner {
    started: Instant,
    deadline: Instant,
    cancellation: CancellationToken,
    timer: CancellationGuard,
    guard: Guard,
    stop: CheckStop,
}

impl Owner {
    fn new() -> Self {
        let started = Instant::now();
        let deadline = started + DIAGNOSTIC_BUDGET;
        let cancellation = CancellationToken::new();
        let timer = cancellation.cancel_after(deadline.saturating_duration_since(Instant::now()));
        let spec = ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Fixed(deadline));
        let guard = current_guard().map_or_else(
            || Guard::root_child(spec.clone()),
            |parent| parent.child(spec.clone()),
        );
        let previous = current_check_stop().expect("capture original caller stop");
        let observed_guard = guard.clone();
        let observed_token = cancellation.clone();
        let stop = Arc::new(move || {
            if observed_token.is_cancelled()
                || observed_guard.exhausted().is_some()
                || previous.as_ref().is_some_and(|stop| stop())
            {
                observed_token.cancel();
                true
            } else {
                false
            }
        });
        Self {
            started,
            deadline,
            cancellation,
            timer,
            guard,
            stop,
        }
    }

    fn check(&self, phase: &str) {
        assert!(
            !(self.stop)(),
            "R26 diagnostic original owner stopped during {phase}"
        );
    }

    fn config(&self) -> AdaptiveConfig {
        self.check("configuration");
        let remaining = self.deadline.saturating_duration_since(Instant::now());
        assert!(
            !remaining.is_zero(),
            "zero must never mean an unlimited solve"
        );
        let mut config =
            AdaptiveConfig::with_budget(remaining, false).with_memory_budget(TERM_MEMORY_BYTES);
        config.strict_proofs = true;
        config.require_ground_unsafe_trace = true;
        config
    }

    fn remaining(&self) -> Duration {
        self.check("remaining original grant");
        let remaining = self.deadline.saturating_duration_since(Instant::now());
        assert!(!remaining.is_zero(), "never renew the original grant");
        remaining
    }

    fn finish(self, k: usize) {
        drop(self.timer); // Wake and join, including when the test unwinds.
        assert!(
            !(self.stop)(),
            "R26 diagnostic original owner stopped during cleanup"
        );
        eprintln!(
            "R26 k={k}: original Unsafe replayed; diagnostic whole-case={:?}, \
             observed GuardTree ticks={} (NOT a complete O(k) work census)",
            self.started.elapsed(),
            self.guard.ledger_ticks()
        );
    }
}

fn assert_source_shape(problem: &ChcProblem, k: usize) {
    assert_eq!(problem.datatype_defs().len(), k);
    assert_eq!(problem.predicates().len(), 3);
    for name in ["bb0", "bb1"] {
        let predicate = problem
            .get_predicate_by_name(name)
            .expect("original relation");
        assert_eq!(
            predicate.arg_sorts.len(),
            1,
            "original datatype column, not flattened leaves"
        );
        assert!(
            matches!(&predicate.arg_sorts[0], ChcSort::Datatype { name, .. } if name == &format!("D{k}"))
        );
    }
}

fn replay_original_and_safe_neighbor(
    witness: &Counterexample,
    original: &ChcProblem,
    input: &str,
    owner: &Owner,
) {
    owner.check("independent original ground replay");
    assert!(
        matches!(witness.ground_checks_unsafe(original), Ok(true)),
        "actual returned witness must independently ground-replay on original datatype clauses"
    );
    owner.check("original ground replay completion");
    // A disconnected/flattened trace must not silently certify a different
    // source. Only this NEGATIVE control changes the body, making error dead.
    let guard = "(and (bb1 bb1_v0)";
    assert_eq!(input.matches(guard).count(), 1);
    let safe_input = input.replacen(guard, "(and false (bb1 bb1_v0)", 1);
    let safe = ChcParser::parse(&safe_input).expect("well-typed unreachable-error neighbor");
    assert_ne!(
        safe.normalized_input_sha256(),
        original.normalized_input_sha256()
    );
    assert!(
        !matches!(witness.ground_checks_unsafe(&safe), Ok(true)),
        "the original witness must not ground-replay on the safe changed source"
    );
    drop(safe);
    drop(safe_input);
    owner.check("negative source-control cleanup");
}

fn solve_original(k: usize, source: impl FnOnce() -> String, identity: Option<(usize, &str)>) {
    let _serial = SERIAL.lock().expect("serialize datatype diagnostic cases");
    let owner = Owner::new();
    {
        let _entered = owner.guard.enter();
        let _stop = enter_check_stop(Arc::clone(&owner.stop));
        let input = source();
        let sha256 = format!("{:x}", Sha256::digest(input.as_bytes()));
        if let Some((size, expected)) = identity {
            assert_eq!((input.len(), sha256.as_str()), (size, expected));
        }
        assert_eq!(
            input,
            super::struct_dag_smt2(k),
            "the original generator semantics stay intact"
        );
        let original = ChcParser::parse(&input).expect("original datatype query parses");
        assert_source_shape(&original, k);
        let original_identity = original.normalized_input_sha256();
        owner.check("source admission and identity");
        eprintln!(
            "R26 k={k}: source bytes={}, sha256={sha256}; 20s diagnostic, not consumer acceptance",
            input.len()
        );
        let portfolio = AdaptivePortfolio::new_for_solve_with_cancellation(
            original.clone(),
            owner.config(),
            &owner.cancellation,
        );
        let report = portfolio.solve_proof_run_with_budget_report();
        let run = report.proof_run();
        eprintln!(
            "R26 k={k}: result={}, solve={:?}",
            run.result(),
            report.budget_report().total_elapsed
        );
        owner.check("production solve and proof metadata");
        assert_eq!(run.problem().normalized_input_sha256(), original_identity);
        let VerifiedChcResult::Unsafe(verified) = run.result() else {
            panic!(
                "R26 k={k} requires actual Unsafe; Unknown/Safe is failure: {}",
                run.result()
            );
        };
        replay_original_and_safe_neighbor(verified.counterexample(), &original, &input, &owner);
        portable::replay(run, &original, k, &owner);
        owner.check("completed source replay");
        drop(report);
        drop(portfolio);
        drop(original_identity);
        drop(original);
        drop(input);
        owner.check("query/result/portfolio cleanup");
    }
    owner.finish(k);
}

#[test]
fn original_k10_requires_unsafe_and_original_clause_replay() {
    solve_original(10, || ORIGINAL_K10.to_owned(), Some((896, K10_SHA256)));
}

#[test]
fn original_k4_generator_requires_unsafe_and_original_clause_replay() {
    solve_original(4, || super::struct_dag_smt2(4), Some((533, K4_SHA256)));
}

#[test]
fn generated_k2_requires_unsafe_and_original_clause_replay() {
    solve_original(2, || super::struct_dag_smt2(2), None);
}

#[test]
fn generated_k16_requires_complete_compact_original_evidence() {
    solve_original(16, || super::struct_dag_smt2(16), None);
}

#[test]
fn generated_k32_requires_complete_compact_original_evidence() {
    solve_original(32, || super::struct_dag_smt2(32), None);
}
