// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::cancellation::CancellationToken;
use crate::ground_derivation::{
    validate_ground_derivation, GroundDerivation, GroundDerivationStep,
};
use crate::lemma_cache::LemmaCache;
use crate::pdr::config::PdrConfig;
use crate::pdr::frame::Lemma;
use crate::pdr::PdrResult;
use crate::{ChcExpr, ChcProblem, ChcSort, ClauseBody, ClauseHead, HornClause};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::{atomic::AtomicBool, Arc};
use std::time::Duration;

mod forward_merge;

fn input() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let fail = problem.declare_predicate("FAIL", vec![]);
    problem.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        p,
        vec![ChcExpr::Int(0)],
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::Int(0)])], None),
        ClauseHead::Predicate(fail, vec![]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(fail, vec![])],
        None,
    )));
    problem
}

fn candidate() -> Counterexample {
    Counterexample::new(vec![]).with_ground_derivation(GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 0,
                env: FxHashMap::default(),
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 1,
                env: FxHashMap::default(),
                premises: vec![0],
            },
        ],
        query_step: 1,
    })
}

fn reordered() -> (PdrSolver, LemmaCache, Counterexample) {
    let cache = LemmaCache::new();
    let mut solver = PdrSolver::new(
        input(),
        PdrConfig {
            preserve_original_clauses: true,
            lemma_cache: Some(cache.clone()),
            verbose: false,
            ..PdrConfig::default()
        },
    );
    assert!(solver.nullary_expansion.is_none());
    // Query, fact, rule: the carried evidence names this transformed order,
    // while the original input still names fact, rule, query.
    solver.problem.clauses_mut().rotate_right(1);
    let ground = GroundDerivation {
        steps: [1, 2, 0]
            .into_iter()
            .enumerate()
            .map(|(index, clause_index)| GroundDerivationStep {
                clause_index,
                env: FxHashMap::default(),
                premises: if index == 0 { vec![] } else { vec![index - 1] },
            })
            .collect(),
        query_step: 2,
    };
    assert_eq!(validate_ground_derivation(&solver.problem, &ground), Ok(()));
    (
        solver,
        cache,
        Counterexample::new(vec![]).with_ground_derivation(ground),
    )
}

#[test]
fn content_reattribution_retains_valid_original_input_evidence_without_nullary_expansion() {
    let (solver, cache, cex) = reordered();
    let PdrResult::Unsafe(cex) = solver.finish_with_result_trace(PdrResult::Unsafe(cex)) else {
        panic!("live original owner should retain content-mapped evidence");
    };
    let ground = cex.ground_derivation.unwrap();
    assert_eq!(
        ground
            .steps
            .iter()
            .map(|step| step.clause_index)
            .collect::<Vec<_>>(),
        vec![0, 1, 2]
    );
    assert_eq!(validate_ground_derivation(&input(), &ground), Ok(()));
    assert!(cache.is_empty());
}

#[test]
fn content_reattribution_observes_mid_mapping_stop_without_fallback_or_export() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    let (solver, _, cex) = reordered();
    let calls = Arc::new(AtomicUsize::new(0));
    let observer = calls.clone();
    let scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        observer.fetch_add(1, Ordering::Relaxed);
        false
    }));
    assert!(matches!(
        solver.finish_with_result_trace(PdrResult::Unsafe(cex)),
        PdrResult::Unsafe(_)
    ));
    let total = calls.load(Ordering::Relaxed);
    drop(scope);
    assert!(total > 4);
    let (solver, cache, cex) = reordered();
    let calls = Arc::new(AtomicUsize::new(0));
    let observer = calls.clone();
    let _scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        observer.fetch_add(1, Ordering::Relaxed) + 1 == total / 2
    }));
    refuses(&solver, &cache, cex);
    assert_eq!(calls.load(Ordering::Relaxed), total / 2);
}

fn prepared(config: PdrConfig) -> (PdrSolver, LemmaCache) {
    let cache = LemmaCache::new();
    let mut solver = PdrSolver::new(
        input(),
        PdrConfig {
            verbose: false,
            lemma_cache: Some(cache.clone()),
            ..config
        },
    );
    assert!(solver.nullary_expansion.is_some());
    let p = solver.problem.lookup_predicate("P").unwrap();
    // Non-trivial scheduling data makes a fresh post-stop export observable.
    solver.frames[1].add_lemma(Lemma::new(p, ChcExpr::Bool(false), 1));
    (solver, cache)
}

fn refuses(solver: &PdrSolver, cache: &LemmaCache, cex: Counterexample) {
    let solves = solver.spacer_stats.smt_solves_total;
    assert!(matches!(
        solver.finish_with_result_trace(PdrResult::Unsafe(cex)),
        PdrResult::Unknown
    ));
    assert!(
        cache.is_empty(),
        "interrupted restatement cannot start lemma export"
    );
    assert_eq!(solver.spacer_stats.smt_solves_total, solves);
}

#[test]
fn accepting_restatement_keeps_the_final_original_input_validation() {
    let (solver, cache) = prepared(PdrConfig::default());
    let PdrResult::Unsafe(cex) = solver.finish_with_result_trace(PdrResult::Unsafe(candidate()))
    else {
        panic!("an accepting owner should retain the valid candidate");
    };
    let ground = cex.ground_derivation.unwrap();
    assert_eq!(ground.steps[ground.query_step].clause_index, 2);
    assert_eq!(validate_ground_derivation(&input(), &ground), Ok(()));
    assert!(cache.is_empty());
}

#[test]
fn cancelled_original_token_is_terminal_unknown_without_export_or_replay() {
    let token = CancellationToken::new();
    let (solver, cache) =
        prepared(PdrConfig::default().with_cancellation_token(Some(token.clone())));
    token.cancel();
    refuses(&solver, &cache, candidate());
}

#[test]
fn upstream_external_token_is_terminal_unknown_without_a_fresh_owner() {
    let parent = CancellationToken::new();
    let config = PdrConfig {
        external_cancellation_token: Some(parent.child()),
        ..PdrConfig::default()
    };
    let (solver, cache) = prepared(config);
    parent.cancel();
    refuses(&solver, &cache, candidate());
}

#[test]
fn spent_original_solve_deadline_refuses_restatement() {
    let (mut solver, cache) = prepared(PdrConfig::default());
    solver.solve_deadline = Some(
        ay_core::time::Instant::now()
            .checked_sub(Duration::from_millis(1))
            .expect("fixture instant supports a one-millisecond offset"),
    );
    refuses(&solver, &cache, candidate());
}

#[test]
fn spent_enclosing_smt_deadline_refuses_restatement() {
    let (solver, cache) = prepared(PdrConfig::default());
    let spent = ay_core::time::Instant::now()
        .checked_sub(Duration::from_millis(1))
        .expect("fixture instant supports a one-millisecond offset");
    let _scope = crate::smt::ScopedSmtDeadline::install_until(spent);
    refuses(&solver, &cache, candidate());
}

#[test]
fn existing_memory_soft_trip_refuses_restatement_without_export() {
    let (solver, cache) = prepared(PdrConfig::default());
    let group = ay_sys::MemoryGroup::new(1024 * 1024, usize::MAX, Arc::new(AtomicBool::new(false)));
    let _scope = ay_sys::enter_memory_group(group);
    ay_sys::charge_current_for_testing(2 * 1024 * 1024);
    refuses(&solver, &cache, candidate());
}

#[test]
fn missing_ground_cannot_turn_an_interrupted_expansion_into_unsafe_fallback() {
    let token = CancellationToken::new();
    let (solver, cache) =
        prepared(PdrConfig::default().with_cancellation_token(Some(token.clone())));
    token.cancel();
    refuses(&solver, &cache, Counterexample::new(vec![]));
}

#[test]
fn ordinary_mapping_rejection_keeps_existing_lost_ground_semantics() {
    let (solver, cache) = prepared(PdrConfig::default());
    let mut cex = candidate();
    cex.ground_derivation.as_mut().unwrap().steps[1].premises = vec![99];
    let PdrResult::Unsafe(cex) = solver.finish_with_result_trace(PdrResult::Unsafe(cex)) else {
        panic!("ordinary rejection is not interruption");
    };
    assert!(cex.ground_derivation.is_none());
    assert!(cache.is_empty());
}

#[test]
fn no_expansion_keeps_the_existing_ordinary_unsafe_finalization() {
    let token = CancellationToken::new();
    let solver = PdrSolver::new(
        ChcProblem::new(),
        PdrConfig::default().with_cancellation_token(Some(token.clone())),
    );
    assert!(solver.nullary_expansion.is_none());
    // Compatibility is preserved under a live original owner, not a stop waiver.
    assert!(!token.is_cancelled());
    assert!(matches!(
        solver.finish_with_result_trace(PdrResult::Unsafe(Counterexample::new(vec![]))),
        PdrResult::Unsafe(_)
    ));
}

#[test]
fn unrelated_unknown_finalization_keeps_its_existing_lemma_export() {
    let (solver, cache) = prepared(PdrConfig::default());
    assert!(matches!(
        solver.finish_with_result_trace(PdrResult::Unknown),
        PdrResult::Unknown
    ));
    assert_eq!(cache.len(), 1);
}

#[test]
fn interrupted_restatement_emits_unknown_not_unsafe_terminal_trace() {
    use ay_sat::TlaTraceable;
    let token = CancellationToken::new();
    let (mut solver, cache) =
        prepared(PdrConfig::default().with_cancellation_token(Some(token.clone())));
    let dir = tempfile::tempdir().unwrap();
    let trace = dir.path().join("restatement.jsonl");
    solver.enable_tla_trace(
        trace.to_str().unwrap(),
        "restatement",
        PdrSolver::tla_variables(),
    );
    token.cancel();
    refuses(&solver, &cache, candidate());
    let contents = std::fs::read_to_string(trace).unwrap();
    let terminal: serde_json::Value =
        serde_json::from_str(contents.lines().last().unwrap()).unwrap();
    assert_eq!(terminal["action"]["name"], "DeclareUnknown");
    assert_eq!(terminal["state"]["result"]["value"], "Unknown");
}

#[test]
fn exact_historical_stopped_nonexpansion_candidate_is_unknown_without_export() {
    let token = CancellationToken::new();
    let cache = LemmaCache::new();
    let solver = PdrSolver::new(
        ChcProblem::new(),
        PdrConfig {
            lemma_cache: Some(cache.clone()),
            ..PdrConfig::default().with_cancellation_token(Some(token.clone()))
        },
    );
    assert!(solver.nullary_expansion.is_none());
    token.cancel();
    refuses(&solver, &cache, Counterexample::new(vec![]));
}

#[test]
fn independent_preclosed_original_interrupt_refuses_without_writing_the_caller() {
    use std::sync::atomic::Ordering;
    let (solver, cache) = prepared(PdrConfig::default());
    let token = CancellationToken::new();
    let flag = Arc::new(AtomicBool::new(true));
    let _lane = crate::smt::ScopedLaneCancellation::install(token.clone(), Some(flag.clone()));
    refuses(&solver, &cache, candidate());
    assert!(flag.load(Ordering::Relaxed));
    assert!(!token.is_cancelled());
}

#[test]
fn observed_original_interrupt_cannot_revive_after_native_validation_and_raw_reset() {
    use std::sync::atomic::Ordering;
    let (solver, cache) = prepared(PdrConfig::default());
    let token = CancellationToken::new();
    let flag = Arc::new(AtomicBool::new(false));
    let _lane = crate::smt::ScopedLaneCancellation::install(token.clone(), Some(flag.clone()));
    let owner = solver.input_restatement_owner();
    let _memory = owner.install_memory();
    let cex = solver.restate_cex_for_input(candidate(), &owner).unwrap();
    assert_eq!(
        validate_ground_derivation(&input(), cex.ground_derivation.as_ref().unwrap()),
        Ok(())
    );
    flag.store(true, Ordering::Relaxed);
    assert!(!owner.open());
    flag.store(false, Ordering::Relaxed);
    assert!(matches!(
        owner.limit_after_cleanup(PdrResult::Unsafe(cex)),
        PdrResult::Unknown
    ));
    assert!(!flag.load(Ordering::Relaxed));
    assert!(!token.is_cancelled());
    assert!(cache.is_empty());
}

#[test]
fn zero_requested_term_cap_is_terminal_even_without_nullary_expansion() {
    let cache = LemmaCache::new();
    let solver = PdrSolver::new(
        ChcProblem::new(),
        PdrConfig {
            lemma_cache: Some(cache.clone()),
            ..PdrConfig::default().with_memory_budget(Some(0))
        },
    );
    assert!(solver.nullary_expansion.is_none());
    refuses(&solver, &cache, Counterexample::new(vec![]));
}

#[test]
fn final_after_cleanup_observation_vetoes_unsafe_without_fresh_export() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    let (solver, cache) = prepared(PdrConfig::default());
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = calls.clone();
    let scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::Relaxed);
        false
    }));
    assert!(matches!(
        solver.finish_with_result_trace(PdrResult::Unsafe(candidate())),
        PdrResult::Unsafe(_)
    ));
    let total = calls.load(Ordering::Relaxed);
    assert!(total > 2);
    drop(scope);
    let (solver, cache2) = prepared(PdrConfig::default());
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = calls.clone();
    let _scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::Relaxed) + 1 == total
    }));
    refuses(&solver, &cache2, candidate());
    assert_eq!(calls.load(Ordering::Relaxed), total);
    assert!(cache.is_empty());
}

#[test]
fn captured_memory_refusal_survives_original_scope_drop_and_healthy_replacement() {
    let (solver, cache) = prepared(PdrConfig::default());
    let group = ay_sys::MemoryGroup::new(1024 * 1024, usize::MAX, Arc::new(AtomicBool::new(false)));
    let scope = ay_sys::enter_memory_group(group);
    let owner = solver.input_restatement_owner();
    assert!(owner.open());
    ay_sys::charge_current_for_testing(2 * 1024 * 1024);
    drop(scope);
    let replacement =
        ay_sys::MemoryGroup::new(usize::MAX, usize::MAX, Arc::new(AtomicBool::new(false)));
    let _replacement = ay_sys::enter_memory_group(replacement);
    assert!(!ay_sys::current_memory_group_soft_tripped());
    assert!(!owner.open());
    assert!(matches!(
        owner.limit_after_cleanup(PdrResult::Unsafe(candidate())),
        PdrResult::Unknown
    ));
    assert!(cache.is_empty());
}

#[test]
fn last_owner_observation_runs_after_temporary_term_scope_restoration() {
    use crate::smt::SmtContext;
    use std::sync::atomic::Ordering;
    let outer_cap = 128 * 1024 * 1024;
    let original_cap = 64 * 1024 * 1024;
    let _outer = SmtContext::scoped_thread_term_memory_budget(Some(outer_cap));
    let (solver, cache) = prepared(PdrConfig::default().with_memory_budget(Some(original_cap)));
    let inside = Arc::new(AtomicBool::new(false));
    let restored = Arc::new(AtomicBool::new(false));
    let inside_poll = inside.clone();
    let restored_poll = restored.clone();
    let _stop = ay_core::resource::enter_check_stop(Arc::new(move || {
        let current = SmtContext::current_thread_term_memory_budget();
        if current == Some(original_cap) {
            inside_poll.store(true, Ordering::Relaxed);
            false
        } else if current == Some(outer_cap) {
            restored_poll.store(true, Ordering::Relaxed);
            true
        } else {
            false
        }
    }));
    // The native input decision succeeds while scoped to the original cap.
    // Only the last poll, after TLS restoration, refuses the returned result.
    refuses(&solver, &cache, candidate());
    assert!(inside.load(Ordering::Relaxed));
    assert!(restored.load(Ordering::Relaxed));
    assert_eq!(
        SmtContext::current_thread_term_memory_budget(),
        Some(outer_cap)
    );
}
