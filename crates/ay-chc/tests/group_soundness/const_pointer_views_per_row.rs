// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! model-checker-consumer's exported CHC queries for three harnesses of
//! `const_pointer_read_type_dual.rs` (model-checker-consumer
//! the development design notes),
//! byte for byte:
//!
//! | fixture | sha256 |
//! | --- | --- |
//! | `model_checker_consumer_safe_wide_array_as_bytes.smt2` | `ef31735e…3193` |
//! | `model_checker_consumer_safe_static_bytes.smt2` | `f74e946a…8440` |
//! | `model_checker_consumer_safe_static_wide_as_bytes.smt2` | `93d9e708…89cc7` |
//!
//! All three are safe; z3 answers `unsat` on each. Solved the way model-checker-consumer
//! solves them in process (one `ChcProblem::query_obligations` slice per
//! `error_pN`, the nullary fail query expanded,
//! `AdaptivePortfolio::new_for_solve_with_cancellation`, `strict_proofs`, 30 s
//! per row), ay's independent model gate caught invalid models on the way at
//! d65293086: 8 to 11 on `safe_wide_array_as_bytes`'s `error_p10`, 45 to 51
//! on each static harness's `error_p9` (the count follows the load). Every
//! one was a TPA reachability check over the SingleLoop encoding (Int
//! location flags, BitVec arguments, a BitVec-indexed memory), decided by the
//! `_BV_LIA_INDEP` lanes: the BV lane answered `sat`, the AUFLIA cross-check
//! answered `unknown` because its own validation refused its witness, and the
//! lane then published the BV lane's witness alone, which values no Int term,
//! without the agreement step an AUFLIA `sat` gets (ay-dpll
//! `executor/theories/combined/bv_lia_indep_agreement.rs`).
//!
//! Every row of all three is proved inside its budget since 2026-10-13: the
//! static harnesses' `error_p9` was `unknown` at 30 s until the projection
//! that back-translates the BV-native discharge kept array variables
//! well-sorted (#mbp-sort-correct-substitution, ay-chc `mbp/project.rs`).
//!
//! The gate's catch is counted through the `tracing` event it emits, by a
//! process-wide subscriber: the rest of `group_soundness` emits none (measured
//! on d65293086), and the three tests here run one at a time, so a count is
//! this module's own.

use ay_chc::{
    engines, AdaptiveConfig, AdaptivePortfolio, CancellationToken, ChcParser, ChcProblem,
    PdrConfig, VerifiedChcResult,
};
use ntest::timeout;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

const WIDE_ARRAY_AS_BYTES: &str =
    include_str!("../fixtures/model_checker_consumer_safe_wide_array_as_bytes.smt2");
const STATIC_BYTES: &str =
    include_str!("../fixtures/model_checker_consumer_safe_static_bytes.smt2");
const STATIC_WIDE_AS_BYTES: &str =
    include_str!("../fixtures/model_checker_consumer_safe_static_wide_as_bytes.smt2");

/// model-checker-consumer's per-harness budget for these queries.
const ROW_BUDGET: Duration = Duration::from_secs(30);

/// The message of the `tracing::warn!` that accompanies every
/// `[AY SOUNDNESS GATE] caught an INVALID model` banner.
const GATE_CATCH: &str = "SOUNDNESS GATE caught an invalid model";

static GATE_CATCHES: AtomicU64 = AtomicU64::new(0);

/// Counts the gate's catch events; enables nothing else.
struct GateCatchCounter;

struct MessageIsGateCatch(bool);

impl tracing::field::Visit for MessageIsGateCatch {
    fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn std::fmt::Debug) {
        if field.name() == "message" && format!("{value:?}").contains(GATE_CATCH) {
            self.0 = true;
        }
    }
}

impl tracing::Subscriber for GateCatchCounter {
    fn enabled(&self, metadata: &tracing::Metadata<'_>) -> bool {
        metadata.is_event() && *metadata.level() == tracing::Level::WARN
    }
    fn new_span(&self, _: &tracing::span::Attributes<'_>) -> tracing::span::Id {
        tracing::span::Id::from_u64(1)
    }
    fn record(&self, _: &tracing::span::Id, _: &tracing::span::Record<'_>) {}
    fn record_follows_from(&self, _: &tracing::span::Id, _: &tracing::span::Id) {}
    fn event(&self, event: &tracing::Event<'_>) {
        let mut visitor = MessageIsGateCatch(false);
        event.record(&mut visitor);
        if visitor.0 {
            GATE_CATCHES.fetch_add(1, Ordering::SeqCst);
        }
    }
    fn enter(&self, _: &tracing::span::Id) {}
    fn exit(&self, _: &tracing::span::Id) {}
}

/// Installs the counter as the process's global subscriber, once, and holds
/// the module's tests to one at a time. A counter that could not be installed
/// would count nothing, so that is a failure, not a pass.
fn exclusive_gate_counter() -> std::sync::MutexGuard<'static, ()> {
    static INSTALLED: OnceLock<bool> = OnceLock::new();
    static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());
    let installed = *INSTALLED
        .get_or_init(|| tracing::subscriber::set_global_default(GateCatchCounter).is_ok());
    assert!(
        installed,
        "another global tracing subscriber is installed; the gate's catches cannot be counted"
    );
    ONE_AT_A_TIME
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

fn rows(query: &str) -> Vec<(String, ChcProblem)> {
    let problem = ChcParser::parse(query).expect("the exported query parses");
    let obligations = problem
        .query_obligations()
        .expect("the exported query slices");
    assert_eq!(obligations.len(), 11, "one obligation per error_pN");
    obligations
        .into_iter()
        .map(|obligation| {
            let (id, mut problem) = obligation.into_parts();
            problem.expand_nullary_fail_queries(false);
            (id.label().to_string(), problem)
        })
        .collect()
}

struct Row {
    label: String,
    result: VerifiedChcResult,
    elapsed: Duration,
    gate_catches: u64,
}

/// Solves every row of `query` the way model-checker-consumer does, and re-validates every
/// `Safe` model against its row. No row may be `Unsafe`: every query here is
/// safe.
fn solve_rows(query: &str) -> Vec<Row> {
    rows(query)
        .into_iter()
        .map(|(label, problem)| {
            let mut config = AdaptiveConfig::with_budget(ROW_BUDGET, false);
            config.strict_proofs = true;
            let parent = CancellationToken::new();
            let before = GATE_CATCHES.load(Ordering::SeqCst);
            let started = Instant::now();
            let report = AdaptivePortfolio::new_for_solve_with_cancellation(
                problem.clone(),
                config,
                &parent,
            )
            .solve_proof_run_with_budget_report();
            let elapsed = started.elapsed();
            let gate_catches = GATE_CATCHES.load(Ordering::SeqCst) - before;
            let result = report.proof_run().result().clone();
            match &result {
                VerifiedChcResult::Safe(invariant) => {
                    let validated = engines::validate_external_invariant_model(
                        &problem,
                        invariant.model(),
                        &PdrConfig::default(),
                    )
                    .expect("validation runs");
                    assert!(validated, "{label}: the Safe model must validate");
                }
                VerifiedChcResult::Unsafe(_) => {
                    panic!("{label}: the query is safe (z3: unsat), got {result:?}")
                }
                // `Unknown`, and any variant added later: no claim to check.
                _ => {}
            }
            Row {
                label,
                result,
                elapsed,
                gate_catches,
            }
        })
        .collect()
}

fn assert_no_gate_catch(rows: &[Row]) {
    let caught: Vec<String> = rows
        .iter()
        .filter(|row| row.gate_catches > 0)
        .map(|row| format!("{} ({})", row.label, row.gate_catches))
        .collect();
    assert!(
        caught.is_empty(),
        "the independent model gate caught invalid models on rows {caught:?}"
    );
}

/// Every row proved inside its budget, with a model that validates, and no
/// invalid model on the way.
fn assert_every_row_proved_in_budget(rows: &[Row]) {
    assert_no_gate_catch(rows);
    for row in rows {
        assert!(
            matches!(row.result, VerifiedChcResult::Safe(_)),
            "{}: the query is safe, got {:?} after {:?}",
            row.label,
            row.result,
            row.elapsed
        );
        assert!(
            row.elapsed < ROW_BUDGET,
            "{}: proved after {:?}, past the {ROW_BUDGET:?} budget",
            row.label,
            row.elapsed
        );
    }
}

#[test]
#[timeout(600_000)]
fn wide_array_as_bytes_rows_are_proved_with_no_invalid_model() {
    let _counter = exclusive_gate_counter();
    assert_every_row_proved_in_budget(&solve_rows(WIDE_ARRAY_AS_BYTES));
}

/// model-checker-consumer does not seed the static these read through a byte view, so it
/// fails the harness closed whatever ay answers; ay's part is to answer each
/// row soundly, with no invalid model on the way, and to prove it.
///
/// `error_p9` of both stayed `unknown` at 30 s until 2026-10-13
/// (#mbp-sort-correct-substitution): the BV-native preprocessing discharged
/// every clause, but the clause inliner's back-translation projected the
/// memory array away through a model-value fallback that answered the `Int` 0
/// for an array, so the translated proof read `(select 0 k)` and its
/// validation could only answer `UNKNOWN`.
#[test]
#[timeout(600_000)]
fn static_bytes_rows_are_proved_with_no_invalid_model() {
    let _counter = exclusive_gate_counter();
    assert_every_row_proved_in_budget(&solve_rows(STATIC_BYTES));
}

#[test]
#[timeout(600_000)]
fn static_wide_as_bytes_rows_are_proved_with_no_invalid_model() {
    let _counter = exclusive_gate_counter();
    assert_every_row_proved_in_budget(&solve_rows(STATIC_WIDE_AS_BYTES));
}
