// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::executor::model::unknown_candidate::{CandidateModelPolicy, Z3SolverPath};
use ay_frontend::parse;

/// A satisfiable query ay answers `unknown` on, with a candidate model kept
/// for `(get-model)`: the injectivity of `I` makes `Poly` infinite, which the
/// ground search does not see.
const UNKNOWN_QUERY: &str = "
(declare-sort Poly 0)
(declare-fun I (Int) Poly)
(declare-fun %I (Poly) Int)
(assert (forall ((x Int)) (! (= x (%I (I x))) :pattern ((I x)))))
(push)
(declare-const a Int)
(declare-const L0 Bool)
(declare-const L1 Bool)
(assert (<= (%I (I a)) 0))
(assert (not (and (=> L1 (< (%I (I a)) 1)) (=> L0 (> (%I (I a)) 0)))))
(check-sat)
";

fn run(exec: &mut Executor, script: &str) -> Vec<String> {
    let commands = parse(script).expect("valid SMT-LIB");
    exec.execute_all(&commands).expect("commands execute")
}

/// Spend `units` of search work on this thread, as split-loop rounds do.
fn spend(units: u64) {
    for _ in 0..units {
        ay_core::resource::work().note_round_trip();
    }
}

/// A publishing executor that has just answered `unknown` and kept a
/// candidate model.
fn answered_unknown() -> Executor {
    let mut exec = Executor::new();
    exec.set_candidate_model_policy(CandidateModelPolicy::PublishAfterUnknown);
    let outputs = run(&mut exec, UNKNOWN_QUERY);
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unknown"),
        "the fixture must answer unknown, or these tests prove nothing"
    );
    exec
}

/// What a client can read after the answer.
fn published(exec: &mut Executor) -> (Option<UnknownReason>, Option<String>, String) {
    let model = run(exec, "(get-model)").pop().unwrap_or_default();
    assert!(
        model.contains("(define-fun L0 () Bool true)"),
        "the fixture keeps a candidate that names the failing assertion: {model}"
    );
    (
        exec.unknown_reason(),
        exec.unknown_detail().map(str::to_owned),
        model,
    )
}

/// A retry body that does what a cut solve does: it spends `units`, asks the
/// executor's own stop poll, drops the candidates that stood and ends
/// `Unknown`. Returns whether the poll said stop.
fn search_for(exec: &mut Executor, units: u64) -> bool {
    spend(units);
    let stopped = exec.should_abort_theory_loop();
    if !stopped {
        exec.record_unknown_from_origin(UnknownOrigin::EmatchingRoundBudget);
    }
    exec.unknown_candidate
        .begin_check(Z3SolverPath::Incremental);
    exec.unknown_candidate
        .finish_check(Some(&SolveResult::Unknown));
    stopped
}

#[test]
fn the_allowance_follows_the_work_before_it_and_has_a_floor() {
    assert_eq!(RetryAllowance::UNBOUNDED.units(), None);
    assert_eq!(
        RetryAllowance::after_work_of(0).units(),
        Some(RETRY_WORK_FLOOR),
        "a pass that ended unknown for free still leaves the retry its floor"
    );
    let work = RETRY_WORK_FLOOR * 40;
    assert_eq!(
        RetryAllowance::after_work_of(work).units(),
        Some(work * RETRY_WORK_FACTOR)
    );
    assert_eq!(
        RetryAllowance::after_work_of(u64::MAX).units(),
        Some(u64::MAX)
    );
}

#[test]
fn a_retry_out_of_work_leaves_the_unknown_that_stood() {
    let mut exec = answered_unknown();
    let before = published(&mut exec);

    let mut stopped = false;
    let result = exec
        .retry_within(RetryAllowance(Some(3)), |exec| {
            stopped = search_for(exec, 3);
            Ok(SolveResult::Unknown)
        })
        .expect("the retry returns");

    assert!(
        stopped,
        "the executor's stop poll must see the spent allowance"
    );
    assert!(matches!(result, SolveResult::Unknown));
    assert_eq!(
        published(&mut exec),
        before,
        "reason, detail and candidate model are the ones that stood before the retry"
    );
    assert_eq!(exec.statistics().get_int(RETRIES_OUT_OF_WORK), Some(1));
    assert!(
        !exec.should_abort_theory_loop(),
        "the ceiling ends with the retry"
    );
}

/// The twin of the test above: one unit less, and the retry's own `Unknown`
/// is the answer, as before allowances existed.
#[test]
fn a_retry_one_unit_inside_its_allowance_keeps_its_own_unknown() {
    let mut exec = answered_unknown();
    let before = published(&mut exec);

    let mut stopped = true;
    let result = exec
        .retry_within(RetryAllowance(Some(3)), |exec| {
            stopped = search_for(exec, 2);
            Ok(SolveResult::Unknown)
        })
        .expect("the retry returns");

    assert!(!stopped, "two of three units leave the retry running");
    assert!(matches!(result, SolveResult::Unknown));
    assert_eq!(
        exec.last_unknown_origin,
        Some(UnknownOrigin::EmatchingRoundBudget),
        "the retry ended by itself, so its reason is the published one"
    );
    assert_ne!(exec.last_unknown_reason, before.0);
    assert_eq!(exec.statistics().get_int(RETRIES_OUT_OF_WORK), None);
}

#[test]
fn a_verdict_is_never_replaced_by_the_standing_unknown() {
    for verdict in [SolveResult::Sat, SolveResult::unsat()] {
        let mut exec = answered_unknown();
        let result = exec
            .retry_within(RetryAllowance(Some(3)), |_| {
                spend(5);
                Ok(verdict.clone())
            })
            .expect("the retry returns");
        assert_eq!(
            std::mem::discriminant(&result),
            std::mem::discriminant(&verdict),
            "a retry that answers keeps its answer whatever it spent"
        );
        assert_eq!(exec.statistics().get_int(RETRIES_OUT_OF_WORK), None);
    }
}

#[test]
fn an_unbounded_retry_is_never_out_of_work() {
    let mut exec = answered_unknown();
    let mut stopped = true;
    let result = exec
        .retry_within(RetryAllowance::UNBOUNDED, |exec| {
            stopped = search_for(exec, 10_000);
            Ok(SolveResult::Unknown)
        })
        .expect("the retry returns");
    assert!(!stopped);
    assert!(matches!(result, SolveResult::Unknown));
    assert_eq!(
        exec.last_unknown_origin,
        Some(UnknownOrigin::EmatchingRoundBudget)
    );
}

#[test]
fn the_ceiling_ends_with_a_retry_that_panics() {
    let mut exec = answered_unknown();
    let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        exec.retry_within(RetryAllowance(Some(1)), |_| {
            spend(2);
            assert!(ay_core::resource::work_ceiling_reached());
            panic!("test: panic inside a retry");
        })
    }));
    assert!(unwound.is_err());
    assert!(!ay_core::resource::work_ceiling_reached());
    assert!(!exec.should_abort_theory_loop());
}
