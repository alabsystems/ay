// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::deadline::{current_lane_token, lane_interrupt_flag};
use crate::{ChcParser, PdrConfig};
use std::time::Duration;

const SOURCE: &str =
    "(set-logic HORN) (declare-fun p () Bool) (assert p) (assert (=> p false)) (check-sat)";

fn solver(config: PdrConfig) -> PdrSolver {
    PdrSolver::new(ChcParser::parse(SOURCE).unwrap(), config)
}

#[test]
fn linked_config_and_ambient_cancellation_are_sticky_without_upstream_writes() {
    let config = CancellationToken::new();
    let ambient = CancellationToken::new();
    let raw = Arc::new(AtomicBool::new(false));
    let _scope = ScopedLaneCancellation::install(ambient.clone(), Some(Arc::clone(&raw)));
    let solver = solver(PdrConfig::default().with_cancellation_token(Some(config.clone())));
    let owner = Control::capture(&solver).unwrap();
    assert!(owner.open());
    ambient.cancel();
    assert!(!owner.open());
    ambient.reset();
    assert!(!owner.open());
    assert!(!config.is_cancelled());
    assert!(!raw.load(Ordering::Relaxed));
}

#[test]
fn original_raw_flag_is_retained_after_lane_drop_and_reset() {
    let raw = Arc::new(AtomicBool::new(false));
    let token = CancellationToken::new();
    let lane = ScopedLaneCancellation::install(token, Some(Arc::clone(&raw)));
    let owner = Control::capture(&solver(PdrConfig::default())).unwrap();
    drop(lane);
    raw.store(true, Ordering::Relaxed);
    assert!(!owner.open());
    raw.store(false, Ordering::Relaxed);
    assert!(!owner.open());
}

#[test]
fn shorter_original_ambient_wall_refuses_search_without_a_fresh_duration() {
    let _wall = ScopedSmtDeadline::install_until(Instant::now());
    let mut solver = solver(PdrConfig::default());
    let owner = Control::capture(&solver).unwrap();
    assert!(!owner.open());
    assert!(matches!(solver.solve(), PdrResult::Unknown));
}

/// `inv(0)` and the query `inv(x) /\ x = 0`: Unsafe at once.
const UNSAFE: &str = "(set-logic HORN) (declare-fun inv (Int) Bool) \
    (assert (forall ((x Int)) (=> (= x 0) (inv x)))) \
    (assert (forall ((x Int)) (=> (and (inv x) (= x 0)) false))) (check-sat)";

fn traced_solve(source: &str, config: PdrConfig) -> (PdrResult, Vec<serde_json::Value>) {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("owner.jsonl");
    let mut solver = PdrSolver::new(ChcParser::parse(source).unwrap(), config);
    solver.enable_tla_trace_from_path(path.to_str().unwrap());
    let result = solver.solve();
    let trace = std::fs::read_to_string(&path).unwrap();
    let steps = trace
        .lines()
        .skip(1)
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    (result, steps)
}

fn failure_reasons(steps: &[serde_json::Value]) -> Vec<&str> {
    steps
        .iter()
        .filter_map(|step| step["telemetry"]["failure"]["reason"].as_str())
        .collect()
}

/// Regression (e1dd374c4, on main since 47276a301): a refused owner returned
/// Unknown with no trace step at all, breaking the Unknown trace contract
/// (#4697) that an initially cancelled solve met at the main loop's first poll.
#[test]
fn a_refused_owner_still_records_its_reason_and_terminal_step() {
    let token = CancellationToken::new();
    token.cancel();
    let (result, steps) = traced_solve(
        UNSAFE,
        PdrConfig::default().with_cancellation_token(Some(token)),
    );
    assert!(matches!(result, PdrResult::Unknown));
    assert_eq!(failure_reasons(&steps), ["solve_owner_closed"]);
    let refusal = &steps[steps.len() - 2];
    assert_eq!(refusal["telemetry"]["counters"]["iterations"], 0);
    let terminal = steps.last().unwrap();
    assert_eq!(terminal["action"]["name"], "DeclareUnknown");
    assert_eq!(terminal["state"]["result"]["value"], "Unknown");
}

/// Negative twin: an open owner searches, and its trace names no refusal.
#[test]
fn an_open_owner_records_no_refusal() {
    let (result, steps) = traced_solve(UNSAFE, PdrConfig::default());
    assert!(matches!(result, PdrResult::Unsafe(_)));
    assert!(!failure_reasons(&steps).contains(&"solve_owner_closed"));
    assert_eq!(steps.last().unwrap()["action"]["name"], "DeclareUnsafe");
}

#[test]
fn zero_original_term_cap_refuses_normal_pdr_search() {
    let mut solver = solver(PdrConfig::default().with_memory_budget(Some(0)));
    assert!(matches!(solver.solve(), PdrResult::Unknown));
}

#[test]
fn healthy_none_preserves_token_absence_and_scope_restoration() {
    let original = lane_interrupt_flag();
    let mut solver = solver(PdrConfig::default());
    solver.config.solve_timeout = Some(Duration::from_secs(1));
    let owner = Control::capture(&solver).unwrap();
    assert!(owner.token.is_none());
    let scope = Scope::enter(&mut solver).unwrap();
    assert!(current_lane_token().is_none());
    assert!(!ay_core::resource::check_stop_requested());
    assert!(matches!(
        scope.finish(PdrResult::Safe(crate::pdr::model::InvariantModel::new())),
        PdrResult::Safe(_)
    ));
    assert!(current_lane_token().is_none());
    let restored = lane_interrupt_flag();
    assert!(match (original, restored) {
        (Some(a), Some(b)) => Arc::ptr_eq(&a, &b),
        (None, None) => true,
        _ => false,
    });
}

#[test]
fn post_tls_cleanup_callback_refusal_vetoes_provisional_result() {
    let armed = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&armed);
    let callback = enter_check_stop(Arc::new(move || {
        observed.load(Ordering::Relaxed) && effective_thread_deadline().is_none()
    }));
    let mut solver = solver(PdrConfig::default());
    solver.config.solve_timeout = Some(Duration::from_secs(1));
    let scope = Scope::enter(&mut solver).unwrap();
    armed.store(true, Ordering::Relaxed);
    assert!(effective_thread_deadline().is_some());
    assert!(matches!(
        scope.finish(PdrResult::Safe(crate::pdr::model::InvariantModel::new())),
        PdrResult::Unknown
    ));
    assert!(effective_thread_deadline().is_none());
    drop(callback);
}

#[test]
fn no_explicit_timeout_establishes_one_original_default_end_before_encoding() {
    let mut solver = solver(PdrConfig::default());
    assert!(solver.solve_deadline.is_none());
    let before = Instant::now();
    let scope = Scope::enter(&mut solver).unwrap();
    let end = solver.solve_deadline.unwrap();
    assert!(end > before);
    assert!(end <= Instant::now() + Duration::from_mins(5));
    assert_eq!(scope.owner.deadline, Some(end));
    assert_eq!(solver.smt.current_global_deadline(), Some(end));
    let _ = solver.solve_init();
    assert_eq!(solver.solve_deadline, Some(end));
    let _ = scope.finish(PdrResult::Unknown);
}

#[test]
fn tighter_context_absolute_end_refuses_before_startup_without_replacement() {
    let mut solver = solver(PdrConfig::default());
    let end = Instant::now();
    solver.smt.set_global_solve_deadline(Some(end));
    assert!(Scope::enter(&mut solver).is_none());
    assert_eq!(solver.solve_deadline, Some(end));
    assert_eq!(solver.smt.current_global_deadline(), Some(end));
    assert!(matches!(solver.solve(), PdrResult::Unknown));
    assert_eq!(solver.solve_deadline, Some(end));
}

#[test]
fn child_raw_refusal_survives_reset_and_forbids_retry_and_final_pdr_publication() {
    let mut solver = solver(PdrConfig::default());
    let raw = Arc::new(AtomicBool::new(false));
    let token = CancellationToken::new();
    let _lane = ScopedLaneCancellation::install(token.clone(), Some(Arc::clone(&raw)));
    let scope = Scope::enter(&mut solver).unwrap();
    let x = solver
        .smt
        .terms
        .mk_var("owner_x", ay_core::Sort::bitvec(128));
    let y = solver
        .smt
        .terms
        .mk_var("owner_y", ay_core::Sort::bitvec(128));
    let product = solver.smt.terms.mk_bvmul(vec![x, y]);
    let mut child = ay_bv::BvSolver::new(&solver.smt.terms);
    child.set_interrupt(Arc::clone(&raw));
    assert!(child.inherit_current_encoding_guard());
    assert_eq!(child.ensure_term_bits(x).unwrap().len(), 128);
    assert_eq!(child.ensure_term_bits(y).unwrap().len(), 128);
    raw.store(true, Ordering::Relaxed);
    assert!(child.ensure_term_bits(product).is_none());
    assert!(!child.encoding_complete());
    drop(child);
    raw.store(false, Ordering::Relaxed);
    assert!(!token.is_cancelled());
    assert!(scope.owner.encoding.get().unwrap().was_stopped());
    let mut retry = ay_bv::BvSolver::new(&solver.smt.terms);
    assert!(!retry.inherit_current_encoding_guard());
    drop(retry);
    assert!(matches!(
        scope.finish(PdrResult::Safe(crate::pdr::model::InvariantModel::new())),
        PdrResult::Unknown
    ));
}

#[test]
fn executor_bv_refusal_reaches_original_pdr_root_after_raw_reset() {
    use std::sync::atomic::AtomicUsize;
    let raw = Arc::new(AtomicBool::new(false));
    let child_raw = Arc::new(AtomicBool::new(false));
    let armed = Arc::new(AtomicBool::new(false));
    let count = Arc::new(AtomicUsize::new(0));
    let flag = Arc::clone(&child_raw);
    let enabled = Arc::clone(&armed);
    let polls = Arc::clone(&count);
    let _callback = enter_check_stop(Arc::new(move || {
        if enabled.load(Ordering::Relaxed) && polls.fetch_add(1, Ordering::Relaxed) == 39 {
            flag.store(true, Ordering::Relaxed);
        }
        false
    }));
    let token = CancellationToken::new();
    let _lane = ScopedLaneCancellation::install(token.clone(), Some(Arc::clone(&raw)));
    let mut pdr = solver(PdrConfig::default());
    let scope = Scope::enter(&mut pdr).unwrap();
    let mut executor = ay_dpll::Executor::new();
    let formula = "(set-logic QF_BV) (declare-const x (_ BitVec 128)) (declare-const y (_ BitVec 128)) (assert (= (bvmul x y) x))";
    executor
        .execute_all(&ay_frontend::parse(formula).unwrap())
        .unwrap();
    executor.set_interrupt(Arc::clone(&child_raw));
    armed.store(true, Ordering::Relaxed);
    assert_eq!(
        executor
            .execute_all(&ay_frontend::parse("(check-sat)").unwrap())
            .unwrap(),
        vec!["unknown"]
    );
    assert!(child_raw.load(Ordering::Relaxed));
    assert!(!raw.load(Ordering::Relaxed));
    assert!(scope.owner.encoding.get().unwrap().was_stopped());
    child_raw.store(false, Ordering::Relaxed);
    armed.store(false, Ordering::Relaxed);
    assert!(!token.is_cancelled());
    assert!(matches!(
        scope.finish(PdrResult::Safe(crate::pdr::model::InvariantModel::new())),
        PdrResult::Unknown
    ));
    drop(_lane);
    drop(_callback);
    let mut fresh = solver(PdrConfig::default());
    let scope = Scope::enter(&mut fresh).unwrap();
    assert!(matches!(
        scope.finish(PdrResult::Safe(crate::pdr::model::InvariantModel::new())),
        PdrResult::Safe(_)
    ));
}
