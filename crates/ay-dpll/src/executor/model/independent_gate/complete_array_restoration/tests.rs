// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

use ay_core::resource::enter_check_stop;
use ay_core::time::Instant;
use ay_core::{Sort, TermData, TermId};
use ay_frontend::parse;

use super::*;

mod native;

const UNIFORM: &str = "(declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
 (assert (= a ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x09)))
 (assert (forall ((i (_ BitVec 64))) (= (select a i) #x09)))";

fn loaded(source: &str, end: Instant) -> Executor {
    let mut exec = Executor::new();
    exec.set_term_memory_limit(Some(128 * 1024 * 1024));
    exec.set_deadline(Some(end));
    let commands = parse(source).expect("complete original source");
    assert!(exec
        .execute_all(&commands)
        .expect("elaboration only")
        .is_empty());
    exec.begin_external_decision_query(false);
    exec.set_deadline(Some(end));
    let mut model = Model::empty();
    exec.install_functional_array_candidate(&mut model);
    assert!(
        model.functional_arrays.is_some(),
        "actual complete producer DATA"
    );
    exec.last_model = Some(model);
    assert!(exec.last_result.is_none());
    exec
}

fn universal(exec: &Executor) -> TermId {
    let mut pending = exec.ctx.assertions.clone();
    while let Some(term) = pending.pop() {
        if matches!(exec.ctx.terms.get(term), TermData::Forall(..)) {
            return term;
        }
        pending.extend(exec.ctx.terms.children(term));
    }
    panic!("original universal")
}

fn app_args(exec: &Executor, term: TermId) -> Vec<TermId> {
    let TermData::App(_, args) = exec.ctx.terms.get(term) else {
        panic!("application")
    };
    args.clone()
}

#[test]
fn exact_uniform_arming_is_paid_but_is_not_a_sat_grant() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let exec = loaded(UNIFORM, end);
    let model = exec.last_model.as_ref().expect("same model");
    let before = model.functional_work_left();
    assert!(exec.complete_array_restoration_candidate(universal(&exec)));
    assert!(
        model.functional_work_left() < before,
        "same retained counter paid recognition"
    );
    assert!(exec.last_result.is_none());
    assert!(
        exec.last_sat_certificate.is_none(),
        "arming cannot mint a certificate"
    );
    assert!(Instant::now() < end);
}

#[test]
fn malformed_indexed_equality_and_triggered_forall_do_not_arm() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(UNIFORM, end);
    let root = universal(&exec);
    let TermData::Forall(vars, body, _) = exec.ctx.terms.get(root).clone() else {
        panic!("forall")
    };
    let TermData::App(_, args) = exec.ctx.terms.get(body).clone() else {
        panic!("equality")
    };
    let malformed = exec
        .ctx
        .terms
        .mk_app(Symbol::indexed("=", vec![7]), args, Sort::Bool);
    let malformed = exec.ctx.terms.mk_forall(vars.clone(), malformed);
    let patterned = exec
        .ctx
        .terms
        .mk_forall_with_triggers(vars, body, vec![vec![body]]);
    assert!(!exec.complete_array_restoration_candidate(malformed));
    assert!(!exec.complete_array_restoration_candidate(patterned));
    exec.last_model.as_mut().expect("same model").projection_ufs =
        crate::executor::model::projection_uf::ProjectionUfModel::from_test_definitions([(
            Symbol::named("projected"),
            vec![Sort::Bool],
            Sort::Bool,
            0,
        )])
        .expect("typed fault-injection model");
    assert!(
        !exec.complete_array_restoration_candidate(root),
        "projection-bearing model is outside this slice"
    );
    assert!(exec.last_result.is_none());
    assert!(Instant::now() < end);
}

#[test]
fn conditional_alternating_and_live_int_roots_keep_the_old_refusal() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(UNIFORM, end);
    let root = universal(&exec);
    let condition = exec.ctx.terms.mk_var("conditional", Sort::Bool);
    let true_term = exec.ctx.terms.mk_bool(true);
    let conditional = exec.ctx.terms.mk_ite(condition, root, true_term);
    let j = exec.ctx.terms.mk_var("j", Sort::Int);
    let zero = exec.ctx.terms.mk_int(0.into());
    let live_j = exec.ctx.terms.mk_eq(j, zero);
    let mixed = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [root, live_j], Sort::Bool);
    let alternating = exec
        .ctx
        .terms
        .mk_exists(vec![("j".into(), Sort::Int)], mixed);
    let x = exec.ctx.terms.mk_var("x", Sort::Int);
    let c = exec.ctx.terms.mk_var("c", Sort::Int);
    let equal = exec.ctx.terms.mk_eq(x, c);
    let live_int = exec
        .ctx
        .terms
        .mk_forall(vec![("x".into(), Sort::Int)], equal);
    for other in [conditional, alternating, live_int] {
        assert!(!exec.complete_array_restoration_candidate(other));
        assert!(!exec.quantified_gate_restoration_candidate(other));
    }
    assert!(Instant::now() < end);
}

#[test]
fn missing_complete_array_and_stale_query_cannot_arm() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(UNIFORM, end);
    let root = universal(&exec);
    let model = exec.last_model.take().expect("original model");
    exec.last_model = Some(Model::empty());
    assert!(!exec.complete_array_restoration_candidate(root));
    exec.last_model = Some(model);
    let changed = exec.ctx.terms.mk_bool(true);
    exec.ctx.assertions.push(changed);
    assert!(!exec.complete_array_restoration_candidate(root));
    assert!(exec.last_result.is_none());
    assert!(Instant::now() < end);
}

#[test]
fn original_raw_refusal_stays_terminal_after_reset_and_new_frame() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(UNIFORM, end);
    let root = universal(&exec);
    let raw = Arc::new(AtomicBool::new(false));
    exec.set_solve_controls(Some(Arc::clone(&raw)), Some(end));
    assert!(exec.complete_array_restoration_candidate(root));
    raw.store(true, Ordering::Release);
    assert!(!exec.complete_array_restoration_candidate(root));
    raw.store(false, Ordering::Release);
    exec.begin_subset_evaluation_attempt();
    assert!(!exec.complete_array_restoration_candidate(root));
    let model = exec.last_model.as_ref().expect("same model");
    assert_eq!(model.functional_work_left(), 0);
    assert!(model.charge_functional_array_work(&exec, 0).is_err());
    assert!(Instant::now() < end);
}

#[test]
fn false_quantified_sibling_cannot_be_filtered_by_the_new_arm() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(
        &format!(
            "{UNIFORM}
      (assert (forall ((j (_ BitVec 64))) (= (select a j) #x08)))"
        ),
        end,
    );
    assert!(exec.complete_array_restoration_candidate(universal(&exec)));
    assert!(
        !exec.quantified_model_gate_confirms_current_assertions(),
        "every quantified sibling must Confirmed, not just the arming leaf"
    );
    assert!(exec.last_sat_certificate.is_none());
    assert!(Instant::now() < end);
}

#[test]
fn one_short_recognition_work_is_sticky_without_an_extra_grant() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let exec = loaded(UNIFORM, end);
    let root = universal(&exec);
    let model = exec.last_model.as_ref().expect("same retained owner");
    // The first call also pays the one-time entry-stamp walk that source
    // validation memoizes per arena snapshot; measure the steady per-call
    // recognition cost so "one short" is short of the work actually needed.
    assert!(exec.complete_array_restoration_candidate(root));
    let before = model.functional_work_left();
    assert!(exec.complete_array_restoration_candidate(root));
    let needed = before - model.functional_work_left();
    assert!(needed > 1);
    let left = model.functional_work_left();
    model
        .charge_functional_array_work(&exec, left - needed + 1)
        .expect("leave one short");
    assert!(!exec.complete_array_restoration_candidate(root));
    assert!(model.charge_functional_array_work(&exec, 0).is_err());
    assert!(Instant::now() < end);
}

#[test]
fn tightened_deadline_refusal_stays_terminal_after_restoring_the_original_end() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(UNIFORM, end);
    let root = universal(&exec);
    assert!(exec.complete_array_restoration_candidate(root));
    exec.set_deadline(Some(Instant::now()));
    assert!(!exec.complete_array_restoration_candidate(root));
    exec.set_deadline(Some(end));
    exec.begin_subset_evaluation_attempt();
    assert!(!exec.complete_array_restoration_candidate(root));
    let model = exec.last_model.as_ref().expect("same retained owner");
    assert!(model.charge_functional_array_work(&exec, 0).is_err());
    assert_eq!(model.functional_work_left(), 0);
    assert!(Instant::now() < end);
}

#[test]
fn exact_copy_arms_all_captures_and_missing_unchosen_source_refuses() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let source = include_str!("tests/copy.smt2")
        .strip_suffix("(check-sat)\n")
        .expect("query suffix");
    let mut exec = loaded(source, end);
    let root = universal(&exec);
    assert!(exec.complete_array_restoration_candidate(root));
    let TermData::Forall(vars, body, _) = exec.ctx.terms.get(root).clone() else {
        panic!("forall")
    };
    let TermData::Ite(condition, positive, negative) = exec.ctx.terms.get(body).clone() else {
        panic!("normalized range equality")
    };
    let equal = app_args(&exec, positive);
    let frame_equal = app_args(&exec, negative);
    let target = equal
        .iter()
        .copied()
        .find(|term| frame_equal.contains(term))
        .expect("shared target");
    let source_read = equal
        .iter()
        .copied()
        .find(|&term| term != target)
        .expect("source read");
    let read = app_args(&exec, source_read);
    let array_sort = exec.ctx.terms.sort(read[0]).clone();
    let missing = exec.ctx.terms.mk_var("uncaptured_array", array_sort);
    let unbound =
        exec.ctx
            .terms
            .mk_app(Symbol::named("select"), [missing, read[1]], Sort::bitvec(8));
    let guards = app_args(&exec, condition);
    let high = guards
        .iter()
        .copied()
        .find(|&term| {
            matches!(exec.ctx.terms.get(term),
        TermData::App(Symbol::Named(name), _) if name == "bvult")
        })
        .expect("upper");
    let low = guards
        .iter()
        .copied()
        .find(|&term| term != high)
        .expect("lower");
    let upper = app_args(&exec, high);
    let zero = exec.ctx.terms.mk_bitvec(0.into(), 64);
    let empty_upper = exec
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), [upper[0], zero], Sort::Bool);
    let empty = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [low, empty_upper], Sort::Bool);
    let changed = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [target, unbound], Sort::Bool);
    let body = exec.ctx.terms.mk_ite_raw(empty, changed, negative);
    let hidden = exec.ctx.terms.mk_forall(vars, body);
    assert!(
        !exec.complete_array_restoration_candidate(hidden),
        "empty arm cannot hide missing complete DATA"
    );
    assert!(exec.last_result.is_none());
    assert!(Instant::now() < end);
}
