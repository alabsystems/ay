// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Candidate-only fixtures except the explicitly native one-conjunction check.

use super::*;
use ay_core::time::Instant;
use ay_core::Symbol;
use std::sync::atomic::AtomicBool;
use std::time::Duration;

const ZERO: &str = "((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)";
const NINE: &str = "((as const (Array (_ BitVec 64) (_ BitVec 8))) #x09)";

fn finite_prepared(body: &str) -> Executor {
    let mut exec = Executor::new();
    exec.execute_all(&parse(&format!("{DECLARATIONS}{body}")).expect("finite original source"))
        .expect("elaboration only");
    exec
}

fn snapshot(exec: &Executor, model: &Model, name: &str) -> Arc<ArraySnapshot> {
    model
        .functional_array_value(exec, variable(exec, name))
        .expect("same original source")
        .expect("complete selected constructor")
}

fn cell(array: &ArraySnapshot, index: u64, expected: u8) {
    let value = array
        .read(&ModelValue::bitvec(index.into(), 64), &mut 100_000)
        .expect("exact complete read");
    assert!(matches!(value, ModelValue::BitVec { width: 8, value } if value == expected.into()));
}

fn conjunction() -> String {
    format!(
        "(assert (and
        (= d (store (store {ZERO} (_ bv0 64) #x07) (_ bv0 64) #x09))
        (= s d)
        (= w (store s (_ bv18446744073709551615 64) #xff))
        (= (select d (_ bv0 64)) #x09)
        (= (select w (_ bv0 64)) #x09)
        (= (select w (_ bv18446744073709551615 64)) #xff)
        (= (select w (_ bv1 64)) #x00)))"
    )
}

#[test]
fn finite_only_nested_one_conjunction_owns_full_stores_aliases_and_max_key() {
    let exec = finite_prepared(&conjunction());
    let model = installed(&exec);
    assert!(matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
    for root in exec.independent_gate_query_roots().unwrap() {
        assert_eq!(exec.evaluate_term(&model, root), EvalValue::Bool(true));
    }
    cell(&snapshot(&exec, &model, "w"), 0, 9);
    cell(&snapshot(&exec, &model, "w"), u64::MAX, 255);
    cell(&snapshot(&exec, &model, "w"), 1, 0);
    assert!(Arc::ptr_eq(
        &snapshot(&exec, &model, "d"),
        &snapshot(&exec, &model, "s")
    ));
    assert!(!exec
        .functional_array_render(&model, variable(&exec, "w"))
        .expect("source")
        .expect("full finite function")
        .contains("lambda"));
    assert!(
        exec.last_result.is_none(),
        "candidate DATA cannot publish a verdict"
    );
}

#[test]
#[ntest::timeout(30000)]
fn native_finite_pins_one_original_conjunction_requires_checked_sat_with_one_end() {
    use crate::api::{Logic, Solver};
    let end = Instant::now() + Duration::from_secs(20);
    let mut solver = Solver::try_new(Logic::All).expect("natural native solver");
    solver.set_term_memory_limit(Some(128 * 1024 * 1024));
    solver
        .parse_smtlib2(&format!("{DECLARATIONS}{}", conjunction()))
        .expect("original complete finite pins");
    assert!(Instant::now() < end);
    solver.set_timeout(Some(end.saturating_duration_since(Instant::now())));
    let result = solver.check_sat_interruptible_internal_query(move || Instant::now() >= end);
    assert!(
        result.is_sat(),
        "fresh full native conjunction, not a DATA shortcut"
    );
    assert!(result.was_model_validated());
    assert!(result.has_sat_emission_witness());
    drop(solver);
    assert!(
        Instant::now() < end,
        "cleanup remains inside the original end"
    );
}

#[test]
fn contradictory_finite_constructor_pins_decline_before_installing_any_entry() {
    let exec = finite_prepared(&format!("(assert (and (= w {ZERO}) (= w {NINE})))"));
    let mut model = Model::empty();
    exec.install_functional_array_candidate(&mut model);
    assert!(model.functional_arrays.is_none());
}

#[test]
fn original_wrong_finite_read_is_neither_repaired_nor_sat_proxied() {
    let exec = finite_prepared(&format!(
        "(assert (and (= w {ZERO})
        (= (select w (_ bv0 64)) #x09)))"
    ));
    let model = installed(&exec);
    assert!(matches!(
        confirm(&exec, &model),
        GateVerdict::ModelViolates { .. }
    ));
    assert_eq!(
        exec.evaluate_term(&model, exec.independent_gate_query_roots().unwrap()[0]),
        EvalValue::Bool(false)
    );
}

#[test]
fn finite_wrong_default_whole_equality_cannot_be_confirmed_from_sat_bits() {
    let exec = finite_prepared(&format!("(assert (and (= w {ZERO}) (= s {NINE}) (= w s)))"));
    let mut model = Model::empty();
    exec.install_functional_array_candidate(&mut model);
    assert!(
        model.functional_arrays.is_none(),
        "incompatible hard alias definitions"
    );
    assert!(!matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
}

#[test]
fn finite_constructor_backedges_decline_atomically_without_base_defaults() {
    for body in [
        "(assert (= w (store w (_ bv0 64) #x09)))",
        "(assert (and (= w (store s (_ bv0 64) #x09)) (= s (store w (_ bv1 64) #x07))))",
    ] {
        let exec = finite_prepared(body);
        let mut model = Model::empty();
        exec.install_functional_array_candidate(&mut model);
        assert!(model.functional_arrays.is_none());
    }
}

#[test]
fn scalar_read_captures_resolve_only_from_the_same_complete_hard_pin_batch() {
    let exec = finite_prepared(&format!(
        "(assert (and (= d {NINE})
        (= w ((as const (Array (_ BitVec 64) (_ BitVec 8))) (select d (_ bv0 64))))
        (= (select w (_ bv18446744073709551615 64)) #x09)))"
    ));
    let model = installed(&exec);
    assert!(matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
    cell(&snapshot(&exec, &model, "w"), u64::MAX, 9);
}

#[test]
fn finite_pins_never_invent_an_unpinned_base_or_scalar_array_capture() {
    for body in [
        "(assert (= w (store d (_ bv0 64) #x09)))",
        "(assert (= w ((as const (Array (_ BitVec 64) (_ BitVec 8))) (select d (_ bv0 64)))))",
    ] {
        let exec = finite_prepared(body);
        let mut model = Model::empty();
        exec.install_functional_array_candidate(&mut model);
        assert!(model.functional_arrays.is_none());
    }
}

#[test]
fn conditional_definitions_bare_aliases_and_read_only_classes_do_not_activate_route() {
    for body in [
        format!("(declare-const flag Bool) (assert (or flag (= w {NINE})))"),
        "(assert (= w d))".to_owned(),
        "(assert (= (select w (_ bv0 64)) #x09))".to_owned(),
    ] {
        let exec = finite_prepared(&body);
        let mut model = Model::empty();
        exec.install_functional_array_candidate(&mut model);
        assert!(model.functional_arrays.is_none());
    }
}

#[test]
fn malformed_finite_occurrence_sorts_and_children_refuse_before_capture() {
    for bad in 0..5 {
        let mut exec = finite_prepared("");
        let w = variable(&exec, "w");
        let sort = exec.ctx.terms.sort(w).clone();
        let byte = exec.ctx.terms.mk_bitvec(9.into(), 8);
        let index = exec
            .ctx
            .terms
            .mk_bitvec(0.into(), if bad == 1 { 32 } else { 64 });
        let other = exec.ctx.terms.mk_bitvec(9.into(), 16);
        let base = exec
            .ctx
            .terms
            .mk_app(Symbol::named("const-array"), [byte], sort.clone());
        let rhs = match bad {
            0 => exec
                .ctx
                .terms
                .mk_app(Symbol::named("const-array"), [other], sort.clone()),
            1 => exec
                .ctx
                .terms
                .mk_app(Symbol::named("store"), [base, index, byte], sort.clone()),
            2 => exec
                .ctx
                .terms
                .mk_app(Symbol::named("store"), [base, index, other], sort.clone()),
            3 => exec.ctx.terms.mk_app(
                Symbol::named("store"),
                [TermId(u32::MAX), index, byte],
                sort.clone(),
            ),
            _ => {
                let scalar = exec.ctx.terms.mk_app(
                    Symbol::named("bvnot"),
                    [TermId(u32::MAX)],
                    Sort::bitvec(8),
                );
                let rhs =
                    exec.ctx
                        .terms
                        .mk_app(Symbol::named("const-array"), [scalar], sort.clone());
                assert!(
                    exec.ctx
                        .terms
                        .children(rhs)
                        .iter()
                        .all(|child| (child.0 as usize) < exec.ctx.terms.len()),
                    "live immediate operands must not hide a dead grandchild"
                );
                rhs
            }
        };
        let equality = exec
            .ctx
            .terms
            .mk_app(Symbol::named("="), [w, rhs], Sort::Bool);
        exec.ctx.assertions.push(equality);
        let mut model = Model::empty();
        exec.install_functional_array_candidate(&mut model);
        assert!(model.functional_arrays.is_none(), "bad occurrence {bad}");
    }
}

#[test]
fn finite_bool_and_bv128_cells_preserve_exact_sort_and_complete_payload() {
    for (cell_sort, datum) in [
        ("Bool", "true"),
        (
            "(_ BitVec 128)",
            "(_ bv340282366920938463463374607431768211455 128)",
        ),
    ] {
        let source = format!(
            "(declare-fun a () (Array (_ BitVec 64) {cell_sort}))
            (assert (and (= a ((as const (Array (_ BitVec 64) {cell_sort})) {datum}))
                (= (select a (_ bv18446744073709551615 64)) {datum})))"
        );
        let exec = finite_prepared(&source);
        let model = installed(&exec);
        assert!(matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
        let value = snapshot(&exec, &model, "a")
            .read(&ModelValue::bitvec(u64::MAX.into(), 64), &mut 100_000)
            .expect("complete max-key read");
        if cell_sort == "Bool" {
            assert!(matches!(value, ModelValue::Bool(true)));
        } else {
            assert!(matches!(value, ModelValue::BitVec { width: 128, value }
                if value == num_bigint::BigInt::from(u128::MAX)));
        }
    }
    for width in [0, 129] {
        let mut exec = finite_prepared("");
        let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(width));
        let variable = exec.ctx.terms.mk_var("outside-finite-slice", sort.clone());
        let datum = exec.ctx.terms.mk_bitvec(0.into(), 129);
        let rhs = exec
            .ctx
            .terms
            .mk_app(Symbol::named("const-array"), [datum], sort);
        let equality = exec
            .ctx
            .terms
            .mk_app(Symbol::named("="), [variable, rhs], Sort::Bool);
        exec.ctx.assertions.push(equality);
        let mut model = Model::empty();
        exec.install_functional_array_candidate(&mut model);
        assert!(
            model.functional_arrays.is_none(),
            "outside finite cell width {width}"
        );
    }
}

#[test]
fn projected_constructor_and_unchosen_projected_scalar_never_get_literal_credit() {
    use crate::executor::model::projection_uf::ProjectionUfModel;
    let exec = finite_prepared(&format!("(assert (= w (store {ZERO} (_ bv0 64) #x09)))"));
    let mut model = Model::empty();
    let array = exec.ctx.terms.sort(variable(&exec, "w")).clone();
    model.projection_ufs = ProjectionUfModel::from_test_definitions([(
        Symbol::named("store"),
        vec![array.clone(), Sort::bitvec(64), Sort::bitvec(8)],
        array,
        0,
    )])
    .expect("fault-injected checked signature");
    exec.install_functional_array_candidate(&mut model);
    assert!(model.functional_arrays.is_none());

    let exec = finite_prepared(
        "(declare-const flag Bool)
        (declare-fun pick ((_ BitVec 8)) (_ BitVec 8))
        (assert (= w ((as const (Array (_ BitVec 64) (_ BitVec 8)))
            (ite flag #x09 (pick #x07)))))",
    );
    let mut model = Model::empty();
    model
        .completed_values
        .insert(variable(&exec, "flag"), EvalValue::Bool(true));
    let info = exec.ctx.symbol_info("pick").expect("original declaration");
    let identity = exec.ctx.symbol_identity_name("pick", info).to_owned();
    model.projection_ufs = ProjectionUfModel::from_test_definitions([(
        Symbol::named(identity),
        vec![Sort::bitvec(8)],
        Sort::bitvec(8),
        0,
    )])
    .expect("exact scalar projection fixture");
    exec.install_functional_array_candidate(&mut model);
    assert!(
        model.functional_arrays.is_none(),
        "whole raw constructor scanned before chosen arm"
    );
}

#[test]
fn unchosen_nested_array_capture_cannot_open_an_unowned_default_grant() {
    let exec = finite_prepared(
        "(declare-const flag Bool)
        (assert (= w ((as const (Array (_ BitVec 64) (_ BitVec 8)))
            (ite flag #x09 (select d (_ bv0 64))))))",
    );
    let mut model = Model::empty();
    model
        .completed_values
        .insert(variable(&exec, "flag"), EvalValue::Bool(true));
    exec.install_functional_array_candidate(&mut model);
    assert!(
        model.functional_arrays.is_none(),
        "all raw array captures require hard definitions"
    );
}

#[test]
fn finite_capture_clones_and_retries_share_the_original_exhausted_work_counter() {
    let exec = finite_prepared(&format!("(assert (= w {NINE}))"));
    let model = installed(&exec);
    let copied = model.clone();
    let used = exec.evaluation_attempt().functional_work_counter();
    assert!(Arc::ptr_eq(
        &used,
        &model.functional_arrays.as_ref().expect("owned").work_used
    ));
    used.store(MAX_FUNCTIONAL_WORK, Ordering::Release);
    assert!(copied
        .functional_array_value(&exec, variable(&exec, "w"))
        .is_err());
    let mut retry = Model::empty();
    exec.install_functional_array_candidate(&mut retry);
    assert!(retry.functional_arrays.is_none());
    assert_eq!(
        used.load(Ordering::Acquire),
        super::super::work_counter::REFUSED
    );
}

#[test]
fn original_interrupt_observation_cannot_reset_into_finite_read_or_install_authority() {
    let mut exec = finite_prepared(&format!("(assert (= w {NINE}))"));
    let model = installed(&exec);
    let flag = Arc::new(AtomicBool::new(true));
    exec.set_interrupt(Arc::clone(&flag));
    assert!(exec.poll_evaluation_stop().is_err());
    flag.store(false, Ordering::Release);
    assert!(model
        .functional_array_value(&exec, variable(&exec, "w"))
        .is_err());
    let mut retry = Model::empty();
    exec.install_functional_array_candidate(&mut retry);
    assert!(retry.functional_arrays.is_none());
    assert!(!matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
}

#[test]
fn finite_source_query_and_fresh_store_stamps_cannot_rebind_owned_data() {
    let mut exec = finite_prepared(&format!("(assert (= w {NINE}))"));
    let model = installed(&exec);
    let w = variable(&exec, "w");
    let entries = exec
        .ctx
        .terms
        .entries_snapshot_with_progress(&mut |_, _| true)
        .expect("bounded tiny fixture");
    let (t, f) = exec.ctx.terms.boolean_constant_ids();
    exec.ctx.terms = TermStore::from_entries(entries, t, f, 0);
    assert!(model.functional_array_value(&exec, w).is_err());
    let mut exec = finite_prepared(&format!("(assert (= w {NINE}))"));
    let model = installed(&exec);
    exec.execute_all(&parse("(assert false)").expect("changed original"))
        .expect("new root");
    assert!(!matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
}
