// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::{Symbol, TermStore};
use ay_frontend::parse;
use ay_model_check::{confirm_completed_model, GateVerdict};

use super::work_counter::REFUSED;
use super::*;
use crate::executor::model::independent_gate::IndependentModelView;
use crate::executor::model::EvalValue;
use crate::executor_types::UnknownOrigin;

const DECLARATIONS: &str = "
 (declare-fun d () (Array (_ BitVec 64) (_ BitVec 8)))
 (declare-fun s () (Array (_ BitVec 64) (_ BitVec 8)))
 (declare-fun w () (Array (_ BitVec 64) (_ BitVec 8)))";

const DEFINITION: &str = "
 (assert (= w (lambda ((i (_ BitVec 64)))
   (ite (and (bvule (_ bv1 64) i) (bvult i (_ bv1152921504606846976 64)))
        (select s (bvsub i (_ bv1 64))) (select d i)))))";

fn prepared(extra: &str) -> Executor {
    let commands =
        parse(&format!("{DECLARATIONS}{DEFINITION}{extra}")).expect("original lambda grammar");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("elaborate without solving");
    exec
}

fn variable(exec: &Executor, name: &str) -> TermId {
    exec.ctx
        .symbol_info(name)
        .and_then(|info| info.term)
        .expect("declared variable")
}

fn installed(exec: &Executor) -> Model {
    let mut model = Model::empty();
    exec.install_functional_array_candidate(&mut model);
    assert!(
        model.functional_arrays.is_some(),
        "actual compact constructor route"
    );
    model
}

fn confirm(exec: &Executor, model: &Model) -> GateVerdict {
    let roots = match exec.independent_gate_query_roots() {
        Ok(roots) => roots,
        Err(origin) => {
            return GateVerdict::CannotConfirm {
                reason: format!("original query roots unavailable: {origin:?}"),
            }
        }
    };
    let view = IndependentModelView::new(exec, model);
    confirm_completed_model(&exec.ctx.terms, &view, &roots)
}

#[test]
fn actual_lambda_candidate_validates_all_original_roots_and_prints_one_complete_model() {
    let exec = prepared(
        "(assert (= (select d (_ bv0 64)) (_ bv7 8)))
        (assert (= (select s (_ bv0 64)) (_ bv9 8)))
        (assert (= (select w (_ bv0 64)) (_ bv7 8)))
        (assert (= (select w (_ bv1 64)) (_ bv9 8)))",
    );
    let model = installed(&exec);
    assert!(matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
    for root in exec.independent_gate_query_roots().unwrap() {
        assert_eq!(exec.evaluate_term(&model, root), EvalValue::Bool(true));
    }
    let output = exec
        .functional_array_render(&model, variable(&exec, "w"))
        .expect("owned rendering")
        .expect("complete function");
    assert!(output.contains("lambda"));
    assert!(output.contains("bv1152921504606846976 64"));
    assert!(output.contains("bv9 8"));
    assert!(output.contains("bv7 8"));
    assert!(output.len() < 2000, "huge range is not enumerated");
}

#[test]
fn original_independent_contradictory_read_is_not_repaired_or_skipped() {
    let exec = prepared(
        "(assert (= (select s (_ bv0 64)) (_ bv9 8)))
        (assert (= (select w (_ bv1 64)) (_ bv7 8)))",
    );
    let model = installed(&exec);
    assert!(matches!(
        confirm(&exec, &model),
        GateVerdict::ModelViolates { .. }
    ));
}

#[test]
fn conflicting_old_source_ground_cells_decline_atomically() {
    let exec = prepared(
        "(assert (= (select s (_ bv0 64)) (_ bv9 8)))
        (assert (= (select s (_ bv0 64)) (_ bv7 8)))",
    );
    let mut model = Model::empty();
    exec.install_functional_array_candidate(&mut model);
    assert!(model.functional_arrays.is_none());
}

#[test]
fn original_alias_source_is_captured_before_destination_changes() {
    let input = format!(
        "{DECLARATIONS}
        (assert (= s d))
        (assert (= (select d (_ bv0 64)) (_ bv7 8)))
        {DEFINITION}
        (assert (= (select w (_ bv1 64)) (_ bv7 8)))"
    );
    let mut exec = Executor::new();
    exec.execute_all(&parse(&input).expect("aliased original"))
        .expect("elaborate");
    let model = installed(&exec);
    assert!(matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
    assert!(model
        .functional_array_value(&exec, variable(&exec, "d"))
        .expect("captured old array")
        .is_some());
}

#[test]
fn cyclic_and_ambiguous_function_definitions_never_install() {
    for extra in [
        "(assert (= s w))",
        "(assert (= w (lambda ((j (_ BitVec 64))) (ite (and (bvule (_ bv2 64) j) (bvult j (_ bv4 64))) (select s (bvsub j (_ bv2 64))) (select d j)))))",
    ] {
        let exec = prepared(extra);
        let mut model = Model::empty();
        exec.install_functional_array_candidate(&mut model);
        assert!(
            model.functional_arrays.is_none(),
            "cyclic/ambiguous definition must fail closed"
        );
    }
}

#[test]
fn changed_query_and_context_refuse_existing_snapshot_including_printing() {
    let mut exec = prepared("");
    let model = installed(&exec);
    let w = variable(&exec, "w");
    exec.execute_all(&parse("(assert false)").expect("additional original root"))
        .expect("source mutation");
    assert!(model.functional_array_value(&exec, w).is_err());
    assert!(exec.functional_array_render(&model, w).is_err());
    assert!(!matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
}

#[test]
fn fresh_term_store_with_same_numeric_ids_is_not_original_source() {
    let mut exec = prepared("");
    let model = installed(&exec);
    let w = variable(&exec, "w");
    let entries = exec
        .ctx
        .terms
        .entries_snapshot_with_progress(&mut |_, _| true)
        .expect("bounded tiny fixture copy");
    let (t, f) = exec.ctx.terms.boolean_constant_ids();
    exec.ctx.terms = TermStore::from_entries(entries, t, f, 0);
    assert!(
        model.functional_array_value(&exec, w).is_err(),
        "fresh private entry stamps cannot replay the retained model"
    );
}

#[test]
fn interrupt_deadline_and_memory_origins_withhold_read_render_and_confirmation() {
    for origin in [
        UnknownOrigin::InterruptFlag,
        UnknownOrigin::SolveDeadline,
        UnknownOrigin::MemoryBudget,
    ] {
        let exec = prepared("");
        let model = installed(&exec);
        let w = variable(&exec, "w");
        exec.record_evaluation_stop(origin);
        assert!(model.functional_array_value(&exec, w).is_err());
        assert!(exec.functional_array_render(&model, w).is_err());
        assert!(!matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
    }
}

#[test]
fn cloned_model_shares_one_original_cumulative_work_allowance() {
    let exec = prepared("");
    let model = installed(&exec);
    let clone = model.clone();
    let original = model.functional_arrays.as_ref().expect("installed");
    let copied = clone.functional_arrays.as_ref().expect("retained");
    assert!(Arc::ptr_eq(&original.work_used, &copied.work_used));
    original
        .work_used
        .store(MAX_FUNCTIONAL_WORK, Ordering::Release);
    assert!(clone
        .functional_array_value(&exec, variable(&exec, "w"))
        .is_err());
    assert!(!matches!(confirm(&exec, &clone), GateVerdict::ConfirmedSat));
}

#[test]
fn scoped_array_override_cannot_reuse_unscoped_model_data() {
    let exec = prepared("");
    let model = installed(&exec);
    let w = variable(&exec, "w");
    crate::executor::model::with_scoped_term_evaluation_override_for_test(
        w,
        EvalValue::Unknown,
        || {
            assert!(model.functional_array_value(&exec, w).is_err());
        },
    );
}

#[test]
fn actual_candidate_mutation_revokes_both_private_model_seals() {
    let exec = prepared("");
    let mut model = Model::empty();
    let confirmation = model.seal_quantified_confirmation();
    let grant = model.seal_quantified_grant_model();
    exec.install_functional_array_candidate(&mut model);
    assert!(model.functional_arrays.is_some());
    assert!(!model.carries_quantified_confirmation(&confirmation));
    assert!(!model.carries_quantified_grant_model(&grant));
}

#[test]
fn printed_closed_lambda_reparses_as_the_same_entire_function() {
    let exec = prepared(
        "(assert (= (select d (_ bv0 64)) (_ bv7 8))) (assert (= (select s (_ bv0 64)) (_ bv9 8)))",
    );
    let model = installed(&exec);
    let original = model
        .functional_array_value(&exec, variable(&exec, "w"))
        .expect("original source")
        .expect("owned data");
    let output = exec
        .functional_array_render(&model, variable(&exec, "w"))
        .expect("original owner")
        .expect("closed output");
    let source = format!(
        "(declare-fun replayed () (Array (_ BitVec 64) (_ BitVec 8))) (assert (= replayed {output}))"
    );
    let mut replay = Executor::new();
    replay
        .execute_all(&parse(&source).expect("actual emitted lambda grammar"))
        .expect("fresh independent parser");
    let root = replay.independent_gate_query_roots().unwrap()[0];
    let ay_core::term::TermData::App(_, args) = replay.ctx.terms.get(root) else {
        panic!("original emitted equality")
    };
    let empty = Model::empty();
    let view = IndependentModelView::new(&replay, &empty);
    let reconstructed = Evaluator::new(&replay.ctx.terms, &view)
        .capture_array_snapshot(args[1])
        .expect("closed whole-function parse");
    assert!(original
        .same_function(&reconstructed, &mut 10_000)
        .expect("complete function comparison"));
}

#[test]
fn symbolic_huge_count_and_modular_source_offset_validate_original_scalar_and_array_assertions() {
    let source = format!("{DECLARATIONS}
 (declare-fun lo () (_ BitVec 64)) (declare-fun count () (_ BitVec 64)) (declare-fun source_lo () (_ BitVec 64))
 (assert (= lo (_ bv1 64))) (assert (= count (_ bv1152921504606846976 64))) (assert (= source_lo (_ bv18446744073709551615 64)))
 (assert (= (select s (_ bv18446744073709551615 64)) (_ bv11 8))) (assert (= (select s (_ bv0 64)) (_ bv12 8)))
 (assert (= w (lambda ((i (_ BitVec 64))) (ite (and (bvule lo i) (bvult i (bvadd lo count)))
   (select s (bvadd (bvsub i lo) source_lo)) (select d i)))))
 (assert (= (select w (_ bv1 64)) (_ bv11 8))) (assert (= (select w (_ bv2 64)) (_ bv12 8)))");
    let mut exec = Executor::new();
    exec.execute_all(&parse(&source).expect("symbolic interval and offset"))
        .expect("elaborate original");
    let mut model = Model::empty();
    for (name, value) in [("lo", 1u64), ("count", 1u64 << 60), ("source_lo", u64::MAX)] {
        model.completed_values.insert(
            variable(&exec, name),
            EvalValue::BitVec {
                value: value.into(),
                width: 64,
            },
        );
    }
    exec.install_functional_array_candidate(&mut model);
    assert!(model.functional_arrays.is_some());
    assert!(matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
    for root in exec.independent_gate_query_roots().unwrap() {
        assert_eq!(exec.evaluate_term(&model, root), EvalValue::Bool(true));
    }
}

#[test]
fn zero_and_reversed_unsigned_ranges_validate_full_original_array_equality() {
    for (lo, hi) in [(0, 0), (9, 4), (u64::MAX, 0)] {
        let source = format!(
            "{DECLARATIONS}
 (assert (= (select d (_ bv7 64)) (_ bv42 8)))
 (assert (= w (lambda ((i (_ BitVec 64))) (ite (and (bvule (_ bv{lo} 64) i) (bvult i (_ bv{hi} 64)))
   (select s (bvsub i (_ bv{lo} 64))) (select d i)))))
 (assert (= w d)) (assert (= (select w (_ bv7 64)) (_ bv42 8)))"
        );
        let mut exec = Executor::new();
        exec.execute_all(&parse(&source).expect("empty original range"))
            .expect("elaborate full query");
        let model = installed(&exec);
        assert!(matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
        for root in exec.independent_gate_query_roots().unwrap() {
            assert_eq!(exec.evaluate_term(&model, root), EvalValue::Bool(true));
        }
    }
}

#[test]
fn failed_constructor_retries_debit_the_same_original_attempt_until_exhausted() {
    let exec = prepared("(assert (= s w))");
    let counter = exec.evaluation_attempt().functional_work_counter();
    let mut model = Model::empty();
    exec.install_functional_array_candidate(&mut model);
    assert!(
        model.functional_arrays.is_none(),
        "cycle declines atomically"
    );
    let first = counter.load(Ordering::Acquire);
    assert!(first > 0);
    exec.install_functional_array_candidate(&mut model);
    assert!(
        counter.load(Ordering::Acquire) > first,
        "retry does not replenish"
    );
    counter.store(MAX_FUNCTIONAL_WORK - 1, Ordering::Release);
    exec.install_functional_array_candidate(&mut model);
    assert!(model.functional_arrays.is_none());
    assert_eq!(counter.load(Ordering::Acquire), REFUSED);
    exec.install_functional_array_candidate(&mut model);
    assert!(model.functional_arrays.is_none());
    assert_eq!(counter.load(Ordering::Acquire), REFUSED);
}

#[test]
fn normalized_identity_alias_validates_all_original_ground_reads_and_refuses_conflicts() {
    for value in [42u8, 43] {
        let source = format!(
            "{DECLARATIONS}
            (assert (= w (lambda ((i (_ BitVec 64))) (select d i))))
            (assert (= w d))
            (assert (= (select d (_ bv7 64)) (_ bv42 8)))
            (assert (= (select w (_ bv7 64)) (_ bv{value} 8)))"
        );
        let mut exec = Executor::new();
        exec.execute_all(&parse(&source).expect("original normalized identity"))
            .expect("actual frontend context");
        let mut model = Model::empty();
        exec.install_functional_array_candidate(&mut model);
        if value == 42 {
            assert!(model.functional_arrays.is_some());
            assert!(matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
            for root in exec.independent_gate_query_roots().unwrap() {
                assert_eq!(exec.evaluate_term(&model, root), EvalValue::Bool(true));
            }
        } else {
            assert!(
                model.functional_arrays.is_none(),
                "both alias reads remain mandatory"
            );
        }
    }
}

#[test]
fn normalized_identity_cycles_and_competing_definitions_still_decline_atomically() {
    for definitions in [
        "(assert (= w (lambda ((i (_ BitVec 64))) (select s i))))
         (assert (= s (lambda ((i (_ BitVec 64))) (select w i))))"
            .to_owned(),
        format!("{DEFINITION}(assert (= w (lambda ((i (_ BitVec 64))) (select d i))))"),
    ] {
        let commands = parse(&format!("{DECLARATIONS}{definitions}"))
            .expect("strict original conflicting constructors");
        let mut exec = Executor::new();
        exec.execute_all(&commands).expect("actual source context");
        let mut model = Model::empty();
        exec.install_functional_array_candidate(&mut model);
        assert!(model.functional_arrays.is_none());
    }
}

mod named_values;

mod fill;

mod finite_pins;

#[test]
fn qmc_array_default_preserves_an_existing_functional_owner() {
    let mut exec = prepared("(declare-fun data (Int) (Array Int Int))");
    let mut owned = installed(&exec);
    let before = exec
        .functional_array_render(&owned, variable(&exec, "w"))
        .unwrap();
    let zero = exec.ctx.terms.mk_int(0.into());
    let value = exec.ctx.terms.mk_const_array(Sort::Int, zero);
    let row = (
        Symbol::named("data"),
        vec![Sort::Int],
        Sort::array(Sort::Int, Sort::Int),
        value,
    );
    let mut fresh = Model::empty();
    assert!(exec
        .install_model_check_array_defaults(&mut fresh, vec![row.clone()])
        .is_some());
    assert!(exec
        .install_model_check_array_defaults(&mut owned, vec![row])
        .is_none());
    assert_eq!(
        exec.functional_array_render(&owned, variable(&exec, "w"))
            .unwrap(),
        before
    );
    assert!(owned.certified_const_interp_entries().is_empty());
}

mod periodic;
