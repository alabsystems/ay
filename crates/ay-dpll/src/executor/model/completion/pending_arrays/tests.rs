// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::model::tests::empty_model;
use std::ops::ControlFlow;
use std::sync::Arc;

fn pairs(connected: bool) -> (Executor, Model, [TermId; 4]) {
    let mut exec = Executor::new();
    let sort = Sort::array(Sort::Int, Sort::Int);
    let a = exec.ctx.terms.mk_var("a", sort.clone());
    let b = exec.ctx.terms.mk_var("b", sort.clone());
    let c = exec.ctx.terms.mk_var("c", sort.clone());
    let d = exec.ctx.terms.mk_var("d", sort);
    for (source, target) in [(a, b), (c, d)] {
        let root = exec.ctx.terms.mk_eq(source, target);
        exec.ctx.assertions.push(root);
        exec.recorded_var_substitutions.insert(source, target);
    }
    if connected {
        let root = exec.ctx.terms.mk_eq(b, c);
        exec.ctx.assertions.push(root);
    }
    let mut model = empty_model();
    let mut arrays = ArrayModel::default();
    for (source, target) in [(a, b), (c, d)] {
        arrays.defer_array_definition(&exec.ctx.terms, source, target);
    }
    model.array_model = Some(arrays);
    (exec, model, [a, b, c, d])
}

#[test]
fn dependency_only_collection_preserves_edges_without_requesting_opaque_definitions() {
    let mut exec = Executor::new();
    let commands = ay_frontend::parse(
        "(set-logic QF_AUFLIA)
         (declare-const a (Array Int Int))
         (declare-const b (Array Int Int))
         (declare-const c (Array Int Int))
         (declare-fun f (Int) (Array Int Int))
         (assert (= a b))
         (assert (= b (store c 0 1)))
         (assert (= (f 0) (store c 1 2)))",
    )
    .unwrap();
    assert!(exec.execute_all(&commands).unwrap().is_empty());
    let model = empty_model();
    let (_, full_edges, _, definitions, _) = exec.collect_array_completion_graph(&model, &[]);
    assert!(definitions
        .iter()
        .any(|&(term, _)| exec.is_opaque_array_valued_app(term)));
    let _owner = ay_core::resource::enter_check_stop(Arc::new(|| false));
    let scope = RecoveryScope::enter(&exec, MAX_WORK as usize, MAX_COPY_BYTES).unwrap();
    let dependency_edges = exec.collect_pending_array_dependency_edges(&model, &[]);
    assert_eq!(dependency_edges, full_edges);
    assert!(scope.admission().pay(0, 0));
    // The ordinary candidate-definition route still refuses that unowned
    // producer inside a recovery transaction. Only the requested DATA API
    // above avoids invoking it.
    let _ = exec.collect_array_completion_graph(&model, &[]);
    assert!(!scope.admission().pay(0, 0));
}

#[test]
fn uncertain_opaque_congruence_keeps_the_other_pending_component_withheld() {
    let mut exec = Executor::new();
    let commands = ay_frontend::parse(
        "(set-logic QF_AUFLIA)
         (declare-const a (Array Int Int))
         (declare-const b (Array Int Int))
         (declare-const c (Array Int Int))
         (declare-const d (Array Int Int))
         (declare-const x Int)
         (declare-const y Int)
         (declare-fun f (Int) (Array Int Int))
         (assert (= a b))
         (assert (= c d))
         (assert (= (f x) a))
         (assert (= (f y) c))",
    )
    .unwrap();
    assert!(exec.execute_all(&commands).unwrap().is_empty());
    let terms = ["a", "b", "c", "d"].map(|wanted| {
        exec.ctx
            .symbol_iter()
            .find_map(|(name, info)| (name == wanted).then_some(info.term).flatten())
            .unwrap()
    });
    let [a, b, c, d] = terms;
    let mut model = empty_model();
    let mut arrays = ArrayModel::default();
    for (source, target) in [(a, b), (c, d)] {
        exec.recorded_var_substitutions.insert(source, target);
        arrays.defer_array_definition(&exec.ctx.terms, source, target);
    }
    model.array_model = Some(arrays);
    let (_, native_edges, _, _, _) = exec.collect_array_completion_graph(&model, &[]);
    let _owner = ay_core::resource::enter_check_stop(Arc::new(|| false));
    let scope = RecoveryScope::enter(&exec, MAX_WORK as usize, MAX_COPY_BYTES).unwrap();
    let edges = exec.collect_pending_array_dependency_edges(&model, &[]);
    assert!(native_edges.iter().all(|edge| edges.contains(edge)));
    assert!(edges.len() > native_edges.len());
    assert!(scope.admission().pay(0, 0));
    // These are direct aliases: structural store taint intentionally travels
    // only base -> result and must not be used to infer a result -> base
    // dependency. Removing only a's pending reason must not expose its values
    // while f(x) might be congruent to f(y), whose pending reason remains.
    model
        .array_model
        .as_mut()
        .unwrap()
        .pending_definitions
        .remove(&a);
    let mask = exec.pending_array_dependency_mask(&model, &edges);
    assert!(terms.iter().all(|term| mask.contains(term)));
    assert!(model
        .array_model
        .as_ref()
        .unwrap()
        .read_conflicted
        .is_empty());
}

#[test]
fn per_record_retry_retains_independent_pending_component() {
    let (exec, mut model, [a, b, c, d]) = pairs(false);
    let (_, edges, _, _, _) = exec.collect_array_completion_graph(&model, &[]);
    let mut checkpoint = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(MAX_WORK, &mut checkpoint);
    exec.refresh_pending_array_dependency_mask(&mut model, &edges, &mut work)
        .unwrap();
    assert!([a, b, c, d]
        .iter()
        .all(|term| model.array_model.as_ref().unwrap().is_withheld(term)));
    let pending = model
        .array_model
        .as_mut()
        .unwrap()
        .pending_definitions
        .remove(&a)
        .unwrap();
    exec.refresh_pending_array_dependency_mask(&mut model, &edges, &mut work)
        .unwrap();
    let arrays = model.array_model.as_ref().unwrap();
    assert!(!arrays.is_withheld(&a) && !arrays.is_withheld(&b));
    assert!(arrays.is_withheld(&c) && arrays.is_withheld(&d));
    assert!(arrays.read_conflicted.is_empty());
    model
        .array_model
        .as_mut()
        .unwrap()
        .pending_definitions
        .insert(a, pending);
    exec.refresh_pending_array_dependency_mask(&mut model, &edges, &mut work)
        .unwrap();
    assert!([a, b, c, d]
        .iter()
        .all(|term| model.array_model.as_ref().unwrap().is_withheld(term)));
}

#[test]
fn another_pending_record_in_shared_component_blocks_the_retry() {
    let (exec, mut model, [a, b, c, d]) = pairs(true);
    let (_, edges, _, _, _) = exec.collect_array_completion_graph(&model, &[]);
    model
        .array_model
        .as_mut()
        .unwrap()
        .pending_definitions
        .remove(&a);
    let mut checkpoint = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(MAX_WORK, &mut checkpoint);
    exec.refresh_pending_array_dependency_mask(&mut model, &edges, &mut work)
        .unwrap();
    let arrays = model.array_model.as_ref().unwrap();
    assert!([a, b, c, d].iter().all(|term| arrays.is_withheld(term)));
    assert!(arrays.read_conflicted.is_empty());
}

#[test]
fn repeated_phase_six_does_not_promote_pending_into_protected_conflict() {
    let (mut exec, mut model, [a, b, c, d]) = pairs(false);
    let original = model
        .array_model
        .as_ref()
        .unwrap()
        .pending_definitions
        .clone();
    for _ in 0..2 {
        exec.complete_array_models_for_validation(&mut model, &[]);
        let arrays = model.array_model.as_ref().unwrap();
        assert_eq!(arrays.pending_definitions, original);
        assert!(arrays.read_conflicted.is_empty());
        assert!([a, b, c, d].iter().all(|term| arrays.is_withheld(term)));
    }
    model
        .array_model
        .as_mut()
        .unwrap()
        .read_conflicted
        .insert(b);
    exec.complete_array_models_for_validation(&mut model, &[]);
    let arrays = model.array_model.as_mut().unwrap();
    assert!(arrays.read_conflicted.contains(&a) && arrays.read_conflicted.contains(&b));
    assert!(!arrays.discharge_array_definition(&exec.ctx.terms, a, b));
    assert!(arrays.is_withheld(&a) && arrays.is_withheld(&b));
    assert!(!arrays.read_conflicted.contains(&c) && !arrays.read_conflicted.contains(&d));
}

fn assignment() -> Arc<crate::executor::model::DtEgraphAssignment> {
    Arc::new(crate::executor::model::DtEgraphAssignment {
        dtm: ay_dt::DtModel::default(),
        class_value: HashMap::default(),
        class_fields: HashMap::default(),
        class_ctor: HashMap::default(),
        poisoned: HashSet::default(),
        diseq_incoherent: HashSet::default(),
        self_check_ok: true,
    })
}

#[test]
fn candidate_error_stop_and_unwind_restore_exact_array_reasons_cache_and_seal() {
    for case in ["error", "no-change", "stop", "panic", "admission-panic"] {
        let (exec, mut model, [a, b, c, _]) = pairs(false);
        model
            .array_model
            .as_mut()
            .unwrap()
            .read_conflicted
            .insert(c);
        let pending = model
            .array_model
            .as_ref()
            .unwrap()
            .pending_definitions
            .clone();
        let epoch = model.seal_quantified_grant_model();
        let previous = assignment();
        exec.dt_egraph_assignment.replace(Some(previous.clone()));
        let candidate = model.array_model.as_ref().unwrap().clone();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            exec.with_pending_array_candidate(
                &mut model,
                candidate,
                |candidate| {
                    let arrays = candidate.array_model.as_mut().unwrap();
                    arrays.pending_definitions.remove(&a);
                    arrays.pending_definition_dependents.insert(b);
                    arrays.read_conflicted.insert(a);
                    exec.dt_egraph_assignment.replace(Some(assignment()));
                    match case {
                        "error" => Err(QueryError::Invalid("actual candidate decline")),
                        "no-change" => Ok(0),
                        "panic" => panic!("candidate panic after private mutation"),
                        _ => Ok(1),
                    }
                },
                || {
                    if case == "admission-panic" {
                        panic!("owner callback panic");
                    }
                    case != "stop"
                },
            )
        }));
        if case == "panic" || case == "admission-panic" {
            assert!(result.is_err());
        } else {
            assert_eq!(result.unwrap(), 0);
        }
        let arrays = model.array_model.as_ref().unwrap();
        assert_eq!(arrays.pending_definitions, pending);
        assert!(arrays.pending_definition_dependents.is_empty());
        assert_eq!(arrays.read_conflicted, [c].into_iter().collect());
        assert!(model.carries_quantified_grant_model(&epoch));
        assert!(exec
            .dt_egraph_assignment
            .borrow()
            .as_ref()
            .is_some_and(|cache| Arc::ptr_eq(cache, &previous)));
    }
}

#[test]
fn a_shared_gate_cache_session_is_an_explicit_recovery_decline() {
    // Use the maintained authored fixture and its actual checked W6 model,
    // rather than fabricating a certificate that happens to reach a guard.
    let script = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../ay-chc/tests/fixtures/quantified_nested_cells/missing_outer_frame.smt2"
    ));
    let mut exec = Executor::new();
    exec.set_timeout(Some(std::time::Duration::from_secs(30)));
    let output = exec
        .execute_all(&ay_frontend::parse(script).unwrap())
        .unwrap();
    assert_eq!(output, ["sat"]);
    let source = exec
        .ctx
        .symbol_iter()
        .find_map(|(name, info)| (name == "after_cells").then_some(info.term).flatten())
        .unwrap();
    let target = *exec
        .recorded_var_substitutions
        .get(&source)
        .expect("the maintained producer must retain its real array replacement");
    let mut model = exec.last_model.take().expect("checked SAT model");
    assert!(exec.last_model_validated);
    assert!(!model.dt_array_field_classes.is_empty());
    assert!(!model.array_model.as_ref().unwrap().is_withheld(&source));
    model
        .array_model
        .as_mut()
        .unwrap()
        .defer_array_definition(&exec.ctx.terms, source, target);
    assert!(model
        .array_model
        .as_ref()
        .unwrap()
        .pending_definitions
        .contains_key(&source));
    let original = model
        .array_model
        .as_ref()
        .unwrap()
        .pending_definitions
        .clone();
    let epoch = model.seal_quantified_grant_model();
    let previous = assignment();
    exec.dt_egraph_assignment.replace(Some(previous.clone()));
    {
        let _session = super::super::super::independent_gate::GateViewCacheSession::new();
        assert!(super::super::super::independent_gate::shared_gate_view_cache_active());
        assert_eq!(
            exec.recover_pending_datatype_array_aliases(&mut model, &[]),
            0
        );
        assert_eq!(
            model.array_model.as_ref().unwrap().pending_definitions,
            original
        );
        assert!(model.carries_quantified_grant_model(&epoch));
        assert!(exec
            .dt_egraph_assignment
            .borrow()
            .as_ref()
            .is_some_and(|cache| Arc::ptr_eq(cache, &previous)));
    }
    // Discriminating opposite: identical model/source is eligible once the
    // fixed-model cache session is gone. Its private mutation retires the old
    // seal/cache, while normal final gates remain the publication boundary.
    assert!(exec.recover_pending_datatype_array_aliases(&mut model, &[]) > 0);
    assert!(!model.array_model.as_ref().unwrap().is_withheld(&source));
    assert!(!model.carries_quantified_grant_model(&epoch));
    assert!(exec.dt_egraph_assignment.borrow().is_none());
}

#[test]
fn two_independent_real_aliases_recover_through_the_complete_production_transaction() {
    let commands = ay_frontend::parse(
        "(set-logic ALL)
         (declare-datatype Cell ((cell (data (Array Int Bool)))))
         (declare-const left (Array (_ BitVec 8) Cell))
         (declare-const right (Array (_ BitVec 8) Cell))
         (declare-const other_left (Array (_ BitVec 8) Cell))
         (declare-const other_right (Array (_ BitVec 8) Cell))
         (assert (= left right))
         (assert (= other_left other_right))
         (assert (= (select left #x01) (cell ((as const (Array Int Bool)) false))))
         (assert (= (select right #x02) (cell ((as const (Array Int Bool)) true))))
         (assert (= (select other_left #x03) (cell ((as const (Array Int Bool)) true))))
         (assert (= (select other_right #x04) (cell ((as const (Array Int Bool)) false))))
         (check-sat)",
    )
    .unwrap();
    let mut exec = Executor::new();
    exec.set_timeout(Some(std::time::Duration::from_secs(30)));
    assert_eq!(exec.execute_all(&commands).unwrap(), ["sat"]);
    assert!(exec.last_model_validated);
    let mut model = exec.last_model.take().unwrap();
    assert!(!exec
        .authenticated_datatype_array_field_classes(&model)
        .unwrap()
        .is_empty());
    let aliases: Vec<_> = exec
        .recorded_var_substitutions
        .iter()
        .filter_map(|(&source, &target)| {
            (matches!(exec.ctx.terms.sort(source), Sort::Array(sort)
            if exec.datatype_sort_carries_array_field(&sort.element_sort))
                && matches!(exec.ctx.terms.get(target), TermData::Var(_, _)))
            .then_some((source, target))
        })
        .collect();
    assert_eq!(aliases.len(), 2);
    let arrays = model.array_model.as_mut().unwrap();
    for &(source, target) in &aliases {
        arrays.defer_array_definition(&exec.ctx.terms, source, target);
        arrays.array_values.remove(&source);
        arrays.array_values.remove(&target);
    }
    model.revoke_all_quantified_model_seals();
    exec.pending_array_mutation_boundary();
    let edges = exec.collect_pending_array_dependency_edges(&model, &[]);
    let mut checkpoint = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(MAX_WORK, &mut checkpoint);
    exec.refresh_pending_array_dependency_mask(&mut model, &edges, &mut work)
        .unwrap();
    assert!(aliases.iter().all(|&(source, target)| {
        let arrays = model.array_model.as_ref().unwrap();
        arrays.is_withheld(&source) && arrays.is_withheld(&target)
    }));
    let _stop = ay_core::resource::enter_check_stop(Arc::new(|| false));
    // No outer RecoveryScope or manual prepare/install calls: exercise the
    // production per-record quarantine and prepare-ALL-before-install loop.
    assert_eq!(
        exec.recover_pending_datatype_array_aliases(&mut model, &[]),
        2
    );
    let arrays = model.array_model.as_ref().unwrap();
    assert!(arrays.pending_definitions.is_empty());
    assert!(arrays.pending_definition_dependents.is_empty());
    assert!(arrays.read_conflicted.is_empty());
    for &(source, target) in &aliases {
        assert!(!arrays.is_withheld(&source) && !arrays.is_withheld(&target));
        assert_eq!(
            arrays.array_values.get(&source),
            arrays.array_values.get(&target)
        );
        let candidate = &arrays.array_values[&source];
        assert!(candidate
            .default
            .as_ref()
            .is_some_and(|value| !value.contains("ay.value-unavailable")));
        assert!(candidate
            .stores
            .iter()
            .all(|(_, value)| !value.contains("ay.value-unavailable")));
    }
    exec.last_model = Some(model);
    assert!(matches!(
        exec.confirm_sat_with_fully_evaluated_independent_gate(),
        ay_model_check::GateVerdict::ConfirmedSat
    ));
    assert!(matches!(
        exec.confirm_sat_with_independent_gate(),
        ay_model_check::GateVerdict::ConfirmedSat
    ));
}
