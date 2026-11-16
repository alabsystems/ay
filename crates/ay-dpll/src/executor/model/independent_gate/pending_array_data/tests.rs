// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::model::recovery_admission::RecoveryScope;
use std::sync::Arc;

const WORK: u64 = 1_000_000;
const BYTES: usize = 64 * 1024 * 1024;

fn data_executor() -> (Executor, String, ay_core::ArraySort) {
    let mut exec = Executor::new();
    let commands =
        ay_frontend::parse("(declare-datatype Cell ((cell (data (Array Int Bool)))))").unwrap();
    assert_eq!(exec.execute_all(&commands).unwrap(), [] as [String; 0]);
    let info = exec.ctx.exact_datatype_member_info("cell").unwrap();
    let ctor = exec.ctx.symbol_identity_name("cell", info).to_string();
    let sort = ay_core::ArraySort {
        index_sort: Sort::bitvec(8),
        element_sort: info.sort.clone(),
    };
    (exec, ctor, sort)
}

fn cell(ctor: &str, default: bool, redundant: bool) -> ModelValue {
    ModelValue::Datatype {
        ctor: ctor.into(),
        args: vec![ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Bool(default),
            store: if redundant {
                vec![(ModelValue::Int(3.into()), ModelValue::Bool(default))]
            } else {
                vec![]
            },
        }))],
    }
}

#[test]
fn equal_evaluated_alias_indices_require_extensionally_equal_complete_rows() {
    let (exec, ctor, sort) = data_executor();
    let _stop = ay_core::resource::enter_check_stop(Arc::new(|| false));
    let scope = RecoveryScope::enter(&exec, WORK as usize, BYTES).unwrap();
    let owner = scope.admission();
    let mut admit = |units, bytes| {
        owner
            .pay(units, bytes)
            .then_some(())
            .ok_or(QueryError::Exhausted)
    };
    let mut work = WorkBudget::with_admission(WORK, &mut admit);
    let mut semantic = SemanticNormalizationBudget::new();
    let mut rows = RowBuilder::new();
    let key = ModelValue::bitvec(17.into(), 8);
    assert_eq!(
        rows.row(
            &exec,
            &key,
            &cell(&ctor, false, false),
            &sort,
            &mut work,
            &mut semantic
        )
        .unwrap(),
        0
    );
    assert_eq!(
        rows.row(
            &exec,
            &key,
            &cell(&ctor, false, true),
            &sort,
            &mut work,
            &mut semantic
        )
        .unwrap(),
        0
    );
    assert_eq!(rows.stores.len(), 1);
    assert!(rows
        .row(
            &exec,
            &key,
            &cell(&ctor, true, false),
            &sort,
            &mut work,
            &mut semantic
        )
        .is_err());
    assert_eq!(
        rows.stores.len(),
        1,
        "a conflict cannot overwrite the existing row"
    );
}

#[test]
fn unknown_indices_partial_values_and_disagreeing_known_defaults_never_become_zero() {
    let (exec, ctor, sort) = data_executor();
    let _stop = ay_core::resource::enter_check_stop(Arc::new(|| false));
    let scope = RecoveryScope::enter(&exec, WORK as usize, BYTES).unwrap();
    let owner = scope.admission();
    let mut admit = |units, bytes| {
        owner
            .pay(units, bytes)
            .then_some(())
            .ok_or(QueryError::Exhausted)
    };
    let mut work = WorkBudget::with_admission(WORK, &mut admit);
    let mut semantic = SemanticNormalizationBudget::new();
    let mut rows = RowBuilder::new();
    assert!(rows
        .row(
            &exec,
            &ModelValue::Uninterpreted("missing-index".into()),
            &cell(&ctor, false, false),
            &sort,
            &mut work,
            &mut semantic
        )
        .is_err());
    rows.known_default(
        &exec,
        &cell(&ctor, false, false),
        &sort.element_sort,
        &mut work,
        &mut semantic,
    )
    .unwrap();
    assert!(rows
        .known_default(
            &exec,
            &cell(&ctor, true, false),
            &sort.element_sort,
            &mut work,
            &mut semantic
        )
        .is_err());
    assert!(rows.default.is_some());
    // The partial payload intentionally refuses the shared grant. Perform
    // the independent default cases first; no grant is reset afterward.
    let partial = ModelValue::Datatype {
        ctor: ctor.clone(),
        args: vec![ModelValue::Uninterpreted(
            "(_ ay.value-unavailable t216)".into(),
        )],
    };
    assert!(rows
        .row(
            &exec,
            &ModelValue::bitvec(0.into(), 8),
            &partial,
            &sort,
            &mut work,
            &mut semantic
        )
        .is_err());
    assert!(rows.points.is_empty());
    assert!(!owner.pay(0, 0));
    assert!(
        work.charge(0).is_err(),
        "the original refusal stays terminal"
    );
}

struct Fixture {
    exec: Executor,
    model: Model,
    record: PendingArrayDefinition,
    other_records: Vec<PendingArrayDefinition>,
    scope: Vec<TermId>,
}

fn fixture() -> Fixture {
    // This is a real checked W6 model. Tests do not create certificates,
    // mutate their payloads, or authorize new generated read terms.
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
    let mut aliases: Vec<_> = exec
        .recorded_var_substitutions
        .iter()
        .filter_map(|(&source, &target)| {
            (matches!(exec.ctx.terms.sort(source), Sort::Array(sort)
            if exec.datatype_sort_carries_array_field(&sort.element_sort))
                && matches!(exec.ctx.terms.get(target), TermData::Var(_, _)))
            .then_some((source, target))
        })
        .collect();
    aliases.sort_unstable();
    assert_eq!(
        aliases.len(),
        2,
        "both real alias preprocessing edges must survive"
    );
    let arrays = model.array_model.as_mut().unwrap();
    let mut records = Vec::new();
    for (source, target) in aliases {
        arrays.defer_array_definition(&exec.ctx.terms, source, target);
        records.push(arrays.pending_definitions.remove(&source).unwrap());
        arrays.array_values.remove(&source);
        arrays.array_values.remove(&target);
    }
    let record = records.remove(0);
    arrays.pending_definition_dependents.clear();
    // No outer interpretation is needed as evidence: authenticated original
    // W6 values remain. This deliberately exercises the complete-row fallback.
    model.revoke_all_quantified_model_seals();
    exec.dt_egraph_assignment.replace(None);
    super::super::super::eval_memo_clear();
    let mut scope = Vec::new();
    let roots = exec
        .independent_gate_authored_assertions
        .as_deref()
        .unwrap_or(&exec.ctx.assertions);
    let mut stack = roots.to_vec();
    while let Some(term) = stack.pop() {
        if scope.contains(&term) {
            continue;
        }
        scope.push(term);
        match exec.ctx.terms.get(term) {
            TermData::App(_, args) => stack.extend_from_slice(args),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
            _ => {}
        }
    }
    scope.sort_unstable();
    Fixture {
        exec,
        model,
        record,
        other_records: records,
        scope,
    }
}

#[test]
fn multiple_alias_plans_keep_all_original_expectations_before_any_candidate_installation() {
    let mut f = fixture();
    let _stop = ay_core::resource::enter_check_stop(Arc::new(|| false));
    let scope = RecoveryScope::enter(&f.exec, WORK as usize, BYTES).unwrap();
    let owner = scope.admission();
    let mut admit = |units, bytes| {
        owner
            .pay(units, bytes)
            .then_some(())
            .ok_or(QueryError::Exhausted)
    };
    let mut work = WorkBudget::with_admission(WORK, &mut admit);
    let mut semantic = SemanticNormalizationBudget::new();
    let records = [f.record, f.other_records[0]];
    let mut plans = Vec::new();
    for record in records {
        plans.push(
            f.exec
                .prepare_pending_array_alias_data(
                    &f.model,
                    record,
                    &f.scope,
                    &mut work,
                    &mut semantic,
                )
                .unwrap()
                .unwrap(),
        );
    }
    assert_eq!(plans.len(), 2);
    for plan in &plans {
        for alias in [plan.record.source(), plan.record.target()] {
            let copy = plan.proposal.try_clone_with_budget(&mut work).unwrap();
            f.model
                .array_model
                .as_mut()
                .unwrap()
                .array_values
                .insert(alias, copy);
        }
    }
    f.exec.dt_egraph_assignment.replace(None);
    super::super::super::eval_memo_clear();
    for plan in &plans {
        assert!(f.exec.pending_array_prepared_reads_match(
            &f.model,
            plan,
            &mut work,
            &mut semantic
        ));
    }
}

#[test]
fn original_w6_rows_cover_both_aliases_and_expected_values_survive_candidate_mutation() {
    let mut f = fixture();
    let _stop = ay_core::resource::enter_check_stop(Arc::new(|| false));
    let scope = RecoveryScope::enter(&f.exec, WORK as usize, BYTES).unwrap();
    let owner = scope.admission();
    let mut admit = |units, bytes| {
        owner
            .pay(units, bytes)
            .then_some(())
            .ok_or(QueryError::Exhausted)
    };
    let mut work = WorkBudget::with_admission(WORK, &mut admit);
    let mut semantic = SemanticNormalizationBudget::new();
    let plan = f
        .exec
        .prepare_pending_array_alias_data(&f.model, f.record, &f.scope, &mut work, &mut semantic)
        .unwrap()
        .unwrap();
    assert!(plan.reads.len() >= 2);
    assert!(plan.proposal.stores.len() >= 2);
    assert!(!plan
        .proposal
        .stores
        .iter()
        .any(|(_, value)| value.contains("ay.value-unavailable")));
    assert!(plan
        .proposal
        .default
        .as_ref()
        .is_some_and(|value| !value.contains("ay.value-unavailable")));
    for alias in [f.record.source(), f.record.target()] {
        let copy = plan.proposal.try_clone_with_budget(&mut work).unwrap();
        f.model
            .array_model
            .as_mut()
            .unwrap()
            .array_values
            .insert(alias, copy);
    }
    f.exec.dt_egraph_assignment.replace(None);
    super::super::super::eval_memo_clear();
    assert!(f
        .exec
        .pending_array_prepared_reads_match(&f.model, &plan, &mut work, &mut semantic));
    // Mutate only candidate DATA. Frozen ORIGINAL expectations must not follow
    // this new value and accidentally validate it against itself.
    let wrong = plan.proposal.default.clone().unwrap();
    for alias in [f.record.source(), f.record.target()] {
        let values = f
            .model
            .array_model
            .as_mut()
            .unwrap()
            .array_values
            .get_mut(&alias)
            .unwrap();
        values
            .stores
            .iter_mut()
            .for_each(|(_, value)| *value = wrong.clone());
    }
    f.exec.dt_egraph_assignment.replace(None);
    super::super::super::eval_memo_clear();
    assert!(!f
        .exec
        .pending_array_prepared_reads_match(&f.model, &plan, &mut work, &mut semantic));
}

#[test]
fn prepared_original_data_declines_stale_edges_and_partial_existing_rows_without_mutation() {
    let mut f = fixture();
    let _stop = ay_core::resource::enter_check_stop(Arc::new(|| false));
    let scope = RecoveryScope::enter(&f.exec, WORK as usize, BYTES).unwrap();
    let owner = scope.admission();
    let mut admit = |units, bytes| {
        owner
            .pay(units, bytes)
            .then_some(())
            .ok_or(QueryError::Exhausted)
    };
    let mut work = WorkBudget::with_admission(WORK, &mut admit);
    let mut semantic = SemanticNormalizationBudget::new();
    let plan = f
        .exec
        .prepare_pending_array_alias_data(&f.model, f.record, &f.scope, &mut work, &mut semantic)
        .unwrap()
        .unwrap();
    assert!(plan.is_current(&f.exec, &mut work).unwrap());
    f.exec.recorded_var_substitutions.remove(&f.record.source());
    assert!(!plan.is_current(&f.exec, &mut work).unwrap());
    f.exec
        .recorded_var_substitutions
        .insert(f.record.source(), f.record.target());
    let partial = ArrayInterpretation {
        default: Some("(_ ay.value-unavailable t216)".into()),
        ..Default::default()
    };
    f.model
        .array_model
        .as_mut()
        .unwrap()
        .array_values
        .insert(f.record.source(), partial.clone());
    assert!(!matches!(
        f.exec.prepare_pending_array_alias_data(
            &f.model,
            f.record,
            &f.scope,
            &mut work,
            &mut semantic
        ),
        Ok(Some(_))
    ));
    assert_eq!(
        f.model.array_model.as_ref().unwrap().array_values[&f.record.source()],
        partial
    );
    let _ = f.exec.ctx.terms.mk_var("new-snapshot", Sort::Bool);
    assert!(!plan.is_current(&f.exec, &mut work).unwrap());
}
