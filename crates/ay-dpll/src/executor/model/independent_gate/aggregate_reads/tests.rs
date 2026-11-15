// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pure output reconstruction checks; these fixtures do not grant SAT authority.

use crate::executor::model::dt_egraph_values::DtEgraphAssignment;
use crate::executor::model::{EvalValue, Model};
use crate::executor::Executor;
use crate::executor_types::UnknownOrigin;
use ay_core::term::TermData;
use ay_core::{DatatypeSort, Sort, Symbol, TermId};
use ay_model_check::{ArrayValue, GateVerdict, ModelValue, ModelView};
use std::sync::Arc;

mod fixtures;
use fixtures::*;

#[test]
fn exact_nested_scalar_reads_ignore_stale_pins_in_one_batch() {
    let mut f = fixture();
    f.model.bv_model = Some(ay_bv::BvModel {
        values: [f.length, f.stored, f.default]
            .into_iter()
            .map(|term| (term, 0.into()))
            .collect(),
        term_to_bits: Default::default(),
        bool_overrides: Default::default(),
    });
    f.model
        .dt_ground
        .insert(f.receiver, row_value(&f.row_ctor, 0));
    f.model.completed_values.insert(
        f.length,
        EvalValue::BitVec {
            value: 0.into(),
            width: 64,
        },
    );
    let before = f.exec.ctx.terms.len();
    let values = f
        .exec
        .independent_aggregate_read_values(&f.model, &requests(&f))
        .unwrap();
    assert_eq!(values.len(), 3, "duplicate requests share one exact value");
    assert_eq!(values[&f.length], rendered(&f.exec, 65, 64));
    assert_eq!(values[&f.stored], rendered(&f.exec, 9, 8));
    assert_eq!(values[&f.default], rendered(&f.exec, 7, 8));
    assert_eq!(f.exec.ctx.terms.len(), before);
}

#[test]
fn ordinary_scalar_and_plain_array_reads_keep_the_legacy_lane() {
    let mut f = fixture();
    let scalar = f.exec.ctx.terms.mk_var("ordinary", Sort::bitvec(8));
    let array = f
        .exec
        .ctx
        .terms
        .mk_var("plain", Sort::array(Sort::Bool, Sort::bitvec(8)));
    let key = f.exec.ctx.terms.false_term();
    let read = app(&mut f.exec, "select", &[array, key], Sort::bitvec(8));
    f.model.bv_model = Some(ay_bv::BvModel {
        values: [(scalar, 4.into()), (read, 9.into())].into_iter().collect(),
        term_to_bits: Default::default(),
        bool_overrides: Default::default(),
    });
    let values = f
        .exec
        .independent_aggregate_read_values(
            &f.model,
            &[("ordinary".into(), scalar), ("plain-read".into(), read)],
        )
        .unwrap();
    assert!(values.is_empty());
    assert_eq!(
        f.exec.term_value_string(&f.model, scalar).unwrap(),
        rendered(&f.exec, 4, 8)
    );
    assert_eq!(
        f.exec.term_value_string(&f.model, read).unwrap(),
        rendered(&f.exec, 9, 8)
    );
}

#[test]
fn malformed_registered_selector_and_projection_refuse_stale_fallback() {
    let mut f = fixture();
    let bad_width = app(&mut f.exec, &f.len_name, &[f.receiver], Sort::bitvec(8));
    let bad_arity = app(
        &mut f.exec,
        &f.len_name,
        &[f.receiver, f.receiver],
        Sort::bitvec(64),
    );
    for bad in [bad_width, bad_arity] {
        f.model.completed_values.insert(
            bad,
            EvalValue::BitVec {
                value: 0.into(),
                width: 8,
            },
        );
        assert!(f
            .exec
            .independent_aggregate_read_values(&f.model, &[("bad".into(), bad)])
            .is_err());
    }
    let symbol = Symbol::named("project_row");
    let projected =
        f.exec
            .ctx
            .terms
            .mk_app(symbol.clone(), [f.receiver, f.receiver], f.row_sort.clone());
    let read = app(&mut f.exec, &f.len_name, &[projected], Sort::bitvec(64));
    f.model.projection_ufs = crate::executor::model::projection_uf::ProjectionUfModel::from_malformed_test_definition_unchecked(
        symbol, vec![f.row_sort.clone(), f.row_sort.clone()], f.row_sort.clone(), 2,
    );
    assert!(f
        .exec
        .independent_aggregate_read_values(&f.model, &[("projected".into(), read)])
        .is_err());
}

#[test]
fn coherent_egraph_must_match_and_poison_cannot_publish_an_independent_alternative() {
    let f = fixture();
    for (length, coherent, accepted) in [(65, true, true), (0, true, false), (65, false, false)] {
        let value = f
            .exec
            .format_gate_model_value(&row_value(&f.row_ctor, length), &f.row_sort)
            .unwrap();
        let mut assigned = assignment(f.receiver, value, coherent);
        for (term, sort, expected) in &f.source_classes {
            let rendered = f.exec.format_gate_model_value(expected, sort).unwrap();
            assert!(assigned.class_value.insert(*term, rendered).is_none());
        }
        assert_eq!(assigned.class_value.len(), 4);
        *f.exec.dt_egraph_assignment.borrow_mut() = Some(Arc::new(assigned));
        let result = f
            .exec
            .independent_aggregate_read_values(&f.model, &requests(&f));
        assert_eq!(
            result.is_ok(),
            accepted,
            "length={length}, coherent={coherent}: {result:?}"
        );
        if let Ok(values) = result {
            assert_eq!(values[&f.length], rendered(&f.exec, 65, 64));
        }
    }
    f.exec.dt_egraph_assignment.replace(None);
    assert!(f
        .exec
        .independent_aggregate_read_values(&f.model, &requests(&f))
        .is_ok());
}

#[test]
fn stopped_batch_cannot_resume_until_a_fresh_read_attempt() {
    let f = fixture();
    let attempt = f.exec.evaluation_attempt();
    f.exec.record_evaluation_stop(UnknownOrigin::MemoryBudget);
    assert!(f
        .exec
        .independent_aggregate_read_values(&f.model, &requests(&f))
        .is_err());
    assert_eq!(attempt.stop_origin(), Some(UnknownOrigin::MemoryBudget));
    {
        let _fresh = f.exec.begin_external_evaluation_read();
        let values = f
            .exec
            .independent_aggregate_read_values(&f.model, &requests(&f))
            .unwrap();
        assert_eq!(values[&f.stored], rendered(&f.exec, 9, 8));
    }
    assert_eq!(
        f.exec.evaluation_stop_origin(),
        Some(UnknownOrigin::MemoryBudget)
    );
    assert!(f
        .exec
        .independent_aggregate_read_values(&f.model, &requests(&f))
        .is_err());
}

struct Unpinned<'a>(&'a Executor);

impl ModelView for Unpinned<'_> {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        None
    }

    fn datatype_def(&self, name: &str) -> Option<DatatypeSort> {
        self.0.dt_registry_lookup(name)
    }
}

#[test]
fn checked_residual_owner_precedes_competing_egraph_and_stale_scope_refuses() {
    let mut f = fixture();
    for command in ay_frontend::parse(
        "(declare-const residual (Array Bool Row))
         (assert (= (len (select residual false)) (_ bv65 64)))",
    )
    .unwrap()
    {
        f.exec.ctx.process_command(&command).unwrap();
    }
    let array = f.exec.ctx.source_constant_for_value("residual").unwrap().0;
    let no = f.exec.ctx.terms.false_term();
    let receiver = app(&mut f.exec, "select", &[array, no], f.row_sort.clone());
    let read = app(&mut f.exec, &f.len_name, &[receiver], Sort::bitvec(64));
    assert_eq!(f.exec.ctx.assertions.len(), 1);
    assert!(matches!(f.exec.ctx.terms.get(f.exec.ctx.assertions[0]),
        TermData::App(Symbol::Named(name), args) if name == "=" && args.contains(&read)));
    let unpinned = Unpinned(&f.exec);
    let (verdict, completion) = ay_model_check::confirm_model_with_array_completion(
        &f.exec.ctx.terms,
        &unpinned,
        &f.exec.ctx.assertions,
    )
    .into_parts();
    assert!(matches!(verdict, GateVerdict::ConfirmedSat), "{verdict:?}");
    let assignments = completion.unwrap().into_assignments().unwrap();
    assert_eq!(assignments.len(), 1);
    f.model
        .install_residual_arrays(&f.exec.ctx, assignments)
        .unwrap();
    let wrong = f
        .exec
        .format_gate_model_value(&row_value(&f.row_ctor, 0), &f.row_sort)
        .unwrap();
    *f.exec.dt_egraph_assignment.borrow_mut() = Some(Arc::new(assignment(receiver, wrong, false)));
    let requested = [("residual-length".into(), read)];
    let values = f
        .exec
        .independent_aggregate_read_values(&f.model, &requested)
        .unwrap();
    assert_eq!(values[&read], rendered(&f.exec, 65, 64));
    for command in ay_frontend::parse("(declare-const later Bool)").unwrap() {
        f.exec.ctx.process_command(&command).unwrap();
    }
    assert!(!f.model.residual_arrays_are_current(&f.exec.ctx));
    assert!(f
        .exec
        .independent_aggregate_read_values(&f.model, &requested)
        .is_err());
}
