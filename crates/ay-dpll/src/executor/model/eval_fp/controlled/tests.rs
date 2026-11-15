// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use ay_core::Symbol;
use ay_fp::FpBuildStage;
use num_bigint::BigInt;

use crate::executor::model::{dt_model, eval_guard, eval_memo, EvalValue};

use super::*;

mod fixtures;
mod resources;
use fixtures::*;

#[test]
fn non_rne_model_evaluation_executes_real_division_and_keeps_exact_rounding_bits() {
    for (mode, expected) in [("RTP", 0x3556), ("RTZ", 0x3555)] {
        let (executor, model, term) = division(mode);
        assert!(model.fp_model.is_none()); // No whole-result pin may skip fallback.
        let _read = executor.begin_external_evaluation_read();
        let rows = Cell::new(0);
        let value = executor.evaluate_fp_term_via_bitblast_controlled(&model, term, &|phase| {
            if matches!(phase, FpEvalPhase::Construction(p) if p.stage == FpBuildStage::DivideRow) {
                rows.set(rows.get() + 1);
            }
        }).unwrap().unwrap();
        assert!(rows.get() > 4);
        assert_eq!(bits(&value), BigInt::from(expected));
        let EvalValue::Fp(actual) = executor.evaluate_term(&model, term) else {
            panic!("the real application fallback must produce the same concrete result")
        };
        assert_eq!(bits(&actual), bits(&value));
        assert_eq!(executor.evaluation_stop_origin(), None);
    }
}

#[test]
fn interior_divider_refusal_poison_is_sticky_across_memo_and_boolean_parent() {
    let (mut executor, model, term) = division("RTP");
    let expected = fp(&mut executor.ctx.terms, 13, 342);
    let parent = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fp.eq"), [term, expected], Sort::Bool);
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));
    let read = executor.begin_external_evaluation_read();
    let memo = eval_memo::EvalMemoSession::new();
    let rows = Cell::new(0);
    let searched = Cell::new(false);
    let result = executor.evaluate_fp_term_via_bitblast_controlled(&model, term, &|phase| {
        if matches!(phase, FpEvalPhase::Construction(p) if p.stage == FpBuildStage::DivideRow) {
            rows.set(rows.get() + 1);
            if rows.get() == 4 {
                interrupt.store(true, Ordering::Relaxed);
            }
        }
        if matches!(phase, FpEvalPhase::SatSearch | FpEvalPhase::Decode) {
            searched.set(true);
        }
    });
    assert!(matches!(result, Err(UnknownOrigin::InterruptFlag)));
    assert_eq!(rows.get(), 4);
    assert!(!searched.get());
    // Concrete operands can fold away clauses; this tests actual row reach,
    // not a claim that every completed row allocates additional CNF.
    interrupt.store(false, Ordering::Relaxed);
    assert!(matches!(
        executor.evaluate_term(&model, parent),
        EvalValue::Unknown
    ));
    assert!(matches!(
        executor.evaluate_term(&model, term),
        EvalValue::Unknown
    ));
    assert!(eval_memo::get(term).is_none() && eval_memo::get(parent).is_none());
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(UnknownOrigin::InterruptFlag)
    );
    drop(memo);
    drop(read);
    let _fresh = executor.begin_external_evaluation_read();
    healthy(&executor, &model, term, 0x3556);
    assert!(matches!(
        executor.evaluate_term(&model, parent),
        EvalValue::Bool(true)
    ));
}

#[test]
fn concretization_observes_scoped_binding_before_ambient_operand_and_result_pins() {
    let (mut executor, mut model, _) = division("RTP");
    let terms = &mut executor.ctx.terms;
    let sort = Sort::FloatingPoint(5, 11);
    let bound = terms.mk_var("bound", sort.clone());
    let three = fp(terms, 16, 512);
    let rm = terms.mk_app(
        Symbol::named("RTP"),
        [],
        Sort::Uninterpreted("RoundingMode".to_string()),
    );
    let term = terms.mk_app(Symbol::named("fp.div"), [rm, bound, three], sort);
    model.fp_model = Some(ay_fp::FpModel {
        values: [
            (
                bound,
                FpModelValue::Fp {
                    sign: false,
                    exponent: 16,
                    significand: 0,
                    eb: 5,
                    sb: 11,
                },
            ),
            (term, FpModelValue::PosZero { eb: 5, sb: 11 }),
        ]
        .into_iter()
        .collect(),
        ..Default::default()
    });
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));
    let stamp = executor.ctx.source_context_stamp();
    let one = EvalValue::Fp(FpModelValue::Fp {
        sign: false,
        exponent: 15,
        significand: 0,
        eb: 5,
        sb: 11,
    });
    dt_model::with_scoped_term_override(bound, one, || {
        let read = executor.begin_external_evaluation_read();
        let visits = Cell::new(0);
        let constructed = Cell::new(false);
        let result = executor.evaluate_fp_term_via_bitblast_controlled(&model, term, &|phase| {
            if let FpEvalPhase::Concretize(_) = phase {
                visits.set(visits.get() + 1);
                if visits.get() == 3 {
                    interrupt.store(true, Ordering::Relaxed);
                }
            }
            if matches!(phase, FpEvalPhase::Construction(_)) {
                constructed.set(true);
            }
        });
        assert!(matches!(result, Err(UnknownOrigin::InterruptFlag)));
        assert_eq!(visits.get(), 3);
        assert!(!constructed.get());
        interrupt.store(false, Ordering::Relaxed);
        drop(read);
        let _fresh = executor.begin_external_evaluation_read();
        healthy(&executor, &model, term, 0x3556);
    });
    assert_eq!(executor.ctx.source_context_stamp(), stamp);
    assert!(model.fp_model.as_ref().unwrap().values[&term].is_zero());
}

#[test]
fn sat_callback_decode_and_restricted_subsetup_refusals_never_return_a_value_after_reset() {
    for target in [
        FpEvalPhase::SatPoll,
        FpEvalPhase::Decode,
        FpEvalPhase::Cleanup,
    ] {
        let (mut executor, model, term) = division("RTP");
        let interrupt = Arc::new(AtomicBool::new(false));
        executor.set_interrupt(Arc::clone(&interrupt));
        let read = executor.begin_external_evaluation_read();
        let hits = Cell::new(0);
        let result = executor.evaluate_fp_term_via_bitblast_controlled(&model, term, &|phase| {
            if std::mem::discriminant(&phase) == std::mem::discriminant(&target) {
                hits.set(hits.get() + 1);
                interrupt.store(true, Ordering::Relaxed);
            }
            if matches!(phase, FpEvalPhase::SatReturned) {
                interrupt.store(false, Ordering::Relaxed);
            }
        });
        assert!(matches!(result, Err(UnknownOrigin::InterruptFlag)));
        assert_eq!(hits.get(), 1);
        interrupt.store(false, Ordering::Relaxed);
        assert_eq!(
            executor.evaluation_stop_origin(),
            Some(UnknownOrigin::InterruptFlag)
        );
        drop(read);
        let _fresh = executor.begin_external_evaluation_read();
        healthy(&executor, &model, term, 0x3556);
    }
}

#[test]
fn child_work_refusal_is_not_reencoded_as_a_new_concrete_input() {
    let (executor, model, term) = division("RTP");
    let read = executor.begin_external_evaluation_read();
    let budget = eval_guard::EvalWorkBudget::new(0);
    let constructed = Cell::new(false);
    let result = executor.evaluate_fp_term_via_bitblast_controlled(&model, term, &|phase| {
        if matches!(phase, FpEvalPhase::Construction(_)) {
            constructed.set(true);
        }
    });
    assert!(matches!(
        result,
        Err(UnknownOrigin::DeterministicResourceBudget)
    ));
    assert!(budget.exhausted());
    assert!(!constructed.get());
    drop(budget);
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(UnknownOrigin::DeterministicResourceBudget)
    );
    drop(read);
    let _fresh = executor.begin_external_evaluation_read();
    healthy(&executor, &model, term, 0x3556);
}
