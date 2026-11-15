// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Real original-model DATA and constructor controls; no fixture SAT authority.

use std::sync::Arc;

use ay_core::term::{TermConstructionAdmission, TermData};
use ay_frontend::parse;
use ay_model_check::{ArrayValue, EvalOutcome, ModelView};
use num_bigint::{BigInt, BigUint};

use super::super::{model_value_to_pin_term, Model, QuantifiedGateElements};
use super::*;

struct Closed;
impl ModelView for Closed {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        None
    }
}

fn fixture() -> (Executor, TermId, ModelValue) {
    let mut exec = Executor::new();
    exec.set_term_memory_limit(Some(128 * 1024 * 1024));
    let source = "(declare-const x (_ FloatingPoint 8 200))
        (declare-fun f (Int) (_ FloatingPoint 8 200))
        (assert (forall ((n Int)) (fp.leq (f n) x)))";
    assert!(exec
        .execute_all(&parse(source).expect("original source"))
        .expect("elaborate without solving")
        .is_empty());
    exec.begin_external_decision_query(false);
    let x = exec
        .ctx
        .symbol_info("x")
        .and_then(|info| info.term)
        .expect("original x");
    let exponent = Arc::new(BigUint::from(127u8));
    let fraction = Arc::new((BigUint::from(1u8) << 198usize) + 1u8);
    let value = ModelValue::floating_point_exact_shared(
        true,
        Arc::clone(&exponent),
        Arc::clone(&fraction),
        8,
        200,
    )
    .expect("199-bit exact fixture data");
    let mut fp = ay_fp::FpModel::default();
    fp.values.insert(
        x,
        ay_fp::FpModelValue::Exact(
            ay_fp::FpFields::from_shared(true, exponent, fraction, 8, 200)
                .expect("same immutable solver fields"),
        ),
    );
    let mut model = Model::empty();
    model.fp_model = Some(fp);
    exec.install_functional_array_candidate(&mut model);
    assert!(
        model.construction_owner.is_some(),
        "retained original counter, independent of array-plan completion"
    );
    exec.last_model = Some(model);
    assert!(exec.last_result.is_none(), "fixture publishes no verdict");
    (exec, x, value)
}

fn authored_root(exec: &Executor) -> TermId {
    let roots = exec.ctx.concrete_authored_assertion_terms();
    assert_eq!(roots.len(), 1, "exactly one original source obligation");
    roots[0]
}

fn checked(terms: &TermStore, term: TermId) -> ModelValue {
    match ay_model_check::evaluate_term(terms, &Closed, term) {
        EvalOutcome::Value(value) => value,
        EvalOutcome::Unevaluable(reason) => {
            panic!("closed literal must independently evaluate: {reason}")
        }
    }
}

fn same_fields(actual: ModelValue, expected: &ModelValue) {
    let ModelValue::FloatingPointExact {
        sign,
        exponent,
        significand,
        exponent_bits,
        significand_bits,
    } = actual
    else {
        panic!("retain exact storage");
    };
    let ModelValue::FloatingPointExact {
        sign: expected_sign,
        exponent: expected_exponent,
        significand: expected_fraction,
        exponent_bits: expected_eb,
        significand_bits: expected_sb,
    } = expected
    else {
        panic!("exact expected data");
    };
    assert_eq!(
        (sign, exponent_bits, significand_bits),
        (*expected_sign, *expected_eb, *expected_sb)
    );
    assert_eq!(&exponent, expected_exponent);
    assert_eq!(&significand, expected_fraction);
}

#[test]
fn wide_scalar_pin_uses_original_owner_and_independent_exact_fields() {
    let (mut exec, x, value) = fixture();
    let frame = Frame::capture(&exec)
        .expect("original frame")
        .expect("original model ledger");
    let source = exec.ctx.source_context_stamp();
    let birth = exec.ctx.terms.entry_stamp(x);
    let mut elements = QuantifiedGateElements::default();
    let term = model_value_to_pin_term(
        &mut exec.ctx.terms,
        &value,
        &Sort::FloatingPoint(8, 200),
        &mut elements,
        Some(&frame),
    )
    .expect("actual dispatcher reconstructs all 199 stored bits");
    same_fields(checked(&exec.ctx.terms, term), &value);
    assert!(
        elements.by_token.is_empty(),
        "FP data never becomes an opaque element"
    );
    assert_eq!(exec.ctx.source_context_stamp(), source);
    assert_eq!(exec.ctx.terms.entry_stamp(x), birth);
    assert!(frame.finish(&exec));
}

#[test]
fn ordinary_quantified_free_leaf_caller_keeps_wide_model_value() {
    let (mut exec, x, value) = fixture();
    let root = authored_root(&exec);
    let pins = exec.quantified_gate_model_pins(
        root,
        &mut QuantifiedGateElements::default(),
        &Default::default(),
    );
    assert!(
        !pins.total,
        "the unrelated UF head still requires its own interpretation; root={}",
        exec.format_term(root)
    );
    assert_eq!(
        pins.equalities.len(),
        1,
        "the actual free FP leaf is expressible"
    );
    let TermData::App(symbol, args) = exec.ctx.terms.get(pins.equalities[0]) else {
        panic!("model equality");
    };
    assert_eq!(symbol.name(), "=");
    assert_eq!(args[0], x, "original source leaf identity");
    same_fields(checked(&exec.ctx.terms, args[1]), &value);
    assert!(
        exec.last_result.is_none(),
        "constructor success supplies no SAT authority"
    );
}

#[test]
fn exact_array_pins_preserve_default_and_newest_override() {
    let (mut exec, _, high) = fixture();
    let frame = Frame::capture(&exec).unwrap().unwrap();
    let positive_zero =
        ModelValue::floating_point_exact(false, 0u8.into(), 0u8.into(), 8, 200).unwrap();
    let negative_zero =
        ModelValue::floating_point_exact(true, 0u8.into(), 0u8.into(), 8, 200).unwrap();
    let key = ModelValue::bitvec(BigInt::from(7u8), 8);
    let value = ModelValue::Array(Box::new(ArrayValue {
        default: positive_zero.clone(),
        store: vec![(key.clone(), high), (key, negative_zero.clone())],
    }));
    let sort = Sort::array(Sort::bitvec(8), Sort::FloatingPoint(8, 200));
    let term = model_value_to_pin_term(
        &mut exec.ctx.terms,
        &value,
        &sort,
        &mut QuantifiedGateElements::default(),
        Some(&frame),
    )
    .expect("whole exact-valued array, no raw constructor fallback");
    assert!(frame.finish(&exec));
    for (index, expected) in [(0u8, positive_zero), (7u8, negative_zero)] {
        let index = exec.ctx.terms.mk_bitvec(BigInt::from(index), 8);
        let select = exec.ctx.terms.mk_select(term, index);
        same_fields(checked(&exec.ctx.terms, select), &expected);
    }
}

#[test]
fn missing_owner_or_mismatched_source_format_cannot_mint_a_wide_pin() {
    let (mut exec, _, value) = fixture();
    let before = exec.ctx.terms.len();
    let mut elements = QuantifiedGateElements::default();
    assert!(model_value_to_pin_term(
        &mut exec.ctx.terms,
        &value,
        &Sort::FloatingPoint(8, 200),
        &mut elements,
        None,
    )
    .is_none());
    let frame = Frame::capture(&exec).unwrap().unwrap();
    for sort in [Sort::FloatingPoint(8, 201), Sort::FloatingPoint(64, 200)] {
        assert!(literal(&mut exec.ctx.terms, &value, &sort, frame.owner()).is_none());
    }
    assert_eq!(exec.ctx.terms.len(), before);
    assert!(frame.finish(&exec));
}

#[test]
fn refusing_original_counter_cannot_be_renewed_by_an_external_read() {
    let (mut exec, _, value) = fixture();
    let frame = Frame::capture(&exec).unwrap().unwrap();
    assert!(frame.owner().admit(usize::MAX, 0).is_err());
    assert!(literal(
        &mut exec.ctx.terms,
        &value,
        &Sort::FloatingPoint(8, 200),
        frame.owner()
    )
    .is_none());
    assert!(!frame.finish(&exec));
    let read = exec.begin_external_evaluation_read();
    assert!(
        exec.evaluation_stop_origin().is_none(),
        "fresh control frame, same model ledger"
    );
    assert!(Frame::capture(&exec).is_err());
    drop(read);
}

#[test]
fn final_frame_rejects_changed_source_or_replaced_original_model_owner() {
    for replace_model in [false, true] {
        let (mut exec, _, value) = fixture();
        let frame = Frame::capture(&exec).unwrap().unwrap();
        assert!(literal(
            &mut exec.ctx.terms,
            &value,
            &Sort::FloatingPoint(8, 200),
            frame.owner()
        )
        .is_some());
        if replace_model {
            exec.begin_external_decision_query(false);
            let mut replacement = Model::empty();
            exec.install_functional_array_candidate(&mut replacement);
            assert!(replacement.construction_owner.is_some());
            exec.last_model = Some(replacement);
        } else {
            exec.execute_all(&parse("(declare-const later Int)").unwrap())
                .unwrap();
        }
        assert!(
            !frame.finish(&exec),
            "construction DATA cannot transfer original source/owner authority"
        );
    }
}

#[test]
fn late_exact_array_entry_without_retained_owner_refuses_before_any_prefix_copy() {
    let (mut exec, _, _) = fixture();
    exec.last_model.as_mut().unwrap().construction_owner = None;
    let frame = Frame::capture(&exec).unwrap().unwrap();
    assert!(
        frame.model_owner().is_none(),
        "current read is not a retained model grant"
    );
    let ordinary = ModelValue::FloatingPoint {
        sign: false,
        exponent: 127,
        significand: 1,
        exponent_bits: 8,
        significand_bits: 24,
    };
    let mut data = ArrayValue {
        default: ordinary.clone(),
        store: vec![
            (ModelValue::bitvec(1u8.into(), 8), ordinary.clone()),
            (ModelValue::bitvec(2u8.into(), 8), ordinary),
        ],
    };
    let exact = ModelValue::floating_point_exact(false, 127u8.into(), 3u8.into(), 8, 24).unwrap();
    data.store.push((ModelValue::bitvec(3u8.into(), 8), exact));
    let sort = Sort::array(Sort::bitvec(8), Sort::FloatingPoint(8, 24));
    let value = ModelValue::Array(Box::new(data));
    let before = exec.ctx.terms.len();
    for owner in [None, Some(&frame)] {
        assert!(model_value_to_pin_term(
            &mut exec.ctx.terms,
            &value,
            &sort,
            &mut QuantifiedGateElements::default(),
            owner,
        )
        .is_none());
        assert_eq!(
            exec.ctx.terms.len(),
            before,
            "no default/earlier store is copied first"
        );
    }
    let ModelValue::Array(mut legacy) = value else {
        unreachable!()
    };
    legacy.store.pop();
    assert!(
        model_value_to_pin_term(
            &mut exec.ctx.terms,
            &ModelValue::Array(legacy),
            &sort,
            &mut QuantifiedGateElements::default(),
            Some(&frame),
        )
        .is_some(),
        "legacy array pins retain their existing supported behavior"
    );
    assert!(frame.finish(&exec));
}

#[test]
fn actual_uf_placeholder_row_reconstructs_wide_result_under_original_owner() {
    let (mut exec, x, value) = fixture();
    let info = exec.ctx.symbol_info("f").unwrap();
    let name = exec.ctx.symbol_identity_name("f", info).to_string();
    let mut euf = ay_euf::EufModel::default();
    euf.function_tables.insert(
        name.clone(),
        vec![(vec!["0".to_string()], format!("@?{}", x.0))],
    );
    exec.last_model.as_mut().unwrap().euf_model = Some(euf);
    let root = authored_root(&exec);
    let (interpretations, _) =
        exec.quantified_gate_uf_interps(root, &mut QuantifiedGateElements::default());
    let interpretation = interpretations.get(&name).unwrap_or_else(|| {
        panic!(
            "whole actual UF head is reconstructible; root={} interpretations={:?}",
            exec.format_term(root),
            interpretations.keys().collect::<Vec<_>>()
        )
    });
    assert!(
        interpretation.rows.is_empty(),
        "one row supplies the printer's else branch"
    );
    same_fields(checked(&exec.ctx.terms, interpretation.else_value), &value);
    assert!(
        exec.last_result.is_none(),
        "row construction supplies no verdict authority"
    );
}

#[test]
fn actual_ground_fold_caller_reconstructs_the_wide_free_value() {
    let (mut exec, x, value) = fixture();
    let birth = exec.ctx.terms.entry_stamp(x);
    let root = authored_root(&exec);
    let folded =
        exec.quantified_gate_fold_ground_values(root, &mut QuantifiedGateElements::default());
    let TermData::Forall(_, body, _) = exec.ctx.terms.get(folded) else {
        panic!("original quantified shape");
    };
    let TermData::App(symbol, args) = exec.ctx.terms.get(*body) else {
        panic!(
            "original matrix equality; root={} folded={}",
            exec.format_term(root),
            exec.format_term(folded)
        );
    };
    assert_eq!(symbol.name(), "fp.leq");
    assert_eq!(args.len(), 2);
    same_fields(checked(&exec.ctx.terms, args[1]), &value);
    assert_eq!(exec.ctx.terms.entry_stamp(x), birth);
    assert!(exec.last_result.is_none());
}
