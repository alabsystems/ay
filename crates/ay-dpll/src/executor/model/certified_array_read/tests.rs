// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::model::{CertifiedConstInterpBody, CertifiedConstInterpWitness};
use ay_core::{kani_compat::DetHashMap, Symbol};
use num_bigint::BigInt;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

mod fixtures;
use fixtures::*;

/// Every package these tests install is a CONSTANT interpretation.
fn constant(value: TermId) -> CertifiedConstInterpWitness {
    CertifiedConstInterpWitness::Constant(value)
}

/// The closed value the package's first (constant) entry publishes.
fn first_value(model: &Model) -> TermId {
    model.certified_const_interp_entries()[0]
        .constant_value()
        .expect("every package these tests install is constant")
}

#[test]
fn nonzero_owned_array_original_fresh_direct_and_public_reads_agree() {
    let mut exec = executor("");
    let a = term(&mut exec, "a");
    let index = term(&mut exec, "#x0000000000000003");
    let original = term(&mut exec, "(select a #x0000000000000003)");
    let mut model = package(&mut exec, "a", 7);
    conflict(&mut model, a, original, 99);
    let fresh = term(&mut exec, "(select a #xffffffffffffffff)");
    assert_eq!(exec.evaluate_select(&model, a, index), bv(7));
    for read in [original, fresh] {
        assert_eq!(exec.evaluate_term(&model, read), bv(7));
        assert_eq!(exec.term_value_string(&model, read).unwrap(), "#x07");
    }
    assert_eq!(
        exec.term_value_string(&model, a).unwrap(),
        "((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07)"
    );
    exec.last_result = Some(crate::executor_types::SolveResult::Sat);
    exec.last_model = Some(model);
    let values = exec.values(&[
        ("a".into(), a),
        ("(select a #xffffffffffffffff)".into(), fresh),
    ]);
    assert!(!values.contains("error"), "{values}");
    assert!(
        values.contains("((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07)"),
        "{values}"
    );
    assert!(values.contains("#x07"), "{values}");
    assert!(!values.contains("#x63"), "{values}");

    // The same owner must beat arithmetic and congruence fallback sources,
    // not just the BV/ArrayModel representations exercised above.
    let mut exec = executor("(declare-const ints (Array Int Int))");
    let array = term(&mut exec, "ints");
    let read = term(&mut exec, "(select ints 3)");
    let seven = exec.ctx.terms.mk_int(BigInt::from(7));
    let ninety_nine = exec.ctx.terms.mk_int(BigInt::from(99));
    let value = exec.ctx.terms.mk_const_array(Sort::Int, seven);
    let mut model = Model::empty();
    model
        .install_certified_const_interps(&exec.ctx, vec![(binding(&exec, "ints"), constant(value))])
        .unwrap();
    let mut raw = DetHashMap::default();
    raw.insert(read, BigInt::from(99));
    model.lia_model = Some(ay_lia::LiaModel { values: raw });
    let mut euf = ay_euf::EufModel::default();
    euf.func_app_const_terms.insert(read, ninety_nine);
    model.euf_model = Some(euf);
    assert_eq!(exec.term_value_string(&model, read).unwrap(), "7");
    assert_eq!(
        exec.term_value_string(&model, array).unwrap(),
        "((as const (Array Int Int)) 7)"
    );
}

#[test]
fn owned_array_clone_preserves_values_but_foreign_model_does_not_inherit_them() {
    let mut exec = executor("");
    let read = term(&mut exec, "(select a #x0000000000000000)");
    let exact = package(&mut exec, "a", 7);
    let cloned = exact.clone();
    let foreign = Model::empty();
    exec.last_model = Some(foreign.clone());
    assert_eq!(exec.evaluate_term(&exact, read), bv(7));
    assert_eq!(exec.evaluate_term(&cloned, read), bv(7));
    assert!(exec.certified_const_array_read(&foreign, read).is_none());
    assert!(matches!(
        exec.evaluate_term(&foreign, read),
        EvalValue::Unknown
    ));
}

#[test]
fn owned_array_slot_reuse_and_scope_redeclaration_are_terminal() {
    let mut exec = executor("");
    let a = term(&mut exec, "a");
    let read = term(&mut exec, "(select a #x0000000000000003)");
    let checkpoint = exec.ctx.terms.rollback_checkpoint();
    let mut model = package(&mut exec, "a", 173);
    let old_value = first_value(&model);
    conflict(&mut model, a, read, 99);
    exec.ctx.terms.rollback_to(checkpoint);
    let replacement_cell = exec.ctx.terms.mk_bitvec(BigInt::from(174), 8);
    let replacement = exec
        .ctx
        .terms
        .mk_const_array(Sort::bitvec(64), replacement_cell);
    assert_eq!(
        replacement, old_value,
        "same numeric value slot, different stamp"
    );
    refuse(&exec, &model, a, read);

    let mut exec = executor("(push 1) (declare-const scoped (Array (_ BitVec 64) (_ BitVec 8)))");
    let mut model = package(&mut exec, "scoped", 7);
    exec.execute_all(
        &ay_frontend::parse("(pop 1) (declare-const scoped (Array (_ BitVec 64) (_ BitVec 8)))")
            .unwrap(),
    )
    .unwrap();
    let a = term(&mut exec, "scoped");
    let read = term(&mut exec, "(select scoped #x0000000000000003)");
    conflict(&mut model, a, read, 99);
    refuse(&exec, &model, a, read);
}

#[test]
fn owned_array_structural_stores_and_nested_reads_use_the_closed_base() {
    let mut exec =
        executor("(declare-const aa (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 8))))");
    let mut model = package(&mut exec, "a", 7);
    let inner = first_value(&model);
    let outer = exec.ctx.terms.mk_const_array(Sort::bitvec(64), inner);
    let a_binding = binding(&exec, "a");
    let aa_binding = binding(&exec, "aa");
    model
        .install_certified_const_interps(
            &exec.ctx,
            vec![(a_binding, constant(inner)), (aa_binding, constant(outer))],
        )
        .unwrap();
    let cases = [
        ("(store a #x0000000000000003 #x09)", "#x0000000000000003", 9),
        ("(store a #x0000000000000003 #x09)", "#xffffffffffffffff", 7),
        ("(select aa #xffffffffffffffff)", "#x0000000000000003", 7),
    ];
    for (array, index, expected) in cases {
        let array = term(&mut exec, array);
        let index = term(&mut exec, index);
        // Do not let mk_select simplify away the ROW1 test before evaluation.
        let read = exec
            .ctx
            .terms
            .mk_app(Symbol::named("select"), [array, index], Sort::bitvec(8));
        assert_eq!(exec.evaluate_select(&model, array, index), bv(expected));
        assert_eq!(exec.evaluate_term(&model, read), bv(expected));
        assert_eq!(
            exec.term_value_string(&model, read).unwrap(),
            format!("#x{expected:02x}")
        );
    }
    let aa = term(&mut exec, "aa");
    assert_eq!(exec.term_value_string(&model, aa).unwrap(), "((as const (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 8)))) ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07))");
}

#[test]
fn owned_scalar_operands_beat_raw_pins_and_compound_store_reads_refuse() {
    let mut exec = executor("(declare-const i (_ BitVec 64)) (declare-const byte (_ BitVec 8))");
    let a = term(&mut exec, "a");
    let i = term(&mut exec, "i");
    let byte = term(&mut exec, "byte");
    let three = exec.ctx.terms.mk_bitvec(BigInt::from(3), 64);
    let four = exec.ctx.terms.mk_bitvec(BigInt::from(4), 64);
    let nine = exec.ctx.terms.mk_bitvec(BigInt::from(9), 8);
    let mut model = package(&mut exec, "a", 7);
    let array_value = first_value(&model);
    model
        .install_certified_const_interps(
            &exec.ctx,
            vec![
                (binding(&exec, "a"), constant(array_value)),
                (binding(&exec, "i"), constant(three)),
                (binding(&exec, "byte"), constant(nine)),
            ],
        )
        .unwrap();
    model.dt_pins.insert(
        i,
        EvalValue::BitVec {
            value: BigInt::from(4),
            width: 64,
        },
    );
    model.dt_pins.insert(byte, bv(88));
    let sort = exec.ctx.terms.sort(a).clone();
    let store = exec
        .ctx
        .terms
        .mk_app(Symbol::named("store"), [a, i, byte], sort.clone());
    for (index, expected) in [(three, 9), (i, 9), (four, 7)] {
        let read = exec
            .ctx
            .terms
            .mk_app(Symbol::named("select"), [store, index], Sort::bitvec(8));
        conflict(&mut model, a, read, 99);
        assert_eq!(exec.evaluate_select(&model, store, index), bv(expected));
        assert_eq!(exec.evaluate_term(&model, read), bv(expected));
        assert_eq!(
            exec.term_value_string(&model, read).unwrap(),
            format!("#x{expected:02x}")
        );
    }
    let one = exec.ctx.terms.mk_bitvec(BigInt::from(1), 64);
    let compound_index = exec
        .ctx
        .terms
        .mk_app(Symbol::named("bvadd"), [i, one], Sort::bitvec(64));
    model.dt_pins.insert(
        compound_index,
        EvalValue::BitVec {
            value: BigInt::from(3),
            width: 64,
        },
    );
    let compound_store = exec.ctx.terms.mk_app(
        Symbol::named("store"),
        [a, compound_index, byte],
        sort.clone(),
    );
    let one_byte = exec.ctx.terms.mk_bitvec(BigInt::from(1), 8);
    let compound_byte =
        exec.ctx
            .terms
            .mk_app(Symbol::named("bvadd"), [byte, one_byte], Sort::bitvec(8));
    model.dt_pins.insert(compound_byte, bv(9));
    let value_store = exec
        .ctx
        .terms
        .mk_app(Symbol::named("store"), [a, i, compound_byte], sort);
    for (array, index) in [
        (store, compound_index),
        (compound_store, three),
        (value_store, three),
    ] {
        let read = exec
            .ctx
            .terms
            .mk_app(Symbol::named("select"), [array, index], Sort::bitvec(8));
        conflict(&mut model, a, read, 99);
        assert!(matches!(
            exec.evaluate_select(&model, array, index),
            EvalValue::Unknown
        ));
        assert!(matches!(
            exec.evaluate_term(&model, read),
            EvalValue::Unknown
        ));
        assert!(exec.term_value_string(&model, read).is_err());
    }
    // A constant function is independent of its argument; no branch/value is
    // chosen using the unsupported compound index's stale cached result.
    let constant = exec.ctx.terms.mk_app(
        Symbol::named("select"),
        [a, compound_index],
        Sort::bitvec(8),
    );
    conflict(&mut model, a, constant, 99);
    assert_eq!(exec.evaluate_term(&model, constant), bv(7));
}

#[test]
fn owned_array_malformed_and_unsupported_reads_cannot_recover_raw_values() {
    let mut exec = executor("(declare-const condition Bool)");
    let a = term(&mut exec, "a");
    let index = term(&mut exec, "#x0000000000000003");
    let short = exec.ctx.terms.mk_bitvec(BigInt::from(3), 32);
    let sort = exec.ctx.terms.sort(a).clone();
    let malformed_store = exec
        .ctx
        .terms
        .mk_app(Symbol::named("store"), [a, index], sort.clone());
    let wrong_cell = exec
        .ctx
        .terms
        .mk_app(Symbol::named("store"), [a, index, short], sort.clone());
    let condition = term(&mut exec, "condition");
    let other = term(&mut exec, "b");
    let conditional = exec.ctx.terms.mk_ite(condition, a, other);
    let mut model = package(&mut exec, "a", 7);
    for array in [malformed_store, wrong_cell, conditional] {
        let read = exec
            .ctx
            .terms
            .mk_app(Symbol::named("select"), [array, index], Sort::bitvec(8));
        conflict(&mut model, array, read, 99);
        assert!(matches!(
            exec.evaluate_term(&model, read),
            EvalValue::Unknown
        ));
        assert!(exec.term_value_string(&model, read).is_err());
    }
    let wrong_index = exec
        .ctx
        .terms
        .mk_app(Symbol::named("select"), [a, short], Sort::bitvec(8));
    let wrong_result = exec
        .ctx
        .terms
        .mk_app(Symbol::named("select"), [a, index], Sort::bitvec(32));
    let wrong_arity =
        exec.ctx
            .terms
            .mk_app(Symbol::named("select"), [a, index, short], Sort::bitvec(8));
    let malformed_owner = exec.ctx.terms.mk_app(Symbol::named("a"), [index], sort);
    for read in [
        wrong_index,
        wrong_result,
        wrong_arity,
        exec.ctx.terms.mk_app(
            Symbol::named("select"),
            [malformed_owner, index],
            Sort::bitvec(8),
        ),
    ] {
        conflict(&mut model, a, read, 99);
        assert!(matches!(
            exec.evaluate_term(&model, read),
            EvalValue::Unknown
        ));
        assert!(exec.term_value_string(&model, read).is_err());
    }
    let ordinary = term(&mut exec, "(select b #x0000000000000003)");
    assert!(exec.certified_const_array_read(&model, ordinary).is_none());
}

#[test]
fn owned_array_stop_is_sticky_and_a_fresh_read_can_succeed() {
    let mut exec = executor("");
    let a = term(&mut exec, "a");
    let read = term(&mut exec, "(select a #x0000000000000003)");
    let mut model = package(&mut exec, "a", 7);
    conflict(&mut model, a, read, 99);
    let flag = Arc::new(AtomicBool::new(true));
    exec.set_interrupt(flag.clone());
    let scope = exec.begin_external_evaluation_read();
    assert!(matches!(
        exec.evaluate_term(&model, read),
        EvalValue::Unknown
    ));
    flag.store(false, Ordering::Relaxed);
    refuse(&exec, &model, a, read);
    drop(scope);
    let scope = exec.begin_external_evaluation_read();
    assert_eq!(exec.evaluate_term(&model, read), bv(7));
    let budget = eval_guard::EvalWorkBudget::new(0);
    assert!(matches!(
        exec.evaluate_term(&model, read),
        EvalValue::Unknown
    ));
    assert!(budget.exhausted());
    drop(budget);
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::DeterministicResourceBudget)
    );
    refuse(&exec, &model, a, read);
    drop(scope);
    let _fresh = exec.begin_external_evaluation_read();
    assert_eq!(exec.evaluate_term(&model, read), bv(7));
}

#[test]
fn owned_array_depth_limit_and_scoped_binding_do_not_publish_fallbacks() {
    let mut exec = executor("(declare-const condition Bool)");
    let a = term(&mut exec, "a");
    let read = term(&mut exec, "(select a #x0000000000000003)");
    let model = package(&mut exec, "a", 7);
    crate::executor::model::with_scoped_term_evaluation_override_for_test(
        a,
        EvalValue::Unknown,
        || {
            assert!(matches!(
                exec.evaluate_term(&model, read),
                EvalValue::Unknown
            ));
            assert!(exec.term_value_string(&model, read).is_err());
        },
    );
    let index = term(&mut exec, "#x0000000000000003");
    let cell = exec.ctx.terms.mk_bitvec(BigInt::from(9), 8);
    let sort = exec.ctx.terms.sort(a).clone();
    let mut deep = a;
    for _ in 0..=MAX_READ_DEPTH {
        deep = exec
            .ctx
            .terms
            .mk_app(Symbol::named("store"), [deep, index, cell], sort.clone());
    }
    let read = exec
        .ctx
        .terms
        .mk_app(Symbol::named("select"), [deep, index], Sort::bitvec(8));
    assert!(matches!(
        exec.evaluate_term(&model, read),
        EvalValue::Unknown
    ));
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::DeterministicResourceBudget)
    );

    // Pin the depth guard independently of the shared work guard: the long
    // production read above may hit either bound first.
    let _fresh = exec.begin_external_evaluation_read();
    assert!(!CertifiedArrayRead::new().visit(&exec, a, MAX_READ_DEPTH + 1));
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::DeterministicResourceBudget)
    );

    let mut exec = executor("");
    let a = term(&mut exec, "a");
    let read = term(&mut exec, "(select a #x0000000000000003)");
    let mut model = package(&mut exec, "a", 7);
    // Duplicate a genuine stamped slot; no additional value authority is
    // introduced, but an oversized retained graph must be refused pre-scan.
    let entry = &mut Arc::get_mut(&mut model.certified_const_interps.entries).unwrap()[0];
    let CertifiedConstInterpBody::Constant { value_graph, .. } = &mut entry.body else {
        panic!("a constant-array package has a constant body");
    };
    let slot = value_graph.slots[0];
    value_graph.slots = vec![slot; MAX_READ_WORK + 1].into_boxed_slice();
    refuse(&exec, &model, a, read);
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::DeterministicResourceBudget)
    );

    let mut exec = executor("(declare-const wide (Array (_ BitVec 64) (_ BitVec 200000)))");
    let wide = term(&mut exec, "wide");
    let cell = exec
        .ctx
        .terms
        .mk_bitvec(BigInt::from(1) << 199_999usize, 200_000);
    let value = exec.ctx.terms.mk_const_array(Sort::bitvec(64), cell);
    let mut model = Model::empty();
    model
        .install_certified_const_interps(&exec.ctx, vec![(binding(&exec, "wide"), constant(value))])
        .unwrap();
    assert!(exec.term_value_string(&model, wide).is_err());
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::DeterministicResourceBudget)
    );
}
