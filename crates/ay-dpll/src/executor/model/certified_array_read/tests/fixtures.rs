// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::model::CertifiedConstInterpWitness;

pub(super) fn executor(suffix: &str) -> Executor {
    let mut exec = Executor::new();
    exec.execute_all(&ay_frontend::parse(&format!("(set-logic ALL) (declare-const a (Array (_ BitVec 64) (_ BitVec 8))) (declare-const b (Array (_ BitVec 64) (_ BitVec 8))) {suffix}")).unwrap()).unwrap();
    exec
}

pub(super) fn term(exec: &mut Executor, spelling: &str) -> TermId {
    let commands = ay_frontend::parse(&format!("(get-value ({spelling}))")).unwrap();
    let ay_frontend::Command::GetValue(terms) = &commands[0] else {
        panic!("getter fixture");
    };
    exec.ctx.elaborate_surface_subterm(&terms[0].1).unwrap()
}

pub(super) fn binding(exec: &Executor, name: &str) -> ay_frontend::CheckedProjectionBinding {
    let info = exec.ctx.symbol_info(name).unwrap();
    exec.ctx
        .check_projection_declaration(&ay_frontend::ProjectionBindingRequest {
            symbol: Symbol::named(exec.ctx.symbol_identity_name(name, info)),
            parameter_sorts: info.arg_sorts.clone(),
            result_sort: info.sort.clone(),
        })
        .unwrap()
}

pub(super) fn package(exec: &mut Executor, name: &str, byte: u8) -> Model {
    let binding = binding(exec, name);
    let cell = exec.ctx.terms.mk_bitvec(BigInt::from(byte), 8);
    let value = exec.ctx.terms.mk_const_array(Sort::bitvec(64), cell);
    let mut model = Model::empty();
    model
        .install_certified_const_interps(
            &exec.ctx,
            vec![(binding, CertifiedConstInterpWitness::Constant(value))],
        )
        .unwrap();
    model
}

pub(super) fn bv(value: u8) -> EvalValue {
    EvalValue::BitVec {
        value: BigInt::from(value),
        width: 8,
    }
}

pub(super) fn conflict(model: &mut Model, array: TermId, read: TermId, value: u8) {
    let mut values = DetHashMap::default();
    values.insert(read, BigInt::from(value));
    model.bv_model = Some(ay_bv::BvModel {
        values,
        term_to_bits: DetHashMap::default(),
        bool_overrides: DetHashMap::default(),
    });
    model.dt_pins.insert(read, bv(value));
    model.completed_values.insert(read, bv(value));
    let mut arrays = ay_arrays::ArrayModel::default();
    arrays.array_values.insert(
        array,
        ay_arrays::ArrayInterpretation {
            default: Some(format!("#x{value:02x}")),
            stores: Vec::new(),
            index_sort: Some(Sort::bitvec(64)),
            element_sort: Some(Sort::bitvec(8)),
        },
    );
    model.array_model = Some(arrays);
}

pub(super) fn refuse(exec: &Executor, model: &Model, array: TermId, read: TermId) {
    assert!(matches!(
        exec.evaluate_term(model, read),
        EvalValue::Unknown
    ));
    assert!(exec.term_value_string(model, read).is_err());
    assert!(exec.term_value_string(model, array).is_err());
    let TermData::App(_, args) = exec.ctx.terms.get(read) else {
        panic!("select fixture");
    };
    assert!(matches!(
        exec.evaluate_select(model, array, args[1]),
        EvalValue::Unknown
    ));
}
