// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort};

struct Unpinned<'a>(&'a Executor);

impl ModelView for Unpinned<'_> {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        None
    }

    fn datatype_def(&self, name: &str) -> Option<DatatypeSort> {
        self.0.dt_registry_lookup(name)
    }
}

pub(super) fn assignments() -> (
    Executor,
    Vec<ay_model_check::CompletedArrayAssignment>,
    TermId,
) {
    let mut executor = Executor::new();
    let source = "(set-option :produce-models true) (set-logic ALL)
        (declare-datatype Inner ((mkInner (len (_ BitVec 64))
          (data (Array (_ BitVec 64) (_ BitVec 8))))))
        (declare-datatype Outer ((mkOuter (flag Bool) (inner Inner))))
        (declare-const a (Array (_ BitVec 64) Outer))
        (assert (= (len (inner (select a (_ bv9 64)))) (_ bv5 64)))";
    for command in ay_frontend::parse(source).unwrap() {
        executor.ctx.process_command(&command).unwrap();
    }
    let array = executor.ctx.source_constant_for_value("a").unwrap().0;
    let view = Unpinned(&executor);
    let (verdict, completion) = ay_model_check::confirm_model_with_array_completion(
        &executor.ctx.terms,
        &view,
        &executor.ctx.assertions,
    )
    .into_parts();
    assert!(matches!(verdict, GateVerdict::ConfirmedSat));
    let assignments = completion
        .expect("a genuinely free array must be completed")
        .into_assignments()
        .unwrap();
    assert_eq!(assignments.len(), 1);
    (executor, assignments, array)
}

pub(super) fn completed() -> (Executor, Model, TermId) {
    let (executor, assignments, array) = assignments();
    let mut model = Model::empty();
    model
        .install_residual_arrays(&executor.ctx, assignments)
        .unwrap();
    (executor, model, array)
}

pub(super) fn length(executor: &mut Executor, array: TermId, index: u64) -> TermId {
    let literal = executor.ctx.terms.mk_bitvec(index.into(), 64);
    let zero = executor.ctx.terms.mk_bitvec(0.into(), 64);
    // Raw addition is deliberately not folded. This select/selector path was
    // absent from the checked source and must still read the owned whole array.
    let index =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("bvadd"), [literal, zero], Sort::bitvec(64));
    let outer = executor
        .ctx
        .terms
        .sort(array)
        .array_element()
        .unwrap()
        .clone();
    let inner = executor.dt_registry_lookup("Outer").unwrap().constructors[0].fields[1]
        .sort
        .clone();
    let cell = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), [array, index], outer);
    let record = executor
        .ctx
        .terms
        .mk_app(Symbol::named("inner"), [cell], inner);
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("len"), [record], Sort::bitvec(64))
}

pub(super) fn five() -> EvalValue {
    EvalValue::BitVec {
        value: 5.into(),
        width: 64,
    }
}

pub(super) fn assert_five(value: ModelValue) {
    assert!(matches!(value, ModelValue::BitVec { value, width: 64 } if value == BigInt::from(5)));
}

pub(super) fn check_array_literal(literal: &str) {
    let inner = Sort::Datatype(DatatypeSort::new(
        "Inner",
        vec![DatatypeConstructor::new(
            "mkInner",
            vec![
                DatatypeField::new("len", Sort::bitvec(64)),
                DatatypeField::new("data", Sort::array(Sort::bitvec(64), Sort::bitvec(8))),
            ],
        )],
    ));
    let outer = Sort::Datatype(DatatypeSort::new(
        "Outer",
        vec![DatatypeConstructor::new(
            "mkOuter",
            vec![
                DatatypeField::new("flag", Sort::Bool),
                DatatypeField::new("inner", inner),
            ],
        )],
    ));
    let sort = Sort::array(Sort::bitvec(64), outer);
    let values = crate::api::ModelValue::decode_typed_literals(&[(literal, &sort)]).unwrap();
    let crate::api::ModelValue::Array { default, stores } = &values[0] else {
        panic!("whole array");
    };
    assert!(
        matches!(default.as_ref(), crate::api::ModelValue::Datatype { constructor, .. } if constructor == "mkOuter")
    );
    let (_, cell) = stores
        .iter()
        .find(|(key, _)| {
            matches!(key,
        crate::api::ModelValue::BitVec { value, width: 64 } if *value == BigInt::from(9))
        })
        .unwrap();
    let crate::api::ModelValue::Datatype { constructor, args } = cell else {
        panic!("outer record");
    };
    assert_eq!(constructor, "mkOuter");
    let crate::api::ModelValue::Datatype { constructor, args } = &args[1] else {
        panic!("inner record");
    };
    assert_eq!(constructor, "mkInner");
    assert!(
        matches!(&args[0], crate::api::ModelValue::BitVec { value, width: 64 } if *value == BigInt::from(5))
    );
    assert!(
        matches!(&args[1], crate::api::ModelValue::Array { default, stores }
        if stores.is_empty() && matches!(default.as_ref(), crate::api::ModelValue::BitVec { value, width: 8 } if *value == BigInt::from(0)))
    );
}
