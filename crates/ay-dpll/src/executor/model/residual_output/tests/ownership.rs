// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Deliberately corrupt private model DATA; this does not construct SAT authority.

use super::*;
use crate::executor::model::{
    CertifiedConstInterpBody, CertifiedConstInterpEntry, StampedClosedValueGraph,
};
use std::sync::Arc;

#[test]
fn a_competing_constant_representation_cannot_hide_the_retained_array_owner() {
    let (mut executor, mut model, array) = fixtures::completed();
    let fresh = fixtures::length(&mut executor, array, 9);
    let alternate = alternate_array(&mut executor, array);
    let sort = executor.ctx.terms.sort(array).clone();
    let binding = executor
        .ctx
        .check_projection_declaration(&ay_frontend::ProjectionBindingRequest {
            symbol: Symbol::named("a"),
            parameter_sorts: vec![],
            result_sort: sort,
        })
        .unwrap();
    // The ordinary installer deliberately does not admit constructor graphs.
    // Inject this second representation solely to test priority under corrupt
    // internal data; no theorem/grant or native publication seal is supplied.
    let mut pending = vec![alternate];
    let mut seen = HashSet::default();
    let mut slots = Vec::new();
    while let Some(term) = pending.pop() {
        if seen.insert(term) {
            slots.push((term, executor.ctx.terms.entry_stamp(term).unwrap()));
            pending.extend(executor.ctx.terms.children(term));
        }
    }
    model.certified_const_interps.entries = Arc::from(
        vec![CertifiedConstInterpEntry {
            binding,
            body: CertifiedConstInterpBody::Constant {
                value: alternate,
                value_graph: StampedClosedValueGraph {
                    slots: slots.into_boxed_slice(),
                },
            },
            declaration_term: Some((array, executor.ctx.terms.entry_stamp(array).unwrap())),
        }]
        .into_boxed_slice(),
    );

    let mut competing_only = model.clone();
    competing_only.residual_arrays = None;
    assert!(
        matches!(executor.independent_completed_model_value(&competing_only, fresh),
        Some(ModelValue::BitVec { value, width: 64 }) if value == BigInt::from(99))
    );
    fixtures::assert_five(
        executor
            .independent_completed_model_value(&model, fresh)
            .unwrap(),
    );
    assert_eq!(executor.evaluate_term(&model, fresh), fixtures::five());
    executor.last_result = Some(crate::executor_types::SolveResult::Sat);
    executor.last_model = Some(model);
    let printed = executor.model();
    assert!(!printed.starts_with("(error"), "{printed}");
    let literal = executor
        .term_value_string(executor.last_model.as_ref().unwrap(), array)
        .unwrap();
    assert!(printed.contains(&literal));
    assert!(!printed.contains("#x0000000000000063"), "{printed}");
    fixtures::check_array_literal(&literal);
}

fn alternate_array(executor: &mut Executor, array: TermId) -> TermId {
    let zero = executor.ctx.terms.mk_bitvec(0.into(), 8);
    let data = executor.ctx.terms.mk_const_array(Sort::bitvec(64), zero);
    let wrong = executor.ctx.terms.mk_bitvec(99.into(), 64);
    let inner_sort = executor.dt_registry_lookup("Outer").unwrap().constructors[0].fields[1]
        .sort
        .clone();
    let inner = executor
        .ctx
        .terms
        .mk_app(Symbol::named("mkInner"), [wrong, data], inner_sort);
    let no = executor.ctx.terms.mk_bool(false);
    let outer_sort = executor
        .ctx
        .terms
        .sort(array)
        .array_element()
        .unwrap()
        .clone();
    let outer = executor
        .ctx
        .terms
        .mk_app(Symbol::named("mkOuter"), [no, inner], outer_sort);
    executor.ctx.terms.mk_const_array(Sort::bitvec(64), outer)
}
