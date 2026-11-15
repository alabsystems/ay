// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
#![allow(clippy::unwrap_used)]

use super::*;

fn bv(width: u32) -> ChcSort {
    ChcSort::BitVec(width)
}

fn declaration(name: &str, args: Vec<ChcSort>, result: ChcSort) -> QuantifiedChcFunction {
    QuantifiedChcFunction::new(name.into(), args, result)
}

fn registry(declarations: Vec<QuantifiedChcFunction>) -> ChcResult<Functions> {
    let problem = ChcProblem::new();
    Functions::new(declarations, &problem, &Registry::new(&problem).unwrap())
}

#[test]
fn ordered_scalar_signatures_and_unused_nullary_declarations_are_exact() {
    let declarations = vec![
        declaration("unused value", vec![], bv(136)),
        declaration("callee", vec![ChcSort::Bool, bv(72), bv(128)], bv(1)),
    ];
    let functions = registry(declarations.clone()).unwrap();
    assert_eq!(functions.declarations(), declarations);
    assert_eq!(
        functions.names().collect::<Vec<_>>(),
        ["unused value", "callee"]
    );
    assert_eq!(functions.application("unused value", &[]).unwrap(), bv(136));
    assert_eq!(
        functions
            .application("callee", &[ChcSort::Bool, bv(72), bv(128)])
            .unwrap(),
        bv(1)
    );
    let text = functions.declarations_smtlib().unwrap();
    assert_eq!(text, "(declare-fun |unused value| () (_ BitVec 136))\n(declare-fun callee (Bool (_ BitVec 72) (_ BitVec 128)) (_ BitVec 1))\n");
    assert!(functions.copy_bytes() >= text.len());
    assert!(functions.work() > 0);
    let empty = registry(Vec::new()).unwrap();
    assert!(empty.is_empty());
    assert_eq!((empty.copy_bytes(), empty.work()), (0, 0));
    assert_eq!(empty.declarations_smtlib().unwrap(), "");
}

#[test]
fn malformed_scalar_signatures_and_application_sort_disagreements_refuse() {
    let array = ChcSort::Array(Box::new(bv(64)), Box::new(bv(8)));
    for sort in [
        bv(0),
        bv(crate::MAX_BITVECTOR_WIDTH + 1),
        ChcSort::Int,
        ChcSort::Real,
        array,
        ChcSort::Uninterpreted("Opaque".into()),
    ] {
        assert!(registry(vec![declaration("f", vec![sort.clone()], bv(8))]).is_err());
        assert!(registry(vec![declaration("f", vec![], sort)]).is_err());
    }
    assert!(registry(vec![declaration("relation", vec![bv(8)], ChcSort::Bool)]).is_err());
    let functions = registry(vec![declaration("f", vec![bv(8), ChcSort::Bool], bv(136))]).unwrap();
    for arguments in [
        vec![],
        vec![bv(8)],
        vec![bv(9), ChcSort::Bool],
        vec![ChcSort::Bool, bv(8)],
        vec![bv(8), bv(1)],
    ] {
        assert!(functions.application("f", &arguments).is_err());
    }
    assert!(functions
        .application("undeclared", &[bv(8), ChcSort::Bool])
        .is_err());
    assert!(functions
        .application("f", &[bv(8), ChcSort::Uninterpreted("Bool".into())])
        .is_err());
}

#[test]
fn ordinary_functions_do_not_overload_or_shadow_any_record_operation() {
    let f = declaration("f", vec![bv(8)], bv(8));
    assert!(registry(vec![f.clone(), f]).is_err());
    assert!(registry(vec![
        declaration("f", vec![bv(8)], bv(8)),
        declaration("f", vec![bv(16)], bv(16))
    ])
    .is_err());
    let mut problem = ChcProblem::new();
    problem.declare_predicate("P", vec![]);
    problem.add_datatype_def(
        "Record".into(),
        vec![("mkRecord".into(), vec![("field".into(), bv(8))])],
    );
    let records = Registry::new(&problem).unwrap();
    for name in ["P", "Record", "mkRecord", "field", "is-mkRecord"] {
        assert!(
            Functions::new(vec![declaration(name, vec![], bv(8))], &problem, &records).is_err()
        );
    }
    assert!(Functions::new(
        vec![declaration("other", vec![], bv(8))],
        &problem,
        &records
    )
    .is_ok());
}

#[test]
fn hostile_symbols_and_complete_signature_sizes_refuse_before_owned_indexing() {
    for name in [
        "",
        "select",
        "forall",
        "as",
        "!",
        "lambda",
        "match",
        "Bool",
        "bvadd",
        "has|bar",
        "back\\slash",
        "control\n",
    ] {
        assert!(
            registry(vec![declaration(name, vec![], bv(8))]).is_err(),
            "{name:?}"
        );
    }
    let exact = "x".repeat(super::super::records::MAX_NAME_BYTES);
    assert!(registry(vec![declaration(&exact, vec![], bv(8))]).is_ok());
    assert!(registry(vec![declaration(&(exact + "x"), vec![], bv(8))]).is_err());
    let oversized = vec![bv(1); super::super::source::MAX_NODES + 1];
    assert!(registry(vec![declaration("arity", oversized, bv(8))]).is_err());
    assert!(registry(vec![declaration(
        "wide",
        vec![bv(crate::MAX_BITVECTOR_WIDTH); 64],
        bv(8)
    )])
    .is_err());
}

#[test]
fn combined_relation_function_count_uses_the_existing_source_cap() {
    let cap = super::super::source::MAX_DECLARATIONS;
    let mut problem = ChcProblem::new();
    for index in 0..cap - 1 {
        problem.declare_predicate(format!("P{index}"), vec![]);
    }
    let records = Registry::new(&problem).unwrap();
    assert!(Functions::new(vec![declaration("last", vec![], bv(8))], &problem, &records).is_ok());
    assert!(Functions::new(
        vec![
            declaration("last", vec![], bv(8)),
            declaration("over", vec![], bv(8))
        ],
        &problem,
        &records
    )
    .is_err());
    // This independently authenticates every unused ordinary declaration.
    let many = (0..cap)
        .map(|index| declaration(&format!("f{index}"), vec![], bv(1)))
        .collect();
    assert_eq!(registry(many).unwrap().declarations().len(), cap);
}
