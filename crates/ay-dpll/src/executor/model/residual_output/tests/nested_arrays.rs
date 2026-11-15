// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Frontend, ordinary publication and typed output tests with an authored empty
//! candidate. These do not run SAT search or forge a prior validation/certificate.

use super::*;
use crate::api::ModelValue as Decoded;
use crate::executor_types::SolveResult;
use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort};

mod stores;

const POSITIVE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../benchmarks/smt/model_checker_consumer_nested_array_residual/pbterm_cells_sat.smt2"
));
const NEGATIVE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../benchmarks/smt/model_checker_consumer_nested_array_residual/pbterm_same_key_unsat.smt2"
));

fn fixture(source: &str) -> (Executor, TermId, TermId) {
    let mut executor = Executor::new();
    for command in ay_frontend::parse("(set-option :produce-models true)").unwrap() {
        executor.execute(&command).unwrap();
    }
    for command in ay_frontend::parse(source).unwrap() {
        match command {
            ay_frontend::Command::CheckSat | ay_frontend::Command::Exit => continue,
            _ => {
                executor.execute(&command).unwrap();
            }
        }
    }
    let a = executor.ctx.source_constant_for_value("a").unwrap().0;
    let b = executor.ctx.source_constant_for_value("b").unwrap().0;
    executor.last_model = Some(Model::empty());
    assert!(!executor.last_model_validated);
    assert!(executor.last_sat_certificate.is_none());
    assert!(!executor.last_model.as_ref().unwrap().has_residual_arrays());
    (executor, a, b)
}

fn fresh_read(executor: &mut Executor, array: TermId, inner: u64) -> TermId {
    let outer_sort = executor
        .ctx
        .terms
        .sort(array)
        .array_element()
        .unwrap()
        .clone();
    let vector_sort = executor.dt_registry_lookup("PbTerm").unwrap().constructors[0].fields[1]
        .sort
        .clone();
    let data_sort = executor
        .dt_registry_lookup("Vec_bv40")
        .unwrap()
        .constructors[0]
        .fields[3]
        .sort
        .clone();
    let zero = executor.ctx.terms.mk_bitvec(0.into(), 64);
    let nine = executor.ctx.terms.mk_bitvec(9.into(), 64);
    let inner = executor.ctx.terms.mk_bitvec(inner.into(), 64);
    let outer = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvadd"), [nine, zero], Sort::bitvec(64));
    let inner = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvadd"), [inner, zero], Sort::bitvec(64));
    let cell = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), [array, outer], outer_sort);
    let vector = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fld_lits"), [cell], vector_sort);
    let data = executor
        .ctx
        .terms
        .mk_app(Symbol::named("fld_data"), [vector], data_sort);
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), [data, inner], Sort::bitvec(40))
}

fn array_sort() -> Sort {
    let vector = Sort::Datatype(DatatypeSort::new(
        "Vec_bv40",
        vec![DatatypeConstructor::new(
            "Vec_bv40_mk",
            vec![
                DatatypeField::new("fld_ptr", Sort::bitvec(64)),
                DatatypeField::new("fld_len", Sort::bitvec(64)),
                DatatypeField::new("fld_cap", Sort::bitvec(64)),
                DatatypeField::new("fld_data", Sort::array(Sort::bitvec(64), Sort::bitvec(40))),
            ],
        )],
    ));
    let element = Sort::Datatype(DatatypeSort::new(
        "PbTerm",
        vec![DatatypeConstructor::new(
            "PbTerm_mk",
            vec![
                DatatypeField::new("fld_coeff", Sort::bitvec(128)),
                DatatypeField::new("fld_lits", vector),
            ],
        )],
    ));
    Sort::array(Sort::bitvec(64), element)
}

fn lookup(value: &Decoded, index: u64) -> &Decoded {
    let Decoded::Array { default, stores } = value else {
        panic!("complete array required");
    };
    stores
        .iter()
        .rev()
        .find_map(|(key, value)| {
            matches!(key, Decoded::BitVec { value, width: 64 } if *value == BigInt::from(index))
                .then_some(value)
        })
        .unwrap_or(default)
}

fn assert_cell(value: &Decoded, index: u64, expected: u64) {
    let Decoded::Datatype { constructor, args } = lookup(value, 9) else {
        panic!("PbTerm");
    };
    assert_eq!(constructor, "PbTerm_mk");
    assert_eq!(args.len(), 2);
    assert!(matches!(&args[0], Decoded::BitVec { value, width: 128 } if *value == BigInt::from(3)));
    let Decoded::Datatype { constructor, args } = &args[1] else {
        panic!("Vec_bv40");
    };
    assert_eq!(constructor, "Vec_bv40_mk");
    assert_eq!(args.len(), 4);
    assert!(
        matches!(lookup(&args[3], index), Decoded::BitVec { value, width: 40 } if *value == BigInt::from(expected))
    );
}

#[test]
fn ordinary_emission_completes_pbterm_inner_arrays_and_serves_fresh_typed_reads() {
    let (mut executor, a, b) = fixture(POSITIVE);
    let before = executor.last_model.as_ref().unwrap();
    assert!(executor.completed_model_value(before, a).unwrap().is_none());
    assert!(matches!(
        executor.evaluate_term(before, a),
        EvalValue::Unknown
    ));
    assert_eq!(
        executor.emit_sat_verdict(SolveResult::Sat, &[]).unwrap(),
        SolveResult::Sat
    );
    assert!(executor.last_model_validated);
    assert!(executor.last_sat_certificate.is_some());
    assert!(executor.last_model.as_ref().unwrap().has_residual_arrays());
    assert!(matches!(
        executor.confirm_sat_with_independent_gate(),
        GateVerdict::ConfirmedSat
    ));

    // Both paths are made after publication and were not per-read commitments.
    let first = fresh_read(&mut executor, a, 64);
    let second = fresh_read(&mut executor, b, 65);
    let model = executor.last_model.as_ref().unwrap();
    for (term, expected) in [(first, 7), (second, 8)] {
        assert_eq!(
            executor.evaluate_term(model, term),
            EvalValue::BitVec {
                value: expected.into(),
                width: 40
            }
        );
        assert!(
            matches!(executor.completed_model_value(model, term).unwrap(),
            Some(ModelValue::BitVec { value, width: 40 }) if value == BigInt::from(expected))
        );
    }
    let a_literal = executor.term_value_string(model, a).unwrap();
    let b_literal = executor.term_value_string(model, b).unwrap();
    assert_eq!(a_literal, b_literal);
    let sort = array_sort();
    let decoded =
        Decoded::decode_typed_literals(&[(&a_literal, &sort), (&b_literal, &sort)]).unwrap();
    for value in &decoded {
        assert_cell(value, 64, 7);
        assert_cell(value, 65, 8);
    }
    let values = executor.values(&[("a".into(), a), ("b".into(), b), ("fresh".into(), first)]);
    assert!(!values.starts_with("(error"), "{values}");
    assert!(values.contains(&format!("(a {a_literal})")), "{values}");
    assert!(values.contains("(fresh #x0000000007)"), "{values}");
    let output = executor.model();
    assert!(!output.starts_with("(error"), "{output}");
    assert!(output.contains(&a_literal), "{output}");
}

#[test]
fn conflicting_semantic_inner_key_never_publishes_the_proposed_sat_candidate() {
    let (mut executor, a, _) = fixture(NEGATIVE);
    assert!(executor
        .completed_model_value(executor.last_model.as_ref().unwrap(), a)
        .unwrap()
        .is_none());
    assert_ne!(
        executor.emit_sat_verdict(SolveResult::Sat, &[]).unwrap(),
        SolveResult::Sat
    );
    assert!(executor.last_sat_certificate.is_none());
    assert!(!executor.last_model_validated);
    assert_ne!(executor.last_result, Some(SolveResult::Sat));
    assert!(executor.model().starts_with("(error"));
    assert!(executor.values(&[("a".into(), a)]).starts_with("(error"));
}
