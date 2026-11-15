// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored source through ordinary publication; no SAT search or planted seal.

use super::*;

const MISS: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../benchmarks/smt/model_checker_consumer_store_miss_residual/outer_inner_miss_sat.smt2"
));
const CONFLICT: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../benchmarks/smt/model_checker_consumer_store_miss_residual/inner_miss_conflict_unsat.smt2"
));
const HIT_CONFLICT: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../benchmarks/smt/model_checker_consumer_store_miss_residual/newest_store_hit_unsat.smt2"
));

#[test]
fn ordinary_emission_recovers_misses_and_fresh_store_reads_use_the_complete_array() {
    let (mut executor, a, b) = fixture(MISS);
    assert!(executor
        .completed_model_value(executor.last_model.as_ref().unwrap(), a)
        .unwrap()
        .is_none());
    assert_eq!(
        executor.emit_sat_verdict(SolveResult::Sat, &[]).unwrap(),
        SolveResult::Sat
    );
    assert!(executor.last_model_validated);
    assert!(executor.last_sat_certificate.is_some());
    assert!(executor.last_model.as_ref().unwrap().has_residual_arrays());
    let base_read = fresh_read(&mut executor, b, 65);
    let ay_core::term::TermData::App(_, arguments) = executor.ctx.terms.get(base_read) else {
        panic!("fresh select");
    };
    let (data, read_key) = (arguments[0], arguments[1]);
    let sort = executor.ctx.terms.sort(data).clone();
    let written_key = executor.ctx.terms.mk_bitvec(64.into(), 64);
    let seven = executor.ctx.terms.mk_bitvec(7.into(), 40);
    let stored =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("store"), [data, written_key, seven], sort);
    let fresh_miss = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        [stored, read_key],
        Sort::bitvec(40),
    );
    let fresh_hit = executor.ctx.terms.mk_app(
        Symbol::named("select"),
        [stored, written_key],
        Sort::bitvec(40),
    );
    let model = executor.last_model.as_ref().unwrap();
    for (term, expected) in [(base_read, 8), (fresh_miss, 8), (fresh_hit, 7)] {
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
    let literal = executor.term_value_string(model, a).unwrap();
    assert_eq!(literal, executor.term_value_string(model, b).unwrap());
    let sort = array_sort();
    let decoded = Decoded::decode_typed_literals(&[(&literal, &sort)]).unwrap();
    let Decoded::Datatype { constructor, args } = lookup(&decoded[0], 9) else {
        panic!("PbTerm");
    };
    assert_eq!(constructor, "PbTerm_mk");
    let Decoded::Datatype { constructor, args } = &args[1] else {
        panic!("Vec_bv40");
    };
    assert_eq!(constructor, "Vec_bv40_mk");
    assert!(
        matches!(lookup(&args[3], 65), Decoded::BitVec { value, width: 40 } if *value == BigInt::from(8))
    );
    let values = executor.values(&[
        ("a".into(), a),
        ("miss".into(), fresh_miss),
        ("hit".into(), fresh_hit),
    ]);
    assert!(!values.starts_with("(error"), "{values}");
    assert!(values.contains("(miss #x0000000008)"), "{values}");
    assert!(values.contains("(hit #x0000000007)"), "{values}");
    assert!(executor.model().contains(&literal));
    assert!(matches!(
        executor.confirm_sat_with_independent_gate(),
        GateVerdict::ConfirmedSat
    ));
}

#[test]
fn alias_miss_conflict_and_newest_hit_conflict_never_publish_sat() {
    for source in [CONFLICT, HIT_CONFLICT] {
        let (mut executor, a, _) = fixture(source);
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
}
