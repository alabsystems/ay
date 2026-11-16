// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Binary128 ground arithmetic needs a checked original-expression proof.

use ay_dpll::api::{Logic, Solver, SolverConfig, Sort};
use num_bigint::BigInt;
use std::time::Duration;

#[test]
fn exact_199_bit_symbolic_model_reaches_native_public_access_without_truncation() {
    let config = SolverConfig::default()
        .with_timeout(Duration::from_secs(5))
        .with_memory_limit(256 * 1024 * 1024);
    let mut solver = Solver::try_new_with_config(Logic::QfFp, config).unwrap();
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 200));
    let fraction = (BigInt::from(1) << 198usize) | BigInt::from(1);
    let sign = solver.try_bv_const_bigint(&BigInt::from(0), 1).unwrap();
    let exponent = solver.try_bv_const_bigint(&BigInt::from(127), 8).unwrap();
    let significand = solver.try_bv_const_bigint(&fraction, 199).unwrap();
    let value = solver
        .try_fp_from_bvs(sign, exponent, significand, 8, 200)
        .unwrap();
    let independent = solver.independent_closed_fp(value).unwrap();
    let agrees = solver.eq(value, independent);
    solver.assert_term(agrees);
    let equality = solver.eq(x, value);
    solver.assert_term(equality);
    let result = solver.check_sat();
    assert!(result.is_sat(), "{result:?}; {:?}", solver.unknown_reason());
    let model = solver.model_map().unwrap();
    let value = model.get("x").unwrap();
    let fields = value.as_fp_exact().unwrap();
    assert!(!fields.sign());
    assert_eq!(fields.exponent(), &num_bigint::BigUint::from(127u32));
    assert_eq!(BigInt::from(fields.significand().clone()), fraction);
    assert_eq!(
        (fields.exponent_bits(), fields.significand_bits()),
        (8, 200)
    );
    assert!(value.as_fp_wide().is_none());
    assert!(solver.try_get_model_for_consumer().is_ok());
}

#[test]
fn exact_199_bit_symbolic_model_reaches_parsed_public_access_without_truncation() {
    let config = SolverConfig::default()
        .with_timeout(Duration::from_secs(5))
        .with_memory_limit(256 * 1024 * 1024);
    let mut solver = Solver::try_new_with_config(Logic::QfFp, config).unwrap();
    solver
        .parse_smtlib2(include_str!("fixtures/fp-model-200-high-low.smt2"))
        .unwrap();
    let result = solver.check_sat();
    assert!(result.is_sat(), "{result:?}; {:?}", solver.unknown_reason());
    let model = solver.try_get_model().unwrap();
    let value = model.model().fp_val("x").unwrap();
    let fields = value.as_fp_exact().unwrap();
    assert!(!fields.sign());
    assert_eq!(fields.exponent(), &num_bigint::BigUint::from(127u32));
    assert_eq!(
        fields.significand(),
        &((num_bigint::BigUint::from(1u32) << 198usize) | num_bigint::BigUint::from(1u32))
    );
    assert_eq!(
        (fields.exponent_bits(), fields.significand_bits()),
        (8, 200)
    );
    assert!(value.as_fp_wide().is_none());
}

#[test]
fn native_model_fields_preserve_a_192_bit_encoding_through_public_model_access() {
    let config = SolverConfig::default()
        .with_timeout(Duration::from_secs(5))
        .with_memory_limit(256 * 1024 * 1024);
    let mut solver = Solver::try_new_with_config(Logic::QfFp, config).unwrap();
    let x = solver.declare_const("x", Sort::FloatingPoint(63, 129));
    let sign = solver.try_bv_const_bigint(&BigInt::from(1), 1).unwrap();
    let exponent = solver
        .try_bv_const_bigint(&BigInt::from((1u64 << 62) - 1), 63)
        .unwrap();
    let fraction = solver
        .try_bv_const_bigint(&BigInt::from(u128::MAX), 128)
        .unwrap();
    let value = solver
        .try_fp_from_bvs(sign, exponent, fraction, 63, 129)
        .unwrap();
    let equality = solver.eq(x, value);
    solver.assert_term(equality);
    let result = solver.check_sat();
    assert!(result.is_sat(), "{result:?}; {:?}", solver.unknown_reason());
    let model = solver.model_map().unwrap();
    assert_eq!(
        model.get("x").unwrap().as_fp_wide(),
        Some((true, (1u64 << 62) - 1, u128::MAX, 63, 129))
    );
}

#[test]
fn model_supported_binary128_ground_unsat_has_a_native_proof_at_publication() {
    let commands = ay_frontend::parse(include_str!(
        "../../ay-proof/tests/fixtures/fp-ground-binary128-model.smt2"
    ))
    .unwrap();
    let mut executor = ay_dpll::Executor::new();
    executor.set_produce_proofs(true);
    assert_eq!(executor.execute_all(&commands).unwrap(), vec!["unsat"]);
    let evidence = executor.last_command_unsat_evidence().unwrap();
    assert_eq!(evidence.level(), ay_dpll::UnsatEvidenceLevel::E2);
    assert!(evidence.corroboration().is_none());
}

#[test]
fn parsed_native_model_fields_reach_the_verified_model_without_narrowing() {
    let config = SolverConfig::default()
        .with_timeout(Duration::from_secs(5))
        .with_memory_limit(256 * 1024 * 1024);
    let mut solver = Solver::try_new_with_config(Logic::QfFp, config).unwrap();
    solver
        .parse_smtlib2(include_str!("fixtures/fp-model-native-fields.smt2"))
        .unwrap();
    let result = solver.check_sat();
    assert!(result.is_sat(), "{result:?}; {:?}", solver.unknown_reason());
    let model = solver.try_get_model().unwrap();
    assert_eq!(
        model.model().fp_val("x").unwrap().as_fp_wide(),
        Some((true, (1u64 << 62) - 1, u128::MAX, 63, 129))
    );
}

#[test]
fn binary128_ground_arithmetic_exports_an_original_bound_native_strict_bundle() {
    let mut solver = Solver::new(Logic::QfFp);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(include_str!(
            "../../ay-proof/tests/fixtures/fp-ground-binary128.smt2"
        ))
        .unwrap();
    let authored = solver.assertions();
    assert_eq!(authored.len(), 1);
    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "{result:?}; {:?}",
        solver.unknown_reason()
    );
    assert_eq!(solver.assertions(), authored);
    let bundle = solver
        .export_last_unsat_bundle()
        .expect("native binary128 proof bundle");
    assert_ne!(
        bundle.obligation_assertions.as_slice(),
        &[] as &[ay_dpll::api::TermId]
    );
    assert!(bundle
        .obligation_assertions
        .iter()
        .all(|id| authored.iter().any(|term| term.id() == *id)));
    assert!(ay_proof::re_check_bundle_strict(&bundle)
        .unwrap()
        .quality
        .is_complete());
    let mut unbound = bundle;
    unbound.obligation_assertions.clear();
    assert!(ay_proof::re_check_bundle_strict(&unbound).is_err());
}

#[test]
fn custom_wide_sat_model_does_not_reuse_a_previous_ground_refutation() {
    let mut solver = Solver::new(Logic::QfFp);
    solver.set_produce_proofs(true);
    solver.push();
    solver
        .parse_smtlib2(include_str!(
            "../../ay-proof/tests/fixtures/fp-ground-binary128.smt2"
        ))
        .unwrap();
    assert!(solver.check_sat().is_unsat());
    let bundle = solver
        .export_last_unsat_bundle()
        .expect("native proof before pop");
    assert!(ay_proof::re_check_bundle_strict(&bundle)
        .unwrap()
        .quality
        .is_complete());
    solver.pop();
    solver
        .parse_smtlib2("(declare-const represented (_ FloatingPoint 2 128))")
        .unwrap();
    assert!(solver.check_sat().is_sat());
    assert!(solver.export_last_unsat_bundle().is_none());
}
