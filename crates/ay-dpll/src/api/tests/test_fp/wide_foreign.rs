// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! End-to-end model authority for FP-valued UF arguments, including the
//! complete finite expansion of a BV8-indexed heap. Unknown is not success.

use super::*;

fn from_bits(solver: &mut Solver, bits: Term) -> Term {
    let sign = solver.try_bvextract(bits, 63, 63).unwrap();
    let exponent = solver.try_bvextract(bits, 62, 52).unwrap();
    let fraction = solver.try_bvextract(bits, 51, 0).unwrap();
    solver
        .try_fp_from_bvs(sign, exponent, fraction, 11, 53)
        .unwrap()
}

fn heap(solver: &mut Solver) -> Term {
    solver.declare_const("mem", Sort::array(Sort::bitvec(8), Sort::bitvec(64)))
}

fn assert_confirmed(solver: &mut Solver) {
    let details = solver.check_sat_with_details();
    assert_eq!(
        details.result,
        SolveResult::Sat,
        "full FP/UF query: {details:?}; statistics: {:?}; unknown reason/detail: {:?}",
        solver.statistics(),
        (
            solver.executor.unknown_reason(),
            solver.executor.unknown_detail()
        )
    );
    assert!(details.verification.sat_model_validated, "{details:?}");
    assert!(solver.try_get_model_for_consumer().is_ok());
    let printed = solver.try_get_model_str().unwrap();
    assert!(printed.contains("define-fun g"), "{printed}");
}

fn assert_values(solver: &Solver, applications: &[Term], polarity: bool) {
    let values = solver.try_get_values(applications).unwrap();
    assert_eq!(values, vec![ModelValue::Bool(polarity); applications.len()]);
}

#[test]
fn wide_fp_uf_forced_outputs_publish_a_validated_ground_model() {
    for polarity in [true, false] {
        let mut solver = Solver::new(Logic::QfBvfp);
        let g = solver.declare_fun("g", &[Sort::FloatingPoint(11, 53)], Sort::Bool);
        let mut applications = Vec::new();
        let mut literals = Vec::new();
        for i in 0..256 {
            let bits = solver.declare_const(&format!("bits_{i}"), Sort::bitvec(64));
            let value = from_bits(&mut solver, bits);
            let application = solver.try_apply(&g, &[value]).unwrap();
            applications.push(application);
            literals.push(if polarity {
                application
            } else {
                solver.not(application)
            });
        }
        let conjunction = solver.and_many(&literals);
        solver.assert_term(conjunction);
        assert_confirmed(&mut solver);
        assert_values(&solver, &applications, polarity);
    }
}

#[test]
fn flattened_fp_uf_values_survive_original_root_restoration() {
    for polarity in [true, false] {
        let mut solver = Solver::new(Logic::QfAbvfp);
        let mem = heap(&mut solver);
        let g = solver.declare_fun("g", &[Sort::FloatingPoint(11, 53)], Sort::Bool);
        let mut applications = Vec::new();
        for i in [0, 42, 255] {
            let index = solver.bv_const(i, 8);
            let bits = solver.select(mem, index);
            let value = from_bits(&mut solver, bits);
            let application = solver.try_apply(&g, &[value]).unwrap();
            applications.push(application);
            let literal = if polarity {
                application
            } else {
                solver.not(application)
            };
            solver.assert_term(literal);
        }
        assert_confirmed(&mut solver);
        assert_values(&solver, &applications, polarity);
    }
}

#[test]
fn aufbvfp_full_bv8_heap_expansion_publishes_a_validated_model() {
    let mut solver = Solver::new(Logic::All);
    solver
        .parse_smtlib2("(set-logic AUFBVFP) (set-option :produce-proofs true)")
        .unwrap();
    let mem = heap(&mut solver);
    let g = solver.declare_fun("g", &[Sort::FloatingPoint(11, 53)], Sort::Bool);
    solver
        .parse_smtlib2(
            "(assert (forall ((q (_ BitVec 8)))
               (g (fp ((_ extract 63 63) (select mem q))
                      ((_ extract 62 52) (select mem q))
                      ((_ extract 51 0) (select mem q))))))",
        )
        .unwrap();
    assert_confirmed(&mut solver);
    assert_eq!(solver.try_get_values(&[mem]).unwrap().len(), 1);
    // Fresh reads must agree with the total function printed for the exact
    // quantified model, not merely a Boolean abstraction of its instances.
    let mut applications = Vec::new();
    for i in [0, 42, 255] {
        let index = solver.bv_const(i, 8);
        let bits = solver.select(mem, index);
        let value = from_bits(&mut solver, bits);
        applications.push(solver.try_apply(&g, &[value]).unwrap());
    }
    assert_values(&solver, &applications, true);
}

#[test]
fn wide_fp_uf_opposite_outputs_on_equal_arguments_cannot_publish_sat() {
    let mut solver = Solver::new(Logic::QfFp);
    let g = solver.declare_fun("g", &[Sort::FloatingPoint(11, 53)], Sort::Bool);
    let mut arguments = Vec::new();
    for i in 0..65 {
        let value = solver.declare_const(&format!("x{i}"), Sort::FloatingPoint(11, 53));
        arguments.push(value);
        let application = solver.try_apply(&g, &[value]).unwrap();
        let literal = if i == 64 {
            solver.not(application)
        } else {
            application
        };
        solver.assert_term(literal);
    }
    let equality = solver.eq(arguments[0], arguments[64]);
    solver.assert_term(equality);
    let details = solver.check_sat_with_details();
    assert_ne!(details.result, SolveResult::Sat, "{details:?}");
    assert!(!details.verification.sat_model_validated);
    assert!(solver.try_get_model_for_consumer().is_err());
    assert!(solver.try_get_model_str().is_err());
}

#[test]
fn flattened_fp_uf_opposite_outputs_preserve_functionality_and_scope() {
    let mut solver = Solver::new(Logic::QfAbvfp);
    let mem = heap(&mut solver);
    let g = solver.declare_fun("g", &[Sort::FloatingPoint(11, 53)], Sort::Bool);
    let mut reads = Vec::new();
    let mut applications = Vec::new();
    for i in 0..2 {
        let index = solver.bv_const(i, 8);
        let bits = solver.select(mem, index);
        reads.push(bits);
        let value = from_bits(&mut solver, bits);
        applications.push(solver.try_apply(&g, &[value]).unwrap());
    }
    solver.assert_term(applications[0]);
    let negative = solver.not(applications[1]);
    solver.assert_term(negative);
    assert_confirmed(&mut solver);
    assert_values(&solver, &applications[..1], true);
    assert_values(&solver, &applications[1..], false);

    solver.push();
    let equal_bits = solver.eq(reads[0], reads[1]);
    solver.assert_term(equal_bits);
    assert!(solver.check_sat().is_unsat());
    assert!(solver.try_get_model_for_consumer().is_err());
    solver.pop();
    assert!(solver.try_get_model_for_consumer().is_err());
    assert_confirmed(&mut solver);
    assert_values(&solver, &applications[..1], true);
    assert_values(&solver, &applications[1..], false);
}
