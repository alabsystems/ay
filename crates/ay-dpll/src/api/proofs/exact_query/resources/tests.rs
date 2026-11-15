// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::api::{Logic, Sort};

const BOOLEAN: &str = "(declare-const p Bool) (assert p) (assert (not p))";
const DATATYPE: &str =
    "(declare-datatype D ((a) (b))) (declare-const x D) (assert (= x a)) (assert (= x b))";

enum ProofMode {
    NativeBundle,
    StrictWire,
}

fn parsed(logic: Logic, source: &str, mode: ProofMode) -> (Solver, ExactSmtlibQueryBinding) {
    let mut solver = Solver::try_new(logic).unwrap();
    solver.set_produce_proofs(true);
    if matches!(mode, ProofMode::StrictWire) {
        solver
            .try_set_option(":check-proofs-strict", "true")
            .unwrap();
    }
    let binding = solver
        .parse_smtlib2_with_exact_query_binding(source)
        .unwrap();
    (solver, binding)
}

fn solved(logic: Logic, source: &str) -> (Solver, ExactSmtlibQueryBinding) {
    let (mut solver, binding) = parsed(logic, source, ProofMode::StrictWire);
    assert!(solver.check_sat().is_unsat());
    (solver, binding)
}

fn trace(solver: &Solver, binding: &ExactSmtlibQueryBinding) -> Vec<(usize, usize)> {
    let mut charges = Vec::new();
    assert!(solver
        .export_last_unsat_bundle_for_exact_query_with_resource_control(
            binding,
            &mut |work, bytes| {
                charges.push((work, bytes));
                true
            },
        )
        .unwrap()
        .is_some());
    charges
}

fn totals(charges: &[(usize, usize)]) -> (usize, usize) {
    charges.iter().fold((0usize, 0usize), |(w, b), (dw, db)| {
        (w.checked_add(*dw).unwrap(), b.checked_add(*db).unwrap())
    })
}

#[test]
fn controlled_export_keeps_exact_boolean_folded_and_native_bundle_bytes() {
    for (logic, source) in [
        (Logic::All, BOOLEAN),
        (Logic::All, "(declare-const x Int) (assert (> x 5)) (assert (< x 3))"),
        (Logic::All, "(declare-const x Int) (assert (and (>= x 0) (not (> x 10)) (> x 10)))"),
        (Logic::QfUfbvlia, "(declare-const x (_ BitVec 16)) (assert (= x #x9c40)) (assert (<= (* (ubv_to_int x) 2) 65535))"),
    ] {
        let (solver, binding) = solved(logic, source);
        let original = solver.export_last_unsat_bundle_for_exact_query(&binding).unwrap();
        let controlled = solver.export_last_unsat_bundle_for_exact_query_with_resource_control(
            &binding, &mut |_, _| true,
        ).unwrap().unwrap();
        assert_eq!(serde_json::to_vec(&original).unwrap(), serde_json::to_vec(&controlled).unwrap());
        assert!(ay_proof::re_check_bundle_strict(&controlled).unwrap().quality.is_complete());
    }
}

#[test]
fn native_datatype_export_keeps_exact_bundle_bytes_and_strict_replay() {
    let (mut solver, binding) = parsed(Logic::All, DATATYPE, ProofMode::NativeBundle);
    assert!(solver.check_sat().is_unsat());
    let original = solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .unwrap();
    let controlled = solver
        .export_last_unsat_bundle_for_exact_query_with_resource_control(&binding, &mut |_, _| true)
        .unwrap()
        .unwrap();
    assert_eq!(
        serde_json::to_vec(&original).unwrap(),
        serde_json::to_vec(&controlled).unwrap()
    );
    assert!(controlled.steps.iter().any(|step| matches!(
        step,
        ay_core::ProofStep::TheoryLemma {
            kind: ay_core::TheoryLemmaKind::DatatypeDistinct,
            ..
        }
    )));
    assert_eq!(controlled.obligation_assertions.len(), 2);
    assert!(ay_proof::re_check_bundle_strict(&controlled)
        .unwrap()
        .quality
        .is_complete());
}

#[test]
fn explicit_datatype_strict_wire_request_still_revokes_verdict_and_artifact() {
    let (mut solver, binding) = parsed(Logic::All, DATATYPE, ProofMode::StrictWire);
    assert!(solver.check_sat().is_unknown());
    assert_eq!(
        solver.unknown_reason(),
        Some(crate::UnknownReason::ProofTrusted)
    );
    assert!(solver.last_proof().is_none());
    assert!(solver.export_last_proof_alethe().is_none());
    assert!(solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .is_none());
    assert!(solver
        .export_last_unsat_bundle_for_exact_query_with_resource_control(&binding, &mut |_, _| true)
        .unwrap()
        .is_none());
}

#[test]
fn controlled_export_has_exact_one_short_and_shared_attempt_boundaries() {
    let (solver, binding) = solved(Logic::All, BOOLEAN);
    let (work, bytes) = totals(&trace(&solver, &binding));
    for (wc, bc, accepted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let (mut w, mut b) = (0, 0);
        let result = solver.export_last_unsat_bundle_for_exact_query_with_resource_control(
            &binding,
            &mut |dw, db| {
                w += dw;
                b += db;
                w <= wc && b <= bc
            },
        );
        if accepted {
            assert!(result.unwrap().is_some());
        } else {
            assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        }
    }
    let (mut w, mut b) = (0, 0);
    let mut shared = |dw, db| {
        w += dw;
        b += db;
        w <= work && b <= bytes
    };
    assert!(solver
        .export_last_unsat_bundle_for_exact_query_with_resource_control(&binding, &mut shared,)
        .unwrap()
        .is_some());
    assert!(matches!(
        solver
            .export_last_unsat_bundle_for_exact_query_with_resource_control(&binding, &mut shared,),
        Err(ProofCheckError::ResourceLimit)
    ));
}

#[test]
fn cancellation_at_every_public_export_checkpoint_is_terminal_and_retry_is_fresh() {
    let (solver, binding) = solved(Logic::All, BOOLEAN);
    let expected = trace(&solver, &binding);
    for stop in 1..=expected.len() {
        let mut actual = Vec::new();
        let result = solver.export_last_unsat_bundle_for_exact_query_with_resource_control(
            &binding,
            &mut |w, b| {
                actual.push((w, b));
                actual.len() != stop
            },
        );
        assert!(
            matches!(result, Err(ProofCheckError::ResourceLimit)),
            "checkpoint {stop}"
        );
        assert_eq!(actual, expected[..stop]);
    }
    assert_eq!(trace(&solver, &binding), expected);
}

#[test]
fn consumer_replay_spends_the_same_allowance_as_both_export_rechecks() {
    let (solver, binding) = solved(Logic::All, BOOLEAN);
    let export_cost = totals(&trace(&solver, &binding));
    let bundle = solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .unwrap();
    let (mut rw, mut rb) = (0, 0);
    re_check_bundle_strict_with_resource_control(&bundle, &mut |w, b| {
        rw += w;
        rb += b;
        true
    })
    .unwrap();
    for (work, bytes, accepted) in [
        (export_cost.0 + rw, export_cost.1 + rb, true),
        (export_cost.0 + rw - 1, export_cost.1 + rb, false),
        (export_cost.0 + rw, export_cost.1 + rb - 1, false),
        (export_cost.0, export_cost.1, false),
    ] {
        let (mut w, mut b) = (0, 0);
        let mut shared = |dw, db| {
            w += dw;
            b += db;
            w <= work && b <= bytes
        };
        let bundle = solver
            .export_last_unsat_bundle_for_exact_query_with_resource_control(&binding, &mut shared)
            .unwrap()
            .unwrap();
        let result = re_check_bundle_strict_with_resource_control(&bundle, &mut shared);
        if accepted {
            assert!(result.unwrap().quality.is_complete());
        } else {
            assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        }
    }
}

#[test]
fn controlled_export_rejects_foreign_changed_and_stale_source_without_fallback() {
    let (mut solver, binding) = solved(Logic::All, BOOLEAN);
    let (sibling, sibling_binding) = solved(Logic::All, BOOLEAN);
    for (solver, binding) in [(&solver, &sibling_binding), (&sibling, &binding)] {
        assert!(solver
            .export_last_unsat_bundle_for_exact_query_with_resource_control(binding, &mut |_, _| {
                true
            },)
            .unwrap()
            .is_none());
    }
    let mut duplicate = binding.clone();
    duplicate.assertions.push(duplicate.assertions[0]);
    assert!(solver
        .export_last_unsat_bundle_for_exact_query_with_resource_control(&duplicate, &mut |_, _| {
            true
        },)
        .unwrap()
        .is_none());
    solver.try_declare_const("late", Sort::Int).unwrap();
    assert!(solver
        .export_last_unsat_bundle_for_exact_query_with_resource_control(&binding, &mut |_, _| true,)
        .unwrap()
        .is_none());
}

#[test]
fn native_sos_export_stays_native_and_stale_seal_is_terminal() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .unwrap();
    let binding = solver
        .parse_smtlib2_with_exact_query_binding("(declare-const x Real) (assert (< (* x x) 0.0))")
        .unwrap();
    // Only the provisional decision is injected. Source authentication, SOS
    // certificate construction and independent checking are production paths.
    assert!(solver
        .executor
        .certify_native_sos_provisional_for_test()
        .is_unsat());
    assert!(solver.executor.has_strict_native_nra_sos_bundle_state());
    let bundle = solver
        .export_last_unsat_bundle_for_exact_query_with_resource_control(&binding, &mut |_, _| true)
        .unwrap()
        .unwrap();
    assert!(bundle
        .steps
        .iter()
        .any(|step| matches!(step, ay_core::ProofStep::NraSos { .. })));
    let _late = solver.fresh_var("late_arena_append", Sort::Bool);
    assert!(solver.executor.has_strict_native_nra_sos_bundle_state());
    assert!(solver
        .export_last_unsat_bundle_for_exact_query_with_resource_control(&binding, &mut |_, _| true,)
        .unwrap()
        .is_none());
}
