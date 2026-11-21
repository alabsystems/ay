// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Whole native entry-point controls. The joint producer tuple also includes
//! binder-safe preprocessing and the canonical lambda-array replay reader.

use std::time::Duration;

use crate::api::{Logic, ModelValue, NativeReplayMetadata, SolveResult, Solver, Sort, Term};

fn query(strict: bool, conflicting: bool) -> (Solver, Vec<(Term, i64)>) {
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    solver.set_timeout(Some(Duration::from_secs(5)));
    solver.set_produce_proofs(strict);
    if strict {
        solver
            .try_set_option(":check-proofs-strict", "true")
            .unwrap();
    }
    let bound = solver.fresh_var("periodic_index", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let residue = solver.modulo(bound, two);
    let divisible = solver.eq(residue, zero);
    let body = solver.ite(divisible, one, zero);
    let lambda = solver.lambda_array(bound, body);
    let array = solver.declare_const("periodic_array", Sort::array(Sort::Int, Sort::Int));
    let alias = solver.declare_const("periodic_alias", Sort::array(Sort::Int, Sort::Int));
    let definition = solver.eq(array, lambda);
    solver.assert_term(definition);
    let same_array = solver.eq(alias, array);
    solver.assert_term(same_array);
    let mut reads = Vec::new();
    for (index, expected) in [(-3, 0), (-2, 1), (0, 1), (1, 0)] {
        let index = solver.int_const(index);
        let read = solver.select(alias, index);
        let expected_term = solver.int_const(expected);
        let equality = solver.eq(read, expected_term);
        solver.assert_term(equality);
        reads.push((read, expected));
    }
    let source_index = solver.declare_const("periodic_source_index", Sort::Int);
    let symbolic_read = solver.select(array, source_index);
    let required = solver.eq(symbolic_read, one);
    solver.assert_term(required);
    if conflicting {
        let read_zero = solver.select(alias, zero);
        let wrong = solver.eq(read_zero, zero);
        solver.assert_term(wrong);
    }
    (solver, reads)
}

#[test]
fn periodic_int_public_alias_model_validates_and_replays_in_both_modes() {
    for strict in [false, true] {
        let (mut solver, reads) = query(strict, false);
        let details = solver.check_sat_with_details();
        assert_eq!(details.result, SolveResult::Sat, "{details:?}");
        assert!(details.result.was_model_validated());
        assert!(details.verification.sat_model_validated);
        assert!(solver.try_get_model_for_consumer().is_ok());
        let model = solver.try_get_model_str().unwrap();
        assert!(model.contains("lambda"), "{model}");
        for (read, expected) in reads {
            assert!(
                matches!(solver.try_get_value(read).unwrap(), ModelValue::Int(value) if value == num_bigint::BigInt::from(expected))
            );
        }
        let artifact =
            solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
        let replay = if strict {
            Solver::replay_native_replay_artifact_with_proofs(&artifact, Duration::from_secs(5))
        } else {
            Solver::replay_native_replay_artifact(&artifact)
        }
        .unwrap();
        assert_eq!(replay.result, SolveResult::Sat, "{replay:?}");
        assert!(replay.result.was_model_validated());
        assert!(replay.verification.sat_model_validated);
    }
}

#[test]
fn periodic_int_public_conflicting_original_read_keeps_strict_refutation() {
    let (mut solver, _) = query(true, true);
    let details = solver.check_sat_with_details();
    assert!(details.result.is_unsat(), "{details:?}");
    assert!(details.verification.unsat_proof_strictly_verified);
    assert_eq!(details.verification.unsat_proof_checker_failures, 0);
    assert_eq!(details.statistics.get_int("proof_trust"), Some(0));
}
