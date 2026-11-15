// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn cumulative_credit_does_not_override_any_numeric_phase_cap() {
    let (terms, clause) = tiny();
    let bytes = bytes(&terms, clause);
    for cap in 0..17 {
        let end = deadline();
        let (mut proof, mut gates) = limits(end);
        let mut wire = wire_limits(end);
        match cap {
            0 => proof.max_expr_nodes = 0,
            1 => proof.max_construction_bytes = 0,
            2 => proof.resolution.max_num_vars = 0,
            3 => proof.resolution.max_input_clauses = 0,
            4 => proof.resolution.max_codec_bytes = 0,
            5 => proof.resolution.validation.max_work = 0,
            6 => proof.resolution.validation.max_bytes = 0,
            7 => proof.resolution.max_derived_steps = 0,
            8 => gates.max_work = 0,
            9 => gates.max_vars = 0,
            10 => wire.max_json_bytes = 0,
            11 => wire.max_rows = 0,
            12 => wire.max_hints = 0,
            13 => wire.max_work = 0,
            14 => wire.max_storage_bytes = 0,
            15 => proof.resolution.max_hints = 0,
            16 => proof.max_expr_occurrences = 0,
            _ => unreachable!(),
        }
        for operation in [Operation::Capture, Operation::Replay] {
            assert!(
                invoke(
                    operation,
                    &terms,
                    clause,
                    &bytes,
                    &proof,
                    &gates,
                    &wire,
                    WorkAllowance::new(GRANT, end),
                    &mut || true
                )
                .is_err(),
                "{operation:?}, cap {cap}"
            );
        }
    }
}

#[test]
fn finite_capture_search_grants_stay_separate_from_replay_credit() {
    let (terms, clause) = tiny();
    let end = deadline();
    let (proof, gates) = limits(end);
    for absent in 0..2 {
        let mut changed = proof.clone();
        if absent == 0 {
            changed.resolution.max_conflicts = None;
        } else {
            changed.resolution.max_decisions = None;
        }
        assert!(matches!(
            invoke(
                Operation::Capture,
                &terms,
                clause,
                b"",
                &changed,
                &gates,
                &wire_limits(end),
                WorkAllowance::new(GRANT, end),
                &mut || true
            ),
            Err(MeteredBridgeError::Bridge(BridgeError::MissingSearchBounds))
        ));
    }
    let mut zero = proof;
    zero.resolution.max_conflicts = Some(0);
    zero.resolution.max_decisions = Some(0);
    assert!(!matches!(
        invoke(
            Operation::Capture,
            &terms,
            clause,
            b"",
            &zero,
            &gates,
            &wire_limits(end),
            WorkAllowance::new(GRANT, end),
            &mut || true
        ),
        Err(MeteredBridgeError::Bridge(BridgeError::MissingSearchBounds))
    ));
}

#[test]
fn specialized_routes_without_work_and_clause_bounds_refuse() {
    for (terms, clause) in [specialized::disjoint(), specialized::outside_frame()] {
        let end = deadline();
        let (mut proof, mut gates) = limits(end);
        proof.max_construction_bytes = 0;
        proof.resolution.max_conflicts = Some(0);
        proof.resolution.max_decisions = Some(0);
        gates.max_work = 0;
        for operation in [Operation::Capture, Operation::Replay] {
            let calls = crate::bv_blast_solver::retained::producer_test_counter::count();
            assert!(invoke(
                operation,
                &terms,
                clause,
                b"{",
                &proof,
                &gates,
                &wire_limits(end),
                WorkAllowance::new(0, end),
                &mut || true
            )
            .is_err());
            assert_eq!(
                crate::bv_blast_solver::retained::producer_test_counter::count(),
                calls
            );
        }
    }
    let mut terms = TermStore::new();
    let unsupported = app(&mut terms, "retained_unsupported_bool", &[], Sort::Bool);
    let cap = crate::checker::bv_bitblast::MAX_PROOF_PRODUCING_CLAUSE_LITERALS;
    let end = deadline();
    let (proof, gates) = limits(end);
    for count in [0, cap, cap + 1] {
        let clause = vec![unsupported; count];
        let result = bridge::replay_clause(
            &terms,
            &clause,
            b"",
            &proof,
            &gates,
            &wire_limits(end),
            WorkAllowance::new(GRANT, end),
            &mut || true,
        );
        if count == cap {
            assert!(matches!(
                result,
                Err(MeteredBridgeError::Bridge(BridgeError::Source(_)))
            ));
        } else {
            assert!(matches!(
                result,
                Err(MeteredBridgeError::Bridge(BridgeError::ClauseBound))
            ));
        }
    }
}
