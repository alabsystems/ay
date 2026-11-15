// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bv_blast_solver::retained::producer_test_counter;

#[test]
fn multibit_owned_wire_replays_without_search_or_legacy_and_binds_fresh_source() {
    let producer_calls = producer_test_counter::count();
    let bytes = {
        let (terms, clause) = arithmetic(0);
        assert!(
            crate::checker::bv_bitblast::bv_bitblast_requires_proof_producer(&terms, &[clause])
        );
        let before = terms.entries_snapshot();
        let mut payload = decode(&bytes(&terms, clause));
        assert!(payload.rows.len() > 1);
        separate_derived_ids(&mut payload);
        assert_eq!(terms.entries_snapshot(), before);
        encode(&payload)
    };
    assert_eq!(producer_test_counter::count(), producer_calls + 1);
    let producer_calls = producer_test_counter::count();
    let (terms, clause) = arithmetic(0);
    let before = terms.entries_snapshot();
    let attempts = crate::checker::bv_bitblast::proof_producing_control::ATTEMPTS.with(Cell::get);
    let end = deadline();
    let (mut proof, gates) = limits(end);
    proof.resolution.max_backward_reconstruction_bytes = 0;
    proof.resolution.max_pending_deletions = 0;
    for bound in [Some(0), None] {
        proof.resolution.max_conflicts = bound;
        proof.resolution.max_decisions = bound;
        let usage = invoke(
            Operation::Replay,
            &terms,
            clause,
            &bytes,
            &proof,
            &gates,
            &wire_limits(end),
            WorkAllowance::new(GRANT, end),
            &mut || true,
        )
        .unwrap();
        assert_eq!(usage.producer_validation, 0);
    }
    let (neighbor, changed) = arithmetic(1);
    assert!(
        matches!(invoke(Operation::Replay, &neighbor, changed, &bytes, &proof, &gates,
        &wire_limits(end), WorkAllowance::new(GRANT, end), &mut || true),
        Err(MeteredBridgeError::Retained(MeteredError::Proof(
            BvExprExportError::RefutationNotSurfaceable(message))))
            if message.starts_with("bounded resolution proof failed:"))
    );
    assert_eq!(terms.entries_snapshot(), before);
    assert_eq!(
        crate::checker::bv_bitblast::proof_producing_control::ATTEMPTS.with(Cell::get),
        attempts
    );
    assert_eq!(producer_test_counter::count(), producer_calls);
}

#[test]
fn corrupt_and_missing_wire_cannot_reuse_prior_acceptance() {
    let (terms, clause) = tiny();
    let bytes = bytes(&terms, clause);
    let producer_calls = producer_test_counter::count();
    let end = deadline();
    let (proof, gates) = limits(end);
    let replay = |input: &[u8]| {
        invoke(
            Operation::Replay,
            &terms,
            clause,
            input,
            &proof,
            &gates,
            &wire_limits(end),
            WorkAllowance::new(GRANT, end),
            &mut || true,
        )
    };
    replay(&bytes).unwrap();
    terms.record_strict_bv_semantics_validated(&[clause]);
    assert!(terms.strict_bv_semantics_validated(&[clause]));
    for bad in [b"".as_slice(), b"null", b"{}", b"{"] {
        assert!(replay(bad).is_err());
    }
    let payload = decode(&bytes);
    for mutation in 0..4 {
        let mut bad = payload.clone();
        match mutation {
            0 => bad.version += 1,
            1 => bad.rows.clear(),
            2 => bad.rows.last_mut().unwrap().hints = vec![u64::MAX],
            3 => bad.empty_clause_id = u64::MAX,
            _ => unreachable!(),
        }
        // Malformed payloads intentionally bypass the bounded writer's shape
        // checks here; production replay must reject untrusted wire itself.
        assert!(replay(&serde_json::to_vec(&bad).unwrap()).is_err());
    }
    replay(&bytes).unwrap();
    assert_eq!(producer_test_counter::count(), producer_calls);
}

#[test]
fn term_id_reuse_and_malformed_live_source_do_not_inherit_old_credit() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("retained_a", Sort::bitvec(8));
    let b = terms.mk_var("retained_b", Sort::bitvec(8));
    let zero = terms.mk_bitvec(0.into(), 8);
    let one = terms.mk_bitvec(1.into(), 8);
    let checkpoint = terms.rollback_checkpoint();
    let (index, stamp, bytes) = {
        let old = equality(&mut terms, a, b, zero);
        (
            old.index(),
            terms.entry_stamp(old).unwrap(),
            bytes(&terms, old),
        )
    };
    terms.rollback_to(checkpoint);
    let changed = equality(&mut terms, a, b, one);
    assert_eq!(changed.index(), index);
    assert_ne!(terms.entry_stamp(changed).unwrap(), stamp);
    let end = deadline();
    let (proof, gates) = limits(end);
    assert!(invoke(
        Operation::Replay,
        &terms,
        changed,
        &bytes,
        &proof,
        &gates,
        &wire_limits(end),
        WorkAllowance::new(GRANT, end),
        &mut || true
    )
    .is_err());
    let wrong = terms.mk_bitvec(0.into(), 7);
    let sum = app(&mut terms, "bvadd", &[a, wrong], Sort::bitvec(8));
    let malformed = app(&mut terms, "=", &[a, sum], Sort::Bool);
    assert!(matches!(
        invoke(
            Operation::Replay,
            &terms,
            malformed,
            &bytes,
            &proof,
            &gates,
            &wire_limits(end),
            WorkAllowance::new(GRANT, end),
            &mut || true
        ),
        Err(MeteredBridgeError::Bridge(BridgeError::Source(_)))
    ));
}
