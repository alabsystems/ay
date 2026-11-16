// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::metered::{self as bridge, MeteredBridgeError};
use super::*;
use crate::bv_blast_solver::retained::{
    wire::{self, WireError, WireLimits},
    work::{MeteredError, WorkAllowance, WorkUsage},
};

mod controls;
mod disjoint;
mod replay;
mod resources;

const GRANT: u64 = 50_000_000;

#[derive(Clone, Copy, Debug)]
enum Operation {
    Capture,
    Replay,
}

fn wire_limits(end: Instant) -> WireLimits {
    WireLimits {
        max_json_bytes: 8 * 1024 * 1024,
        max_rows: 4096,
        max_literals: 64_000,
        max_hints: 64_000,
        max_work: GRANT,
        max_storage_bytes: 128 * 1024 * 1024,
        deadline: end,
    }
}

// Small real live-source graph for exhaustive callback ordinals; the separate
// width-eight test requires the ordinary expensive producer classification.
fn tiny() -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("metered_identity", Sort::bitvec(1));
    let zero = terms.mk_bitvec(0.into(), 1);
    let sum = app(&mut terms, "bvadd", &[a, zero], Sort::bitvec(1));
    let clause = app(&mut terms, "=", &[a, sum], Sort::Bool);
    (terms, clause)
}

fn bytes(terms: &TermStore, clause: TermId) -> Vec<u8> {
    let end = deadline();
    let (proof, gates) = limits(end);
    bridge::capture_clause(
        terms,
        &[clause],
        &proof,
        &gates,
        &wire_limits(end),
        WorkAllowance::new(GRANT, end),
        &mut || true,
    )
    .unwrap()
    .value
}

#[expect(
    clippy::too_many_arguments,
    reason = "the test drives the complete retained bridge boundary positionally"
)]
fn invoke(
    operation: Operation,
    terms: &TermStore,
    clause: TermId,
    bytes: &[u8],
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    wire: &WireLimits,
    allowance: WorkAllowance,
    poll: &mut dyn FnMut() -> bool,
) -> Result<WorkUsage, MeteredBridgeError> {
    match operation {
        Operation::Capture => {
            bridge::capture_clause(terms, &[clause], proof, gates, wire, allowance, poll)
                .map(|result| result.work)
        }
        Operation::Replay => {
            bridge::replay_clause(terms, &[clause], bytes, proof, gates, wire, allowance, poll)
                .map(|result| result.work)
        }
    }
}

fn total(usage: WorkUsage) -> u64 {
    usage.producer_validation + usage.retained_prefix + usage.gates + usage.dag + usage.wire
}

fn encode(payload: &RetainedBvRefutation) -> Vec<u8> {
    let end = deadline();
    let (proof, gates) = limits(end);
    wire::encode(payload, &wire_limits(end), &proof, &gates, &mut || true)
        .result
        .unwrap()
}

fn decode(bytes: &[u8]) -> RetainedBvRefutation {
    let end = deadline();
    let (proof, gates) = limits(end);
    wire::decode(bytes, &wire_limits(end), &proof, &gates, &mut || true)
        .result
        .unwrap()
}

#[test]
fn one_credit_covers_all_phases_with_exact_and_one_short_boundaries() {
    let (terms, clause) = tiny();
    let bytes = bytes(&terms, clause);
    for operation in [Operation::Capture, Operation::Replay] {
        let end = deadline();
        let (proof, gates) = limits(end);
        let wire = wire_limits(end);
        let usage = invoke(
            operation,
            &terms,
            clause,
            &bytes,
            &proof,
            &gates,
            &wire,
            WorkAllowance::new(GRANT, end),
            &mut || true,
        )
        .unwrap();
        assert!(usage.retained_prefix > 0 && usage.gates > 0 && usage.dag > 0 && usage.wire > 0);
        match operation {
            Operation::Capture => assert!(usage.producer_validation > 0),
            Operation::Replay => assert_eq!(usage.producer_validation, 0),
        }
        let exact = total(usage);
        assert_eq!(
            invoke(
                operation,
                &terms,
                clause,
                &bytes,
                &proof,
                &gates,
                &wire,
                WorkAllowance::new(exact, end),
                &mut || true
            )
            .unwrap(),
            usage
        );
        let largest = [
            usage.producer_validation,
            usage.retained_prefix,
            usage.gates,
            usage.dag,
            usage.wire,
        ]
        .into_iter()
        .max()
        .unwrap();
        assert!(largest < exact);
        for grant in [0, exact - 1, largest] {
            assert!(
                invoke(
                    operation,
                    &terms,
                    clause,
                    &bytes,
                    &proof,
                    &gates,
                    &wire,
                    WorkAllowance::new(grant, end),
                    &mut || true
                )
                .is_err(),
                "{operation:?}: grant {grant} must not renew at phase boundaries"
            );
        }
    }
}
