// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fixture for Sledgehammer QEpres `uf.787634`
//! (#exists-bridge-chain). Split out of `demand_probes` to keep that
//! file under the quality gate's size cap; the verdict pin lives in
//! `demand_probes`' PRODUCTION_FLIPS.

use super::*;

/// Sledgehammer QEpres `uf.787634` (SMT-LIB UF, z3-UNSAT in <0.1s): the
/// refutation is a 4-instantiation bridge chain
/// (`f22`-id → `f23`↔`f3` bridge → exists-witness bridge → closing
/// implication) whose closing instance binds terms minted by the
/// witness instance, so it is generation-2 and parks at F=1. The lane
/// computes the refutation (parked instance flushed with provenance
/// per #demand-flush-provenance) and the exists-bridge chain producer
/// (#exists-bridge-chain) certifies it: bridge instantiation,
/// antecedent discharge through the second bridge plus a congruence
/// transport, one-binder-at-a-time Skolemization, closing instances.
pub(super) const UF787634_BRIDGE_CHAIN: &str = r#"
(set-logic UF)
(declare-sort S1 0)
(declare-sort S2 0)
(declare-sort S3 0)
(declare-sort S4 0)
(declare-sort S5 0)
(declare-sort S6 0)
(declare-sort S7 0)
(declare-sort S8 0)
(declare-sort S9 0)
(declare-sort S10 0)
(declare-sort S11 0)
(declare-sort S12 0)
(declare-sort S13 0)
(declare-sort S14 0)
(declare-sort S15 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S2) S2)
(declare-fun f6 (S6 S2) S5)
(declare-fun f7 () S6)
(declare-fun f8 (S7 S4) S2)
(declare-fun f9 (S8 S4) S7)
(declare-fun f10 () S8)
(declare-fun f11 () S4)
(declare-fun f12 (S9 S10) S1)
(declare-fun f13 (S11 S4) S9)
(declare-fun f14 (S12 S2) S11)
(declare-fun f15 () S12)
(declare-fun f16 (S13) S10)
(declare-fun f17 (S14) S13)
(declare-fun f18 () S14)
(declare-fun f19 () S1)
(declare-fun f20 (S15 S3) S2)
(declare-fun f21 () S15)
(declare-fun f22 (S3) S3)
(declare-fun f23 (S2 S3) S1)
(declare-fun f24 (S10 S9) S1)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) (exists ((?v1 S4) (?v2 S2)) (and (= ?v0 (f5 (f6 f7 ?v2) (f8 (f9 f10 ?v1) f11))) (= (f12 (f13 (f14 f15 ?v2) ?v1) (f16 (f17 f18))) f1))))))
(assert (not (= f19 f1)))
(assert (forall ((?v0 S2) (?v1 S4)) (=> (= (f12 (f13 (f14 f15 ?v0) ?v1) (f16 (f17 f18))) f1) (=> (= (f20 f21 (f22 f4)) (f5 (f6 f7 ?v0) (f8 (f9 f10 ?v1) f11))) (= f19 f1)))))
(assert (let ((?v_0 (f22 f4))) (= (f23 (f20 f21 ?v_0) ?v_0) f1)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f23 ?v0 ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S9) (?v1 S10)) (= (= (f12 ?v0 ?v1) f1) (= (f24 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f22 ?v0) ?v0)))
(check-sat)
"#;

/// The published `unsat` must retain a strict authored-scope
/// certificate (the exists-bridge chain producer's whole point).
#[test]
fn uf787634_bridge_chain_unsat_retains_strict_certificate() {
    let commands = parse(UF787634_BRIDGE_CHAIN).expect("parse uf787634 probe");
    let mut exec = Executor::new();
    exec.set_best_effort_produce_proofs(1_000_000);
    exec.set_timeout(Some(std::time::Duration::from_secs(20)));
    let outputs = exec.execute_all(&commands).expect("execute uf787634 probe");
    assert_eq!(outputs.last().cloned().unwrap_or_default(), "unsat");
    let proof = exec
        .last_proof()
        .cloned()
        .expect("the published unsat retains its certificate");
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
}
