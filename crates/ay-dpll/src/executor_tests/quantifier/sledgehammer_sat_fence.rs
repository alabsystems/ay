// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-side demand-fence regression for Sledgehammer
//! `Fundamental_Theorem_Algebra/uf.624244` (#demand-post-interleave-fence).
//! Instances parked by the interleaved E-matching rounds (Phase 1) must
//! be flushed/fenced before the SAT classification concludes (LAW #2);
//! before the Phase-1.5 fence the solve concluded
//! `unknown (quantifier-unhandled)` with 16 instances still parked and
//! zero flushes. Publishing `sat` additionally needed a certificate
//! for the triggerless unhandled quantifiers, which the finite-domain
//! UF certificate (#finite-domain-uf-cert) now provides by exhibiting
//! a finite model; the fence behavior itself is pinned by the
//! counters below.

use super::*;

/// z3-SAT in <0.1s.
const UF624244: &str = r#"
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
(declare-sort S16 0)
(declare-sort S17 0)
(declare-sort S18 0)
(declare-sort S19 0)
(declare-sort S20 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S4 S3) S3)
(declare-fun f4 (S5 S3) S4)
(declare-fun f5 (S6 S2) S5)
(declare-fun f6 () S6)
(declare-fun f7 () S5)
(declare-fun f8 (S7 S2) S4)
(declare-fun f9 () S7)
(declare-fun f10 () S2)
(declare-fun f11 () S7)
(declare-fun f12 (S8 S6) S4)
(declare-fun f13 (S9 S3) S8)
(declare-fun f14 () S9)
(declare-fun f15 () S3)
(declare-fun f16 () S2)
(declare-fun f17 (S10 S11) S11)
(declare-fun f18 (S12 S3) S10)
(declare-fun f19 () S12)
(declare-fun f20 () S11)
(declare-fun f21 (S13 S14) S14)
(declare-fun f22 () S13)
(declare-fun f23 () S14)
(declare-fun f24 (S15 S13) S13)
(declare-fun f25 (S16 S11) S15)
(declare-fun f26 () S16)
(declare-fun f27 () S16)
(declare-fun f28 () S12)
(declare-fun f29 (S17 S13) S15)
(declare-fun f30 () S17)
(declare-fun f31 (S18 S11) S10)
(declare-fun f32 () S18)
(declare-fun f33 (S19 S2) S2)
(declare-fun f34 (S20 S2) S19)
(declare-fun f35 () S20)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (= (f3 (f4 (f5 f6 ?v0) ?v1) ?v2) (f3 (f4 f7 (f3 (f8 f9 f10) ?v2)) (f3 (f8 f11 ?v0) ?v2)))))
(assert (not (= (f3 (f12 (f13 f14 f15) f6) f15) f15)))
(assert (= (f3 (f8 f11 f16) f15) f15))
(assert (= (f17 (f18 f19 f15) f20) f20))
(assert (= (f21 f22 f23) f23))
(assert (= (f24 (f25 f26 f20) f22) f22))
(assert (forall ((?v0 S2)) (= (f3 (f8 f9 ?v0) f15) f15)))
(assert (forall ((?v0 S11)) (= (f24 (f25 f27 ?v0) f22) f22)))
(assert (forall ((?v0 S3)) (= (f17 (f18 f28 ?v0) f20) f20)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f7 ?v0) f15) ?v0)))
(assert (forall ((?v0 S13)) (= (f24 (f29 f30 ?v0) f22) ?v0)))
(assert (forall ((?v0 S11)) (= (f17 (f31 f32 ?v0) f20) ?v0)))
(assert (forall ((?v0 S2)) (= (f33 (f34 f35 ?v0) f16) ?v0)))
(check-sat)
"#;

/// The post-interleave fence must grant every parked instance before
/// the verdict concludes (flushed > 0, none remaining), and the
/// finite-domain UF certificate publishes the z3-SAT verdict.
#[test]
fn uf624244_post_interleave_fence_grants_parked_instances() {
    let commands = parse(UF624244).expect("parse uf624244 probe");
    let mut exec = Executor::new();
    exec.set_timeout(Some(std::time::Duration::from_secs(20)));
    let outputs = exec.execute_all(&commands).expect("execute uf624244 probe");
    let verdict = outputs.last().cloned().unwrap_or_default();
    assert_ne!(
        verdict, "unsat",
        "uf624244 returned unsat but is z3-SAT — soundness regression"
    );
    let stats = exec.statistics().clone();
    let flushed = stats.get_int("quantifier.demand.flushed").unwrap_or(0);
    let parked_remaining = stats
        .get_int("quantifier.demand.parked_remaining")
        .unwrap_or(0);
    assert!(
        flushed > 0,
        "post-interleave fence must flush parked instances (flushed={flushed})"
    );
    assert_eq!(
        parked_remaining, 0,
        "no instance may remain parked at conclusion (LAW #2 fence)"
    );
    assert_eq!(
        verdict, "sat",
        "the finite-domain UF certificate must publish the z3-SAT \
         verdict. Got: {verdict}"
    );
}
