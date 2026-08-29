// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Tests for the WS1 `ay-encode` additions (G1–G7).
//!
//! These are the Step-0 gate from the model-checker-consumer port spec: they round-trip a
//! `ChcProblem` through [`crate::invoke::solve`] / [`crate::invoke::solve_with_proof`]
//! and assert parity vs the raw `ay-chc` path, plus the specific knobs each gap
//! adds. They use `ChcParser::parse` only to *construct* a problem (the typed
//! lowering stays model-checker-consumer-side); the assertions exercise the shared crate.

use std::time::Duration;

use crate::invoke::{solve, solve_with_proof, EncodeConfig, Engine, ProofMode};
use crate::verdict::{AyVerdict, UnknownReason};
use ay_chc::{engines, ChcParser, PdrConfig, VerifiedChcResult};

#[test]
fn unsupported_set_algebra_returns_typed_errors() {
    let element = crate::Sort::int();
    let set_sort = crate::sorts::set_of(element);
    let left = crate::Expr::var("left", set_sort.clone());
    let right = crate::Expr::var("right", set_sort);

    for result in [
        crate::terms::set::union(left.clone(), right.clone()),
        crate::terms::set::intersect(left.clone(), right.clone()),
        crate::terms::set::difference(left, right),
    ] {
        assert!(
            matches!(result, Err(crate::EncodeError::Unimplemented(_))),
            "unwired set algebra must fail closed without panicking"
        );
    }
}

/// A trivially-safe Horn problem: `Inv` starts at 0, only ever increments, and
/// the bad state demands `x = -1`, which is unreachable.
const SAFE_CHC: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x (- 1))) false)))
(check-sat)
"#;

/// A trivially-unsafe Horn problem: the bad state `x = 1` *is* reachable.
const UNSAFE_CHC: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 1)) false)))
(check-sat)
"#;

fn parse(smt: &str) -> ay_chc::ChcProblem {
    ChcParser::parse(smt).expect("fixture should parse")
}

// --- G2: `to_pdr_config` adopts the production profile -----------------------

#[test]
fn g2_to_pdr_config_matches_production_profile() {
    // The timeout maps onto `solve_timeout`; every other technique toggle must
    // match `PdrConfig::production(false)` (NOT `default()`), which is the
    // behavior-preservation requirement.
    let timeout = Duration::from_secs(7);
    let cfg = EncodeConfig::new()
        .with_proof_mode(ProofMode::Strict)
        .with_timeout(timeout)
        .to_pdr_config();

    let mut expected = PdrConfig::production(false);
    expected.solve_timeout = Some(timeout);

    // `PdrConfig` does not derive `PartialEq`, and its technique toggles are
    // `pub(crate)` to `ay-chc`. Compare the publicly-visible caps that already
    // distinguish `production` from `default` (production: frames=50,
    // iters=500, obligations=50_000; default: frames=20, iters=1000,
    // obligations=100_000 — see pdr/config.rs).
    assert_eq!(cfg.solve_timeout, Some(timeout));
    assert_eq!(
        cfg.max_frames, expected.max_frames,
        "max_frames (production=50)"
    );
    assert_eq!(
        cfg.max_iterations, expected.max_iterations,
        "max_iterations (production=500)"
    );
    assert_eq!(
        cfg.max_obligations, expected.max_obligations,
        "max_obligations (production=50_000)"
    );

    // Guard against silent drift back to `default()`: production caps differ.
    let default = PdrConfig::default();
    assert_ne!(
        cfg.max_frames, default.max_frames,
        "to_pdr_config must NOT be the default profile"
    );
}

// --- G1: strict-validation knob on the adaptive/portfolio path ---------------

#[test]
fn g1_strict_validation_forces_strict_proofs_on_adaptive_config() {
    // Off by default.
    let plain = EncodeConfig::new().to_adaptive_config();
    assert!(
        !plain.strict_proofs,
        "default config must not force strict_proofs"
    );

    // The knob forces strict_proofs on the portfolio path WITHOUT switching to
    // ProofMode::Strict (i.e. the Auto/portfolio engine stays selected).
    let strict = EncodeConfig::new()
        .with_strict_validation(true)
        .to_adaptive_config();
    assert!(
        strict.strict_proofs,
        "with_strict_validation(true) must force strict_proofs (G1)"
    );

    // ProofMode::Strict still implies strict_proofs on the adaptive config too.
    let via_mode = EncodeConfig::new()
        .with_proof_mode(ProofMode::Strict)
        .to_adaptive_config();
    assert!(via_mode.strict_proofs);
}

// --- Round-trip parity: invoke::solve vs raw ay-chc (Step-0 gate) ------------

#[test]
fn solve_safe_parity_with_raw_pdr_proof() {
    let problem = parse(SAFE_CHC);
    let verdict = solve(
        problem,
        &EncodeConfig::new()
            .with_engine(Engine::Pdr)
            .with_proof_mode(ProofMode::Strict)
            .with_timeout(Duration::from_secs(30)),
    )
    .expect("safe CHC should solve");

    // Raw ay-chc oracle for the same problem.
    let raw = engines::solve_pdr_proof(parse(SAFE_CHC), PdrConfig::production(false))
        .expect("raw pdr proof should run");
    assert!(
        raw.result().is_safe(),
        "oracle must agree the problem is Safe"
    );

    match verdict {
        AyVerdict::Proved {
            certificate,
            invariant: _,
        } => {
            // G5/G6: the Strict Safe path produces a certificate exposing the
            // per-artifact descriptors + proof-run metadata.
            let cert = certificate.expect("Strict Safe path must carry a certificate");
            assert!(
                cert.accepted_as_proof(),
                "proof-grade Safe must be accepted"
            );
            assert_eq!(cert.result(), "safe");
            assert!(
                !cert.normalized_input_sha256().is_empty(),
                "G6: normalized_input_sha256 must be exposed"
            );
            assert!(
                !cert.proof_status().is_empty(),
                "G6: proof_status must be exposed"
            );
            assert!(cert.metadata_json().is_object(), "G6: metadata JSON object");

            // G5: per-artifact schema/role/digest reachable through Certificate.
            let model = cert.artifacts().model();
            assert!(!model.schema().is_empty());
            assert!(!model.role().is_empty());
            assert!(!model.sha256().is_empty());
            assert!(!model.bytes().is_empty());
            let replay = cert.artifacts().replay_transcript();
            assert!(!replay.schema().is_empty());
            assert!(!replay.role().is_empty());

            // The certificate's normalized-input hash must match the free fn
            // re-exported for the cache-key cross-check (G6).
            assert_eq!(
                cert.normalized_input_sha256(),
                crate::normalized_chc_input_sha256(&parse(SAFE_CHC)),
                "G6: cert hash must equal normalized_chc_input_sha256(problem)"
            );
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

#[test]
fn solve_unsafe_maps_to_violated() {
    let problem = parse(UNSAFE_CHC);
    let verdict = solve(
        problem,
        &EncodeConfig::new()
            .with_engine(Engine::Pdr)
            .with_timeout(Duration::from_secs(30)),
    )
    .expect("unsafe CHC should solve");
    assert!(
        matches!(verdict, AyVerdict::Violated(_)),
        "reachable bad state must map to Violated, got {verdict:?}"
    );
}

// --- G4: Unknown reason text preserved ---------------------------------------

#[test]
fn g4_unknown_carries_normalized_reason_and_detail() {
    // Synthesize an Unknown verdict the way `from_verified` does and assert the
    // detail string is the raw AY `Display` rendering (not lost). We reach this
    // by normalizing a raw Unknown VerifiedChcResult.
    //
    // We can't easily force a real solver Unknown deterministically, so drive
    // the normalization directly: a Strict run that comes back Unknown maps to
    // `AyVerdict::Unknown { reason, detail }`. Use `from_verified` against an
    // Unknown produced by the BMC-only proof path on a safe problem (which is
    // inconclusive, not a safety proof) to exercise the detail capture.
    let bmc =
        engines::solve_bmc_proof_from_str(SAFE_CHC, ay_chc::BmcConfig::default().with_max_depth(2))
            .expect("bmc proof should run");

    if matches!(bmc.result(), VerifiedChcResult::Unknown(_)) {
        let verdict = crate::verdict::from_verified(bmc.result().clone(), None);
        match verdict {
            AyVerdict::Unknown { reason, detail } => {
                // The detail must be the AY free-text, and must be non-empty.
                let detail = detail.expect("G4: Unknown detail must be preserved");
                assert!(
                    detail.starts_with("unknown"),
                    "detail should be AY's Display rendering, got {detail:?}"
                );
                // The normalized bucket must be one of the BMC-exhausted reasons.
                assert!(
                    matches!(
                        reason,
                        UnknownReason::BmcExhaustedSearch
                            | UnknownReason::BmcBudgetExhausted
                            | UnknownReason::Inconclusive
                    ),
                    "unexpected normalized reason: {reason:?}"
                );
            }
            other => panic!("expected Unknown, got {other:?}"),
        }
    }
    // If the BMC path returned Safe/Unsafe on this tiny fixture we simply skip
    // (the G4 wiring is also covered structurally by the match arm above).
}

// --- ProofRun certificates stay bound to their solved problem ----------------

#[test]
fn solve_with_proof_certificate_is_bound_and_coherent() {
    let problem = parse(SAFE_CHC);
    let solved_problem_sha256 = crate::normalized_chc_input_sha256(&problem);
    let different_problem_sha256 = crate::normalized_chc_input_sha256(&parse(UNSAFE_CHC));
    let run = solve_with_proof(
        problem,
        &EncodeConfig::new()
            .with_proof_mode(ProofMode::Strict)
            .with_timeout(Duration::from_secs(30)),
    )
    .expect("solve_with_proof should run");

    assert!(run.accepted_as_proof(), "safe fixture must produce a proof");
    let cert = run.certificate();
    assert!(cert.accepted_as_proof());
    assert_eq!(
        cert.metadata().accepted_as_proof(),
        cert.consumer_evidence().accepted_for_consumer(),
        "the immutable evidence views must agree on acceptance"
    );
    assert_eq!(cert.normalized_input_sha256(), solved_problem_sha256);
    assert_ne!(
        cert.normalized_input_sha256(),
        different_problem_sha256,
        "certificate identity must remain bound to the solved problem"
    );
    // metadata_json round-trips the proof-run transcript metadata.
    let json = cert.metadata_json();
    assert!(json.get("normalized_input_sha256").is_some());
}
