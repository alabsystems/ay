// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay::chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};

const INPUT: &str = r#"
(set-logic HORN)
(declare-rel P ((Array (_ BitVec 8) Bool)))
(declare-rel Q ((Array (_ BitVec 8) Bool)))
(declare-rel error ())
(declare-var a (Array (_ BitVec 8) Bool))
(rule (P (store ((as const (Array (_ BitVec 8) Bool)) false) #x01 true)))
(rule (=> (P a) (Q a)))
(rule (=> (and (Q a) (select a #x01)) error))
(query error)
"#;

fn fixture() -> (ChcProblem, Counterexample) {
    let problem = ChcParser::parse(INPUT).expect("original multi-predicate array source");
    let mut config = AdaptiveConfig::default().with_time_budget(Duration::from_secs(5));
    config.strict_proofs = true;
    config.require_ground_unsafe_trace = true;
    let run = AdaptivePortfolio::new(problem.clone(), config).solve_proof_run();
    let VerifiedChcResult::Unsafe(verified) = run.result() else {
        panic!(
            "fixture requires an original ground refutation: {:?}",
            run.result()
        );
    };
    assert!(verified.counterexample().has_ground_derivation());
    (problem, verified.counterexample().clone())
}

#[test]
fn ground_publication_without_stats_preserves_source_and_descriptor_authority() {
    let (problem, counterexample) = fixture();
    let no_stats = stats_output::StatsConfig {
        human: false,
        full: false,
        json: false,
    };
    let scope = ChcArtifactScope::for_unsafe(no_stats, &counterexample);
    assert!(scope.includes_replay_obligations());
    let temp = tempfile::tempdir().expect("owned publication directory");
    let config = ProofConfig {
        path: temp.path().join("proof.chccert").display().to_string(),
        format: super::super::super::ProofFormat::Alethe,
        binary: false,
        artifact_path: None,
        is_temp: false,
        synthesized_default: false,
        format_was_explicit: false,
    };
    let publication = write_chc_unsafe_certificate_artifacts(
        Some(&config),
        ChcProofGates::for_script("", false),
        &counterexample.to_certificate(&problem),
        scope,
        || unsafe_replay_payloads_with_progress(&problem, &counterexample, &mut || true),
    );
    let ChcCertificatePublication::Available(mut artifacts) = publication else {
        panic!("the canonical original ground evidence must publish");
    };
    artifacts
        .validate()
        .expect("retained publication authority");
    assert_eq!(artifacts.replay_obligations.len(), 1);
    let descriptor = &artifacts.replay_obligations[0];
    assert_eq!(descriptor.kind, ChcReplayObligationKind::TraceValidity);
    assert_eq!(
        descriptor.payload_format,
        ChcReplayPayloadFormat::GroundDerivationV1
    );
    assert_eq!(descriptor.query.role, CHC_GROUND_DERIVATION_ARTIFACT_ROLE);
    let path = PathBuf::from(descriptor.query.path.as_ref().expect("retained JSON path"));
    assert_eq!(path.extension().and_then(|ext| ext.to_str()), Some("json"));
    let bytes = fs::read(&path).expect("published proof bytes");
    let checked = ay::chc::validate_chc_ground_derivation_artifact(&problem, &bytes)
        .expect("fresh public reader replays the exact original clauses");
    assert!(checked.step_count() >= 3);
    let changed = ChcParser::parse(&INPUT.replace("(select a #x01)", "(select a #x00)"))
        .expect("changed safe source");
    assert!(ay::chc::validate_chc_ground_derivation_artifact(&changed, &bytes).is_err());
    let mut corrupted: serde_json::Value = serde_json::from_slice(&bytes).expect("native envelope");
    corrupted["query_step"] = serde_json::json!(0);
    assert!(ay::chc::validate_chc_ground_derivation_artifact(
        &problem,
        &serde_json::to_vec(&corrupted).expect("corrupted envelope"),
    )
    .is_err());
    let mut replaced = bytes;
    replaced[0] = b'[';
    fs::write(&path, replaced).expect("replace published bytes without changing length");
    assert!(artifacts.validate().is_err());
}

#[test]
fn ground_export_rejection_is_not_legacy_trace_absence() {
    let (problem, counterexample) = fixture();
    let changed = ChcParser::parse(&INPUT.replace("(select a #x01)", "(select a #x00)"))
        .expect("changed safe source");
    assert!(unsafe_replay_payloads_with_progress(&changed, &counterexample, &mut || true).is_err());
    assert!(unsafe_replay_payloads_with_progress(&problem, &counterexample, &mut || true).is_ok());
}

#[test]
fn interrupted_ground_export_never_retries_with_a_fresh_grant() {
    let (problem, counterexample) = fixture();
    let mut polls = 0;
    let result = unsafe_replay_payloads_with_progress(&problem, &counterexample, &mut || {
        polls += 1;
        polls != 2
    });
    assert!(result.is_err());
    assert_eq!(polls, 2, "the v1 refusal cannot resume in v2 or SMT");
}

#[test]
fn ordinary_uf_evidence_uses_the_authenticated_v2_payload() {
    let input = r#"(set-logic HORN)
(declare-fun f (Int) Int)
(declare-fun P (Int) Bool)
(assert (P (f 0)))
(assert (forall ((x Int)) (=> (P x) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(input).expect("original UF source");
    let result = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::default()).solve_bmc_only(
        ay::chc::BmcConfig::default()
            .with_max_depth(2)
            .with_acyclic_safe(true)
            .with_time_budget(Duration::from_secs(20)),
    );
    let VerifiedChcResult::Unsafe(verified) = result else {
        panic!("the finite UF fixture must carry an original ground proof");
    };
    let counterexample = verified.counterexample();
    assert_eq!(
        counterexample
            .ground_derivation_artifact(&problem)
            .expect_err("v1 stays UF-free")
            .reason,
        ChcGroundDerivationArtifactErrorReason::UnsupportedUninterpretedFunction,
    );
    let mut payloads = unsafe_replay_payloads_with_progress(&problem, counterexample, &mut || true)
        .expect("the same source-authenticated proof may use v2");
    assert_eq!(payloads.len(), 1);
    let file = payloads
        .pop()
        .expect("ground payload")
        .into_file()
        .expect("typed file");
    assert_eq!(file.format, ChcReplayPayloadFormat::GroundDerivationV2);
    assert_eq!(file.role, CHC_GROUND_DERIVATION_ARTIFACT_V2_ROLE);
    let checked = ay::chc::validate_chc_ground_derivation_artifact_v2(&problem, &file.bytes)
        .expect("fresh v2 reader authenticates the original UF observations");
    assert!(checked.uf_observation_count() > 0);
    assert!(ay::chc::validate_chc_ground_derivation_artifact(&problem, &file.bytes).is_err());
    let changed = ChcParser::parse(
        &input
            .replace("declare-fun f", "declare-fun g")
            .replace("(f 0)", "(g 0)"),
    )
    .expect("changed UF source");
    assert!(ay::chc::validate_chc_ground_derivation_artifact_v2(&changed, &file.bytes).is_err());
}
