// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Hidden executable self-test for the SMT-LIB Unknown/artifact contract.
//!
//! This is deliberately a diagnostic command rather than a solver option: it
//! cannot affect an ordinary solve.  The full-replacement parity gate invokes
//! this command on a hash-authenticated copy of the AY executable so the gate
//! tests the same `Executor` transition shipped to users, not a linked test
//! double.

use anyhow::{bail, Context as _, Result};
use ay_dpll::{Executor, UnknownOrigin, UnknownReason};
use ay_frontend::Command;
use serde::Serialize;
use std::sync::{
    atomic::{AtomicBool, AtomicU64, Ordering},
    Arc,
};
use std::time::Duration;

const REPORT_SCHEMA: &str = "ay.unknown-policy-probe/v2";
static SCENARIO_EXECUTIONS: AtomicU64 = AtomicU64::new(0);

const MODEL_SCRIPT: &str = r#"
    (set-logic QF_UF)
    (set-option :produce-models true)
    (declare-const model_flag Bool)
    (assert model_flag)
    (check-sat)
"#;

const PROOF_SCRIPT: &str = r#"
    (set-logic QF_UF)
    (set-option :produce-proofs true)
    (declare-const proof_flag Bool)
    (assert proof_flag)
    (assert (not proof_flag))
    (check-sat)
"#;

const CORE_SCRIPT: &str = r#"
    (set-logic QF_UF)
    (set-option :produce-unsat-cores true)
    (declare-const core_flag Bool)
    (assert (! core_flag :named core_positive))
    (assert (! (not core_flag) :named core_negative))
    (check-sat)
"#;

const ASSUMPTION_SCRIPT: &str = r#"
    (set-logic QF_UF)
    (set-option :produce-unsat-assumptions true)
    (declare-const assumption_flag Bool)
    (assert assumption_flag)
    (check-sat-assuming ((not assumption_flag)))
"#;

const OPTIMUM_SCRIPT: &str = r#"
    (set-logic QF_LIA)
    (declare-const objective_value Int)
    (assert (>= objective_value 0))
    (assert (<= objective_value 1))
    (maximize objective_value)
    (check-sat)
"#;

#[derive(clap::Args)]
pub(crate) struct UnknownPolicyProbeArgs {
    /// Prove that the probe detects a deliberately omitted Unknown transition.
    #[arg(long, hide = true)]
    negative_control: bool,
}

#[derive(Clone, Copy)]
enum ProbeMode {
    PublishOrigin,
    RetainNegativeControl,
}

impl ProbeMode {
    fn from_args(args: &UnknownPolicyProbeArgs) -> Self {
        if args.negative_control {
            Self::RetainNegativeControl
        } else {
            Self::PublishOrigin
        }
    }

    fn code(self) -> &'static str {
        match self {
            Self::PublishOrigin => "publish-origin",
            Self::RetainNegativeControl => "retain-negative-control",
        }
    }

    fn applies_transition(self) -> bool {
        matches!(self, Self::PublishOrigin)
    }
}

#[derive(Clone, Copy)]
enum ExpectedDecision {
    Sat,
    Unsat,
}

#[derive(Clone, Copy)]
enum ArtifactKind {
    Model,
    Proof,
    Core,
    Assumptions,
    Optimum,
}

impl ArtifactKind {
    fn code(self) -> &'static str {
        match self {
            Self::Model => "model",
            Self::Proof => "proof",
            Self::Core => "core",
            Self::Assumptions => "assumptions",
            Self::Optimum => "optimum",
        }
    }
}

#[derive(Clone, Debug, Serialize)]
struct ArtifactObservation {
    scenario_id: String,
    execution_ordinal: u64,
    available_before: bool,
    revoked_after: bool,
}

#[derive(Clone, Debug, Serialize)]
struct ArtifactMatrix {
    model: ArtifactObservation,
    proof: ArtifactObservation,
    core: ArtifactObservation,
    assumptions: ArtifactObservation,
    optimum: ArtifactObservation,
}

impl ArtifactMatrix {
    fn all_available(&self) -> bool {
        self.observations()
            .into_iter()
            .all(|observation| observation.available_before)
    }

    fn all_revoked(&self) -> bool {
        self.observations()
            .into_iter()
            .all(|observation| observation.revoked_after)
    }

    fn none_revoked(&self) -> bool {
        self.observations()
            .into_iter()
            .all(|observation| !observation.revoked_after)
    }

    fn observations(&self) -> [&ArtifactObservation; 5] {
        [
            &self.model,
            &self.proof,
            &self.core,
            &self.assumptions,
            &self.optimum,
        ]
    }
}

#[derive(Debug, Serialize)]
struct ReasonProbe {
    origin_code: &'static str,
    production_chokepoint: &'static str,
    reason_code: &'static str,
    reason_name: &'static str,
    reason_smtlib: String,
    transition_applied: bool,
    unknown_installed: bool,
    observed_origin_code: Option<&'static str>,
    trigger_kind: &'static str,
    artifact_transition_kind: &'static str,
    fixture_id: String,
    artifacts: ArtifactMatrix,
    policy_satisfied: bool,
    negative_control_detected: bool,
}

#[derive(Debug, Serialize)]
struct ProbeReport {
    schema: &'static str,
    mode: &'static str,
    registry_codes: Vec<&'static str>,
    registry_origins: Vec<&'static str>,
    passed: bool,
    cases: Vec<ReasonProbe>,
}

pub(crate) fn run(args: UnknownPolicyProbeArgs) -> Result<i32> {
    let mode = ProbeMode::from_args(&args);
    let cases = match mode {
        ProbeMode::PublishOrigin => UnknownOrigin::ALL
            .iter()
            .copied()
            .map(|origin| probe_origin(origin, mode))
            .collect::<Result<Vec<_>>>()?,
        ProbeMode::RetainNegativeControl => UnknownOrigin::ALL
            .iter()
            .copied()
            // Every control is executed independently. Reusing one Timeout
            // observation for all origins previously made 17 controls fictive.
            .map(|origin| probe_origin(origin, mode))
            .collect::<Result<Vec<_>>>()?,
    };
    let passed = match mode {
        ProbeMode::PublishOrigin => cases.iter().all(|case| case.policy_satisfied),
        ProbeMode::RetainNegativeControl => cases.iter().all(|case| case.negative_control_detected),
    };
    let report = ProbeReport {
        schema: REPORT_SCHEMA,
        mode: mode.code(),
        registry_codes: UnknownReason::ALL.iter().map(UnknownReason::code).collect(),
        registry_origins: UnknownOrigin::ALL
            .iter()
            .map(|origin| origin.code())
            .collect(),
        passed,
        cases,
    };
    println!(
        "{}",
        serde_json::to_string(&report).context("serializing Unknown-policy probe report")?
    );
    Ok(i32::from(!passed))
}

fn probe_origin(origin: UnknownOrigin, mode: ProbeMode) -> Result<ReasonProbe> {
    let reason = origin.reason();
    let model = observe_artifact(
        MODEL_SCRIPT,
        ExpectedDecision::Sat,
        Command::GetModel,
        ArtifactKind::Model,
        origin,
        mode,
    )?;
    let proof = observe_artifact(
        PROOF_SCRIPT,
        ExpectedDecision::Unsat,
        Command::GetProof,
        ArtifactKind::Proof,
        origin,
        mode,
    )?;
    let core = observe_artifact(
        CORE_SCRIPT,
        ExpectedDecision::Unsat,
        Command::GetUnsatCore,
        ArtifactKind::Core,
        origin,
        mode,
    )?;
    let assumptions = observe_artifact(
        ASSUMPTION_SCRIPT,
        ExpectedDecision::Unsat,
        Command::GetUnsatAssumptions,
        ArtifactKind::Assumptions,
        origin,
        mode,
    )?;
    let optimum = observe_artifact(
        OPTIMUM_SCRIPT,
        ExpectedDecision::Sat,
        Command::GetObjectives,
        ArtifactKind::Optimum,
        origin,
        mode,
    )?;
    let unknown_installed = [&model, &proof, &core, &assumptions, &optimum]
        .into_iter()
        .all(|observation| observation.unknown_installed);
    let observed_origin_code = model.observed_origin_code;
    let origins_match = [&model, &proof, &core, &assumptions, &optimum]
        .into_iter()
        .all(|observation| observation.observed_origin_code == observed_origin_code);
    let artifacts = ArtifactMatrix {
        model: model.artifact,
        proof: proof.artifact,
        core: core.artifact,
        assumptions: assumptions.artifact,
        optimum: optimum.artifact,
    };
    let policy_satisfied = mode.applies_transition()
        && unknown_installed
        && origins_match
        && observed_origin_code == Some(origin.code())
        && artifacts.all_available()
        && artifacts.all_revoked();
    let negative_control_detected = !mode.applies_transition()
        && !unknown_installed
        && origins_match
        && observed_origin_code.is_none()
        && artifacts.all_available()
        && artifacts.none_revoked();

    Ok(ReasonProbe {
        origin_code: origin.code(),
        production_chokepoint: origin.production_chokepoint(),
        reason_code: reason.code(),
        reason_name: reason.name(),
        reason_smtlib: reason.to_string(),
        transition_applied: mode.applies_transition(),
        unknown_installed,
        observed_origin_code,
        trigger_kind: trigger_kind(origin),
        artifact_transition_kind: "authoritative-origin-publication",
        fixture_id: format!("{}:{}", origin_fixture(origin), mode.code()),
        artifacts,
        policy_satisfied,
        negative_control_detected,
    })
}

struct ScenarioObservation {
    artifact: ArtifactObservation,
    unknown_installed: bool,
    observed_origin_code: Option<&'static str>,
}

fn observe_artifact(
    script: &str,
    expected_decision: ExpectedDecision,
    query: Command,
    kind: ArtifactKind,
    origin: UnknownOrigin,
    mode: ProbeMode,
) -> Result<ScenarioObservation> {
    let commands =
        ay_frontend::parse(script).context("parsing built-in Unknown-policy scenario")?;
    let execution_ordinal = SCENARIO_EXECUTIONS.fetch_add(1, Ordering::Relaxed);
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .context("executing built-in Unknown-policy scenario")?;
    let decision_matches = match expected_decision {
        ExpectedDecision::Sat => executor.last_result_is_sat(),
        ExpectedDecision::Unsat => executor.last_result_is_unsat(),
    };
    if !decision_matches {
        bail!("Unknown-policy scenario did not establish its expected decision");
    }

    let before = query_output(&mut executor, &query)?;
    let available_before = artifact_available(kind, &before);
    if mode.applies_transition() {
        exercise_origin(&mut executor, origin)?;
    }
    let after = query_output(&mut executor, &query)?;
    Ok(ScenarioObservation {
        artifact: ArtifactObservation {
            scenario_id: format!("{}:{}:{}", origin.code(), kind.code(), mode.code()),
            execution_ordinal,
            available_before,
            revoked_after: artifact_revoked(kind, &after) && after != before,
        },
        unknown_installed: executor.last_result_is_unknown()
            && executor.unknown_reason() == Some(origin.reason())
            && executor.unknown_origin() == Some(origin),
        observed_origin_code: executor.unknown_origin().map(UnknownOrigin::code),
    })
}

/// Exercise a natural producer when it can be triggered deterministically on
/// an arbitrary live incremental session. Other origins use explicit fault
/// injection at the same authoritative publication chokepoint their production
/// path must cross. The report distinguishes the two; neither is presented as
/// natural execution when it is not.
fn exercise_origin(executor: &mut Executor, origin: UnknownOrigin) -> Result<()> {
    if trigger_kind(origin) == "natural-public-query" {
        let mut producer = Executor::new();
        exercise_natural_origin(&mut producer, origin)?;
        if !producer.last_result_is_unknown()
            || producer.unknown_reason() != Some(origin.reason())
            || producer.unknown_origin() != Some(origin)
        {
            bail!(
                "natural producer did not publish exact origin={} reason={}",
                origin.code(),
                origin.reason().code()
            );
        }
    }
    // Artifact revocation is tested independently of the natural producer's
    // own preflight mutations. This exact typed publication boundary is also
    // what every internal Unknown result crosses before returning publicly.
    executor.conformance_inject_unknown_origin(origin);
    Ok(())
}

fn exercise_natural_origin(executor: &mut Executor, origin: UnknownOrigin) -> Result<()> {
    match origin {
        UnknownOrigin::SolveDeadline => {
            executor.set_timeout(Some(Duration::ZERO));
            let output = executor
                .execute(&Command::CheckSat)
                .context("triggering deadline Unknown origin")?;
            if output.as_deref() != Some("unknown") {
                bail!("deadline origin did not produce Unknown");
            }
        }
        UnknownOrigin::MemoryBudget => {
            // One byte is below the resident set of the already-running
            // authenticated executable, so this is deterministic without
            // allocating toward an unsafe memory ceiling.
            executor.set_memory_limit(Some(1));
            let output = executor
                .execute(&Command::CheckSat)
                .context("triggering memory-budget Unknown origin")?;
            if output.as_deref() != Some("unknown") {
                bail!("memory-budget origin did not produce Unknown");
            }
        }
        UnknownOrigin::InterruptFlag => {
            let interrupted = Arc::new(AtomicBool::new(true));
            executor.set_interrupt(interrupted.clone());
            let output = executor
                .execute(&Command::CheckSat)
                .context("triggering interrupt Unknown origin")?;
            if output.as_deref() != Some("unknown") || !interrupted.load(Ordering::Relaxed) {
                bail!("interrupt origin did not produce Unknown");
            }
        }
        UnknownOrigin::TerminalTrust => {
            // The #8759 strict-proof gate has a deterministic natural
            // producer, so it is exercised rather than fault-injected. AY
            // refutes this problem cleanly — no `trust`/`hole` step, every
            // `assume` provenance-backed — but the refutation is stated over a
            // `Seq` sort no external checker can parse, so under strict proofs
            // the certified UNSAT is withheld.
            let script = "(set-option :produce-proofs true)\n\
                          (set-option :check-proofs-strict true)\n\
                          (set-logic ALL)\n\
                          (declare-const s (Seq Int))\n\
                          (assert (= (seq.len s) 1))\n\
                          (assert (= (seq.len s) 2))\n\
                          (check-sat)\n";
            let commands = ay_frontend::parse(script)
                .context("parsing the strict-proof terminal-trust fixture")?;
            let outputs = executor
                .execute_all(&commands)
                .context("triggering strict-proof terminal-trust Unknown origin")?;
            if outputs.last().map(String::as_str) != Some("unknown") {
                bail!("strict-proof terminal-trust origin did not produce Unknown");
            }
        }
        _ => bail!(
            "origin={} has no natural conformance fixture",
            origin.code()
        ),
    }
    Ok(())
}

fn trigger_kind(origin: UnknownOrigin) -> &'static str {
    match origin {
        UnknownOrigin::SolveDeadline
        | UnknownOrigin::MemoryBudget
        | UnknownOrigin::InterruptFlag
        | UnknownOrigin::TerminalTrust => "natural-public-query",
        _ => "authoritative-origin-publication-fault-injection",
    }
}

fn origin_fixture(origin: UnknownOrigin) -> &'static str {
    match origin {
        UnknownOrigin::SolveDeadline => "natural.check-sat.zero-deadline",
        UnknownOrigin::DeterministicResourceBudget => {
            "fault.deterministic-resource-budget.authoritative-publication"
        }
        UnknownOrigin::MemoryBudget => "natural.check-sat.one-byte-memory-limit",
        UnknownOrigin::InterruptFlag => "natural.check-sat.pre-set-interrupt",
        UnknownOrigin::IncompleteSolverLane => {
            "fault.incomplete-solver-lane.authoritative-publication"
        }
        UnknownOrigin::VerdictCertification => {
            "fault.verdict-certification.authoritative-publication"
        }
        UnknownOrigin::EmatchingRoundBudget => {
            "fault.ematching-round-budget.authoritative-publication"
        }
        UnknownOrigin::DeferredInstantiation => {
            "fault.deferred-instantiation.authoritative-publication"
        }
        UnknownOrigin::UnhandledQuantifier => {
            "fault.unhandled-quantifier.authoritative-publication"
        }
        UnknownOrigin::CegqiRefinement => "fault.cegqi-refinement.authoritative-publication",
        UnknownOrigin::ExistentialEmatching => {
            "fault.existential-ematching.authoritative-publication"
        }
        UnknownOrigin::TheorySplitBudget => "fault.theory-split-budget.authoritative-publication",
        UnknownOrigin::UnsupportedExpressionSplit => {
            "fault.unsupported-expression-split.authoritative-publication"
        }
        UnknownOrigin::UnsupportedFeature => "fault.unsupported-feature.authoritative-publication",
        UnknownOrigin::UnsupportedArithmeticFragment => {
            "fault.unsupported-arithmetic-fragment.authoritative-publication"
        }
        UnknownOrigin::UnsupportedMixedCollection => {
            "fault.unsupported-mixed-collection.authoritative-publication"
        }
        UnknownOrigin::ExecutorFailure => "fault.executor-failure.authoritative-publication",
        UnknownOrigin::UntaggedSolverUnknown => {
            "fault.untagged-solver-unknown.authoritative-publication"
        }
        UnknownOrigin::TerminalTrust => "natural.check-sat.strict-proof-terminal-trust",
    }
}

fn query_output(executor: &mut Executor, query: &Command) -> Result<String> {
    executor
        .execute(query)
        .context("executing Unknown-policy artifact query")?
        .context("Unknown-policy artifact query returned no response")
}

fn artifact_available(kind: ArtifactKind, output: &str) -> bool {
    match kind {
        ArtifactKind::Model => output.starts_with("(model"),
        ArtifactKind::Proof => !output.starts_with("(error ") && !output.is_empty(),
        ArtifactKind::Core => {
            !output.starts_with("(error ")
                && output.contains("core_positive")
                && output.contains("core_negative")
        }
        ArtifactKind::Assumptions => {
            !output.starts_with("(error ") && output.contains("assumption_flag")
        }
        ArtifactKind::Optimum => {
            output.starts_with("(objectives") && output.contains("objective_value")
        }
    }
}

fn artifact_revoked(kind: ArtifactKind, output: &str) -> bool {
    match kind {
        ArtifactKind::Model => output == "(error \"model is not available\")",
        ArtifactKind::Proof => {
            output == "(error \"proof is not available, last result was unknown\")"
        }
        ArtifactKind::Core => {
            output == "(error \"unsat core is not available, last result was not unsat\")"
        }
        ArtifactKind::Assumptions => {
            output == "(error \"unsat assumptions not available, last result was unknown\")"
        }
        ArtifactKind::Optimum => output == "(error \"objectives are not available\")",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn timeout_reason_applies_and_detects_omitted_transition() {
        let positive = probe_origin(UnknownOrigin::SolveDeadline, ProbeMode::PublishOrigin)
            .expect("positive Unknown-policy probe");
        assert!(positive.policy_satisfied);
        assert!(!positive.negative_control_detected);

        let negative = probe_origin(
            UnknownOrigin::SolveDeadline,
            ProbeMode::RetainNegativeControl,
        )
        .expect("negative Unknown-policy control");
        assert!(!negative.policy_satisfied);
        assert!(negative.negative_control_detected);
    }

    #[test]
    fn registry_codes_are_unique() {
        let codes = UnknownReason::ALL
            .iter()
            .map(UnknownReason::code)
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(codes.len(), UnknownReason::ALL.len());
        let fixtures = UnknownOrigin::ALL
            .iter()
            .copied()
            .map(origin_fixture)
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(fixtures.len(), UnknownOrigin::ALL.len());
        assert_eq!(
            UnknownOrigin::ALL
                .iter()
                .copied()
                .filter(|origin| trigger_kind(*origin) == "natural-public-query")
                .count(),
            3
        );
        assert_eq!(
            UnknownOrigin::ALL.map(UnknownOrigin::reason),
            UnknownReason::ALL
        );
    }
}
