// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Registered executable validator for SAT model authority.
//!
//! AY has one compiler-enforced SAT publication funnel.  These probes exercise
//! that funnel through the shipped executable in plain, assumption, incremental,
//! and optimization epochs.  They run with `--self-check`, where an assertion
//! the separate `ay-model-check` evaluator cannot confirm must become `unknown`.

use super::*;

pub(super) const VALIDATOR_ID: &str = "builtin.sat-models.v1";

const DIMENSION_ID: &str = "results.sat-models";
const REQUIREMENT_ID: &str = "results.sat-models.independent-validation";

#[derive(Clone, Debug, Eq, PartialEq)]
enum OutputExpectation {
    Exact(&'static str),
    Contains {
        ordered: &'static [&'static str],
        forbidden: &'static [&'static str],
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CaseSpec {
    id: &'static str,
    input: &'static str,
    expectation: OutputExpectation,
    purpose: &'static str,
}

#[derive(Debug, Eq, PartialEq)]
struct Execution {
    ay_sha256: String,
    resource_envelope: String,
    result: ValidatorResult,
    cases: CaseCounts,
    case_results: Vec<ValidatorCase>,
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    let mut manifest: Option<PathBuf> = None;
    let mut receipt_path: Option<PathBuf> = None;
    let mut ay_override: Option<PathBuf> = None;
    let mut timeout_secs = 10u64;
    let mut index = 0usize;
    while index < args.len() {
        match args[index].as_str() {
            "--receipt" => {
                index += 1;
                receipt_path = Some(PathBuf::from(
                    args.get(index).ok_or("--receipt needs a path")?,
                ));
            }
            "--ay" => {
                index += 1;
                ay_override = Some(PathBuf::from(args.get(index).ok_or("--ay needs a path")?));
            }
            "--timeout" => {
                index += 1;
                timeout_secs = args
                    .get(index)
                    .ok_or("--timeout needs seconds")?
                    .parse()
                    .map_err(|_| "--timeout must be a positive integer")?;
                if timeout_secs == 0 || timeout_secs > 3600 {
                    return Err("--timeout must be between 1 and 3600 seconds".to_string());
                }
            }
            flag if flag.starts_with("--") => {
                return Err(format!("unknown sat-models flag {flag:?}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("sat-models takes exactly one manifest path".to_string());
                }
            }
        }
        index += 1;
    }

    let manifest = manifest.ok_or("sat-models needs a manifest path")?;
    let receipt_path = receipt_path.ok_or("sat-models requires --receipt <path>")?;
    let loaded = load_contract(&manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let envelope = loaded
        .contract
        .resource_envelope
        .as_deref()
        .ok_or("sat-models requires contract.resource_envelope")?;
    let parsed = parse_resource_envelope(envelope)?;
    if parsed.jobs != 1 || parsed.timeout != Duration::from_secs(timeout_secs) {
        return Err("sat-models requires the matching one-job resource envelope".to_string());
    }
    let dimension = sat_dimension(&loaded.contract)?;
    let subject = loaded
        .contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("sat-models requires subject.ay_executable")?;
    let ay = ay_override.unwrap_or_else(|| artifact_path(&loaded.base, &subject.path));
    let execution = execute(
        &loaded.contract,
        &ay,
        Duration::from_secs(timeout_secs),
        Some(envelope),
    )?;
    let current_exe = fs::canonicalize(
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?,
    )
    .map_err(|error| format!("canonicalizing parity executable: {error}"))?;
    let receipt = ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: loaded.contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: dimension.id.clone(),
        requirement_ids: vec![REQUIREMENT_ID.to_string()],
        inventory_sha256: dimension.inventory.sha256.clone(),
        validator: ValidatorIdentity {
            id: VALIDATOR_ID.to_string(),
            kind: ValidatorKind::IndependentModelChecker,
            path: current_exe.to_string_lossy().into_owned(),
            sha256: sha256_file(&current_exe, "parity validator")?,
        },
        subject: ReceiptSubject {
            ay_executable_sha256: Some(execution.ay_sha256),
            ay_shared_library_sha256: loaded
                .contract
                .subject
                .ay_shared_library
                .as_ref()
                .map(|artifact| artifact.sha256.clone()),
        },
        z3_binary_sha256: None,
        z3_shared_library_sha256: None,
        reference_inputs: Vec::new(),
        auxiliary_tools: Vec::new(),
        source_provenance: None,
        resource_envelope: Some(execution.resource_envelope),
        exhaustive: true,
        result: execution.result,
        cases: execution.cases,
        case_results: execution.case_results,
    };
    let bytes = pretty_json(&receipt)?;
    atomic_write_new(&receipt_path, &bytes)?;
    let relative = future_relative_output(&loaded.base, &receipt_path)?;
    let receipt_sha = sha256_bytes(&bytes);
    println!(
        "sat-models={} receipt={} sha256={}",
        if receipt.result == ValidatorResult::Pass {
            "PASS"
        } else {
            "FAIL"
        },
        relative,
        receipt_sha
    );
    println!(
        "attach to {REQUIREMENT_ID}: {{\"path\":\"{relative}\",\"sha256\":\"{receipt_sha}\"}}"
    );
    if !report.complete {
        println!(
            "note: the rest of the contract remains incomplete ({} existing blockers)",
            report.blockers.len()
        );
    }
    Ok(i32::from(receipt.result != ValidatorResult::Pass))
}

pub(super) fn validate_and_replay(
    receipt: &ValidatorReceipt,
    context: EvidenceContext<'_>,
) -> Result<(), String> {
    if receipt.validator.kind != ValidatorKind::IndependentModelChecker
        || context.dimension.id != DIMENSION_ID
        || receipt.requirement_ids != [REQUIREMENT_ID.to_string()]
        || !receipt.exhaustive
        || receipt.z3_binary_sha256.is_some()
        || receipt.z3_shared_library_sha256.is_some()
        || !receipt.reference_inputs.is_empty()
        || !receipt.auxiliary_tools.is_empty()
        || receipt.source_provenance.is_some()
    {
        return Err(format!(
            "{VALIDATOR_ID} has invalid kind, dimension, coverage, or bindings"
        ));
    }
    let expected_ids = catalog()
        .iter()
        .map(|case| case.id.to_string())
        .collect::<Vec<_>>();
    let actual_ids = receipt
        .case_results
        .iter()
        .map(|row| row.id.clone())
        .collect::<Vec<_>>();
    if actual_ids != expected_ids {
        return Err(format!("{VALIDATOR_ID} detailed case inventory drift"));
    }
    if context.mode.replays_registered_validators() {
        let envelope = receipt
            .resource_envelope
            .as_deref()
            .ok_or("sat-models receipt has no resource envelope")?;
        let parsed = parse_resource_envelope(envelope)?;
        if parsed.jobs != 1 {
            return Err("sat-models receipts require a one-job envelope".to_string());
        }
        let subject = context
            .contract
            .subject
            .ay_executable
            .as_ref()
            .ok_or("sat-models replay requires subject.ay_executable")?;
        let live = execute(
            context.contract,
            &artifact_path(context.manifest_dir, &subject.path),
            parsed.timeout,
            Some(envelope),
        )?;
        if receipt.result != live.result
            || receipt.cases != live.cases
            || receipt.case_results != live.case_results
        {
            return Err(format!(
                "{VALIDATOR_ID} receipt does not match fresh executable replay"
            ));
        }
    }
    Ok(())
}

fn execute(
    contract: &Contract,
    ay_source: &Path,
    timeout: Duration,
    required_envelope: Option<&str>,
) -> Result<Execution, String> {
    let subject = contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("sat-models requires subject.ay_executable")?;
    let staged = stage_authenticated_executable(ay_source, &subject.sha256, "AY executable")?;
    let repo_root = locate_repo_root()?;
    let resources =
        PlannedResources::plan(&repo_root, 1, "ay-z3-parity smtlib-conformance sat-models")
            .map_err(|error| error.to_string())?;
    let envelope = effective_execution_envelope(
        &resources.plan,
        ENFORCEMENT_RSS_WATCHDOG_V1,
        timeout.as_secs_f64(),
    )
    .map_err(|error| error.to_string())?;
    if required_envelope.is_some_and(|expected| expected != envelope) {
        return Err("live sat-models resource envelope drift".to_string());
    }

    let mut rows = Vec::new();
    for spec in catalog() {
        let output = resources
            .run_external_transcript(
                &staged.path,
                ["--z3-mode", "--quiet", "--self-check", "-in"],
                spec.input.as_bytes(),
                timeout,
                &format!("SAT model case {}", spec.id),
            )
            .map_err(|error| error.to_string())?;
        rows.push(case_row(spec, output));
    }
    if sha256_file(&staged.path, "staged AY after SAT model probes")? != subject.sha256 {
        return Err("authenticated AY bytes changed during SAT model probes".to_string());
    }
    rows.sort_by(|left, right| left.id.cmp(&right.id));
    let cases = case_counts_from_rows(&rows)?;
    Ok(Execution {
        ay_sha256: subject.sha256.clone(),
        resource_envelope: envelope,
        result: overall_validator_result(&rows),
        cases,
        case_results: rows,
    })
}

fn case_row(spec: CaseSpec, output: GuardedTranscriptOutput) -> ValidatorCase {
    let status = output.status.and_then(|status| status.code());
    let stdout_result = String::from_utf8(output.stdout);
    let stderr_result = String::from_utf8(output.stderr);
    let streams_utf8 = stdout_result.is_ok() && stderr_result.is_ok();
    let stdout = stdout_result
        .unwrap_or_else(|error| String::from_utf8_lossy(error.as_bytes()).into_owned());
    let stderr = stderr_result
        .unwrap_or_else(|error| String::from_utf8_lossy(error.as_bytes()).into_owned());
    let process = ProcessObservation {
        stdin_complete: output.stdin_complete,
        timed_out: output.timed_out,
        memout: output.memout,
        stdout_truncated: output.stdout_truncated,
        stderr_truncated: output.stderr_truncated,
    };
    let output_matches = match &spec.expectation {
        OutputExpectation::Exact(expected) => stdout == *expected,
        OutputExpectation::Contains { ordered, forbidden } => {
            let mut offset = 0usize;
            let ordered_match = ordered.iter().all(|fragment| {
                let Some(found) = stdout[offset..].find(fragment) else {
                    return false;
                };
                offset += found + fragment.len();
                true
            });
            ordered_match && forbidden.iter().all(|fragment| !stdout.contains(fragment))
        }
    };
    let outcome = if process.memout {
        ValidatorCaseOutcome::Memout
    } else if process.timed_out {
        ValidatorCaseOutcome::Timeout
    } else if status.is_none() {
        ValidatorCaseOutcome::Crash
    } else if status != Some(0)
        || !process.stdin_complete
        || process.stdout_truncated
        || process.stderr_truncated
        || !streams_utf8
        || !stderr.is_empty()
        || !output_matches
    {
        ValidatorCaseOutcome::Fail
    } else {
        ValidatorCaseOutcome::Pass
    };
    ValidatorCase {
        id: spec.id.to_string(),
        input_sha256: sha256_bytes(spec.input.as_bytes()),
        expected: format!(
            "{}; --self-check; independent model confirmation or fail-closed unknown; exit=0; stderr-empty",
            spec.purpose
        ),
        observed: format!(
            "exit={status:?};stdin-complete={};timeout={};memout={};stdout-truncated={};stderr-truncated={};streams-utf8={streams_utf8};output-match={output_matches};stdout-sha256={};stderr-sha256={}",
            process.stdin_complete,
            process.timed_out,
            process.memout,
            process.stdout_truncated,
            process.stderr_truncated,
            sha256_bytes(stdout.as_bytes()),
            sha256_bytes(stderr.as_bytes())
        ),
        stdout: Some(stdout),
        stderr: Some(stderr),
        exit_code: status,
        process: Some(process),
        outcome,
    }
}

fn catalog() -> Vec<CaseSpec> {
    let mut cases = vec![
        CaseSpec {
            id: "sat-model.array-read",
            input: "(set-option :produce-models true)\n(set-logic QF_AX)\n(declare-const a (Array Int Int))\n(assert (= (select a 0) 9))\n(check-sat)\n(get-value ((select a 0)))\n",
            expectation: OutputExpectation::Exact("sat\n(((select a 0) 9))\n"),
            purpose: "array interpretation satisfies the authored read",
        },
        CaseSpec {
            id: "sat-model.assumption-epoch",
            input: "(set-option :produce-models true)\n(set-logic QF_UF)\n(declare-const p Bool)\n(check-sat-assuming (p))\n(get-value (p))\n",
            expectation: OutputExpectation::Exact("sat\n((p true))\n"),
            purpose: "query-local assumption is part of the validated model obligation",
        },
        CaseSpec {
            id: "sat-model.bitvector",
            input: "(set-option :produce-models true)\n(set-logic QF_BV)\n(declare-const b (_ BitVec 8))\n(assert (= b #x2a))\n(check-sat)\n(get-value (b))\n",
            expectation: OutputExpectation::Exact("sat\n((b #x2a))\n"),
            purpose: "width-tagged bit-vector model is validated exactly",
        },
        CaseSpec {
            id: "sat-model.boolean",
            input: "(set-option :produce-models true)\n(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(check-sat)\n(get-value (p))\n",
            expectation: OutputExpectation::Exact("sat\n((p true))\n"),
            purpose: "Boolean authored assertion evaluates true",
        },
        CaseSpec {
            id: "sat-model.cannot-confirm-negative-control",
            input: "(set-option :produce-models true)\n(set-logic AUFLIA)\n(declare-fun f (Int) Int)\n(assert (forall ((x Int)) (= (f x) x)))\n(check-sat)\n(get-model)\n(get-info :reason-unknown)\n",
            expectation: OutputExpectation::Contains {
                ordered: &["unknown\n", "model is not available", ":reason-unknown", "incomplete"],
                forbidden: &["sat\n", "(define-fun f"],
            },
            purpose: "an independently unevaluable quantified model fails closed under self-check",
        },
        CaseSpec {
            id: "sat-model.epoch-invalidation",
            input: "(set-option :produce-models true)\n(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(check-sat)\n(push 1)\n(assert (not p))\n(get-model)\n(check-sat)\n(get-model)\n(pop 1)\n(check-sat)\n(get-value (p))\n",
            expectation: OutputExpectation::Exact("sat\n(error \"model is not available\")\nunsat\n(error \"model is not available\")\nsat\n((p true))\n"),
            purpose: "semantic mutation and later UNSAT revoke stale model authority",
        },
        CaseSpec {
            id: "sat-model.integer-multi-assertion",
            input: "(set-option :produce-models true)\n(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= x 7))\n(assert (= (+ x 1) 8))\n(check-sat)\n(get-value (x (+ x 1)))\n",
            expectation: OutputExpectation::Exact("sat\n((x 7) ((+ x 1) 8))\n"),
            purpose: "every authored integer assertion is validated",
        },
        CaseSpec {
            id: "sat-model.optimization-epoch",
            input: "(set-option :produce-models true)\n(set-logic QF_LIA)\n(declare-const x Int)\n(assert (and (>= x 0) (<= x 3)))\n(maximize x)\n(check-sat)\n(get-value (x))\n(get-objectives)\n",
            expectation: OutputExpectation::Exact(
                "sat\n((x 3))\n(objectives\n (x 3)\n)\n",
            ),
            purpose: "optimization SAT passes the same model funnel and binds optimum authority",
        },
        CaseSpec {
            id: "sat-model.real",
            input: "(set-option :produce-models true)\n(set-logic QF_LRA)\n(declare-const r Real)\n(assert (= r (/ 3 2)))\n(check-sat)\n(get-value (r))\n",
            expectation: OutputExpectation::Contains {
                ordered: &["sat\n", "((r ", "3", "2", "))\n"],
                forbidden: &["unknown", "error"],
            },
            purpose: "exact rational model satisfies the authored equality",
        },
        CaseSpec {
            id: "sat-model.string",
            input: "(set-option :produce-models true)\n(set-logic ALL)\n(declare-const s String)\n(assert (= s \"abc\"))\n(assert (= (str.len s) 3))\n(check-sat)\n(get-value (s (str.len s)))\n",
            expectation: OutputExpectation::Exact("sat\n((s \"abc\") ((str.len s) 3))\n"),
            purpose: "Unicode string and derived length agree in the final model",
        },
        CaseSpec {
            id: "sat-model.uf-congruence",
            input: "(set-option :produce-models true)\n(set-logic QF_UFLIA)\n(declare-fun f (Int) Int)\n(assert (= (f 0) 11))\n(assert (= (f (+ 0 0)) 11))\n(check-sat)\n(get-value ((f 0) (f (+ 0 0))))\n",
            expectation: OutputExpectation::Exact("sat\n(((f 0) 11) ((f (+ 0 0)) 11))\n"),
            purpose: "equal argument values receive one UF interpretation",
        },
        CaseSpec {
            id: "sat-model.vacuous",
            input: "(set-option :produce-models true)\n(check-sat)\n(get-model)\n",
            expectation: OutputExpectation::Exact("sat\n(\n)\n"),
            purpose: "empty conjunction receives explicit vacuous authority",
        },
    ];
    cases.sort_by_key(|case| case.id);
    cases
}

fn sat_dimension(contract: &Contract) -> Result<&Dimension, String> {
    contract
        .dimensions
        .iter()
        .find(|dimension| dimension.id == DIMENSION_ID)
        .ok_or_else(|| format!("closed dimension {DIMENSION_ID:?} is missing"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn catalog_is_sorted_and_covers_each_result_epoch_class() {
        let cases = catalog();
        assert!(cases.windows(2).all(|pair| pair[0].id < pair[1].id));
        assert!(cases.iter().any(|case| case.id.contains("assumption")));
        assert!(cases.iter().any(|case| case.id.contains("epoch")));
        assert!(cases
            .iter()
            .any(|case| case.id.contains("negative-control")));
        assert!(cases.iter().all(|case| case.input.contains("check-sat")));
    }
}
