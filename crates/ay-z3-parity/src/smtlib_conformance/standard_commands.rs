// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Registered executable validator for the 32 SMT-LIB 2.7 command forms.
//!
//! The command inventory comes only from the authenticated, pinned language
//! snapshot.  Every case invokes a private hash-authenticated copy of the
//! manifest-bound AY executable through the repository RSS watchdog.  A case
//! passes from its retained process transcript, never from receipt aggregates.

use super::*;
use reference_inventory::LanguageCommandProduction;

pub(super) const VALIDATOR_ID: &str = "builtin.standard-commands.v1";

const DIMENSION_ID: &str = "language.commands";
const RECOVERY_MARKER: &str = "__ay_standard_command_recovered__";
const COMMAND_MARKER: &str = "__ay_standard_command_completed__";
const EXPECTED_CASE_COUNT: usize = 118;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ExpectedStatus {
    ExitZero,
    RejectedExitOne,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum StdoutExpectation {
    Exact(String),
    Contains {
        fragments: Vec<String>,
        verdict: Option<&'static str>,
        marker: Option<&'static str>,
        unsupported: bool,
    },
    Rejected,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CaseSpec {
    id: String,
    command: String,
    source_production_sha256: String,
    input: Vec<u8>,
    status: ExpectedStatus,
    stdout: StdoutExpectation,
}

impl CaseSpec {
    fn expected(&self) -> String {
        let class = match self.status {
            ExpectedStatus::ExitZero => "accepted-exit-zero",
            ExpectedStatus::RejectedExitOne => "rejected-exit-one-with-recovery",
        };
        let stdout = match &self.stdout {
            StdoutExpectation::Exact(value) => {
                format!("exact-stdout-sha256={}", sha256_bytes(value.as_bytes()))
            }
            StdoutExpectation::Contains {
                fragments,
                verdict,
                marker,
                unsupported,
            } => format!(
                "stdout-fragments={fragments:?};verdict={verdict:?};marker={marker:?};unsupported={unsupported}"
            ),
            StdoutExpectation::Rejected => {
                "one-error-response-followed-by-recovery-marker".to_string()
            }
        };
        format!(
            "authenticated SMT-LIB 2.7 production {} sha256={}; class={class}; {stdout}; stderr-empty; guarded-process-complete",
            self.command, self.source_production_sha256
        )
    }
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
    let mut snapshot_path: Option<PathBuf> = None;
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
            "--source-snapshot" => {
                index += 1;
                snapshot_path = Some(PathBuf::from(
                    args.get(index).ok_or("--source-snapshot needs a path")?,
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
                return Err(format!("unknown standard-commands flag {flag:?}"));
            }
            value => {
                if manifest.replace(PathBuf::from(value)).is_some() {
                    return Err("standard-commands takes exactly one manifest path".to_string());
                }
            }
        }
        index += 1;
    }

    let manifest = manifest.ok_or("standard-commands needs a manifest path")?;
    let receipt_path = receipt_path.ok_or("standard-commands requires --receipt <path>")?;
    let snapshot_path = snapshot_path
        .as_deref()
        .ok_or("standard-commands requires --source-snapshot <path>")?;
    let loaded = load_contract(&manifest)?;
    let report = validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    if loaded.contract.campaign_id == UNASSIGNED_CAMPAIGN {
        return Err("assign a real --campaign id before producing evidence".to_string());
    }
    let contract_envelope = loaded
        .contract
        .resource_envelope
        .as_deref()
        .ok_or("standard-commands requires contract.resource_envelope")?;
    let parsed_envelope = parse_resource_envelope(contract_envelope)?;
    if parsed_envelope.jobs != 1 {
        return Err("standard-commands requires a one-job resource envelope".to_string());
    }
    if parsed_envelope.timeout != Duration::from_secs(timeout_secs) {
        return Err(format!(
            "--timeout does not match contract.resource_envelope: expected {:?}",
            parsed_envelope.timeout
        ));
    }
    let dimension = command_dimension(&loaded.contract)?;
    let source = reference_inventory::load_language_commands(
        &loaded.contract,
        dimension,
        &loaded.base,
        Some(snapshot_path),
    )?;
    let subject_ay = loaded
        .contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("standard-commands requires subject.ay_executable")?;
    let ay = ay_override.unwrap_or_else(|| artifact_path(&loaded.base, &subject_ay.path));
    let output_relative = future_relative_output(&loaded.base, &receipt_path)?;
    let execution = execute(
        &loaded.contract,
        &ay,
        &source.productions,
        Duration::from_secs(timeout_secs),
        Some(contract_envelope),
    )?;
    let current_exe = fs::canonicalize(
        std::env::current_exe().map_err(|error| format!("locating parity executable: {error}"))?,
    )
    .map_err(|error| format!("canonicalizing parity executable: {error}"))?;
    let validator_sha = sha256_file(&current_exe, "parity validator")?;
    let requirement_ids = dimension
        .requirements
        .iter()
        .map(|requirement| requirement.id.clone())
        .collect::<Vec<_>>();
    let receipt = ValidatorReceipt {
        schema: VALIDATOR_RECEIPT_SCHEMA.to_string(),
        campaign_id: loaded.contract.campaign_id.clone(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        dimension_id: dimension.id.clone(),
        requirement_ids,
        inventory_sha256: dimension.inventory.sha256.clone(),
        validator: ValidatorIdentity {
            id: VALIDATOR_ID.to_string(),
            kind: ValidatorKind::TranscriptConformance,
            path: current_exe.to_string_lossy().into_owned(),
            sha256: validator_sha,
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
        reference_inputs: vec![source.binding],
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
    let receipt_sha = sha256_bytes(&bytes);
    println!(
        "standard-commands={} receipt={} sha256={}",
        if receipt.result == ValidatorResult::Pass {
            "PASS"
        } else {
            "FAIL"
        },
        output_relative,
        receipt_sha
    );
    println!(
        "attach to all 32 language.commands rows: {{\"path\":\"{output_relative}\",\"sha256\":\"{receipt_sha}\"}}"
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
    if receipt.validator.kind != ValidatorKind::TranscriptConformance
        || context.dimension.id != DIMENSION_ID
        || !receipt.exhaustive
        || receipt.z3_binary_sha256.is_some()
        || receipt.z3_shared_library_sha256.is_some()
        || !receipt.auxiliary_tools.is_empty()
        || receipt.source_provenance.is_some()
    {
        return Err(format!(
            "{VALIDATOR_ID} has invalid kind, dimension, exhaustive flag, or foreign bindings"
        ));
    }
    let expected_requirement_ids = context
        .dimension
        .requirements
        .iter()
        .map(|requirement| requirement.id.clone())
        .collect::<Vec<_>>();
    if receipt.requirement_ids != expected_requirement_ids
        || expected_requirement_ids.len() != SMTLIB_COMMANDS.len()
    {
        return Err(format!(
            "{VALIDATOR_ID} does not cover the exact 32-row command inventory"
        ));
    }
    let input = match receipt.reference_inputs.as_slice() {
        [input]
            if input.id == "smtlib-language"
                && input.cohort == SourceCohort::SmtlibLanguage
                && input.repository
                    == context
                        .contract
                        .profile
                        .standard
                        .language_sources
                        .repository
                && input.revision
                    == context.contract.profile.standard.language_sources.revision
                && input.selection_sha256
                    == context.contract.profile.standard.language_sources.sha256 =>
        {
            input
        }
        _ => {
            return Err(format!(
                "{VALIDATOR_ID} requires exactly the pinned SMT-LIB language snapshot"
            ))
        }
    };

    if context.mode.replays_registered_validators() {
        let productions = reference_inventory::load_bound_language_commands(
            input,
            context.manifest_dir,
            &canonical_profile(),
        )?;
        validate_receipt_rows(receipt, &productions)?;
        let envelope = receipt
            .resource_envelope
            .as_deref()
            .ok_or("standard-commands receipt has no resource envelope")?;
        let parsed = parse_resource_envelope(envelope)?;
        if parsed.jobs != 1 {
            return Err(
                "standard-commands receipts require a one-job resource envelope".to_string(),
            );
        }
        let subject = context
            .contract
            .subject
            .ay_executable
            .as_ref()
            .ok_or("standard-commands replay requires subject.ay_executable")?;
        let ay = artifact_path(context.manifest_dir, &subject.path);
        let live = execute(
            context.contract,
            &ay,
            &productions,
            parsed.timeout,
            Some(envelope),
        )?;
        if receipt.result != live.result
            || receipt.cases != live.cases
            || receipt.case_results != live.case_results
        {
            return Err(format!(
                "{VALIDATOR_ID} receipt does not match a fresh authenticated executable replay"
            ));
        }
    }
    Ok(())
}

fn execute(
    contract: &Contract,
    ay_source: &Path,
    productions: &[LanguageCommandProduction],
    timeout: Duration,
    required_envelope: Option<&str>,
) -> Result<Execution, String> {
    if timeout.is_zero() || timeout > Duration::from_hours(1) {
        return Err("standard-commands timeout must be between 1ns and 3600 seconds".to_string());
    }
    let subject = contract
        .subject
        .ay_executable
        .as_ref()
        .ok_or("standard-commands requires subject.ay_executable")?;
    let staged = stage_authenticated_executable(ay_source, &subject.sha256, "AY executable")?;
    let catalog = case_catalog(productions)?;
    let repo_root = locate_repo_root()?;
    let resources = PlannedResources::plan(
        &repo_root,
        1,
        "ay-z3-parity smtlib-conformance standard-commands",
    )
    .map_err(|error| error.to_string())?;
    let resource_envelope = effective_execution_envelope(
        &resources.plan,
        ENFORCEMENT_RSS_WATCHDOG_V1,
        timeout.as_secs_f64(),
    )
    .map_err(|error| error.to_string())?;
    if let Some(expected) = required_envelope {
        if expected != resource_envelope {
            return Err(format!(
                "live standard-commands replay resource envelope drift: expected {expected:?}, got {resource_envelope:?}"
            ));
        }
    }

    let mut rows = Vec::with_capacity(catalog.len());
    for spec in &catalog {
        let output = resources
            .run_external_transcript(
                &staged.path,
                ["--quiet", "-in"],
                &spec.input,
                timeout,
                &format!("SMT-LIB standard command case {}", spec.id),
            )
            .map_err(|error| error.to_string())?;
        rows.push(row_from_output(spec, output));
    }
    let post_sha = sha256_file(&staged.path, "staged AY after standard-command probes")?;
    if post_sha != subject.sha256 {
        return Err("authenticated AY bytes changed during standard-command probes".to_string());
    }
    rows.sort_by(|left, right| left.id.cmp(&right.id));
    let expected_ids = catalog
        .iter()
        .map(|case| case.id.clone())
        .collect::<Vec<_>>();
    let actual_ids = rows.iter().map(|row| row.id.clone()).collect::<Vec<_>>();
    if actual_ids != expected_ids {
        return Err("internal standard-command case inventory drift".to_string());
    }
    let cases = case_counts_from_rows(&rows)?;
    Ok(Execution {
        ay_sha256: subject.sha256.clone(),
        resource_envelope,
        result: overall_validator_result(&rows),
        cases,
        case_results: rows,
    })
}

fn case_catalog(productions: &[LanguageCommandProduction]) -> Result<Vec<CaseSpec>, String> {
    let production_map = productions
        .iter()
        .map(|production| (production.name.as_str(), production))
        .collect::<BTreeMap<_, _>>();
    let expected_names = SMTLIB_COMMANDS.iter().copied().collect::<BTreeSet<_>>();
    let actual_names = production_map.keys().copied().collect::<BTreeSet<_>>();
    if actual_names != expected_names || production_map.len() != SMTLIB_COMMANDS.len() {
        return Err(
            "standard-command catalog is not bound to exactly 32 source productions".to_string(),
        );
    }
    for production in productions {
        if production.path != "Reference/syntax-macros.tex"
            || production.production.is_empty()
            || production.production_sha256 != sha256_bytes(production.production.as_bytes())
            || production.content_sha256.len() != 64
            || production.git_blob.len() != 40
        {
            return Err(format!(
                "authenticated command production metadata drift for {}",
                production.name
            ));
        }
    }

    let mut cases = Vec::new();

    // One normative, state-observing positive witness for every exact command
    // alternative.  Query commands establish the prerequisite result epoch;
    // mutating commands are followed by a use or state query that would fail
    // if the mutation had not occurred.
    push_exact(
        &mut cases,
        &production_map,
        "assert",
        "positive",
        "(assert true)\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "check-sat",
        "positive",
        "(assert true)\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "check-sat-assuming",
        "positive-empty",
        "(check-sat-assuming ())\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "check-sat-assuming",
        "positive-nonempty",
        "(declare-const a Bool)\n(check-sat-assuming (a (not a)))\n",
        &format!("unsat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "declare-const",
        "positive",
        "(declare-const x Bool)\n(assert x)\n(check-sat-assuming ((not x)))\n",
        &format!("unsat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "declare-datatype",
        "positive",
        "(declare-datatype D ((a) (b (sel Bool))))\n(declare-const d D)\n(assert (= d a))\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "declare-datatypes",
        "positive",
        "(declare-datatypes ((A 0) (B 0)) (((a)) ((b))))\n(declare-const x A)\n(declare-const y B)\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "declare-fun",
        "positive",
        "(declare-fun f (Bool) Bool)\n(assert (= (f true) (f true)))\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "declare-fun",
        "positive-nullary",
        "(declare-fun c () Bool)\n(assert (= c c))\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "declare-sort",
        "positive",
        "(declare-sort S 0)\n(declare-const x S)\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "declare-sort-parameter",
        "positive",
        "(declare-sort-parameter X)\n(declare-fun poly (X) X)\n",
        &format!("{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "define-const",
        "positive",
        "(define-const c Bool true)\n(assert c)\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "define-fun",
        "positive",
        "(define-fun f ((x Bool)) Bool x)\n(assert (f true))\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "define-fun",
        "positive-nullary",
        "(define-fun c () Bool true)\n(assert c)\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "define-fun-rec",
        "positive",
        "(define-fun-rec f ((x Bool)) Bool x)\n(assert (f true))\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "define-fun-rec",
        "positive-nullary",
        "(define-fun-rec c () Bool true)\n(assert c)\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "define-funs-rec",
        "positive",
        "(define-funs-rec ((f ((x Bool)) Bool) (g () Bool)) (x true))\n(assert (and (f true) g))\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "define-sort",
        "positive",
        "(define-sort Alias (X) X)\n(declare-const x (Alias Bool))\n(assert (= x x))\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "define-sort",
        "positive-nullary",
        "(define-sort Alias () Bool)\n(declare-const x Alias)\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "echo",
        "positive",
        "(echo \"standard-command-echo\")\n",
        &format!("standard-command-echo\n{COMMAND_MARKER}\n"),
    )?;
    push_exact_without_marker(
        &mut cases,
        &production_map,
        "exit",
        "positive",
        &format!("(exit)\n(echo \"{COMMAND_MARKER}\")\n"),
        "",
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "get-assertions",
        "positive",
        "(set-option :produce-assertions true)\n(assert true)\n(get-assertions)\n",
        &format!("(true)\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "get-assignment",
        "positive",
        "(set-option :produce-assignments true)\n(assert (! true :named a))\n(check-sat)\n(get-assignment)\n",
        &format!("sat\n((a true))\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "get-info",
        "positive",
        "(get-info :assertion-stack-levels)\n",
        &format!("(:assertion-stack-levels 0)\n{COMMAND_MARKER}\n"),
    )?;
    push_contains(
        &mut cases,
        &production_map,
        "get-model",
        "positive",
        "(set-option :produce-models true)\n(check-sat)\n(get-model)\n",
        &["\n(\n", "\n)\n"],
        Some("sat"),
        Some(COMMAND_MARKER),
        false,
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "get-option",
        "positive",
        "(get-option :print-success)\n",
        &format!("false\n{COMMAND_MARKER}\n"),
    )?;
    push_contains(
        &mut cases,
        &production_map,
        "get-proof",
        "positive",
        "(set-option :produce-proofs true)\n(assert false)\n(check-sat)\n(get-proof)\n",
        &[":rule"],
        Some("unsat"),
        Some(COMMAND_MARKER),
        false,
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "get-unsat-assumptions",
        "positive",
        "(set-option :produce-unsat-assumptions true)\n(declare-const a Bool)\n(check-sat-assuming (a (not a)))\n(get-unsat-assumptions)\n",
        &format!("unsat\n(a (not a))\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "get-unsat-core",
        "positive",
        "(set-option :produce-unsat-cores true)\n(assert (! false :named a))\n(check-sat)\n(get-unsat-core)\n",
        &format!("unsat\n(a)\n{COMMAND_MARKER}\n"),
    )?;
    push_contains(
        &mut cases,
        &production_map,
        "get-value",
        "positive",
        "(set-option :produce-models true)\n(declare-const x Bool)\n(check-sat)\n(get-value (x true))\n",
        &["((x ", "(true true))"],
        Some("sat"),
        Some(COMMAND_MARKER),
        false,
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "pop",
        "positive",
        "(push 2)\n(pop 1)\n(get-info :assertion-stack-levels)\n",
        &format!("(:assertion-stack-levels 1)\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "push",
        "positive",
        "(push 2)\n(get-info :assertion-stack-levels)\n",
        &format!("(:assertion-stack-levels 2)\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "reset",
        "positive",
        "(declare-const x Bool)\n(push 2)\n(assert false)\n(reset)\n(get-info :assertion-stack-levels)\n(check-sat)\n",
        &format!("(:assertion-stack-levels 0)\nsat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "reset-assertions",
        "positive",
        "(declare-const x Bool)\n(assert false)\n(push 2)\n(reset-assertions)\n(get-info :assertion-stack-levels)\n(assert x)\n(check-sat)\n",
        &format!("(:assertion-stack-levels 0)\nsat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "set-info",
        "positive",
        "(set-info :status sat)\n(get-info :status)\n",
        &format!("(:status sat)\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "set-info",
        "positive-valueless-attribute",
        "(set-info :custom)\n",
        &format!("{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "set-logic",
        "positive",
        "(set-logic QF_UF)\n(declare-const x Bool)\n(assert (= x x))\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "set-option",
        "positive",
        "(set-option :print-success false)\n(get-option :print-success)\n",
        &format!("false\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "set-option",
        "positive-valueless-unsupported",
        "(set-option :custom)\n",
        &format!("unsupported\n{COMMAND_MARKER}\n"),
    )?;

    // The exact Z3 5.1.0 overlay deliberately accepts these shapes in
    // addition to the normative production.  Keeping them in this closed
    // catalog prevents a standard negative witness from falsely condemning a
    // required replacement behavior.
    push_exact(
        &mut cases,
        &production_map,
        "check-sat",
        "overlay-temporary-assumptions",
        "(declare-const a Bool)\n(check-sat a (not a))\n",
        &format!("unsat\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "declare-sort",
        "overlay-default-arity-zero",
        "(declare-sort S)\n(declare-const x S)\n(check-sat)\n",
        &format!("sat\n{COMMAND_MARKER}\n"),
    )?;
    push_contains(
        &mut cases,
        &production_map,
        "get-model",
        "overlay-u32-indices",
        "(set-option :produce-models true)\n(check-sat)\n(get-model 0 4294967295)\n",
        &["\n(\n", "\n)\n"],
        Some("sat"),
        Some(COMMAND_MARKER),
        false,
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "pop",
        "overlay-default-one",
        "(push 1)\n(pop)\n(get-info :assertion-stack-levels)\n",
        &format!("(:assertion-stack-levels 0)\n{COMMAND_MARKER}\n"),
    )?;
    push_exact(
        &mut cases,
        &production_map,
        "push",
        "overlay-default-one",
        "(push)\n(get-info :assertion-stack-levels)\n",
        &format!("(:assertion-stack-levels 1)\n{COMMAND_MARKER}\n"),
    )?;

    add_rejected_boundaries(&mut cases, &production_map)?;

    cases.sort_by(|left, right| left.id.cmp(&right.id));
    if cases.len() != EXPECTED_CASE_COUNT || cases.windows(2).any(|pair| pair[0].id >= pair[1].id) {
        return Err(format!(
            "standard-command case catalog count/order drift: expected {EXPECTED_CASE_COUNT}, got {}",
            cases.len()
        ));
    }
    for command in SMTLIB_COMMANDS {
        let prefix = format!("command.{command}.");
        if !cases.iter().any(|case| {
            case.id == format!("{prefix}positive") || case.id == format!("{prefix}positive-empty")
        }) || !cases.iter().any(|case| case.id.starts_with(&prefix))
        {
            return Err(format!("closed catalog has no positive case for {command}"));
        }
    }
    Ok(cases)
}

fn add_rejected_boundaries(
    cases: &mut Vec<CaseSpec>,
    productions: &BTreeMap<&str, &LanguageCommandProduction>,
) -> Result<(), String> {
    const MISSING: [(&str, &str); 19] = [
        ("assert", "(assert)"),
        ("check-sat-assuming", "(check-sat-assuming)"),
        ("declare-const", "(declare-const x)"),
        ("declare-datatype", "(declare-datatype D)"),
        ("declare-datatypes", "(declare-datatypes ((D 0)))"),
        ("declare-fun", "(declare-fun f (Bool))"),
        ("declare-sort-parameter", "(declare-sort-parameter)"),
        ("define-const", "(define-const c Bool)"),
        ("define-fun", "(define-fun f () Bool)"),
        ("define-fun-rec", "(define-fun-rec f () Bool)"),
        ("define-funs-rec", "(define-funs-rec ((f () Bool)))"),
        ("define-sort", "(define-sort S () )"),
        ("echo", "(echo)"),
        ("get-info", "(get-info)"),
        ("get-option", "(get-option)"),
        ("get-value", "(get-value)"),
        ("set-info", "(set-info)"),
        ("set-logic", "(set-logic)"),
        ("set-option", "(set-option)"),
    ];
    for (command, target) in MISSING {
        push_rejected(cases, productions, command, "missing", target)?;
    }

    const TRAILING: [(&str, &str); 30] = [
        ("assert", "(assert true extra)"),
        ("check-sat-assuming", "(check-sat-assuming () extra)"),
        ("declare-const", "(declare-const x Bool extra)"),
        ("declare-datatype", "(declare-datatype D ((a)) extra)"),
        (
            "declare-datatypes",
            "(declare-datatypes ((D 0)) (((a))) extra)",
        ),
        ("declare-fun", "(declare-fun f () Bool extra)"),
        ("declare-sort", "(declare-sort S 0 extra)"),
        ("declare-sort-parameter", "(declare-sort-parameter X extra)"),
        ("define-const", "(define-const c Bool true extra)"),
        ("define-fun", "(define-fun f () Bool true extra)"),
        ("define-fun-rec", "(define-fun-rec f () Bool true extra)"),
        (
            "define-funs-rec",
            "(define-funs-rec ((f () Bool)) (true) extra)",
        ),
        ("define-sort", "(define-sort S () Bool extra)"),
        ("echo", "(echo \"x\" extra)"),
        ("exit", "(exit extra)"),
        ("get-assertions", "(get-assertions extra)"),
        ("get-assignment", "(get-assignment extra)"),
        ("get-info", "(get-info :name extra)"),
        ("get-option", "(get-option :print-success extra)"),
        ("get-proof", "(get-proof extra)"),
        ("get-unsat-assumptions", "(get-unsat-assumptions extra)"),
        ("get-unsat-core", "(get-unsat-core extra)"),
        ("get-value", "(get-value (true) extra)"),
        ("pop", "(pop 1 extra)"),
        ("push", "(push 1 extra)"),
        ("reset", "(reset extra)"),
        ("reset-assertions", "(reset-assertions extra)"),
        ("set-info", "(set-info :status sat extra)"),
        ("set-logic", "(set-logic QF_UF extra)"),
        ("set-option", "(set-option :print-success false extra)"),
    ];
    for (command, target) in TRAILING {
        push_rejected(cases, productions, command, "trailing", target)?;
    }

    const MALFORMED: [(&str, &str, &str); 24] = [
        ("assert", "malformed-term", "(assert ())"),
        (
            "check-sat",
            "malformed-overlay-assumption",
            "(check-sat ())",
        ),
        (
            "check-sat-assuming",
            "malformed-list",
            "(check-sat-assuming true)",
        ),
        (
            "declare-const",
            "malformed-symbol",
            "(declare-const \"x\" Bool)",
        ),
        (
            "declare-datatype",
            "malformed-empty-declaration",
            "(declare-datatype D ())",
        ),
        (
            "declare-datatypes",
            "malformed-empty-lists",
            "(declare-datatypes () ())",
        ),
        (
            "declare-fun",
            "malformed-sort-list",
            "(declare-fun f Bool Bool)",
        ),
        ("declare-sort", "malformed-numeral", "(declare-sort S nope)"),
        (
            "declare-sort-parameter",
            "malformed-symbol",
            "(declare-sort-parameter \"X\")",
        ),
        ("define-const", "malformed-sort", "(define-const c () true)"),
        (
            "define-fun",
            "malformed-parameter-list",
            "(define-fun f x Bool true)",
        ),
        (
            "define-fun-rec",
            "malformed-parameter-list",
            "(define-fun-rec f x Bool true)",
        ),
        (
            "define-funs-rec",
            "malformed-empty-lists",
            "(define-funs-rec () ())",
        ),
        (
            "define-sort",
            "malformed-parameter-list",
            "(define-sort S X Bool)",
        ),
        ("echo", "malformed-string", "(echo x)"),
        ("get-info", "malformed-keyword", "(get-info name)"),
        ("get-model", "malformed-index", "(get-model nope)"),
        (
            "get-model",
            "malformed-index-overflow",
            "(get-model 4294967296)",
        ),
        (
            "get-option",
            "malformed-keyword",
            "(get-option print-success)",
        ),
        ("get-value", "malformed-empty-list", "(get-value ())"),
        ("pop", "malformed-numeral", "(pop nope)"),
        ("push", "malformed-numeral", "(push nope)"),
        ("set-info", "malformed-attribute", "(set-info custom)"),
        ("set-logic", "malformed-symbol", "(set-logic \"QF_UF\")"),
    ];
    for (command, variant, target) in MALFORMED {
        push_rejected(cases, productions, command, variant, target)?;
    }
    push_rejected(
        cases,
        productions,
        "set-option",
        "malformed-option",
        "(set-option print-success false)",
    )?;
    Ok(())
}

fn push_exact(
    cases: &mut Vec<CaseSpec>,
    productions: &BTreeMap<&str, &LanguageCommandProduction>,
    command: &str,
    variant: &str,
    body: &str,
    expected_stdout: &str,
) -> Result<(), String> {
    let mut input = body.as_bytes().to_vec();
    if !input.ends_with(b"\n") {
        input.push(b'\n');
    }
    input.extend_from_slice(format!("(echo \"{COMMAND_MARKER}\")\n").as_bytes());
    push_case(
        cases,
        productions,
        command,
        variant,
        input,
        ExpectedStatus::ExitZero,
        StdoutExpectation::Exact(expected_stdout.to_string()),
    )
}

fn push_exact_without_marker(
    cases: &mut Vec<CaseSpec>,
    productions: &BTreeMap<&str, &LanguageCommandProduction>,
    command: &str,
    variant: &str,
    input: &str,
    expected_stdout: &str,
) -> Result<(), String> {
    push_case(
        cases,
        productions,
        command,
        variant,
        input.as_bytes().to_vec(),
        ExpectedStatus::ExitZero,
        StdoutExpectation::Exact(expected_stdout.to_string()),
    )
}

#[allow(clippy::too_many_arguments)]
fn push_contains(
    cases: &mut Vec<CaseSpec>,
    productions: &BTreeMap<&str, &LanguageCommandProduction>,
    command: &str,
    variant: &str,
    body: &str,
    fragments: &[&str],
    verdict: Option<&'static str>,
    marker: Option<&'static str>,
    unsupported: bool,
) -> Result<(), String> {
    let mut input = body.as_bytes().to_vec();
    if !input.ends_with(b"\n") {
        input.push(b'\n');
    }
    if let Some(marker) = marker {
        input.extend_from_slice(format!("(echo \"{marker}\")\n").as_bytes());
    }
    push_case(
        cases,
        productions,
        command,
        variant,
        input,
        ExpectedStatus::ExitZero,
        StdoutExpectation::Contains {
            fragments: fragments
                .iter()
                .map(|fragment| (*fragment).to_string())
                .collect(),
            verdict,
            marker,
            unsupported,
        },
    )
}

fn push_rejected(
    cases: &mut Vec<CaseSpec>,
    productions: &BTreeMap<&str, &LanguageCommandProduction>,
    command: &str,
    variant: &str,
    target: &str,
) -> Result<(), String> {
    let input = format!("{target}\n(echo \"{RECOVERY_MARKER}\")\n").into_bytes();
    push_case(
        cases,
        productions,
        command,
        variant,
        input,
        ExpectedStatus::RejectedExitOne,
        StdoutExpectation::Rejected,
    )
}

fn push_case(
    cases: &mut Vec<CaseSpec>,
    productions: &BTreeMap<&str, &LanguageCommandProduction>,
    command: &str,
    variant: &str,
    input: Vec<u8>,
    status: ExpectedStatus,
    stdout: StdoutExpectation,
) -> Result<(), String> {
    let production = productions
        .get(command)
        .ok_or_else(|| format!("case catalog names command absent from source: {command}"))?;
    cases.push(CaseSpec {
        id: format!("command.{command}.{variant}"),
        command: command.to_string(),
        source_production_sha256: production.production_sha256.clone(),
        input,
        status,
        stdout,
    });
    Ok(())
}

fn row_from_output(spec: &CaseSpec, output: GuardedTranscriptOutput) -> ValidatorCase {
    let exit_code = output.status.as_ref().and_then(|status| status.code());
    let stdout_utf8 = String::from_utf8(output.stdout);
    let stderr_utf8 = String::from_utf8(output.stderr);
    let streams_valid = stdout_utf8.is_ok() && stderr_utf8.is_ok();
    let stdout =
        stdout_utf8.unwrap_or_else(|error| String::from_utf8_lossy(error.as_bytes()).into_owned());
    let stderr =
        stderr_utf8.unwrap_or_else(|error| String::from_utf8_lossy(error.as_bytes()).into_owned());
    let process = ProcessObservation {
        stdin_complete: output.stdin_complete,
        timed_out: output.timed_out,
        memout: output.memout,
        stdout_truncated: output.stdout_truncated,
        stderr_truncated: output.stderr_truncated,
    };
    let (outcome, observed) =
        evaluate_observation(spec, exit_code, &process, &stdout, &stderr, streams_valid);
    ValidatorCase {
        id: spec.id.clone(),
        input_sha256: sha256_bytes(&spec.input),
        expected: spec.expected(),
        observed,
        stdout: Some(stdout),
        stderr: Some(stderr),
        exit_code,
        process: Some(process),
        outcome,
    }
}

fn evaluate_observation(
    spec: &CaseSpec,
    exit_code: Option<i32>,
    process: &ProcessObservation,
    stdout: &str,
    stderr: &str,
    streams_valid: bool,
) -> (ValidatorCaseOutcome, String) {
    let mut failures = Vec::new();
    let outcome = if process.memout {
        failures.push("memout");
        ValidatorCaseOutcome::Memout
    } else if process.timed_out {
        failures.push("timeout");
        ValidatorCaseOutcome::Timeout
    } else if !process.stdin_complete
        || process.stdout_truncated
        || process.stderr_truncated
        || !streams_valid
    {
        if !process.stdin_complete {
            failures.push("stdin-incomplete");
        }
        if process.stdout_truncated {
            failures.push("stdout-truncated");
        }
        if process.stderr_truncated {
            failures.push("stderr-truncated");
        }
        if !streams_valid {
            failures.push("non-utf8-stream");
        }
        ValidatorCaseOutcome::Fail
    } else if exit_code.is_none() {
        failures.push("no-exit-code");
        ValidatorCaseOutcome::Crash
    } else {
        validate_semantic_observation(spec, exit_code, stdout, stderr, &mut failures);
        if failures.is_empty() {
            ValidatorCaseOutcome::Pass
        } else {
            ValidatorCaseOutcome::Fail
        }
    };
    let detail = if failures.is_empty() {
        "match".to_string()
    } else {
        failures.join(",")
    };
    let observed = format!(
        "exit={exit_code:?};stdin-complete={};timeout={};memout={};stdout-truncated={};stderr-truncated={};streams-utf8={streams_valid};stdout-sha256={};stderr-sha256={};semantic={detail}",
        process.stdin_complete,
        process.timed_out,
        process.memout,
        process.stdout_truncated,
        process.stderr_truncated,
        sha256_bytes(stdout.as_bytes()),
        sha256_bytes(stderr.as_bytes()),
    );
    (outcome, observed)
}

fn validate_semantic_observation(
    spec: &CaseSpec,
    exit_code: Option<i32>,
    stdout: &str,
    stderr: &str,
    failures: &mut Vec<&'static str>,
) {
    let expected_exit = match spec.status {
        ExpectedStatus::ExitZero => 0,
        ExpectedStatus::RejectedExitOne => 1,
    };
    if exit_code != Some(expected_exit) {
        failures.push("exit-class");
    }
    if !stderr.is_empty() {
        failures.push("stderr-nonempty");
    }
    match &spec.stdout {
        StdoutExpectation::Exact(expected) => {
            if stdout != expected {
                failures.push("stdout-exact");
            }
        }
        StdoutExpectation::Contains {
            fragments,
            verdict,
            marker,
            unsupported,
        } => {
            if fragments.iter().any(|fragment| !stdout.contains(fragment)) {
                failures.push("stdout-fragment");
            }
            let lines = stdout.lines().collect::<Vec<_>>();
            if lines.iter().any(|line| line.starts_with("(error ")) {
                failures.push("unexpected-error");
            }
            let unsupported_count = lines.iter().filter(|line| **line == "unsupported").count();
            if unsupported_count != usize::from(*unsupported) {
                failures.push("unsupported-class");
            }
            for candidate in ["sat", "unsat", "unknown"] {
                let count = lines.iter().filter(|line| **line == candidate).count();
                let expected = usize::from(verdict.is_some_and(|value| value == candidate));
                if count != expected {
                    failures.push("verdict-class");
                    break;
                }
            }
            if let Some(marker) = marker {
                if lines.iter().filter(|line| **line == *marker).count() != 1 {
                    failures.push("completion-marker");
                }
            }
        }
        StdoutExpectation::Rejected => {
            let lines = stdout.lines().collect::<Vec<_>>();
            if lines.len() != 2
                || !lines[0].starts_with("(error \"")
                || !lines[0].ends_with(")")
                || lines[1] != RECOVERY_MARKER
            {
                failures.push("rejection-transcript");
            }
            if lines
                .iter()
                .any(|line| matches!(*line, "sat" | "unsat" | "unknown" | "unsupported"))
            {
                failures.push("rejection-result-class");
            }
        }
    }
}

fn validate_receipt_rows(
    receipt: &ValidatorReceipt,
    productions: &[LanguageCommandProduction],
) -> Result<(), String> {
    let catalog = case_catalog(productions)?;
    if receipt.case_results.len() != catalog.len() {
        return Err(format!(
            "{VALIDATOR_ID} has {} rows; exact catalog has {}",
            receipt.case_results.len(),
            catalog.len()
        ));
    }
    for (row, spec) in receipt.case_results.iter().zip(&catalog) {
        let (Some(process), Some(stdout), Some(stderr)) = (
            row.process.as_ref(),
            row.stdout.as_deref(),
            row.stderr.as_deref(),
        ) else {
            return Err(format!(
                "{VALIDATOR_ID} row {} is not bound to the closed source/case catalog",
                spec.id
            ));
        };
        if row.id != spec.id
            || row.input_sha256 != sha256_bytes(&spec.input)
            || row.expected != spec.expected()
        {
            return Err(format!(
                "{VALIDATOR_ID} row {} is not bound to the closed source/case catalog",
                spec.id
            ));
        }
        if row.outcome == ValidatorCaseOutcome::Pass {
            let (derived_outcome, derived_observed) =
                evaluate_observation(spec, row.exit_code, process, stdout, stderr, true);
            if derived_outcome != ValidatorCaseOutcome::Pass || row.observed != derived_observed {
                return Err(format!(
                    "{VALIDATOR_ID} row {} claims pass without its required raw transcript",
                    row.id
                ));
            }
        }
    }
    Ok(())
}

fn command_dimension(contract: &Contract) -> Result<&Dimension, String> {
    contract
        .dimensions
        .iter()
        .find(|dimension| dimension.id == DIMENSION_ID)
        .ok_or_else(|| "closed language.commands dimension is missing".to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn productions() -> Vec<LanguageCommandProduction> {
        SMTLIB_COMMANDS
            .iter()
            .map(|name| {
                let production = format!("( {name} production )");
                LanguageCommandProduction {
                    name: (*name).to_string(),
                    path: "Reference/syntax-macros.tex".to_string(),
                    git_blob: "1".repeat(40),
                    content_sha256: "2".repeat(64),
                    production_sha256: sha256_bytes(production.as_bytes()),
                    production,
                }
            })
            .collect()
    }

    #[test]
    fn catalog_is_sorted_closed_and_has_every_command_boundary() {
        let catalog = case_catalog(&productions()).expect("catalog");
        assert!(catalog.windows(2).all(|pair| pair[0].id < pair[1].id));
        assert_eq!(catalog.len(), EXPECTED_CASE_COUNT);
        for command in SMTLIB_COMMANDS {
            let prefix = format!("command.{command}.");
            assert!(catalog.iter().any(|case| case.id.starts_with(&prefix)));
        }
    }

    #[test]
    fn validator_owned_rejection_exit_one_is_a_logical_pass() {
        let catalog = case_catalog(&productions()).expect("catalog");
        let spec = catalog
            .iter()
            .find(|case| case.id == "command.assert.trailing")
            .expect("assert trailing case");
        let process = ProcessObservation {
            stdin_complete: true,
            timed_out: false,
            memout: false,
            stdout_truncated: false,
            stderr_truncated: false,
        };
        let stdout = format!("(error \"assert requires exactly one term\")\n{RECOVERY_MARKER}\n");
        let (outcome, _) = evaluate_observation(spec, Some(1), &process, &stdout, "", true);
        assert_eq!(outcome, ValidatorCaseOutcome::Pass);
        let (outcome, _) = evaluate_observation(spec, Some(0), &process, &stdout, "", true);
        assert_eq!(outcome, ValidatorCaseOutcome::Fail);

        let accepted = catalog
            .iter()
            .find(|case| case.id == "command.assert.positive")
            .expect("assert positive case");
        let accepted_stdout = format!("sat\n{COMMAND_MARKER}\n");
        let (outcome, _) =
            evaluate_observation(accepted, Some(1), &process, &accepted_stdout, "", true);
        assert_eq!(outcome, ValidatorCaseOutcome::Fail);
    }

    #[test]
    fn accepted_case_cannot_substitute_unknown_for_a_verdict() {
        let catalog = case_catalog(&productions()).expect("catalog");
        let spec = catalog
            .iter()
            .find(|case| case.id == "command.check-sat.positive")
            .expect("check-sat positive case");
        let process = ProcessObservation {
            stdin_complete: true,
            timed_out: false,
            memout: false,
            stdout_truncated: false,
            stderr_truncated: false,
        };
        let stdout = format!("unknown\n{COMMAND_MARKER}\n");
        let (outcome, _) = evaluate_observation(spec, Some(0), &process, &stdout, "", true);
        assert_eq!(outcome, ValidatorCaseOutcome::Fail);
    }
}
