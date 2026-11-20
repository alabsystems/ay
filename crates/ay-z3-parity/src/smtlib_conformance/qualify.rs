// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One execution owner for the complete registered conformance campaign.
//!
//! The orchestrator never infers success from a receipt's existence. Each
//! receipt is authenticated and replayed by the existing attachment/check
//! owners. Missing inputs and refused validators remain visible stages, and
//! execution continues so one failure cannot conceal another missing surface.

use super::*;

#[path = "qualify_status.rs"]
mod status;

pub(super) fn status_command(args: &[String]) -> Result<i32, String> {
    status::run(args)
}

const SUMMARY_SCHEMA: &str = "ay-z3-qualification-run/v2";
const STOCK_SUITE_TIMEOUT_SECONDS: u64 = 120;

#[derive(Debug)]
struct Options {
    directory: PathBuf,
    campaign: String,
    ay: Option<PathBuf>,
    library: Option<PathBuf>,
    language: Option<PathBuf>,
    registry: Option<PathBuf>,
    z3_source: Option<PathBuf>,
    corpus: Option<PathBuf>,
    fetch_corpus: bool,
    carcara: Option<PathBuf>,
    provision_root: Option<PathBuf>,
    timeout: u64,
    plan: bool,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Stage {
    id: String,
    command: Vec<String>,
    status: String,
    exit_code: Option<i32>,
    error: Option<String>,
    receipt: Option<String>,
    attached_manifest: Option<String>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Summary {
    schema: String,
    profile_id: String,
    campaign_id: String,
    manifest: PathBuf,
    evaluator_sha256: String,
    evidence: Vec<EvidenceRef>,
    stages: Vec<Stage>,
    passed_stages: usize,
    completed_registered_qualification: bool,
    universal_equivalence_proven: bool,
    full_product_ready: bool,
    missing_product_acceptance: Vec<String>,
    claim: String,
}

fn usage() -> &'static str {
    "\
ay-z3-parity smtlib-conformance qualify <new-output-directory> [options]

Run all registered inventory, semantic, corpus, proof and performance owners.
A failure or missing dependency is recorded and later stages still run. Nothing
is silently skipped or counted as passed. The output directory is create-new;
completed stage journals survive interruption. qualification.json is published
only after the final completion check. A completed run is bounded evidence for
the named profile/build/corpus/envelope, never proof for every possible input.

  --campaign ID             evidence campaign id (default: generated unique id)
  --ay-executable PATH      AY CLI under test (required except with --plan)
  --ay-shared-library PATH  AY C ABI library under test
  --language-snapshot PATH  authenticated SMT-LIB language source snapshot
  --registry-snapshot PATH  authenticated SMT-LIB theory/logic snapshot
  --z3-source-snapshot PATH authenticated Z3 source snapshot
  --corpus-manifest PATH    immutable complete official SMT-LIB corpus manifest
  --carcara PATH            exact independent proof checker
  --provision-root DIR      dependency cache (default: <output-directory>.inputs)
  --timeout SECONDS         per-query limit, 1..3600 (default: 10)
  --plan                    print every stage and required input without running

Pinned Z3 is selected by the active profile; arbitrary ambient Z3 is not used.
Runs are sequential, and each existing execution owner obtains shared machine
admission and enforces its own child time/memory/output limits. Transfer the
source, AY build and dependencies to the benchmark machine, then run this same
command there. No existing evidence directory is overwritten or trusted on
resume. Missing snapshots, unsupported validators or corpus gaps leave a
nonzero result. Full product and universal equivalence claims remain false.
"
}

fn parse(args: &[String]) -> Result<Options, String> {
    let mut options = Options {
        directory: PathBuf::new(),
        campaign: format!("qualification-{}", unix_time_ms()?),
        ay: None,
        library: None,
        language: None,
        registry: None,
        z3_source: None,
        corpus: None,
        fetch_corpus: true,
        carcara: None,
        provision_root: None,
        timeout: 10,
        plan: false,
    };
    let mut directory = None;
    let mut index = 0;
    while index < args.len() {
        let arg = args[index].as_str();
        if arg == "--plan" {
            options.plan = true;
        } else if arg.starts_with("--") {
            index += 1;
            let value = args
                .get(index)
                .ok_or_else(|| format!("{arg} needs a value"))?;
            match arg {
                "--campaign" => options.campaign = value.clone(),
                "--ay-executable" => options.ay = Some(PathBuf::from(value)),
                "--ay-shared-library" => options.library = Some(PathBuf::from(value)),
                "--language-snapshot" => options.language = Some(PathBuf::from(value)),
                "--registry-snapshot" => options.registry = Some(PathBuf::from(value)),
                "--z3-source-snapshot" => options.z3_source = Some(PathBuf::from(value)),
                "--corpus-manifest" => {
                    options.corpus = Some(PathBuf::from(value));
                    options.fetch_corpus = false;
                }
                "--carcara" => options.carcara = Some(PathBuf::from(value)),
                "--provision-root" => options.provision_root = Some(PathBuf::from(value)),
                "--timeout" => {
                    options.timeout = value.parse().map_err(|_| "--timeout must be an integer")?;
                    if !(1..=3600).contains(&options.timeout) {
                        return Err("--timeout must be between 1 and 3600".to_string());
                    }
                }
                _ => return Err(format!("unknown qualify option {arg}")),
            }
        } else if directory.replace(PathBuf::from(arg)).is_some() {
            return Err("qualify takes exactly one new output directory".to_string());
        }
        index += 1;
    }
    options.directory = directory.ok_or("qualify needs a new output directory")?;
    validate_id(&options.campaign, "campaign id")?;
    if options.campaign == UNASSIGNED_CAMPAIGN {
        return Err("qualify requires a real campaign id".to_string());
    }
    if options.ay.is_none() && !options.plan {
        return Err("qualify requires --ay-executable".to_string());
    }
    if options.provision_root.is_none() {
        let mut root = options.directory.as_os_str().to_os_string();
        root.push(".inputs");
        options.provision_root = Some(PathBuf::from(root));
    }
    if let Some(root) = &options.provision_root {
        options
            .language
            .get_or_insert_with(|| root.join("language-source.json"));
        options
            .registry
            .get_or_insert_with(|| root.join("registry-source.json"));
        options
            .z3_source
            .get_or_insert_with(|| root.join("z3-source.json"));
        options
            .corpus
            .get_or_insert_with(|| root.join("official-corpus.json"));
    }
    Ok(options)
}

fn path_text(path: &Path) -> Result<String, String> {
    path.to_str()
        .map(str::to_owned)
        .ok_or_else(|| format!("path is not UTF-8: {}", path.display()))
}

fn flag_path(args: &mut Vec<String>, flag: &str, value: Option<&Path>) -> Result<(), String> {
    if let Some(value) = value {
        args.extend([flag.to_string(), path_text(value)?]);
    }
    Ok(())
}

/// Every registered execution owner has a stage even when its current version
/// deliberately refuses the active profile. Such a refusal is an open gap.
fn validators(options: &Options) -> Vec<(&'static str, Option<&'static str>, Option<&Path>)> {
    vec![
        (
            "reference-inventory",
            Some("language.lexical-and-grammar"),
            options.language.as_deref(),
        ),
        (
            "reference-inventory",
            Some("language.commands"),
            options.language.as_deref(),
        ),
        (
            "reference-inventory",
            Some("registry.logics"),
            options.registry.as_deref(),
        ),
        (
            "reference-inventory",
            Some("registry.theories"),
            options.registry.as_deref(),
        ),
        (
            "reference-inventory",
            Some("semantics.typing-and-scope"),
            options.language.as_deref(),
        ),
        (
            "reference-inventory",
            Some("semantics.command-state-machine"),
            options.language.as_deref(),
        ),
        ("reference-inventory", Some("results.sat-models"), None),
        ("reference-inventory", Some("results.unsat-proofs"), None),
        ("reference-inventory", Some("results.unknown-policy"), None),
        ("reference-inventory", Some("gate.integrity"), None),
        ("z3-reference-inventory", None, options.z3_source.as_deref()),
        ("official-corpus-inventory", None, None),
        // Bind one campaign-wide resource envelope before dependent validators.
        ("target-identity", None, None),
        ("lexical-grammar", None, options.language.as_deref()),
        ("standard-commands", None, options.language.as_deref()),
        ("logic-registry", None, options.registry.as_deref()),
        ("theory-registry", None, options.registry.as_deref()),
        ("type-scope", None, options.language.as_deref()),
        ("command-state-machine", None, options.language.as_deref()),
        ("z3-abi-current", None, None),
        ("z3-source-inventory", None, options.z3_source.as_deref()),
        ("z3-behavioral", None, options.z3_source.as_deref()),
        ("gate-integrity", None, None),
        ("sat-models", None, None),
        ("unknown-policy", None, None),
        ("unsat-proofs", None, None),
        // Keep the expensive corpus last; its attachment owns fresh replay.
        ("official-corpus", None, None),
    ]
}

fn validator_command(
    options: &Options,
    owner: &str,
    dimension: Option<&str>,
    snapshot: Option<&Path>,
    manifest: &Path,
    receipt: &Path,
) -> Result<Vec<String>, String> {
    let mut args = vec![
        owner.to_string(),
        path_text(manifest)?,
        "--receipt".to_string(),
        path_text(receipt)?,
    ];
    if let Some(dimension) = dimension {
        args.extend(["--dimension".to_string(), dimension.to_string()]);
    }
    flag_path(&mut args, "--source-snapshot", snapshot)?;
    if owner == "z3-abi-current" {
        let root = options
            .provision_root
            .as_ref()
            .ok_or("current ABI source root missing")?;
        args.extend(["--source".to_string(), path_text(&root.join("z3-source"))?]);
    }
    if matches!(owner, "official-corpus" | "official-corpus-inventory") {
        flag_path(&mut args, "--corpus-manifest", options.corpus.as_deref())?;
    }
    if owner == "official-corpus" {
        args.extend([
            "--results".to_string(),
            path_text(&options.directory.join("official-corpus-results.json"))?,
        ]);
    }
    if !matches!(
        owner,
        "reference-inventory"
            | "z3-reference-inventory"
            | "official-corpus-inventory"
            | "gate-integrity"
    ) {
        args.extend(["--timeout".to_string(), options.timeout.to_string()]);
    }
    if matches!(owner, "unsat-proofs" | "official-corpus") {
        flag_path(&mut args, "--carcara", options.carcara.as_deref())?;
    }
    Ok(args)
}

fn stage(id: String, command: Vec<String>) -> Stage {
    Stage {
        id,
        command,
        status: "planned".to_string(),
        exit_code: None,
        error: None,
        receipt: None,
        attached_manifest: None,
    }
}

fn result_stage(stage: &mut Stage, result: Result<i32, String>) {
    match result {
        Ok(code) => {
            stage.exit_code = Some(code);
            stage.status = if code == 0 { "passed" } else { "failed" }.to_string();
        }
        Err(error) => {
            stage.status = "blocked".to_string();
            stage.error = Some(error);
        }
    }
}

fn journal(directory: &Path, index: usize, stage: &Stage) -> Result<(), String> {
    atomic_write_new(
        &directory.join(format!("stage-{index:03}.json")),
        &pretty_json(stage)?,
    )
}

fn copy_input(input: &mut Option<PathBuf>, directory: &Path, name: &str) -> Result<(), String> {
    let Some(source) = input else {
        return Ok(());
    };
    // Missing dependencies belong in stage results, not a silently shortened run.
    if !source.exists() {
        return Ok(());
    }
    let metadata = fs::symlink_metadata(&*source)
        .map_err(|error| format!("inspect {}: {error}", source.display()))?;
    if !metadata.is_file() || metadata.file_type().is_symlink() {
        return Err(format!(
            "input must be a regular non-symlink file: {}",
            source.display()
        ));
    }
    let destination = directory.join(name);
    if source.canonicalize().ok().as_ref() == Some(&destination) {
        *source = destination;
        return Ok(());
    }
    let mut output = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&destination)
        .map_err(|error| format!("create {}: {error}", destination.display()))?;
    let mut reader =
        fs::File::open(&*source).map_err(|error| format!("open {}: {error}", source.display()))?;
    std::io::copy(&mut reader, &mut output)
        .map_err(|error| format!("copy {}: {error}", source.display()))?;
    output
        .sync_all()
        .map_err(|error| format!("sync {}: {error}", destination.display()))?;
    *source = destination;
    Ok(())
}

/// Replay each newly produced receipt exactly once here. Earlier receipts are
/// still hash/shape checked after every addition, and the final Completion
/// replay re-executes every owner. Calling the public `attach` command instead
/// repeats all earlier experiments twice per stage, including corpus runs.
fn attach_new_receipt(manifest: &Path, receipt_path: &Path, output: &Path) -> Result<(), String> {
    let loaded = load_contract(manifest)?;
    validate_contract(&loaded.contract, &loaded.base, ValidationMode::Structural)?;
    require_manifest_output_directory(&loaded.base, output)?;
    let relative = future_relative_output(&loaded.base, receipt_path)?;
    let receipt_path = resolve_relative_evidence_path(&loaded.base, &relative)?;
    let reference = EvidenceRef {
        path: relative,
        sha256: sha256_file(&receipt_path, "qualification validator receipt")?,
    };
    let mut cache = ReceiptCache::default();
    let receipt = load_validator_receipt(&reference, &loaded.base, &mut cache)?.clone();
    let mut candidate = loaded.contract;
    attach_receipt_reference(&mut candidate, reference, &receipt)?;
    let dimension = candidate
        .dimensions
        .iter()
        .find(|row| row.id == receipt.dimension_id)
        .ok_or("receipt dimension is missing")?;
    let requirement_ids = dimension
        .requirements
        .iter()
        .map(|row| row.id.clone())
        .collect::<BTreeSet<_>>();
    let reference_extractor = receipt.validator.kind == ValidatorKind::ReferenceExtractor;
    let spec = DIMENSIONS
        .iter()
        .find(|row| row.id == dimension.id)
        .ok_or("receipt dimension has no registered specification")?;
    validate_validator_receipt(
        &receipt,
        EvidenceContext {
            contract: &candidate,
            manifest_dir: &loaded.base,
            dimension,
            expected_kind: if reference_extractor {
                ValidatorKind::ReferenceExtractor
            } else {
                spec.validator_kind
            },
            required_requirement_id: None,
            exact_requirement_ids: if reference_extractor {
                Some(&requirement_ids)
            } else {
                None
            },
            mode: ValidationMode::Audit,
        },
    )?;
    reconcile_attached_receipt_gaps(&mut candidate, &loaded.base, &receipt)?;
    validate_contract(&candidate, &loaded.base, ValidationMode::Structural)?;
    atomic_write_new(output, &pretty_json(&candidate)?)
}

fn tool_command(
    ay: &Path,
    operation: &str,
    directory: &Path,
    label: &str,
) -> Result<GuardedTranscriptOutput, String> {
    let root = locate_repo_root()?;
    let mut args = vec![
        "tool".to_string(),
        "--manifest".to_string(),
        path_text(&root.join("reference/tools.toml"))?,
        operation.to_string(),
        "carcara".to_string(),
    ];
    let resources = PlannedResources::plan(&root, 1, label).map_err(|error| error.to_string())?;
    let installing = operation == "install";
    let program = if installing {
        let mut admitted = vec!["--".to_string(), path_text(ay)?];
        admitted.append(&mut args);
        args = admitted;
        PathBuf::from("build-slot")
    } else {
        ay.to_path_buf()
    };
    let output = resources
        .run_external_transcript(
            &program,
            &args,
            b"",
            Duration::from_secs(if installing { 3600 } else { 30 }),
            label,
        )
        .map_err(|error| error.to_string())?;
    atomic_write_new(
        &directory.join(format!("{label}.json")),
        &pretty_json(&serde_json::json!({
            "program": program,
            "args": args,
            "exit_code": output.status.as_ref().and_then(|status| status.code()),
            "timed_out": output.timed_out,
            "memout": output.memout,
            "stdout_truncated": output.stdout_truncated,
            "stderr_truncated": output.stderr_truncated,
            "stdout": String::from_utf8_lossy(&output.stdout),
            "stderr": String::from_utf8_lossy(&output.stderr),
        }))?,
    )?;
    Ok(output)
}

fn successful_tool_output(output: &GuardedTranscriptOutput) -> bool {
    output
        .status
        .as_ref()
        .is_some_and(|status| status.success())
        && !output.timed_out
        && !output.memout
        && !output.stdout_truncated
        && !output.stderr_truncated
}

fn checker_path(output: &GuardedTranscriptOutput) -> Result<PathBuf, String> {
    if !successful_tool_output(output) {
        return Err("native Carcara locator failed; see retained transcript".to_string());
    }
    let path = std::str::from_utf8(&output.stdout)
        .map_err(|error| format!("Carcara locator UTF-8: {error}"))?
        .trim();
    let path = PathBuf::from(path);
    if !path.is_file() {
        return Err("native Carcara locator returned no executable file".to_string());
    }
    fs::canonicalize(&path).map_err(|error| format!("canonicalize Carcara: {error}"))
}

fn prepare_checker(ay: &Path, directory: &Path) -> Result<PathBuf, String> {
    if let Some(path) =
        std::env::var_os("CARCARA_PATH").or_else(|| std::env::var_os("AY_TOOL_CARCARA"))
    {
        let path = fs::canonicalize(PathBuf::from(path))
            .map_err(|error| format!("CARCARA_PATH: {error}"))?;
        return checker_cohort::authenticate(&path).map(|identity| identity.path);
    }
    let located = tool_command(ay, "which", directory, "carcara-locate")?;
    if let Ok(path) = checker_path(&located) {
        if let Ok(identity) = checker_cohort::authenticate(&path) {
            return Ok(identity.path);
        }
    }
    checker_cohort::provision(&directory.join("checker-inputs"))
}

fn current_abi_command(options: &Options) -> Result<Vec<String>, String> {
    let root = options
        .provision_root
        .as_ref()
        .ok_or("current ABI source root missing")?;
    let mut command = vec![
        "--source".to_string(),
        path_text(&root.join("z3-source"))?,
        "--out".to_string(),
        path_text(&options.directory.join("current-abi.json"))?,
    ];
    flag_path(&mut command, "--ay-library", options.library.as_deref())?;
    Ok(command)
}

fn current_behavior_command(options: &Options) -> Result<Vec<String>, String> {
    let mut command = vec![
        "--inventory".to_string(),
        path_text(&options.directory.join("current-release-inventory.json"))?,
        "--out".to_string(),
        path_text(&options.directory.join("current-behavior.json"))?,
    ];
    flag_path(&mut command, "--ay", options.ay.as_deref())?;
    Ok(command)
}

fn stock_python_command(options: &Options) -> Result<Vec<String>, String> {
    let mut command = vec![
        "--directory".to_string(),
        path_text(&options.directory.join("stock-python"))?,
        "--timeout".to_string(),
        options.timeout.max(STOCK_SUITE_TIMEOUT_SECONDS).to_string(),
    ];
    flag_path(&mut command, "--ay-library", options.library.as_deref())?;
    Ok(command)
}

fn stock_cpp_command(options: &Options) -> Result<Vec<String>, String> {
    let root = options
        .provision_root
        .as_ref()
        .ok_or("stock C++ source root missing")?;
    let mut command = vec![
        "--source".to_string(),
        path_text(&root.join("z3-source"))?,
        "--out".to_string(),
        path_text(&options.directory.join("stock-cpp.json"))?,
        "--timeout".to_string(),
        options.timeout.max(STOCK_SUITE_TIMEOUT_SECONDS).to_string(),
    ];
    flag_path(&mut command, "--ay-library", options.library.as_deref())?;
    Ok(command)
}

fn stock_c_command(options: &Options) -> Result<Vec<String>, String> {
    let root = options
        .provision_root
        .as_ref()
        .ok_or("stock C source root missing")?;
    let mut command = vec![
        "--source".to_string(),
        path_text(&root.join("z3-source"))?,
        "--out".to_string(),
        path_text(&options.directory.join("stock-c.json"))?,
        "--timeout".to_string(),
        options.timeout.max(STOCK_SUITE_TIMEOUT_SECONDS).to_string(),
    ];
    flag_path(&mut command, "--ay-library", options.library.as_deref())?;
    Ok(command)
}

fn completion_command(options: &Options, manifest: &Path) -> Result<Vec<String>, String> {
    Ok(vec![
        path_text(manifest)?,
        "--require-complete".to_string(),
        "--receipt".to_string(),
        path_text(&options.directory.join("completion-check.json"))?,
    ])
}

fn validate_summary_claims(summary: &Summary) -> Result<(), String> {
    if summary.schema != SUMMARY_SCHEMA
        || summary.profile_id != PROFILE_ID
        || summary.universal_equivalence_proven
        || summary.full_product_ready
        || summary.stages.is_empty()
        || summary.stages.len() > 100
    {
        return Err("unsupported qualification summary or unsupported product claim".to_string());
    }
    validate_id(&summary.campaign_id, "campaign id")?;
    let mut ids = BTreeSet::new();
    for stage in &summary.stages {
        if !ids.insert(stage.id.as_str()) {
            return Err(format!("duplicate qualification stage {}", stage.id));
        }
        match stage.status.as_str() {
            "passed" if stage.exit_code == Some(0) && stage.error.is_none() => {}
            "failed" if stage.exit_code.is_some_and(|code| code != 0) || stage.error.is_some() => {}
            "blocked" if stage.error.is_some() => {}
            _ => return Err(format!("inconsistent qualification stage {}", stage.id)),
        }
    }
    // No shortened campaign may be presented as the complete registered suite.
    let options = parse(&["unused".to_string(), "--plan".to_string()])?;
    for (owner, dimension, _) in validators(&options) {
        let id = dimension.map_or_else(|| owner.to_string(), |value| format!("{owner}:{value}"));
        if !ids.contains(id.as_str()) {
            return Err(format!("qualification omits required stage {id}"));
        }
    }
    for id in [
        "provision",
        "provision-checker",
        "current-release-inventory",
        "current-abi",
        "current-behavior",
        "stock-python",
        "stock-cpp",
        "stock-c",
        "performance-domination",
        "completion-check",
    ] {
        if !ids.contains(id) {
            return Err(format!("qualification omits required stage {id}"));
        }
    }
    let passed = summary
        .stages
        .iter()
        .filter(|stage| stage.status == "passed")
        .count();
    if summary.passed_stages != passed
        || summary.completed_registered_qualification != (passed == summary.stages.len())
    {
        return Err("qualification aggregate differs from its stage outcomes".to_string());
    }
    Ok(())
}

fn authenticate_summary_evidence(
    summary: &Summary,
    base: &Path,
) -> Result<BTreeSet<String>, String> {
    let mut paths = BTreeSet::new();
    for evidence in &summary.evidence {
        if !paths.insert(evidence.path.clone()) {
            return Err("duplicate qualification evidence path".to_string());
        }
        let path = resolve_relative_evidence_path(base, &evidence.path)?;
        if sha256_file(&path, "qualification evidence")? != evidence.sha256 {
            return Err(format!("qualification evidence changed: {}", evidence.path));
        }
    }
    let manifest_relative = future_relative_output(base, &summary.manifest)?;
    if !paths.contains(&manifest_relative) {
        return Err("qualification final manifest is not authenticated".to_string());
    }
    for (index, stage) in summary.stages.iter().enumerate() {
        let relative = format!("stage-{index:03}.json");
        if !paths.contains(&relative) {
            return Err(format!(
                "qualification lacks authenticated journal {relative}"
            ));
        }
        let bytes = read_bounded_bytes(&base.join(&relative), 1024 * 1024, "stage journal", true)?;
        let retained: Stage = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
        if retained != *stage {
            return Err(format!(
                "qualification stage differs from journal {relative}"
            ));
        }
    }
    Ok(paths)
}

/// Replay registered correctness evidence and recompute retained performance.
/// Hashes detect changed retained inputs; independent timing reproduction still
/// requires another measured run. Never execute arbitrary commands from JSON.
pub(super) fn check(args: &[String]) -> Result<i32, String> {
    if args.len() != 1 {
        return Err("usage: smtlib-conformance qualify-check QUALIFICATION.json".to_string());
    }
    let path = fs::canonicalize(&args[0]).map_err(|error| error.to_string())?;
    let base = path.parent().ok_or("qualification report has no parent")?;
    let bytes = read_bounded_bytes(&path, 4 * 1024 * 1024, "qualification summary", true)?;
    let summary: Summary = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    validate_summary_claims(&summary)?;
    if sha256_file(
        &std::env::current_exe().map_err(|error| error.to_string())?,
        "qualification evaluator",
    )? != summary.evaluator_sha256
    {
        return Err("qualification evaluator differs from the recorded executable".to_string());
    }
    let paths = authenticate_summary_evidence(&summary, base)?;
    let loaded = load_contract(&summary.manifest)?;
    if loaded.contract.campaign_id != summary.campaign_id {
        return Err("qualification campaign differs from final manifest".to_string());
    }
    let mut checks = vec![(
        "completion-check",
        check_command(&[
            path_text(&summary.manifest)?,
            "--require-complete".to_string(),
        ]),
    )];
    for (id, filename, check) in [
        (
            "current-release-inventory",
            "current-release-inventory.json",
            current_release::check as fn(&[String]) -> Result<i32, String>,
        ),
        ("current-abi", "current-abi.json", current_abi::check),
        (
            "current-behavior",
            "current-behavior.json",
            current_behavior::check,
        ),
        (
            "stock-python",
            "stock-python/stock-python.json",
            stock_python::check,
        ),
        ("stock-cpp", "stock-cpp.json", stock_cpp::check),
        ("stock-c", "stock-c.json", stock_c::check),
    ] {
        checks.push((
            id,
            if paths.contains(filename) {
                check(&[path_text(&base.join(filename))?])
            } else {
                Err(format!("missing authenticated report {filename}"))
            },
        ));
    }
    checks.push((
        "performance-domination",
        if paths.contains("performance/domination.json") {
            domination::check(&[
                path_text(&summary.manifest)?,
                "--corpus-manifest".to_string(),
                path_text(&base.join("official-corpus.json"))?,
                "--receipt".to_string(),
                path_text(&base.join("performance/domination.json"))?,
            ])
        } else {
            Err("missing authenticated performance report".to_string())
        },
    ));
    let mut complete = summary.completed_registered_qualification;
    let mut consistent = true;
    for (id, result) in checks {
        match result {
            Ok(0) => println!("qualification_replay {id}=passed"),
            Ok(code) => {
                complete = false;
                println!("qualification_replay {id}=incomplete exit={code}");
            }
            Err(error) => {
                complete = false;
                consistent = false;
                eprintln!("qualification_replay {id}=failed: {error}");
            }
        }
    }
    println!("retained_evidence_consistent={consistent} qualification_complete={complete} universal_equivalence_proven=false full_product_ready=false");
    Ok(i32::from(!complete))
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    if args
        .iter()
        .any(|arg| matches!(arg.as_str(), "--help" | "-h"))
    {
        print!("{}", usage());
        return Ok(0);
    }
    let mut options = parse(args)?;
    if !options.plan {
        for (path, label) in [
            (&mut options.ay, "AY executable"),
            (&mut options.library, "AY shared library"),
        ] {
            if let Some(value) = path {
                *value = fs::canonicalize(&*value).map_err(|error| {
                    format!("canonicalize {label} {}: {error}", value.display())
                })?;
            }
        }
    }
    let initial_manifest = options.directory.join("manifest-000.json");
    let mut plan = Vec::new();
    if let Some(root) = &options.provision_root {
        plan.push(stage(
            "provision".to_string(),
            vec!["--directory".to_string(), path_text(root)?],
        ));
        plan.push(stage(
            "current-release-inventory".to_string(),
            vec![
                "--source".to_string(),
                path_text(&root.join("z3-source"))?,
                "--out".to_string(),
                path_text(&options.directory.join("current-release-inventory.json"))?,
            ],
        ));
        plan.push(stage(
            "current-behavior".to_string(),
            current_behavior_command(&options)?,
        ));
        plan.push(stage(
            "stock-python".to_string(),
            stock_python_command(&options)?,
        ));
        plan.push(stage("stock-cpp".to_string(), stock_cpp_command(&options)?));
        plan.push(stage("stock-c".to_string(), stock_c_command(&options)?));
        if options.fetch_corpus {
            plan.push(stage(
                "provision-official-corpus".to_string(),
                vec![path_text(root)?],
            ));
        }
    }
    plan.push(stage(
        "provision-checker".to_string(),
        vec!["authenticated same-source Carcara cohort (provision if absent)".to_string()],
    ));
    for (index, (owner, dimension, snapshot)) in validators(&options).into_iter().enumerate() {
        let id = dimension.map_or_else(
            || owner.to_string(),
            |dimension| format!("{owner}:{dimension}"),
        );
        plan.push(stage(
            id,
            validator_command(
                &options,
                owner,
                dimension,
                snapshot,
                &initial_manifest,
                &options.directory.join(format!("receipt-{index:03}.json")),
            )?,
        ));
    }
    let performance_args = |manifest: &Path, options: &Options| -> Result<Vec<String>, String> {
        let mut command = vec![
            path_text(manifest)?,
            "--directory".to_string(),
            path_text(&options.directory.join("performance"))?,
            "--repetitions".to_string(),
            "3".to_string(),
            "--timeout".to_string(),
            options.timeout.to_string(),
        ];
        flag_path(&mut command, "--corpus-manifest", options.corpus.as_deref())?;
        Ok(command)
    };
    plan.push(stage(
        "current-abi".to_string(),
        current_abi_command(&options)?,
    ));
    plan.push(stage(
        "performance-domination".to_string(),
        performance_args(&initial_manifest, &options)?,
    ));
    // Receipt attachment determines the final manifest during execution. The
    // plan must still disclose the completion replay, including when earlier
    // validators will refuse the profile or leave gaps.
    plan.push(stage(
        "completion-check".to_string(),
        completion_command(
            &options,
            &options.directory.join("<final-attached-manifest>"),
        )?,
    ));
    if options.plan {
        println!("{}", serde_json::to_string_pretty(&serde_json::json!({
            "schema": SUMMARY_SCHEMA,
            "mode": "plan",
            "profile_id": PROFILE_ID,
            "campaign_id": options.campaign,
            "directory": options.directory,
            "provision_root": options.provision_root,
            "stages": plan,
            "universal_equivalence_proven": false,
            "full_product_ready": false,
            "claim": "Plan only; no checks have run. Execution covers every registered owner, including currently refused or missing surfaces. The final attached manifest is selected during execution."
        })).map_err(|error| error.to_string())?);
        return Ok(0);
    }
    fs::create_dir(&options.directory).map_err(|error| {
        format!(
            "create new qualification directory {}: {error}",
            options.directory.display()
        )
    })?;
    options.directory = fs::canonicalize(&options.directory)
        .map_err(|error| format!("canonicalize output directory: {error}"))?;
    let mut stages = Vec::new();
    if let Some(root) = &options.provision_root {
        let command = vec!["--directory".to_string(), path_text(root)?];
        let mut provision_stage = stage("provision".to_string(), command.clone());
        result_stage(&mut provision_stage, provision::run(&command));
        journal(&options.directory, stages.len(), &provision_stage)?;
        stages.push(provision_stage);
        let command = vec![
            "--source".to_string(),
            path_text(&root.join("z3-source"))?,
            "--out".to_string(),
            path_text(&options.directory.join("current-release-inventory.json"))?,
        ];
        let mut inventory_stage = stage("current-release-inventory".to_string(), command.clone());
        result_stage(&mut inventory_stage, current_release::run(&command));
        journal(&options.directory, stages.len(), &inventory_stage)?;
        stages.push(inventory_stage);
        let command = current_behavior_command(&options)?;
        let mut behavior_stage = stage("current-behavior".to_string(), command.clone());
        result_stage(&mut behavior_stage, current_behavior::run(&command));
        journal(&options.directory, stages.len(), &behavior_stage)?;
        stages.push(behavior_stage);
        let command = stock_python_command(&options)?;
        let mut python_stage = stage("stock-python".to_string(), command.clone());
        result_stage(&mut python_stage, stock_python::run(&command));
        journal(&options.directory, stages.len(), &python_stage)?;
        stages.push(python_stage);
        let command = stock_cpp_command(&options)?;
        let mut cpp_stage = stage("stock-cpp".to_string(), command.clone());
        result_stage(&mut cpp_stage, stock_cpp::run(&command));
        journal(&options.directory, stages.len(), &cpp_stage)?;
        stages.push(cpp_stage);
        let command = stock_c_command(&options)?;
        let mut c_stage = stage("stock-c".to_string(), command.clone());
        result_stage(&mut c_stage, stock_c::run(&command));
        journal(&options.directory, stages.len(), &c_stage)?;
        stages.push(c_stage);
        if options.fetch_corpus {
            let mut corpus_stage = stage(
                "provision-official-corpus".to_string(),
                vec![path_text(root)?],
            );
            let result = provision::prepare_corpus(root).map(|path| {
                options.corpus = Some(path);
                0
            });
            result_stage(&mut corpus_stage, result);
            journal(&options.directory, stages.len(), &corpus_stage)?;
            stages.push(corpus_stage);
        }
    }
    let mut checker_stage = stage(
        "provision-checker".to_string(),
        vec!["authenticated same-source Carcara cohort (provision if absent)".to_string()],
    );
    let checker_result = if let Some(path) = &options.carcara {
        fs::canonicalize(path)
            .map_err(|error| format!("explicit Carcara {}: {error}", path.display()))
            .and_then(|path| checker_cohort::authenticate(&path).map(|identity| identity.path))
    } else {
        prepare_checker(
            options.ay.as_deref().ok_or("missing AY executable")?,
            &options.directory,
        )
    };
    result_stage(
        &mut checker_stage,
        checker_result.map(|path| {
            options.carcara = Some(path);
            0
        }),
    );
    journal(&options.directory, stages.len(), &checker_stage)?;
    stages.push(checker_stage);
    for (input, name) in [
        (&mut options.language, "language-source.json"),
        (&mut options.registry, "registry-source.json"),
        (&mut options.z3_source, "z3-source.json"),
        (&mut options.corpus, "official-corpus.json"),
    ] {
        copy_input(input, &options.directory, name)?;
    }
    let mut init_args = vec![
        path_text(&options.directory.join("manifest-000.json"))?,
        "--campaign".to_string(),
        options.campaign.clone(),
    ];
    flag_path(&mut init_args, "--ay-executable", options.ay.as_deref())?;
    flag_path(
        &mut init_args,
        "--ay-shared-library",
        options.library.as_deref(),
    )?;
    init_command(&init_args)?;
    let mut manifest = options.directory.join("manifest-000.json");
    for (index, (owner, dimension, snapshot)) in validators(&options).into_iter().enumerate() {
        let receipt = options.directory.join(format!("receipt-{index:03}.json"));
        let command = validator_command(&options, owner, dimension, snapshot, &manifest, &receipt)?;
        let id = dimension.map_or_else(
            || owner.to_string(),
            |dimension| format!("{owner}:{dimension}"),
        );
        let mut outcome = stage(id, command.clone());
        eprintln!(
            "qualification stage {}/{}: {}",
            index + 1,
            plan.len(),
            outcome.id
        );
        result_stage(&mut outcome, run_validator_command(&command));
        if receipt.is_file() {
            outcome.receipt = Some(path_text(&receipt)?);
            let next = options
                .directory
                .join(format!("manifest-{:03}.json", index + 1));
            match attach_new_receipt(&manifest, &receipt, &next) {
                Ok(()) => {
                    outcome.attached_manifest = Some(path_text(&next)?);
                    manifest = next;
                }
                Err(error) => {
                    outcome.status = "failed".to_string();
                    outcome.error = Some(format!("receipt attachment refused: {error}"));
                }
            }
        } else if outcome.status == "passed" {
            outcome.status = "failed".to_string();
            outcome.error = Some(
                "validator returned success without publishing its required receipt".to_string(),
            );
        }
        journal(&options.directory, stages.len(), &outcome)?;
        stages.push(outcome);
    }
    let command = current_abi_command(&options)?;
    let mut abi = stage("current-abi".to_string(), command.clone());
    eprintln!("qualification stage: current-abi");
    result_stage(&mut abi, current_abi::run(&command));
    journal(&options.directory, stages.len(), &abi)?;
    stages.push(abi);
    let command = performance_args(&manifest, &options)?;
    let mut performance = stage("performance-domination".to_string(), command.clone());
    eprintln!("qualification stage: performance-domination");
    result_stage(&mut performance, domination::run(&command));
    journal(&options.directory, stages.len(), &performance)?;
    stages.push(performance);
    let command = completion_command(&options, &manifest)?;
    let mut completion = stage("completion-check".to_string(), command.clone());
    eprintln!("qualification stage: completion-check (replaying retained evidence)");
    result_stage(&mut completion, check_command(&command));
    journal(&options.directory, stages.len(), &completion)?;
    stages.push(completion);
    let passed = stages
        .iter()
        .filter(|stage| stage.status == "passed")
        .count();
    let total_stages = stages.len();
    let complete = passed == total_stages;
    let mut evidence_paths = vec![manifest.clone()];
    for index in 0..stages.len() {
        evidence_paths.push(options.directory.join(format!("stage-{index:03}.json")));
    }
    for name in [
        "completion-check.json",
        "current-release-inventory.json",
        "current-abi.json",
        "current-behavior.json",
        "stock-python/stock-python.json",
        "stock-cpp.json",
        "stock-c.json",
        "performance/domination.json",
    ] {
        let path = options.directory.join(name);
        if path.exists() {
            evidence_paths.push(path);
        }
    }
    let evidence = evidence_paths
        .into_iter()
        .map(|path| {
            Ok(EvidenceRef {
                path: future_relative_output(&options.directory, &path)?,
                sha256: sha256_file(&path, "qualification evidence")?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let mut missing_product_acceptance = vec![
        "Current-release exhaustive ABI and behavioral contracts".to_string(),
        "Exhaustive stock language binding, packaging, and downstream embedding contracts; selected Python consumers do not close this surface".to_string(),
        "Full CHC, optimization, and platform resource behavior".to_string(),
    ];
    if !stages
        .iter()
        .any(|stage| stage.id == "official-corpus" && stage.status == "passed")
    {
        missing_product_acceptance.push(
            "Accepted independent model/proof evidence for every decided corpus query".to_string(),
        );
    }
    let summary = Summary {
        schema: SUMMARY_SCHEMA.to_string(),
        profile_id: PROFILE_ID.to_string(),
        campaign_id: options.campaign,
        manifest,
        evaluator_sha256: sha256_file(
            &std::env::current_exe().map_err(|error| error.to_string())?,
            "qualification evaluator",
        )?,
        evidence,
        stages,
        passed_stages: passed,
        completed_registered_qualification: complete,
        universal_equivalence_proven: false,
        full_product_ready: false,
        missing_product_acceptance,
        claim: "Bounded registered qualification only. A finite campaign does not prove equivalence on all inputs or full product compatibility. Use qualify-check to replay retained evidence before quoting a result; reproducing timing also requires a fresh measured run.".to_string(),
    };
    atomic_write_new(
        &options.directory.join("qualification.json"),
        &pretty_json(&summary)?,
    )?;
    println!("qualification={} passed={passed}/{total_stages} universal_equivalence_proven=false full_product_ready=false", if complete { "passed" } else { "incomplete" });
    Ok(i32::from(!complete))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn summary_fixture(base: &Path) -> Summary {
        let options = parse(&strings(&["unused", "--plan"])).unwrap();
        let mut ids = validators(&options)
            .into_iter()
            .map(|(owner, dimension, _)| {
                dimension.map_or_else(|| owner.to_string(), |id| format!("{owner}:{id}"))
            })
            .collect::<Vec<_>>();
        ids.extend(
            [
                "provision",
                "provision-checker",
                "current-release-inventory",
                "current-abi",
                "current-behavior",
                "stock-python",
                "stock-cpp",
                "stock-c",
                "performance-domination",
                "completion-check",
            ]
            .into_iter()
            .map(str::to_string),
        );
        let stages = ids
            .into_iter()
            .map(|id| {
                let mut stage = stage(id, vec![]);
                result_stage(&mut stage, Ok(0));
                stage
            })
            .collect::<Vec<_>>();
        Summary {
            schema: SUMMARY_SCHEMA.to_string(),
            profile_id: PROFILE_ID.to_string(),
            campaign_id: "fixture".to_string(),
            manifest: base.join("manifest.json"),
            evaluator_sha256: sha256_bytes(b"fixture"),
            evidence: vec![],
            passed_stages: stages.len(),
            stages,
            completed_registered_qualification: true,
            universal_equivalence_proven: false,
            full_product_ready: false,
            missing_product_acceptance: vec!["fixture".to_string()],
            claim: "fixture".to_string(),
        }
    }

    #[test]
    fn summary_cannot_upgrade_failures_or_shorten_the_campaign() {
        let temporary = tempfile::tempdir().unwrap();
        let mut summary = summary_fixture(temporary.path());
        validate_summary_claims(&summary).unwrap();
        summary.stages[0].status = "failed".to_string();
        summary.stages[0].exit_code = Some(1);
        assert!(validate_summary_claims(&summary).is_err());
        summary.passed_stages -= 1;
        summary.completed_registered_qualification = false;
        validate_summary_claims(&summary).unwrap();
        summary.stages.remove(0);
        assert!(validate_summary_claims(&summary).is_err());
    }

    #[test]
    fn evidence_replay_rejects_mutation_before_running_any_solver() {
        let temporary = tempfile::tempdir().unwrap();
        let base = temporary.path();
        let mut summary = summary_fixture(base);
        summary.stages.clear();
        fs::write(&summary.manifest, b"original").unwrap();
        summary.evidence.push(EvidenceRef {
            path: "manifest.json".to_string(),
            sha256: sha256_bytes(b"original"),
        });
        authenticate_summary_evidence(&summary, base).unwrap();
        fs::write(&summary.manifest, b"changed").unwrap();
        assert!(authenticate_summary_evidence(&summary, base)
            .unwrap_err()
            .contains("changed"));
    }

    fn strings(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| (*value).to_string()).collect()
    }

    #[test]
    fn plan_does_not_require_binaries_but_execution_does() {
        assert!(parse(&strings(&["absent-output", "--plan"])).is_ok());
        assert!(parse(&strings(&["absent-output"])).is_err());
        assert!(parse(&strings(&["absent-output", "--plan", "--timeout", "0"])).is_err());
        assert!(parse(&strings(&[
            "absent-output",
            "--plan",
            "--campaign",
            "unassigned"
        ]))
        .is_err());
    }

    #[test]
    fn all_owners_remain_in_plan_when_dependencies_are_missing() {
        let options = parse(&strings(&["absent-output", "--plan"])).unwrap();
        let stages = validators(&options);
        for owner in [
            "z3-abi-current",
            "z3-behavioral",
            "z3-source-inventory",
            "official-corpus",
            "unsat-proofs",
            "sat-models",
            "target-identity",
        ] {
            assert!(
                stages.iter().any(|(candidate, _, _)| *candidate == owner),
                "{owner}"
            );
        }
        assert_eq!(
            stages
                .iter()
                .filter(|(owner, _, _)| *owner == "reference-inventory")
                .count(),
            10
        );
    }

    #[test]
    fn a_missing_dependency_or_failed_process_never_passes() {
        let mut missing = stage("missing".to_string(), vec![]);
        result_stage(&mut missing, Err("missing dependency".to_string()));
        assert_eq!(missing.status, "blocked");
        let mut failed = stage("failed".to_string(), vec![]);
        result_stage(&mut failed, Ok(1));
        assert_eq!(failed.status, "failed");
        assert_ne!(missing.status, "passed");
        assert_ne!(failed.status, "passed");
    }

    #[test]
    fn plan_creates_no_output_or_download_directory() {
        let temporary = tempfile::tempdir().unwrap();
        let output = temporary.path().join("qualification");
        let inputs = temporary.path().join("inputs");
        assert_eq!(
            run(&[
                output.to_str().unwrap().to_string(),
                "--provision-root".to_string(),
                inputs.to_str().unwrap().to_string(),
                "--plan".to_string(),
            ])
            .unwrap(),
            0
        );
        assert!(!output.exists());
        assert!(!inputs.exists());
    }

    #[test]
    fn invalid_receipt_is_not_attached_or_published() {
        let temporary = tempfile::tempdir().unwrap();
        let manifest = temporary.path().join("manifest.json");
        let receipt = temporary.path().join("receipt.json");
        let output = temporary.path().join("attached.json");
        init_command(&[
            manifest.to_str().unwrap().to_string(),
            "--campaign".to_string(),
            "invalid-receipt-control".to_string(),
        ])
        .unwrap();
        fs::write(&receipt, b"{\"result\":\"pass\"}").unwrap();
        assert!(attach_new_receipt(&manifest, &receipt, &output).is_err());
        assert!(!output.exists());
    }
}
