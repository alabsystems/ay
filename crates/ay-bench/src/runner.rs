// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eval runner: discovers evals from the YAML registry, executes benchmarks
//! natively in Rust, and applies competition-standard scoring.

use crate::error::{BenchError, Result, WithContext};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use crate::db::{ResultRow, ResultsStore, StorePath};
use crate::scoring::{self, Competition, ResultsFile};

// ===================================================================
// Eval registry
// ===================================================================

/// Minimal YAML eval spec — we only need a few fields.
#[derive(Debug)]
struct EvalSpec {
    id: Option<String>,
    competition: Option<String>,
    scoring: Option<String>,
    inputs: Option<EvalInputs>,
}

#[derive(Debug)]
struct EvalInputs {
    timeout_sec: Option<f64>,
    benchmarks_dir: Option<String>,
    /// Text file listing benchmark paths, one per line (e.g., SAT heldout set).
    list_file: Option<String>,
    /// Set manifest file relative to benchmarks_dir (e.g., CHC-COMP LIA.set).
    set_file: Option<String>,
    /// Number of runs per benchmark for statistical reliability.
    runs: Option<u32>,
    /// Subdirectories to scope discovery to (e.g., QF_BV, QF_LIA).
    suite_dirs: Option<Vec<String>>,
    /// Reference solver binary name for comparison (e.g., "z3").
    reference_solver: Option<String>,
    /// Competition-standard timeout declared by the eval registry.
    standard_timeout_sec: Option<f64>,
    /// CSV file with consensus results for HWMCC benchmarks.
    /// Format: benchmark,config,result,time_real,time_cpu,memory
    #[allow(dead_code)] // serde: deserialized from eval TOML but not yet loaded at runtime
    consensus_csv: Option<String>,
}

fn repo_root() -> PathBuf {
    repo_root_public()
}

/// Public wrapper: walk parents looking for the repo root (contains both
/// `Cargo.toml` and an `evals/` directory). Shared with the harvester module.
#[must_use]
pub fn repo_root_public() -> PathBuf {
    let mut dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    loop {
        if dir.join("Cargo.toml").exists() && dir.join("evals").exists() {
            return dir;
        }
        if !dir.pop() {
            return std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        }
    }
}

fn registry_dir() -> PathBuf {
    repo_root().join("evals").join("registry")
}

fn discover_evals() -> Result<Vec<(String, EvalSpec)>> {
    let dir = registry_dir();
    if !dir.exists() {
        return Err(BenchError::EvalRegistryMissing { path: dir });
    }

    let mut evals = Vec::new();
    for entry in std::fs::read_dir(&dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("yaml") {
            continue;
        }
        let text = std::fs::read_to_string(&path)
            .with_bench_context(|| format!("reading {}", path.display()))?;
        let spec = parse_eval_spec_minimal(&text, &path)?;
        let eval_id = spec.id.clone().unwrap_or_else(|| {
            path.file_stem()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string()
        });
        evals.push((eval_id, spec));
    }
    evals.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(evals)
}

/// Minimal YAML parser — extracts only the fields we need without a yaml dependency.
fn parse_eval_spec_minimal(text: &str, path: &Path) -> Result<EvalSpec> {
    let mut id = None;
    let mut competition = None;
    let mut scoring = None;
    let mut timeout_sec = None;
    let mut benchmarks_dir = None;
    let mut list_file = None;
    let mut set_file = None;
    let mut runs = None;
    let mut reference_solver = None;
    let mut standard_timeout_sec = None;
    let mut consensus_csv = None;
    let mut suite_dirs: Option<Vec<String>> = None;
    let mut in_suite_dirs = false;

    for line in text.lines() {
        let trimmed = line.trim();

        // Collect suite_dirs list items (YAML list under suite_dirs:)
        if in_suite_dirs {
            if let Some(item) = trimmed.strip_prefix("- ") {
                suite_dirs
                    .get_or_insert_with(Vec::new)
                    .push(strip_yaml_value(item));
                continue;
            } else {
                in_suite_dirs = false;
            }
        }

        if let Some(rest) = trimmed.strip_prefix("id:") {
            id = Some(strip_yaml_value(rest));
        } else if let Some(rest) = trimmed.strip_prefix("competition:") {
            competition = Some(strip_yaml_value(rest));
        } else if let Some(rest) = trimmed.strip_prefix("scoring:") {
            scoring = Some(strip_yaml_value(rest));
        } else if let Some(rest) = trimmed.strip_prefix("timeout_sec:") {
            timeout_sec = strip_yaml_value(rest).parse::<f64>().ok();
        } else if let Some(rest) = trimmed.strip_prefix("benchmarks_dir:") {
            benchmarks_dir = Some(strip_yaml_value(rest));
        } else if let Some(rest) = trimmed.strip_prefix("list_file:") {
            list_file = Some(strip_yaml_value(rest));
        } else if let Some(rest) = trimmed.strip_prefix("set_file:") {
            set_file = Some(strip_yaml_value(rest));
        } else if let Some(rest) = trimmed.strip_prefix("runs:") {
            runs = strip_yaml_value(rest).parse::<u32>().ok();
        } else if let Some(rest) = trimmed.strip_prefix("reference_solver:") {
            reference_solver = Some(strip_yaml_value(rest));
        } else if let Some(rest) = trimmed.strip_prefix("standard_timeout_sec:") {
            standard_timeout_sec = strip_yaml_value(rest).parse::<f64>().ok();
        } else if let Some(rest) = trimmed.strip_prefix("consensus_csv:") {
            consensus_csv = Some(strip_yaml_value(rest));
        } else if trimmed == "suite_dirs:" {
            in_suite_dirs = true;
            suite_dirs = Some(Vec::new());
        }
    }

    if id.is_none() {
        id = Some(
            path.file_stem()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string(),
        );
    }

    Ok(EvalSpec {
        id,
        competition,
        scoring,
        inputs: Some(EvalInputs {
            timeout_sec,
            benchmarks_dir,
            list_file,
            set_file,
            runs,
            suite_dirs,
            reference_solver,
            standard_timeout_sec,
            consensus_csv,
        }),
    })
}

/// Find a solver binary by name, checking PATH.
fn find_solver(name: &str) -> Option<PathBuf> {
    // Try the name directly (which checks)
    let output = std::process::Command::new("which")
        .arg(name)
        .output()
        .ok()?;
    if output.status.success() {
        let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
        if !path.is_empty() {
            return Some(PathBuf::from(path));
        }
    }
    None
}

/// Infer competition domain from eval ID prefix.
fn infer_domain(eval_id: &str) -> &str {
    if eval_id.starts_with("sat-") {
        "sat"
    } else if eval_id.starts_with("smt-") {
        "smt"
    } else if eval_id.starts_with("chccomp-") || eval_id.starts_with("chc-") {
        "chc"
    } else if eval_id.starts_with("hwmcc-") {
        "hwmcc"
    } else if eval_id.starts_with("sygus-") {
        "sygus"
    } else if eval_id.starts_with("maxsat-") {
        "maxsat"
    } else if eval_id.starts_with("qbf-") {
        "qbf"
    } else if eval_id.starts_with("allsat-") {
        "allsat"
    } else if eval_id.starts_with("counting-") {
        "counting"
    } else if eval_id.starts_with("omt-") {
        "omt"
    } else if eval_id.starts_with("security-") {
        if eval_id.contains("sygus") {
            "sygus"
        } else if eval_id.contains("omt") || eval_id.contains("maxsmt") {
            "omt"
        } else if eval_id.contains("qbf") || eval_id.contains("qdimacs") {
            "qbf"
        } else if eval_id.contains("allsat") || eval_id.contains("allsmt") {
            "allsat"
        } else if eval_id.contains("counting") || eval_id.contains("qif") {
            "counting"
        } else {
            // Default covers svcomp and anything else under `security-`.
            "smt"
        }
    } else {
        "unknown"
    }
}

fn infer_competition(eval_id: &str) -> Competition {
    match infer_domain(eval_id) {
        "sat" => Competition::SatComp,
        "smt" => Competition::SmtComp,
        "chc" => Competition::ChcComp,
        "hwmcc" => Competition::HwmccComp,
        "sygus" | "maxsat" | "qbf" | "allsat" | "counting" | "omt" => Competition::ChcComp,
        _ => Competition::SmtComp,
    }
}

fn infer_division(eval_id: &str) -> String {
    if let Some(suffix) = eval_id.strip_prefix("smt-smtcomp-") {
        suffix.to_uppercase().replace('-', "_")
    } else if let Some(suffix) = eval_id.strip_prefix("smt-local-") {
        if suffix == "suite" {
            "mixed".to_string()
        } else {
            suffix.to_uppercase().replace('-', "_")
        }
    } else {
        "unknown".to_string()
    }
}

fn infer_track(eval_id: &str) -> String {
    if eval_id.contains("extra-small-lia") {
        "LIA-extra-small".to_string()
    } else if eval_id.contains("lia-lin") {
        "LIA-Lin".to_string()
    } else if eval_id.contains("lia") {
        "LIA".to_string()
    } else {
        "unknown".to_string()
    }
}

fn infer_hwmcc_track(eval_id: &str) -> String {
    if eval_id.contains("wordlevel-bv") {
        "wordlevel-bv".to_string()
    } else if eval_id.contains("wordlevel-array") {
        "wordlevel-array".to_string()
    } else if eval_id.contains("bitlevel") {
        "bitlevel".to_string()
    } else {
        "unknown".to_string()
    }
}

fn inferred_scoring_label(eval_id: &str) -> &'static str {
    match infer_competition(eval_id) {
        Competition::SatComp => "sat-comp",
        Competition::SmtComp => "smt-comp",
        Competition::ChcComp => "chc-comp",
        Competition::HwmccComp => "hwmcc",
    }
}

fn scoring_label(eval_id: &str, spec: &EvalSpec) -> String {
    spec.scoring
        .as_deref()
        .or(spec.competition.as_deref())
        .map(ToOwned::to_owned)
        .unwrap_or_else(|| inferred_scoring_label(eval_id).to_string())
}

fn standard_timeout_sec(eval_id: &str, spec: &EvalSpec) -> f64 {
    spec.inputs
        .as_ref()
        .and_then(|i| i.standard_timeout_sec)
        .unwrap_or_else(|| infer_competition(eval_id).standard_timeout())
}

fn competition_timeout(eval_id: &str) -> f64 {
    infer_competition(eval_id).standard_timeout()
}

// ===================================================================
// Eval execution
// ===================================================================

pub struct RunArgs {
    pub eval_ids: Vec<String>,
    pub all: bool,
    pub domain: Option<String>,
    pub competition: bool,
    pub ay: PathBuf,
    pub timeout: Option<f64>,
    pub output: Option<PathBuf>,
    /// CLI override for number of runs per benchmark.
    /// `None` means use the YAML registry value, then fall back to 1.
    pub runs: Option<u32>,
    /// CLI override for reference solvers as (name, path) pairs, in the
    /// order given on the command line. Empty means fall back to the YAML
    /// spec's single `reference_solver` name.
    pub reference_solvers: Vec<(String, PathBuf)>,
    /// Comparison run class ("replay" | "laptop") stamped into results.json
    /// with a host fingerprint. Never verified here — `bench compare` owns
    /// verification; a class stamped this way is recorded as unverified.
    pub run_class: Option<String>,
    pub quiet: bool,
    /// When `true`, compute proof-complexity features for each input
    /// file and persist them alongside the solver result (#8774).
    pub with_features: bool,
    /// SAT-COMP track metadata recorded in results for profile-correct SAT runs.
    pub sat_track: Option<String>,
    /// SAT-COMP AI-class metadata recorded in results for profile-correct SAT runs.
    pub sat_ai_class: Option<String>,
    /// SAT solver variant passed to ay as `--sat-variant` for SAT runs.
    pub sat_variant: Option<String>,
}

/// Score an existing results file and print the result.
fn score_and_print(
    results_path: &Path,
    eval_id: &str,
    timeout: f64,
    competition_mode: bool,
) -> Result<serde_json::Value> {
    let data = ResultsFile::load(results_path)?;
    let items = data.items();
    let mode = if competition_mode {
        "competition"
    } else {
        "dev"
    };
    let comp = infer_competition(eval_id);

    match comp {
        Competition::SatComp => {
            let score = scoring::score_sat(items, timeout);
            println!("  [{mode}, T={timeout:.0}s] {score}");
            Ok(serde_json::to_value(&score)?)
        }
        Competition::SmtComp => {
            let div = infer_division(eval_id);
            let score = scoring::score_smt(items, timeout, &div);
            println!("  [{mode}, T={timeout:.0}s] {score}");
            Ok(serde_json::to_value(&score)?)
        }
        Competition::ChcComp => {
            let track = infer_track(eval_id);
            let score = scoring::score_chc(items, timeout, &track);
            println!("  [{mode}, T={timeout:.0}s] {score}");
            Ok(serde_json::to_value(&score)?)
        }
        Competition::HwmccComp => {
            let track = infer_hwmcc_track(eval_id);
            let score = scoring::score_hwmcc(items, timeout, &track);
            println!("  [{mode}, T={timeout:.0}s] {score}");
            Ok(serde_json::to_value(&score)?)
        }
    }
}

fn run_single_eval(eval_id: &str, spec: &EvalSpec, args: &RunArgs) -> Result<serde_json::Value> {
    let inputs = spec.inputs.as_ref();

    // Determine timeout
    let timeout = if let Some(t) = args.timeout {
        t
    } else if args.competition {
        competition_timeout(eval_id)
    } else {
        inputs.and_then(|i| i.timeout_sec).unwrap_or(60.0)
    };
    if !timeout.is_finite() || timeout <= 0.0 {
        return Err(BenchError::InvalidArgs {
            reason: format!("timeout for eval {eval_id} must be finite and positive"),
        });
    }

    let mode_label = if args.competition {
        "COMPETITION"
    } else {
        "dev"
    };

    if !args.quiet {
        eprintln!();
        eprintln!("{}", "=".repeat(60));
        eprintln!("[{eval_id}] mode={mode_label} timeout={timeout:.0}s");
        eprintln!("{}", "=".repeat(60));
    }

    let root = repo_root();
    let domain = infer_domain(eval_id);
    // Native eval execution is intentionally sequential, but the job-1 case
    // still needs an explicit envelope: the main ay binary otherwise claims
    // 85% of machine RAM.  Keep `_oom_guard.py` as the admission-policy source
    // and persist its exact plan in results.json.
    let resources = crate::resource::PlannedResources::plan(&root, 1, "ay bench run")?;
    if !args.quiet {
        eprintln!(
            "[resource] jobs={} --memory={} MiB NBCORE={} headroom={} MiB",
            resources.plan.jobs,
            resources.plan.memlimit_mb_per_child,
            resources.plan.nbcore_per_child,
            resources.plan.headroom_mb,
        );
    }

    // Determine benchmarks_dir from spec or infer from domain
    let benchmarks_dir = spec
        .inputs
        .as_ref()
        .and_then(|i| i.benchmarks_dir.as_deref())
        .map(|d| expand_tilde(d, &root))
        .unwrap_or_else(|| root.join("benchmarks").join(domain));

    let ay_path = if args.ay.is_relative() {
        root.join(&args.ay)
    } else {
        args.ay.clone()
    };

    // Build explicit file list from list_file, set_file, or suite_dirs
    let file_list = build_file_list(spec, &root, &benchmarks_dir)?
        .or_else(|| build_suite_dirs_list(spec, &benchmarks_dir, domain));

    let runs = effective_runs(args, inputs);

    // Resolve reference solvers: CLI --reference-solver values override the
    // YAML spec's single reference_solver name.
    let reference_solvers: Vec<(String, PathBuf)> = if args.reference_solvers.is_empty() {
        inputs
            .and_then(|i| i.reference_solver.as_deref())
            .and_then(find_solver)
            .map(|path| vec![(crate::native::reference_display_name(&path), path)])
            .unwrap_or_default()
    } else {
        args.reference_solvers.clone()
    };

    let environment = crate::environment::Environment::capture(&ay_path);
    let run_id = environment.timestamp.replace(':', "-");
    let output_dir = bench_results_root(&root).join(eval_id).join(&run_id);
    let artifact_output_dir = if domain == "sat" {
        Some(output_dir.join("artifacts"))
    } else {
        None
    };

    let mut solver_args = solver_args_for_eval(domain, args);
    if resources.plan.memlimit_mb_per_child > 0 {
        solver_args.push("--memory".to_string());
        solver_args.push(resources.plan.memlimit_mb_per_child.to_string());
    }
    let native_args = crate::native::NativeRunArgs {
        ay: &ay_path,
        benchmarks_dir: &benchmarks_dir,
        timeout_sec: timeout,
        domain,
        quiet: args.quiet,
        file_list,
        runs,
        reference_solvers,
        run_class: args.run_class.clone(),
        solver_args,
        sat_track: args.sat_track.clone(),
        sat_ai_class: args.sat_ai_class.clone(),
        sat_variant: args.sat_variant.clone(),
        environment: Some(environment),
        artifact_output_dir,
        resources: Some(resources.clone()),
    };

    let results = crate::native::run_native(&native_args)?;

    // Print comparison summaries if reference solvers were used
    if let Some(references) = results.references.as_deref() {
        if !args.quiet {
            for summary in references {
                eprintln!();
                eprintln!(
                    "[{eval_id}] comparison vs {} {} ({})",
                    summary.reference_solver,
                    summary.reference_solver_build_stamp,
                    summary.reference_solver_path,
                );
                eprintln!(
                    "  agree={} disagree={} ay_only={} ref_only={}",
                    summary.agree, summary.disagree, summary.ay_only, summary.ref_only,
                );
                if summary.both_solved > 0 {
                    eprintln!(
                        "  both_solved={}: ay_faster={} ref_faster={} ay_total={:.1}s ref_total={:.1}s",
                        summary.both_solved,
                        summary.ay_faster,
                        summary.ref_faster,
                        summary.ay_total_time,
                        summary.ref_total_time,
                    );
                }
            }
        }
    }

    // Write results.json in the standard location
    std::fs::create_dir_all(&output_dir)?;

    let results_path = output_dir.join("results.json");
    let json = serde_json::to_string_pretty(&results)?;
    std::fs::write(&results_path, &json)?;

    if !args.quiet {
        eprintln!("[{eval_id}] results written to {}", results_path.display());
    }

    // Persist per-benchmark rows into the SQLite store (keyed by current git HEAD).
    // Failures here are logged but do not abort the run — the JSON results
    // file remains the primary artifact and we never want a missing git or a
    // read-only filesystem to break `ay-bench run`.
    if let Err(e) = persist_results(&root, eval_id, &results, args.with_features) {
        eprintln!("[{eval_id}] warning: failed to persist results to store: {e:#}");
    }

    // Score the results
    score_and_print(&results_path, eval_id, timeout, args.competition)
}

fn bench_results_root(repo_root: &Path) -> PathBuf {
    resolve_results_root(
        repo_root,
        std::env::var_os("AY_BENCH_RESULTS_ROOT").map(PathBuf::from),
    )
}

fn resolve_results_root(repo_root: &Path, configured: Option<PathBuf>) -> PathBuf {
    let Some(path) = configured.filter(|path| !path.as_os_str().is_empty()) else {
        return repo_root.join("evals").join("results");
    };
    if path.is_absolute() {
        path
    } else {
        repo_root.join(path)
    }
}

fn effective_runs(args: &RunArgs, inputs: Option<&EvalInputs>) -> u32 {
    args.runs
        .or_else(|| inputs.and_then(|i| i.runs))
        .unwrap_or(1)
        .max(1)
}

fn solver_args_for_eval(domain: &str, args: &RunArgs) -> Vec<String> {
    let mut solver_args = Vec::new();
    if domain == "sat" {
        if let Some(variant) = args.sat_variant.as_deref() {
            solver_args.push("--sat-variant".to_string());
            solver_args.push(variant.to_string());
        }
    }
    solver_args
}

/// Persist a completed eval's per-benchmark rows into the sqlite store at
/// `.ay-bench/results.sqlite` under `repo_root`, keyed by the current git HEAD.
///
/// Returns without persisting (Ok) if the commit hash cannot be resolved — we
/// cannot key rows without a stable commit identifier.
fn persist_results(
    repo_root: &Path,
    eval_id: &str,
    results: &crate::native::NativeResults,
    with_features: bool,
) -> Result<()> {
    let commit_hash = match crate::db::resolve_head(repo_root) {
        Some(h) => h,
        None => {
            eprintln!(
                "[{eval_id}] warning: could not resolve git HEAD; skipping persistent store write"
            );
            return Ok(());
        }
    };

    let store_path = StorePath::default_at(repo_root);
    let mut store = ResultsStore::open(store_path.as_path())?;
    let rows = build_rows(&commit_hash, eval_id, results, with_features);
    store.upsert_rows(&rows)?;
    Ok(())
}

/// Build `ResultRow`s from a completed `NativeResults`. Each row encodes the
/// per-benchmark verdict plus a three-valued `verifier_ok` flag:
///
/// * `1` if the comparison block declares the result "agree" with the
///   reference solver, OR if the parsed verdict matches the `expected` label
///   embedded in the path.
/// * `0` if the comparison says "disagree" (i.e. wrong answer).
/// * `-1` when there was no comparison and no expected label — verdict is
///   taken at face value.
fn build_rows(
    commit_hash: &str,
    eval_id: &str,
    results: &crate::native::NativeResults,
    with_features: bool,
) -> Vec<ResultRow> {
    // Index comparison items (if present) by file path so we can look up
    // agreement quickly.
    let comp_index: BTreeMap<&str, &'static str> = results
        .comparisons
        .as_deref()
        .unwrap_or(&[])
        .iter()
        .map(|c| (c.file.as_str(), c.agreement))
        .collect();

    let timestamp = results.environment.timestamp.clone();
    let resource_envelope = results
        .settings
        .resource_plan
        .as_ref()
        .map(crate::resource::ResourcePlan::execution_envelope);

    results
        .items
        .iter()
        .map(|item| {
            let verifier_ok = classify_verifier(item, &comp_index);
            let runtime_ms = (item.time_sec.max(0.0) * 1000.0) as i64;
            let extracted = if with_features {
                match crate::features::extract_from_file(Path::new(&item.benchmark_path)) {
                    Ok(ef) => Some(ef),
                    Err(e) => {
                        eprintln!(
                            "[{eval_id}] warning: feature extraction failed for {}: {e:#}",
                            item.benchmark_path
                        );
                        None
                    }
                }
            } else {
                None
            };
            let (family, fmax, fmean, xor, card, modu, fms) = match extracted {
                Some(ef) => (
                    ef.family,
                    Some(i64::from(ef.features.clause_width_max)),
                    Some(ef.features.clause_width_mean),
                    Some(ef.features.xor_density),
                    Some(ef.features.cardinality_density),
                    Some(ef.features.modularity),
                    Some(ef.extract_ms),
                ),
                None => (None, None, None, None, None, None, None),
            };
            let artifacts = item.artifacts.as_ref();
            let artifact_output_dir = artifacts.map(|artifacts| artifacts.output_dir.clone());
            let proof_path = artifacts.and_then(|artifacts| artifacts.proof_path.clone());
            let proof_format = artifacts.and_then(|artifacts| artifacts.proof_format.clone());
            let proof_exists = artifacts.and_then(|artifacts| artifacts.proof_exists);
            let proof_bytes = artifacts
                .and_then(|artifacts| artifacts.proof_bytes)
                .and_then(|bytes| i64::try_from(bytes).ok());
            let proof_hash = artifacts.and_then(|artifacts| artifacts.proof_hash.clone());
            ResultRow {
                commit_hash: commit_hash.to_string(),
                eval_name: eval_id.to_string(),
                benchmark_path: item.benchmark_path.clone(),
                result: item.result.clone(),
                runtime_ms,
                // NativeResultItem does not currently capture per-benchmark
                // peak RSS; leave the column as zero until we add that.
                memory_mb: 0,
                verifier_ok,
                timestamp: timestamp.clone(),
                resource_envelope: resource_envelope.clone(),
                benchmark_content_hash: item.benchmark_content_hash.clone(),
                artifact_output_dir,
                proof_path,
                proof_format,
                proof_exists,
                proof_bytes,
                proof_hash,
                family,
                clause_width_max: fmax,
                clause_width_mean: fmean,
                xor_density: xor,
                cardinality_density: card,
                modularity: modu,
                feature_extract_ms: fms,
            }
        })
        .collect()
}

/// Classify a `NativeResultItem` against the comparison index and expected
/// label to produce `verifier_ok` (-1 / 0 / 1).
fn classify_verifier(
    item: &crate::native::NativeResultItem,
    comp_index: &BTreeMap<&str, &'static str>,
) -> i32 {
    if let Some(agreement) = comp_index.get(item.file.as_str()) {
        return match *agreement {
            "agree" => 1,
            "disagree" => 0,
            // ay_only / ref_only mean one side timed out — not a wrong answer,
            // but also not verified. Use -1.
            _ => -1,
        };
    }
    // No comparison available. Fall back to `expected` label (when present).
    if let Some(expected) = item.expected.as_deref() {
        let got = item.result.to_ascii_lowercase();
        let exp = expected.to_ascii_lowercase();
        if got == exp {
            return 1;
        }
        // Only call it wrong if the solver claimed a verdict.
        if got == "sat" || got == "unsat" {
            return 0;
        }
    }
    -1
}

pub fn cmd_run(args: RunArgs) -> Result<()> {
    let evals = discover_evals()?;
    if evals.is_empty() {
        return Err(BenchError::msg("no eval specs found in evals/registry/"));
    }

    // Determine which evals to run
    let selected = select_evals_for_run(evals, &args)?;

    if selected.is_empty() {
        return Err(BenchError::msg("no matching evals found"));
    }

    // Check AY binary
    let ay_path = if args.ay.is_relative() {
        repo_root().join(&args.ay)
    } else {
        args.ay.clone()
    };
    if !ay_path.exists() {
        return Err(BenchError::msg(format!(
            "AY binary not found: {}\nBuild first: cargo build --release -p ay",
            ay_path.display()
        )));
    }

    let mut all_scores = Vec::new();

    for (eval_id, spec) in &selected {
        match run_single_eval(eval_id, spec, &args) {
            Ok(score) => all_scores.push(serde_json::json!({
                "eval_id": eval_id,
                "competition": infer_competition(eval_id).name(),
                "score": score,
            })),
            Err(e) => {
                eprintln!("[{eval_id}] error: {e:#}");
                all_scores.push(serde_json::json!({
                    "eval_id": eval_id,
                    "error": format!("{e:#}"),
                }));
            }
        }
    }

    // Print scorecard
    let mode = if args.competition {
        "competition-standard timeouts"
    } else {
        "dev timeouts"
    };
    println!();
    println!("{}", "=".repeat(60));
    println!("SCORECARD ({mode})");
    println!("{}", "=".repeat(60));
    println!("Scores printed above per eval.");

    // Write combined output
    if let Some(ref output_path) = args.output {
        let env = crate::environment::Environment::capture(&ay_path);
        let scorecard = serde_json::json!({
            "environment": env,
            "mode": if args.competition { "competition" } else { "dev" },
            "results": all_scores,
        });
        if let Some(parent) = output_path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(output_path, serde_json::to_string_pretty(&scorecard)?)?;
        println!("Scorecard written to: {}", output_path.display());
    }

    Ok(())
}

fn select_evals_for_run(
    evals: Vec<(String, EvalSpec)>,
    args: &RunArgs,
) -> Result<Vec<(String, EvalSpec)>> {
    let selected: Vec<(String, EvalSpec)> = if args.all {
        evals
    } else if let Some(ref domain) = args.domain {
        evals
            .into_iter()
            .filter(|(id, _)| infer_domain(id) == domain.as_str())
            .collect()
    } else if !args.eval_ids.is_empty() {
        let available: Vec<String> = evals.iter().map(|(id, _)| id.clone()).collect();
        let unknown: Vec<String> = args
            .eval_ids
            .iter()
            .filter(|id| !available.contains(id))
            .cloned()
            .collect();
        if !unknown.is_empty() {
            return Err(BenchError::EvalNotFound {
                ids: format!(
                    "{}\navailable: {}",
                    unknown.join(", "),
                    available.join(", ")
                ),
            });
        }
        evals
            .into_iter()
            .filter(|(id, _)| args.eval_ids.contains(id))
            .collect()
    } else {
        return Err(BenchError::InvalidArgs {
            reason: "specify eval IDs, --all, or --domain {sat,smt,chc}".to_string(),
        });
    };

    Ok(selected)
}

// ===================================================================
// diff command
// ===================================================================

/// Output format for `ay-bench diff`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiffFormat {
    Table,
    Json,
    /// GitHub-flavored-markdown; suitable for PR comments.
    Markdown,
}

/// Arguments for `ay-bench diff`.
pub struct DiffArgs {
    pub base: String,
    pub head: String,
    pub eval: Option<String>,
    pub format: DiffFormat,
    /// Slowdown threshold in percent (default 20.0).
    pub slowdown_threshold_pct: f64,
}

impl Default for DiffArgs {
    fn default() -> Self {
        Self {
            base: "HEAD~10".to_string(),
            head: "HEAD".to_string(),
            eval: None,
            format: DiffFormat::Table,
            slowdown_threshold_pct: 20.0,
        }
    }
}

/// Run the `ay-bench diff` subcommand. Returns `true` iff regressions or
/// non-comparable resource envelopes were detected (the CLI layer maps that
/// to a non-zero exit code rather than silently accepting an invalid diff).
pub fn cmd_diff(args: DiffArgs) -> Result<bool> {
    let root = repo_root();

    // Resolve base / head to commit hashes. Fall back to the raw input so
    // users can pass explicit SHAs for commits that may not be present in
    // the worktree (e.g. imported from another machine).
    let base_hash = crate::db::resolve_rev(&root, &args.base).unwrap_or_else(|| args.base.clone());
    let head_hash = crate::db::resolve_rev(&root, &args.head).unwrap_or_else(|| args.head.clone());

    let store_path = StorePath::default_at(&root);
    if !store_path.as_path().exists() {
        return Err(BenchError::msg(format!(
            "no persistent results store at {} — run `ay-bench run <eval>` first",
            store_path.as_path().display()
        )));
    }
    let store = ResultsStore::open(store_path.as_path())?;

    let opts = crate::diff::DiffOptions {
        slowdown_threshold_pct: args.slowdown_threshold_pct,
    };
    let report =
        crate::diff::diff_from_store(&store, &base_hash, &head_hash, args.eval.as_deref(), opts)?;

    match args.format {
        DiffFormat::Table => {
            print!("{}", crate::diff::render_table(&report));
        }
        DiffFormat::Json => {
            println!("{}", crate::diff::render_json(&report)?);
        }
        DiffFormat::Markdown => {
            print!("{}", crate::diff::render_markdown(&report));
        }
    }

    Ok(report.has_regressions() || report.has_non_comparable())
}

// ===================================================================
// list command
// ===================================================================

pub fn cmd_list() -> Result<()> {
    let evals = discover_evals()?;
    if evals.is_empty() {
        println!("No evals found in evals/registry/");
        return Ok(());
    }

    println!(
        "{:<40} {:<8} {:<12} {:<10} {:<12}",
        "Eval ID", "Domain", "Scoring", "Timeout", "Std Timeout"
    );
    println!("{}", "-".repeat(90));

    for row in eval_list_rows(&evals) {
        println!(
            "{:<40} {:<8} {:<12} {:<10} {:<12}",
            row.eval_id, row.domain, row.scoring, row.dev_timeout, row.standard_timeout,
        );
    }

    Ok(())
}

#[derive(Debug, PartialEq, Eq)]
struct EvalListRow {
    eval_id: String,
    domain: String,
    scoring: String,
    dev_timeout: String,
    standard_timeout: String,
}

fn eval_list_rows(evals: &[(String, EvalSpec)]) -> Vec<EvalListRow> {
    evals
        .iter()
        .map(|(eval_id, spec)| {
            let dev_timeout = spec
                .inputs
                .as_ref()
                .and_then(|i| i.timeout_sec)
                .map(|t| format!("{t:.0}s"))
                .unwrap_or_else(|| "?".to_string());
            EvalListRow {
                eval_id: eval_id.clone(),
                domain: infer_domain(eval_id).to_string(),
                scoring: scoring_label(eval_id, spec),
                dev_timeout,
                standard_timeout: format!("{:.0}s", standard_timeout_sec(eval_id, spec)),
            }
        })
        .collect()
}

// ===================================================================
// Helpers
// ===================================================================

/// Build an explicit benchmark file list from list_file or set_file.
///
/// - `list_file`: text file with one path per line (relative to repo root).
///   Lines starting with `#` or empty are skipped. Optional second column
///   is ignored (used for expected result in some formats).
/// - `set_file`: manifest relative to benchmarks_dir, listing paths relative
///   to benchmarks_dir. Lines ending in `.yml` are converted to `.smt2`.
///
/// Returns `None` if neither is specified (caller uses directory discovery).
fn build_file_list(
    spec: &EvalSpec,
    root: &Path,
    benchmarks_dir: &Path,
) -> Result<Option<Vec<PathBuf>>> {
    let inputs = match spec.inputs.as_ref() {
        Some(i) => i,
        None => return Ok(None),
    };

    if let Some(ref list_path) = inputs.list_file {
        let path = root.join(list_path);
        let text = std::fs::read_to_string(&path)
            .with_bench_context(|| format!("reading list_file {}", path.display()))?;
        let mut files = Vec::new();
        let mut total = 0u32;
        let mut missing = 0u32;
        for line in text.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            total += 1;
            // First column is the path, rest is optional metadata
            let file_path = trimmed.split_whitespace().next().unwrap();
            let full = root.join(file_path);
            if full.exists() {
                files.push(full);
            } else {
                missing += 1;
            }
        }
        if missing > 0 {
            eprintln!(
                "warning: list_file {}: {missing}/{total} benchmarks not found on disk",
                list_path
            );
        }
        files.sort();
        return Ok(Some(files));
    }

    if let Some(ref set_name) = inputs.set_file {
        let set_path = benchmarks_dir.join(set_name);
        let text = std::fs::read_to_string(&set_path)
            .with_bench_context(|| format!("reading set_file {}", set_path.display()))?;
        let mut files = Vec::new();
        let mut total = 0u32;
        let mut missing = 0u32;
        for line in text.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            total += 1;
            // CHC-COMP set files list .yml paths; convert to .smt2
            let smt2_name = if trimmed.ends_with(".yml") {
                trimmed.replace(".yml", ".smt2")
            } else {
                trimmed.to_string()
            };
            let full = benchmarks_dir.join(&smt2_name);
            if full.exists() {
                files.push(full);
            } else {
                missing += 1;
            }
        }
        if missing > 0 {
            eprintln!(
                "warning: set_file {}: {missing}/{total} benchmarks not found on disk",
                set_name
            );
        }
        files.sort();
        return Ok(Some(files));
    }

    Ok(None)
}

/// Build file list from suite_dirs — discover benchmarks from listed subdirectories only.
fn build_suite_dirs_list(
    spec: &EvalSpec,
    benchmarks_dir: &Path,
    domain: &str,
) -> Option<Vec<PathBuf>> {
    let dirs = spec.inputs.as_ref()?.suite_dirs.as_ref()?;
    if dirs.is_empty() {
        return None;
    }
    let mut files = Vec::new();
    for subdir in dirs {
        let path = benchmarks_dir.join(subdir);
        if path.is_dir() {
            if let Ok(discovered) = crate::native::discover_benchmarks(&path, domain) {
                files.extend(discovered);
            }
        } else {
            eprintln!("warning: suite_dirs entry not found: {}", path.display());
        }
    }
    files.sort();
    Some(files)
}

/// Expand `~` prefix to the user's home directory. If the path does not start
/// with `~`, treat it as relative to `root`.
fn expand_tilde(path: &str, root: &Path) -> PathBuf {
    if let Some(rest) = path.strip_prefix("~/") {
        if let Some(home) = std::env::var_os("HOME") {
            PathBuf::from(home).join(rest)
        } else {
            root.join(path)
        }
    } else {
        root.join(path)
    }
}

/// Strip YAML quoting and inline comments from a value string.
fn strip_yaml_value(raw: &str) -> String {
    let trimmed = raw.trim();
    // Strip inline comment (# preceded by whitespace)
    let no_comment = trimmed
        .find(" #")
        .map(|i| &trimmed[..i])
        .unwrap_or(trimmed)
        .trim();
    // Strip surrounding quotes
    if (no_comment.starts_with('"') && no_comment.ends_with('"'))
        || (no_comment.starts_with('\'') && no_comment.ends_with('\''))
    {
        no_comment[1..no_comment.len() - 1].to_string()
    } else {
        no_comment.to_string()
    }
}

// ===================================================================
// Tests
// ===================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn test_run_args() -> RunArgs {
        RunArgs {
            eval_ids: Vec::new(),
            all: false,
            domain: None,
            competition: false,
            ay: PathBuf::from("target/debug/ay"),
            timeout: None,
            output: None,
            runs: None,
            reference_solvers: Vec::new(),
            run_class: None,
            quiet: true,
            with_features: false,
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
        }
    }

    #[test]
    fn test_resolve_results_root_defaults_under_repo() {
        let repo = Path::new("/tmp/ay-repo");

        assert_eq!(
            resolve_results_root(repo, None),
            PathBuf::from("/tmp/ay-repo/evals/results")
        );
        assert_eq!(
            resolve_results_root(repo, Some(PathBuf::new())),
            PathBuf::from("/tmp/ay-repo/evals/results")
        );
    }

    #[test]
    fn test_resolve_results_root_honors_relative_and_absolute_override() {
        let repo = Path::new("/tmp/ay-repo");

        assert_eq!(
            resolve_results_root(repo, Some(PathBuf::from("bench-results"))),
            PathBuf::from("/tmp/ay-repo/bench-results")
        );
        assert_eq!(
            resolve_results_root(repo, Some(PathBuf::from("/tmp/ay-bench-results"))),
            PathBuf::from("/tmp/ay-bench-results")
        );
    }

    #[test]
    fn test_infer_domain() {
        assert_eq!(infer_domain("sat-par2-dev"), "sat");
        assert_eq!(infer_domain("smt-smtcomp-qf-lia"), "smt");
        assert_eq!(infer_domain("smt-local-suite"), "smt");
        assert_eq!(infer_domain("chccomp-2025-lia"), "chc");
        assert_eq!(infer_domain("chc-something"), "chc");
        assert_eq!(infer_domain("hwmcc-wordlevel-bv-2025"), "hwmcc");
        assert_eq!(infer_domain("other"), "unknown");
        // Security benchmark domains
        assert_eq!(infer_domain("sygus-security-inv"), "sygus");
        assert_eq!(infer_domain("maxsat-eval-2023"), "maxsat");
        assert_eq!(infer_domain("qbf-qbflib"), "qbf");
        assert_eq!(infer_domain("allsat-security-cnf"), "allsat");
        assert_eq!(infer_domain("counting-security-qif"), "counting");
        assert_eq!(infer_domain("omt-security-lra"), "omt");
        assert_eq!(infer_domain("security-sygus-inv"), "sygus");
        assert_eq!(infer_domain("security-omt-lra"), "omt");
        assert_eq!(infer_domain("security-svcomp-bv"), "smt");
    }

    #[test]
    fn test_infer_competition() {
        assert_eq!(infer_competition("sat-par2-dev"), Competition::SatComp);
        assert_eq!(infer_competition("smt-local-suite"), Competition::SmtComp);
        assert_eq!(infer_competition("chccomp-2025-lia"), Competition::ChcComp);
        assert_eq!(
            infer_competition("hwmcc-wordlevel-bv-2025"),
            Competition::HwmccComp,
        );
        assert_eq!(infer_competition("unknown-eval"), Competition::SmtComp);
    }

    #[test]
    fn test_infer_hwmcc_track() {
        assert_eq!(infer_hwmcc_track("hwmcc-wordlevel-bv-2025"), "wordlevel-bv");
        assert_eq!(
            infer_hwmcc_track("hwmcc-wordlevel-array-2025"),
            "wordlevel-array"
        );
        assert_eq!(infer_hwmcc_track("hwmcc-bitlevel-2024"), "bitlevel");
        assert_eq!(infer_hwmcc_track("hwmcc-other"), "unknown");
    }

    #[test]
    fn test_infer_division() {
        assert_eq!(infer_division("smt-smtcomp-qf-lia"), "QF_LIA");
        assert_eq!(infer_division("smt-smtcomp-qf-bv"), "QF_BV");
        assert_eq!(infer_division("smt-local-suite"), "mixed");
        assert_eq!(infer_division("smt-local-qf-lia"), "QF_LIA");
        assert_eq!(infer_division("chccomp-2025-lia"), "unknown");
    }

    #[test]
    fn test_infer_track() {
        assert_eq!(
            infer_track("chccomp-2025-extra-small-lia"),
            "LIA-extra-small"
        );
        assert_eq!(infer_track("chccomp-2025-lia-lin"), "LIA-Lin");
        assert_eq!(infer_track("chccomp-2025-lia"), "LIA");
        assert_eq!(infer_track("sat-par2-dev"), "unknown");
    }

    #[test]
    fn test_strip_yaml_value() {
        assert_eq!(strip_yaml_value(" hello "), "hello");
        assert_eq!(strip_yaml_value(" \"quoted\" "), "quoted");
        assert_eq!(strip_yaml_value(" 'single' "), "single");
        assert_eq!(strip_yaml_value(" 60 # seconds "), "60");
        assert_eq!(strip_yaml_value(" value#nospace "), "value#nospace");
    }

    #[test]
    fn test_parse_eval_spec_minimal() {
        let yaml = "\
id: sat-par2-dev
version: 1
inputs:
  timeout_sec: 20
  benchmarks_dir: benchmarks/sat/sample
";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.id.as_deref(), Some("sat-par2-dev"));
        let inputs = spec.inputs.unwrap();
        assert_eq!(inputs.timeout_sec, Some(20.0));
        assert_eq!(
            inputs.benchmarks_dir.as_deref(),
            Some("benchmarks/sat/sample")
        );
    }

    #[test]
    fn test_parse_eval_spec_sat_comp_metadata() {
        let yaml = "\
id: sat-par2-dev
competition: sat-comp
scoring: sat-comp
inputs:
  timeout_sec: 20
  standard_timeout_sec: 5000
  benchmarks_dir: benchmarks/sat/sample
";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.competition.as_deref(), Some("sat-comp"));
        assert_eq!(spec.scoring.as_deref(), Some("sat-comp"));
        let inputs = spec.inputs.as_ref().unwrap();
        assert_eq!(inputs.timeout_sec, Some(20.0));
        assert_eq!(inputs.standard_timeout_sec, Some(5000.0));
        assert_eq!(scoring_label("sat-par2-dev", &spec), "sat-comp");
        assert_eq!(standard_timeout_sec("sat-par2-dev", &spec), 5000.0);
    }

    #[test]
    fn test_parse_eval_spec_quoted_id() {
        let yaml = "id: \"my-eval\"\ntimeout_sec: 30\n";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.id.as_deref(), Some("my-eval"));
    }

    #[test]
    fn test_parse_eval_spec_inline_comment() {
        let yaml = "id: eval1\ntimeout_sec: 60 # seconds\n";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.inputs.unwrap().timeout_sec, Some(60.0));
    }

    #[test]
    fn test_parse_eval_spec_fallback_id() {
        let yaml = "timeout_sec: 10\n";
        let spec =
            parse_eval_spec_minimal(yaml, Path::new("/evals/registry/my-eval.yaml")).unwrap();
        assert_eq!(spec.id.as_deref(), Some("my-eval"));
    }

    #[test]
    fn test_parse_eval_spec_runs() {
        let yaml = "id: test\nruns: 3\ntimeout_sec: 20\n";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.inputs.unwrap().runs, Some(3));
    }

    #[test]
    fn test_effective_runs_uses_yaml_when_cli_omitted() {
        let yaml = "id: test\nruns: 3\ntimeout_sec: 20\n";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        let args = RunArgs {
            runs: None,
            ..test_run_args()
        };

        assert_eq!(effective_runs(&args, spec.inputs.as_ref()), 3);
    }

    #[test]
    fn test_effective_runs_respects_explicit_single_run_override() {
        let yaml = "id: test\nruns: 3\ntimeout_sec: 20\nreference_solver: z3\n";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        let args = RunArgs {
            runs: Some(1),
            reference_solvers: vec![("z3".to_string(), PathBuf::from("z3"))],
            ..test_run_args()
        };

        assert_eq!(effective_runs(&args, spec.inputs.as_ref()), 1);
    }

    #[test]
    fn test_parse_eval_spec_suite_dirs() {
        let yaml = "\
id: smt-local-suite
inputs:
  benchmarks_dir: benchmarks/smt/
  suite_dirs:
    - QF_BV
    - QF_LIA
    - QF_LRA
  timeout_sec: 30
";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        let inputs = spec.inputs.unwrap();
        let dirs = inputs.suite_dirs.unwrap();
        assert_eq!(dirs, vec!["QF_BV", "QF_LIA", "QF_LRA"]);
    }

    #[test]
    fn test_parse_eval_spec_reference_solver() {
        let yaml = "id: sat-par2-dev\nreference_solver: z3\ntimeout_sec: 20\n";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.inputs.unwrap().reference_solver.as_deref(), Some("z3"));
    }

    #[test]
    fn test_parse_eval_spec_consensus_csv() {
        let yaml = "\
id: hwmcc-wordlevel-bv-2025
consensus_csv: ~/labels/hwmcc25-wordlevel-bv.csv
timeout_sec: 30
";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(
            spec.inputs.unwrap().consensus_csv.as_deref(),
            Some("~/labels/hwmcc25-wordlevel-bv.csv")
        );
    }

    #[test]
    fn test_eval_list_row_uses_sat_comp_registry_metadata() {
        let yaml = "\
id: sat-par2-dev
competition: sat-comp
scoring: sat-comp
inputs:
  timeout_sec: 20
  standard_timeout_sec: 5000
";
        let spec = parse_eval_spec_minimal(yaml, Path::new("sat-par2-dev.yaml")).unwrap();
        let rows = eval_list_rows(&[("sat-par2-dev".to_string(), spec)]);

        assert_eq!(
            rows,
            vec![EvalListRow {
                eval_id: "sat-par2-dev".to_string(),
                domain: "sat".to_string(),
                scoring: "sat-comp".to_string(),
                dev_timeout: "20s".to_string(),
                standard_timeout: "5000s".to_string(),
            }]
        );
    }

    #[test]
    fn test_discover_sat_par2_registry_specs() {
        let evals = discover_evals().unwrap();
        let dev = evals
            .iter()
            .find(|(id, _)| id == "sat-par2-dev")
            .expect("sat-par2-dev registry spec should exist");
        let heldout = evals
            .iter()
            .find(|(id, _)| id == "sat-par2-heldout")
            .expect("sat-par2-heldout registry spec should exist");

        for (eval_id, spec) in [dev, heldout] {
            assert_eq!(infer_domain(eval_id), "sat");
            assert_eq!(infer_competition(eval_id), Competition::SatComp);
            assert_eq!(scoring_label(eval_id, spec), "sat-comp");
            assert_eq!(standard_timeout_sec(eval_id, spec), 5000.0);
        }
    }

    #[test]
    fn test_select_sat_domain_evals_for_run() {
        let evals = discover_evals().unwrap();
        let args = RunArgs {
            eval_ids: Vec::new(),
            all: false,
            domain: Some("sat".to_string()),
            competition: false,
            ay: PathBuf::from("target/debug/ay"),
            timeout: None,
            output: None,
            runs: None,
            reference_solvers: Vec::new(),
            run_class: None,
            quiet: true,
            with_features: false,
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
        };

        let selected = select_evals_for_run(evals, &args).unwrap();
        let ids: Vec<_> = selected.iter().map(|(id, _)| id.as_str()).collect();
        assert!(ids.contains(&"sat-par2-dev"));
        assert!(ids.contains(&"sat-par2-heldout"));
        assert!(selected
            .iter()
            .all(|(eval_id, _)| infer_domain(eval_id) == "sat"));
    }

    #[test]
    fn test_expand_tilde() {
        let root = Path::new("/repo");
        // Non-tilde path joins with root
        assert_eq!(
            expand_tilde("benchmarks/sat", root),
            root.join("benchmarks/sat")
        );
        // Tilde path expands home
        let home = std::env::var_os("HOME").unwrap();
        let expected = PathBuf::from(&home).join("hwmcc/benchmarks");
        assert_eq!(expand_tilde("~/hwmcc/benchmarks", root), expected);
    }

    #[test]
    fn test_build_rows_persists_sat_artifact_metadata() {
        let artifact_output_dir = "/tmp/ay-bench/artifacts".to_string();
        let proof_hash = "fh128:0123456789abcdef0123456789abcdef".to_string();
        let item = crate::native::NativeResultItem {
            file: "proof.cnf".to_string(),
            benchmark_path: "proof.cnf".to_string(),
            benchmark_content_hash: Some("fh128:proof".to_string()),
            solver_input_path: None,
            expected: Some("unsat".to_string()),
            result: "unsat".to_string(),
            time_sec: 0.25,
            cpu_time_sec: 0.25,
            exit_code: Some(20),
            solver_argv: Vec::new(),
            solver_env: Default::default(),
            artifacts: Some(crate::native::SolverArtifactMetadata {
                output_dir: artifact_output_dir.clone(),
                proof_path: Some("/tmp/ay-bench/artifacts/proof.lrat".to_string()),
                proof_format: Some("lrat".to_string()),
                proof_exists: Some(true),
                proof_bytes: Some(128),
                proof_hash: Some(proof_hash.clone()),
            }),
            sat_run: None,
        };
        let missing_proof_item = crate::native::NativeResultItem {
            file: "missing.cnf".to_string(),
            benchmark_path: "missing.cnf".to_string(),
            benchmark_content_hash: Some("fh128:missing".to_string()),
            solver_input_path: None,
            expected: Some("unsat".to_string()),
            result: "unsat".to_string(),
            time_sec: 0.5,
            cpu_time_sec: 0.5,
            exit_code: Some(20),
            solver_argv: Vec::new(),
            solver_env: Default::default(),
            artifacts: Some(crate::native::SolverArtifactMetadata {
                output_dir: artifact_output_dir.clone(),
                proof_path: Some("/tmp/ay-bench/artifacts/missing.lrat".to_string()),
                proof_format: Some("lrat".to_string()),
                proof_exists: Some(false),
                proof_bytes: None,
                proof_hash: None,
            }),
            sat_run: None,
        };
        let results = crate::native::NativeResults {
            environment: crate::environment::Environment {
                timestamp: "2026-04-25T00:00:00Z".to_string(),
                git_commit: "commit".to_string(),
                git_dirty: false,
                ay_path: "ay".to_string(),
                ay_version: "ay test".to_string(),
                ay_build_version: "test".to_string(),
                ay_build_commit: "commit".to_string(),
                ay_build_datetime_utc: "2026-04-25T00:00:00Z".to_string(),
                ay_build_stamp: "test".to_string(),
                hostname: "host".to_string(),
                os: "test",
                arch: "test",
                cpu_model: "cpu".to_string(),
                cpu_count: 1,
                memory_bytes: 1,
                load_avg: [0.0, 0.0, 0.0],
            },
            items: vec![item, missing_proof_item],
            settings: crate::native::NativeSettings {
                benchmarks_dir: ".".to_string(),
                timeout_sec: 1.0,
                domain: "sat".to_string(),
                benchmark_count: 2,
                runs: 1,
                solver_args: Vec::new(),
                solver_env: Default::default(),
                artifact_output_dir: Some(artifact_output_dir.clone()),
                sat_track: Some("main".to_string()),
                sat_ai_class: Some("regular".to_string()),
                sat_variant: Some("default".to_string()),
                sat_competition_profile: None,
                resource_plan: None,
                resource_enforcement: None,
            },
            comparison: None,
            comparisons: None,
            run_class: None,
            run_class_verified: None,
            host_fingerprint: None,
            references: None,
        };

        let rows = build_rows("commit", "sat-main", &results, false);

        assert_eq!(rows.len(), 2);
        assert_eq!(
            rows[0].artifact_output_dir.as_deref(),
            Some(artifact_output_dir.as_str())
        );
        assert_eq!(
            rows[0].proof_path.as_deref(),
            Some("/tmp/ay-bench/artifacts/proof.lrat")
        );
        assert_eq!(rows[0].proof_format.as_deref(), Some("lrat"));
        assert_eq!(rows[0].proof_exists, Some(true));
        assert_eq!(rows[0].proof_bytes, Some(128));
        assert_eq!(rows[0].proof_hash.as_deref(), Some(proof_hash.as_str()));
        assert_eq!(
            rows[1].artifact_output_dir.as_deref(),
            Some(artifact_output_dir.as_str())
        );
        assert_eq!(
            rows[1].proof_path.as_deref(),
            Some("/tmp/ay-bench/artifacts/missing.lrat")
        );
        assert_eq!(rows[1].proof_format.as_deref(), Some("lrat"));
        assert_eq!(rows[1].proof_exists, Some(false));
        assert_eq!(rows[1].proof_bytes, None);
        assert_eq!(rows[1].proof_hash, None);
    }

    #[test]
    fn test_select_representative_single() {
        let item = crate::native::NativeResultItem {
            file: "test.cnf".to_string(),
            benchmark_path: "test.cnf".to_string(),
            benchmark_content_hash: Some("fh128:test".to_string()),
            solver_input_path: None,
            expected: None,
            result: "sat".to_string(),
            time_sec: 1.5,
            cpu_time_sec: 1.5,
            exit_code: Some(10),
            solver_argv: Vec::new(),
            solver_env: Default::default(),
            artifacts: None,
            sat_run: None,
        };
        let rep = crate::native::select_representative(vec![item]);
        assert_eq!(rep.time_sec, 1.5);
    }

    #[test]
    fn test_select_representative_median() {
        let make = |t: f64| crate::native::NativeResultItem {
            file: "test.cnf".to_string(),
            benchmark_path: "test.cnf".to_string(),
            benchmark_content_hash: Some("fh128:test".to_string()),
            solver_input_path: None,
            expected: None,
            result: "sat".to_string(),
            time_sec: t,
            cpu_time_sec: t,
            exit_code: Some(10),
            solver_argv: Vec::new(),
            solver_env: Default::default(),
            artifacts: None,
            sat_run: None,
        };
        // 3 runs: 1.0, 3.0, 2.0 — median is 2.0
        let rep = crate::native::select_representative(vec![make(1.0), make(3.0), make(2.0)]);
        assert_eq!(rep.time_sec, 2.0);
    }
}
