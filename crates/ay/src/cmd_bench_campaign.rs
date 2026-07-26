// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reviewer-facing execution of every currently runnable campaign lane.
//!
//! The command deliberately emits one disposition for every catalog track.
//! Running a proxy lane never creates an official or retroactive score for the
//! track; unavailable formats and missing replay recipes remain explicit.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::{BufReader, Read as _, Write as _};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

use anyhow::{anyhow, bail, Context, Result};
use clap::{Args, Subcommand};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const DEFAULT_CATALOG: &str = "benchmarks/continuous-2025-2026.toml";
const DEFAULT_ASSETS: &str = "benchmarks/competition-assets-2025-2026.toml";
const DEFAULT_CORPORA: &str = "benchmarks/corpora.toml";
const DEFAULT_LANES: &str = "benchmarks/continuous-lanes.toml";
const DEFAULT_PROFILES: &str = "benchmarks/competition-run-profiles.toml";
const VERDICT_EVIDENCE_CLASSIFICATION: &str = "reference-or-authoritative-label-agreement";

#[derive(Args)]
#[command(
    about = "Run every currently supported 2025/2026 campaign benchmark",
    long_about = "Run every locally executable campaign lane and emit a catalog-complete external-reviewer campaign packet with one explicit disposition for every catalog track. Unsupported, unavailable, and recipe-pending tracks are reported rather than silently skipped. Proxy evidence is never admitted as an official retroactive score."
)]
pub(crate) struct CampaignArgs {
    #[command(subcommand)]
    command: CampaignCommand,
}

#[derive(Subcommand)]
enum CampaignCommand {
    /// Show the catalog-complete external-reviewer plan without running solvers.
    Plan(CampaignPlanArgs),
    /// Run all eligible lanes under the validated reviewer-full guarded profile.
    Run(CampaignRunArgs),
}

#[derive(Args, Clone)]
struct CampaignFiles {
    /// Continuous competition track catalog.
    #[arg(long, default_value = DEFAULT_CATALOG)]
    catalog: PathBuf,
    /// Track-to-asset and support crosswalk.
    #[arg(long, default_value = DEFAULT_ASSETS)]
    assets: PathBuf,
    /// Internet acquisition manifest.
    #[arg(long, default_value = DEFAULT_CORPORA)]
    corpora: PathBuf,
    /// Executable lane manifest.
    #[arg(long, default_value = DEFAULT_LANES)]
    lanes: PathBuf,
    /// Resource and subset profiles.
    #[arg(long, default_value = DEFAULT_PROFILES)]
    profiles: PathBuf,
}

#[derive(Args)]
struct CampaignPlanArgs {
    #[command(flatten)]
    files: CampaignFiles,
    /// Reviewer profile to validate and plan.
    #[arg(long, default_value = "reviewer-full")]
    profile: String,
    /// Write JSON to this path instead of standard output.
    #[arg(long)]
    output: Option<PathBuf>,
}

#[derive(Args)]
struct CampaignRunArgs {
    #[command(flatten)]
    files: CampaignFiles,
    /// Campaign profile. Only reviewer-full, the validated full-corpus proxy
    /// profile, is currently accepted; all other declared profiles remain
    /// declarative.
    #[arg(long, default_value = "reviewer-full")]
    profile: String,
    /// Candidate AY binary; defaults to this running executable.
    #[arg(long)]
    ay: Option<PathBuf>,
    /// Campaign packet destination.
    #[arg(long)]
    output: Option<PathBuf>,
    /// Refuse to run unless core, external evidence, and linked competitor
    /// assets all pass `corpus campaign-audit --require-installed`.
    #[arg(long)]
    require_installed: bool,
}

#[derive(Debug, Deserialize)]
struct Catalog {
    #[serde(default, rename = "track")]
    tracks: Vec<CatalogTrack>,
}

#[derive(Debug, Deserialize)]
struct CatalogTrack {
    id: String,
    competition: String,
    edition: u32,
}

#[derive(Debug, Deserialize)]
struct AssetManifest {
    #[serde(default, rename = "event")]
    events: Vec<AssetEvent>,
}

#[derive(Debug, Deserialize)]
struct AssetEvent {
    id: String,
    competition: String,
    edition: u32,
    #[serde(default)]
    track_ids: Vec<String>,
    corpus_status: String,
    official_machine_status: String,
    local_run_support: String,
    reason: String,
}

#[derive(Debug, Deserialize)]
struct LaneManifest {
    #[serde(default, rename = "lane")]
    lanes: Vec<Lane>,
}

#[derive(Debug, Deserialize)]
struct Lane {
    id: String,
    kind: String,
    eval_id: String,
    #[serde(default = "default_true")]
    enabled: bool,
    #[serde(default)]
    requires_paths: Vec<String>,
    #[serde(default)]
    requires_tools: Vec<String>,
    #[serde(default = "default_min_benchmarks")]
    min_benchmarks: usize,
    #[serde(default)]
    competition_refs: Vec<String>,
    blocked_reason: Option<String>,
}

#[derive(Debug, Deserialize)]
struct ProfileManifest {
    #[serde(default, rename = "profile")]
    profiles: Vec<Profile>,
}

#[derive(Debug, Clone, Deserialize)]
struct Profile {
    id: String,
    run_class: String,
    timeout_sec: f64,
    shard_size: usize,
    max_jobs: usize,
    per_child_memory_mib: usize,
    #[serde(default)]
    per_child_cores: usize,
    cpu_policy: String,
    oom_guard_required: bool,
    same_host_competitors: usize,
    score_comparable: bool,
    #[serde(default)]
    requires_exact_hardware: bool,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct SatScoreFields {
    par2_total: f64,
    par2_avg: f64,
    solved: u64,
    solved_sat: u64,
    solved_unsat: u64,
    unsolved: u64,
    wrong: u64,
    disqualified: bool,
    total: u64,
    timeout_sec: f64,
    wrong_answers: Vec<serde_json::Value>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct SmtScoreFields {
    division: String,
    errors: u64,
    solved: u64,
    wall_time: f64,
    cpu_time: f64,
    total: u64,
    solved_sat: u64,
    solved_unsat: u64,
    timeout_count: u64,
    sound: bool,
    wrong_answers: Vec<serde_json::Value>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct ChcScoreFields {
    track: String,
    solved: u64,
    solved_sat: u64,
    solved_unsat: u64,
    cpu_time: f64,
    unsolved: u64,
    wrong: u64,
    total: u64,
    timeout_sec: f64,
    wrong_answers: Vec<serde_json::Value>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct ScorecardEvidence {
    results_path: String,
    verified: u64,
    wrong: u64,
    unverified_definitive: u64,
    non_definitive: u64,
    total: u64,
}

#[derive(Debug, Deserialize, Serialize)]
struct NativeEvidenceDocument {
    environment: RunnerEnvironmentEvidence,
    items: Vec<NativeResultItemEvidence>,
    preprocessing: Vec<NativeInputPreparationEvidence>,
    settings: NativeSettingsEvidence,
    comparisons: Option<Vec<NativeComparisonItemEvidence>>,
    reference_comparisons: Option<Vec<NativeReferenceComparisonEvidence>>,
    #[serde(default)]
    references: Vec<NativeReferenceEvidence>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
struct NativeResultItemEvidence {
    file: String,
    benchmark_path: String,
    benchmark_content_hash: Option<String>,
    solver_input_hash: Option<String>,
    solver_input_path: Option<String>,
    expected: Option<String>,
    expected_source: String,
    result: String,
    time_sec: f64,
    cpu_time_sec: f64,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
struct NativeInputPreparationEvidence {
    benchmark_path: String,
    source_hash: String,
    solver_input_hash: String,
    source_bytes: u64,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
struct NativeReferenceRunEvidence {
    result: String,
    solver_input_path: String,
    solver_input_hash: String,
    stdout_sha256: String,
    stderr_sha256: String,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
struct NativeComparisonItemEvidence {
    file: String,
    solver_input_hash: String,
    ay_result: String,
    ref_result: String,
    agreement: String,
    reference_runs: Vec<NativeReferenceRunEvidence>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
struct NativeReferenceComparisonEvidence {
    reference_solver: String,
    items: Vec<NativeComparisonItemEvidence>,
}

#[derive(Debug, Deserialize, Serialize)]
struct NativeSettingsEvidence {
    benchmarks_dir: String,
    timeout_sec: f64,
    domain: String,
    benchmark_count: usize,
    runs: u32,
    resource_plan: ay_bench::ResourcePlan,
    resource_enforcement: String,
    #[serde(default)]
    shard: Option<NativeShardIdentityPacket>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
struct NativeReferenceEvidence {
    reference_solver: String,
    reference_solver_path: String,
    reference_solver_sha256: String,
    reference_solver_size_bytes: u64,
    reference_solver_version: String,
    reference_solver_build_version: String,
    reference_solver_build_commit: String,
    reference_solver_build_datetime_utc: String,
    reference_solver_build_stamp: String,
    reference_resource_enforcement: String,
    reference_resource_envelope: String,
    agree: u64,
    disagree: u64,
    ay_only: u64,
    ref_only: u64,
}

#[derive(Debug, Clone)]
struct ValidatedLaneEvidence {
    score_competition: String,
    score: serde_json::Value,
    solve_summary: SolveSummaryPacket,
    evidence_counts: EvidenceCountsPacket,
    reference_solvers: Vec<ReferenceSolverProvenancePacket>,
    results_path: String,
    benchmark_count: usize,
    native_results: NativeResultsIdentityPacket,
    corpus: CorpusIdentityPacket,
    enforced_envelope: EnforcedEnvelopePacket,
}

#[derive(Debug, Clone)]
struct ValidatedNativeLaneEvidence {
    results_path: String,
    benchmark_count: usize,
    native_results: NativeResultsIdentityPacket,
    corpus: CorpusIdentityPacket,
    reference_solvers: Vec<ReferenceSolverProvenancePacket>,
    enforced_envelope: EnforcedEnvelopePacket,
}

#[derive(Debug, Clone)]
struct ValidatedScorecardRow {
    competition: String,
    score: serde_json::Value,
    solve_summary: SolveSummaryPacket,
    evidence: ScorecardEvidence,
}

#[derive(Debug, Clone, Serialize, PartialEq)]
struct SolveSummaryPacket {
    solved: u64,
    total: u64,
    solve_rate: f64,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
struct EvidenceCountsPacket {
    verified: u64,
    wrong: u64,
    unverified_definitive: u64,
    non_definitive: u64,
    total: u64,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
struct NativeResultsIdentityPacket {
    sha256: String,
    size_bytes: u64,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
struct ReferenceSolverProvenancePacket {
    name: String,
    canonical_path: String,
    sha256: String,
    size_bytes: u64,
    version: String,
    build_version: String,
    build_commit: String,
    build_datetime_utc: String,
    build_stamp: String,
    resource_enforcement: String,
    resource_envelope: String,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct NativeShardIdentityPacket {
    requested_index: usize,
    shard_index: usize,
    shard_size: usize,
    shard_count: usize,
    corpus_benchmark_count: usize,
    selected_benchmark_count: usize,
    corpus_path_inventory_sha256: String,
    selector: String,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
struct CorpusIdentityPacket {
    benchmarks_dir: String,
    domain: String,
    benchmark_count: usize,
    content_inventory_sha256: String,
    shard: Option<NativeShardIdentityPacket>,
}

#[derive(Debug, Clone, Serialize)]
struct LanePacket {
    lane_id: String,
    eval_id: String,
    evidence_class: String,
    status: String,
    reason: String,
    benchmark_count: Option<usize>,
    score_competition: Option<String>,
    score: Option<serde_json::Value>,
    solve_summary: Option<SolveSummaryPacket>,
    evidence_counts: Option<EvidenceCountsPacket>,
    verdict_evidence_classification: Option<String>,
    reference_solvers: Vec<ReferenceSolverProvenancePacket>,
    results_path: Option<String>,
    native_results: Option<NativeResultsIdentityPacket>,
    corpus: Option<CorpusIdentityPacket>,
    enforced_envelope: Option<EnforcedEnvelopePacket>,
}

#[derive(Debug, Serialize)]
struct TrackPacket {
    track_id: String,
    competition: String,
    edition: u32,
    event_id: String,
    execution_disposition: String,
    official_replay_status: String,
    score_admitted: bool,
    underpowered_vs_official: String,
    reason: String,
    lane_ids: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct CandidatePacket {
    ay_path: String,
    ay_sha256: Option<String>,
    ay_size_bytes: Option<u64>,
    ay_build_commit: Option<String>,
    git_commit: String,
    git_dirty: bool,
}

#[derive(Debug, Serialize)]
struct CampaignCoveragePacket {
    declared_tracks: usize,
    accounted_tracks: usize,
    declared_lanes: usize,
    eligible_lanes: usize,
    blocked_lanes: usize,
    passed_lanes: usize,
    failed_lanes: usize,
}

#[derive(Debug, Serialize)]
struct RequestedEnvelopePacket {
    timeout_sec: f64,
    max_jobs: usize,
    per_child_memory_mib: usize,
    per_child_cores: usize,
    cpu_policy: String,
    oom_guard_required: bool,
    guard_script: String,
}

#[derive(Debug, Clone, Serialize)]
struct EnforcedEnvelopePacket {
    timeout_sec: f64,
    resource_plan: ay_bench::ResourcePlan,
    resource_enforcement: String,
    effective_envelope: String,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq)]
struct RunnerEnvironmentEvidence {
    timestamp: String,
    git_commit: String,
    git_dirty: Option<bool>,
    comparable_git_state: bool,
    ay_path: String,
    ay_sha256: String,
    ay_size_bytes: u64,
    ay_version: String,
    ay_build_version: String,
    ay_build_commit: String,
    ay_build_datetime_utc: String,
    ay_build_stamp: String,
    hostname: String,
    os: String,
    arch: String,
    cpu_model: String,
    cpu_count: u32,
    memory_bytes: u64,
    load_avg: [f64; 3],
}

#[derive(Debug, Serialize)]
struct RuntimeHostPacket {
    evidence_source: &'static str,
    hostname: String,
    os: &'static str,
    arch: &'static str,
    cpu_model: String,
    system_logical_cpu_count: Option<usize>,
    scheduler_available_cpu_count: Option<usize>,
    physical_core_count: Option<usize>,
    memory_total_bytes: Option<u64>,
    swap_total_bytes: Option<u64>,
    cgroup_v2_path: Option<String>,
    cgroup_memory_max: Option<String>,
    cgroup_memory_high: Option<String>,
    cgroup_swap_max: Option<String>,
    cgroup_cpu_max: Option<String>,
    cgroup_cpuset_effective: Option<String>,
    official_hardware_match_verified: bool,
}

#[derive(Debug, Serialize)]
struct CampaignPacket {
    schema_version: u32,
    generated_unix_sec: u64,
    scope: &'static str,
    profile: String,
    run_class: String,
    overall_status: String,
    score_comparable: bool,
    coverage: CampaignCoveragePacket,
    requested_envelope: RequestedEnvelopePacket,
    runtime_host: RuntimeHostPacket,
    runner_environment: Option<RunnerEnvironmentEvidence>,
    candidate: CandidatePacket,
    scorecard_path: Option<String>,
    runner_error: Option<String>,
    lanes: Vec<LanePacket>,
    tracks: Vec<TrackPacket>,
}

fn default_true() -> bool {
    true
}

fn default_min_benchmarks() -> usize {
    1
}

#[cfg(feature = "bench")]
pub(crate) fn run(args: CampaignArgs) -> Result<()> {
    match args.command {
        CampaignCommand::Plan(args) => run_plan(args),
        CampaignCommand::Run(args) => run_campaign(args),
    }
}

#[cfg(not(feature = "bench"))]
pub(crate) fn run(_args: CampaignArgs) -> Result<()> {
    bail!("ay bench was built without benchmark support; rebuild with --features bench")
}

fn run_plan(args: CampaignPlanArgs) -> Result<()> {
    let repo = find_repo_root()?;
    let loaded = LoadedCampaign::load(&repo, &args.files, &args.profile)?;
    let lane_packets = plan_lanes(&repo, &loaded.lanes);
    let tracks = track_packets(&loaded, &lane_packets);
    let coverage = coverage_packet(&loaded, &lane_packets, &tracks);
    let packet = CampaignPacket {
        schema_version: 3,
        generated_unix_sec: unix_time()?,
        scope: "all-declared-tracks-and-all-locally-executable-campaign-lanes",
        profile: loaded.profile.id.clone(),
        run_class: loaded.profile.run_class.clone(),
        overall_status: "planned-with-expected-blocks".to_string(),
        score_comparable: loaded.profile.score_comparable,
        coverage,
        requested_envelope: requested_envelope_packet(&repo, &loaded.profile),
        runtime_host: runtime_host_packet(),
        runner_environment: None,
        candidate: candidate_packet(&repo, None)?,
        scorecard_path: None,
        runner_error: None,
        lanes: lane_packets,
        tracks,
    };
    write_or_print(&repo, args.output.as_deref(), &packet)
}

#[cfg(feature = "bench")]
fn run_campaign(args: CampaignRunArgs) -> Result<()> {
    let repo = find_repo_root()?;
    let loaded = LoadedCampaign::load(&repo, &args.files, &args.profile)?;
    validate_executable_profile(&loaded.profile)?;
    let ay = resolve_ay(&repo, args.ay)?;
    if args.require_installed {
        let status = Command::new(&ay)
            .current_dir(&repo)
            .arg("corpus")
            .arg("campaign-audit")
            .arg("--require-installed")
            .arg("--manifest")
            .arg(resolve_input(&repo, &args.files.corpora))
            .arg("--assets")
            .arg(resolve_input(&repo, &args.files.assets))
            .arg("--catalog")
            .arg(resolve_input(&repo, &args.files.catalog))
            .status()
            .context("run corpus campaign-audit --require-installed")?;
        if !status.success() {
            bail!("campaign assets are incomplete (corpus campaign-audit exited with {status})");
        }
    }

    let output = args.output.unwrap_or_else(|| {
        repo.join("evals/results/campaign")
            .join(format!("{}.json", loaded.profile.id))
    });
    let output = resolve_output(&repo, &output);
    // Capture the requested binary and source checkout before any benchmark
    // process starts. The scorecard gate re-captures both after the run and
    // refuses evidence that is not byte-for-byte and commit-for-commit bound
    // to this snapshot.
    let candidate = candidate_packet(&repo, Some(&ay))?;
    let run_started = unix_time()?;
    let scorecard = output.with_extension(format!(
        "scorecard.{run_started}.{}.json",
        std::process::id()
    ));
    if let Some(parent) = scorecard.parent() {
        fs::create_dir_all(parent)
            .with_context(|| format!("create campaign output {}", parent.display()))?;
    }

    let mut lane_packets = plan_lanes(&repo, &loaded.lanes);
    let runnable_eval_ids = lane_packets
        .iter()
        .filter(|lane| lane.status == "eligible")
        .map(|lane| lane.eval_id.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();

    let no_runnable_lanes = runnable_eval_ids.is_empty();
    let run_error = if no_runnable_lanes {
        Some("no campaign lanes are locally executable".to_string())
    } else {
        ay_bench::runner::cmd_run(ay_bench::runner::RunArgs {
            eval_ids: runnable_eval_ids,
            all: false,
            domain: None,
            competition: false,
            ay: ay.clone(),
            timeout: Some(loaded.profile.timeout_sec),
            output: Some(scorecard.clone()),
            runs: Some(1),
            shard_index: None,
            shard_size: None,
            reference_solvers: Vec::new(),
            run_class: None,
            quiet: false,
            with_features: false,
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
            resource_memory_cap_mib: Some(loaded.profile.per_child_memory_mib),
            resource_core_cap: Some(loaded.profile.per_child_cores),
        })
        .err()
        .map(|error| format!("{error:#}"))
    };

    let runner_environment = apply_scorecard_status(
        &repo,
        &scorecard,
        &mut lane_packets,
        &loaded.profile,
        Some(&candidate),
        run_error.as_deref(),
    )?;
    let failed = no_runnable_lanes
        || run_error.is_some()
        || lane_packets.iter().any(|lane| lane.status == "failed");
    let tracks = track_packets(&loaded, &lane_packets);
    let coverage = coverage_packet(&loaded, &lane_packets, &tracks);
    let packet = CampaignPacket {
        schema_version: 3,
        generated_unix_sec: unix_time()?,
        scope: "all-declared-tracks-and-all-locally-executable-campaign-lanes",
        profile: loaded.profile.id.clone(),
        run_class: loaded.profile.run_class.clone(),
        overall_status: if failed {
            "failed".to_string()
        } else {
            "passed-with-expected-blocks".to_string()
        },
        score_comparable: loaded.profile.score_comparable,
        coverage,
        requested_envelope: requested_envelope_packet(&repo, &loaded.profile),
        runtime_host: runtime_host_packet(),
        runner_environment,
        candidate,
        scorecard_path: scorecard
            .strip_prefix(&repo)
            .unwrap_or(&scorecard)
            .to_str()
            .map(ToOwned::to_owned),
        runner_error: run_error.clone(),
        lanes: lane_packets,
        tracks,
    };
    write_json_atomic(&output, &packet)?;
    println!("Campaign packet written to: {}", output.display());
    if failed {
        bail!("campaign execution failed; see {}", output.display());
    }
    Ok(())
}

struct LoadedCampaign {
    catalog: Catalog,
    events: BTreeMap<String, AssetEvent>,
    lanes: Vec<Lane>,
    profile: Profile,
}

impl LoadedCampaign {
    fn load(repo: &Path, files: &CampaignFiles, profile_id: &str) -> Result<Self> {
        let catalog: Catalog = load_toml(repo, &files.catalog)?;
        let assets: AssetManifest = load_toml(repo, &files.assets)?;
        let lanes: LaneManifest = load_toml(repo, &files.lanes)?;
        let profiles: ProfileManifest = load_toml(repo, &files.profiles)?;
        let mut profile_ids = BTreeSet::new();
        for profile in &profiles.profiles {
            if !profile_ids.insert(profile.id.as_str()) {
                bail!("campaign profiles repeat id {:?}", profile.id);
            }
        }
        let profile = profiles
            .profiles
            .into_iter()
            .find(|profile| profile.id == profile_id)
            .ok_or_else(|| anyhow!("unknown campaign profile {profile_id:?}"))?;
        validate_profile(&profile)?;

        if catalog.tracks.is_empty() {
            bail!("campaign catalog is empty");
        }
        let mut track_ids = BTreeSet::new();
        for track in &catalog.tracks {
            if !track_ids.insert(track.id.clone()) {
                bail!("campaign catalog repeats track {:?}", track.id);
            }
        }
        let mut events = BTreeMap::new();
        let mut assigned = BTreeSet::new();
        for event in assets.events {
            if event.id != format!("{}-{}", event.competition, event.edition) {
                bail!("invalid campaign event id {:?}", event.id);
            }
            for track_id in &event.track_ids {
                if !track_ids.contains(track_id) {
                    bail!("event {} references unknown track {track_id}", event.id);
                }
                let track = catalog
                    .tracks
                    .iter()
                    .find(|track| track.id == *track_id)
                    .expect("track membership checked above");
                if track.competition != event.competition || track.edition != event.edition {
                    bail!(
                        "event {} assigns track {} from {}-{}",
                        event.id,
                        track.id,
                        track.competition,
                        track.edition
                    );
                }
                if !assigned.insert(track_id.clone()) {
                    bail!("track {track_id} is assigned more than once");
                }
            }
            if events.insert(event.id.clone(), event).is_some() {
                bail!("campaign assets repeat an event id");
            }
        }
        if assigned != track_ids {
            let missing = track_ids
                .difference(&assigned)
                .map(String::as_str)
                .collect::<Vec<_>>();
            bail!(
                "campaign assets do not assign every track: {}",
                missing.join(", ")
            );
        }
        let mut lane_ids = BTreeSet::new();
        for lane in &lanes.lanes {
            if !lane_ids.insert(lane.id.as_str()) {
                bail!("campaign lanes repeat id {:?}", lane.id);
            }
            if lane.competition_refs.is_empty() {
                bail!("campaign lane {} has no competition_refs", lane.id);
            }
            if lane.min_benchmarks == 0 {
                bail!("campaign lane {} has min_benchmarks=0", lane.id);
            }
            for track_id in &lane.competition_refs {
                if !track_ids.contains(track_id) {
                    bail!(
                        "campaign lane {} references unknown track {}",
                        lane.id,
                        track_id
                    );
                }
            }
            let eval_path = repo
                .join("evals/registry")
                .join(format!("{}.yaml", lane.eval_id));
            if !eval_path.is_file() {
                bail!(
                    "campaign lane {} references missing eval {}",
                    lane.id,
                    eval_path.display()
                );
            }
        }
        Ok(Self {
            catalog,
            events,
            lanes: lanes.lanes,
            profile,
        })
    }
}

fn validate_profile(profile: &Profile) -> Result<()> {
    if !profile.oom_guard_required {
        bail!(
            "campaign profile {} does not require _oom_guard",
            profile.id
        );
    }
    if !profile.timeout_sec.is_finite() || profile.timeout_sec <= 0.0 {
        bail!("campaign profile {} needs a positive timeout", profile.id);
    }
    if profile.shard_size != 0 {
        bail!(
            "campaign profile {} is not a full-corpus reviewer profile",
            profile.id
        );
    }
    if profile.max_jobs != 1 || profile.per_child_memory_mib == 0 || profile.per_child_cores == 0 {
        bail!(
            "campaign profile {} needs max_jobs=1 and positive per-child caps",
            profile.id
        );
    }
    if profile.same_host_competitors != 0 || profile.score_comparable {
        bail!(
            "reviewer campaign profile {} cannot claim competitor or comparable scoring",
            profile.id
        );
    }
    Ok(())
}

fn validate_executable_profile(profile: &Profile) -> Result<()> {
    if profile.id != "reviewer-full" {
        bail!(
            "campaign execution supports only reviewer-full; profile {} remains declarative",
            profile.id
        );
    }
    if profile.requires_exact_hardware || profile.run_class == "official-replay" {
        bail!(
            "official replay is unavailable: exact dynamic hardware, checker, corpus, and competitor gates are not implemented"
        );
    }
    if profile.cpu_policy != "planner-budget-no-affinity-claim" {
        bail!(
            "profile {} requests unsupported CPU policy {:?}",
            profile.id,
            profile.cpu_policy
        );
    }
    Ok(())
}

fn plan_lanes(repo: &Path, lanes: &[Lane]) -> Vec<LanePacket> {
    lanes
        .iter()
        .map(|lane| {
            let (blocked, benchmark_count) = if !lane.enabled {
                (
                    Some(
                        lane.blocked_reason
                            .clone()
                            .unwrap_or_else(|| "lane disabled".to_string()),
                    ),
                    None,
                )
            } else if lane.kind == "official" {
                (
                    Some(
                        lane.blocked_reason
                            .clone()
                            .unwrap_or_else(|| "official replay gate is disabled".to_string()),
                    ),
                    None,
                )
            } else if let Some(reason) = &lane.blocked_reason {
                (Some(reason.clone()), None)
            } else if !tool_available("python3") {
                (
                    Some("missing mandatory python3 runtime for scripts/_oom_guard.py".to_string()),
                    None,
                )
            } else {
                let missing_paths = lane
                    .requires_paths
                    .iter()
                    .filter(|path| !repo.join(path).exists())
                    .cloned()
                    .collect::<Vec<_>>();
                if !missing_paths.is_empty() {
                    (
                        Some(format!("missing path(s): {}", missing_paths.join(", "))),
                        None,
                    )
                } else {
                    let missing_tools = lane
                        .requires_tools
                        .iter()
                        .filter(|tool| !tool_available(tool))
                        .cloned()
                        .collect::<Vec<_>>();
                    if !missing_tools.is_empty() {
                        (
                            Some(format!("missing tool(s): {}", missing_tools.join(", "))),
                            None,
                        )
                    } else {
                        match ay_bench::runner::preflight_eval_benchmark_count(&lane.eval_id) {
                            Ok(count) if count < lane.min_benchmarks => (
                                Some(format!(
                                    "eval {} has {count} benchmarks; lane requires at least {}",
                                    lane.eval_id, lane.min_benchmarks
                                )),
                                Some(count),
                            ),
                            Ok(count) => (None, Some(count)),
                            Err(error) => (
                                Some(format!(
                                    "eval {} corpus preflight failed: {error}",
                                    lane.eval_id
                                )),
                                None,
                            ),
                        }
                    }
                }
            };
            LanePacket {
                lane_id: lane.id.clone(),
                eval_id: lane.eval_id.clone(),
                evidence_class: "proxy".to_string(),
                status: if blocked.is_some() {
                    "blocked".to_string()
                } else {
                    "eligible".to_string()
                },
                reason: blocked.unwrap_or_else(|| {
                    "locally executable under the guarded reviewer profile".to_string()
                }),
                benchmark_count,
                score_competition: None,
                score: None,
                solve_summary: None,
                evidence_counts: None,
                verdict_evidence_classification: None,
                reference_solvers: Vec::new(),
                results_path: None,
                native_results: None,
                corpus: None,
                enforced_envelope: None,
            }
        })
        .collect()
}

fn apply_scorecard_status(
    repo: &Path,
    path: &Path,
    lanes: &mut [LanePacket],
    profile: &Profile,
    candidate: Option<&CandidatePacket>,
    run_error: Option<&str>,
) -> Result<Option<RunnerEnvironmentEvidence>> {
    let expected_eval_ids = lanes
        .iter()
        .filter(|lane| lane.status == "eligible")
        .map(|lane| lane.eval_id.as_str())
        .collect::<BTreeSet<_>>();
    let expected_benchmark_counts = lanes
        .iter()
        .filter(|lane| lane.status == "eligible")
        .filter_map(|lane| {
            lane.benchmark_count
                .map(|count| (lane.eval_id.as_str(), count))
        })
        .collect::<BTreeMap<_, _>>();
    let (runner_environment, results) = if path.is_file() {
        let body = fs::read_to_string(path)
            .with_context(|| format!("read campaign scorecard {}", path.display()))?;
        let value: serde_json::Value = serde_json::from_str(&body)
            .with_context(|| format!("parse campaign scorecard {}", path.display()))?;
        let runner_environment = match value.get("environment") {
            Some(environment) => {
                match serde_json::from_value::<RunnerEnvironmentEvidence>(environment.clone()) {
                    Ok(environment) => environment,
                    Err(error) => {
                        mark_eligible_lanes_failed(
                            lanes,
                            &format!("campaign scorecard environment is invalid: {error}"),
                        );
                        return Ok(None);
                    }
                }
            }
            None => {
                mark_eligible_lanes_failed(lanes, "campaign scorecard lacks environment evidence");
                return Ok(None);
            }
        };
        if let Err(error) = validate_runner_environment(&runner_environment) {
            mark_eligible_lanes_failed(lanes, &error);
            return Ok(Some(runner_environment));
        }
        if let Some(candidate) = candidate {
            let observed = match candidate_packet(repo, Some(Path::new(&candidate.ay_path))) {
                Ok(observed) => observed,
                Err(error) => {
                    mark_eligible_lanes_failed(
                        lanes,
                        &format!("campaign candidate cannot be revalidated: {error:#}"),
                    );
                    return Ok(Some(runner_environment));
                }
            };
            if let Err(error) =
                validate_candidate_binding(candidate, &observed, &runner_environment)
            {
                mark_eligible_lanes_failed(
                    lanes,
                    &format!("campaign candidate provenance mismatch: {error}"),
                );
                return Ok(Some(runner_environment));
            }
        }
        if value.get("mode").and_then(serde_json::Value::as_str) != Some("dev") {
            mark_eligible_lanes_failed(
                lanes,
                "campaign scorecard mode is not the guarded reviewer dev/proxy mode",
            );
            return Ok(Some(runner_environment));
        }
        let results = match value.get("results") {
            Some(serde_json::Value::Array(results)) => results.clone(),
            Some(_) => {
                mark_eligible_lanes_failed(
                    lanes,
                    "campaign scorecard results field is not an array",
                );
                return Ok(Some(runner_environment));
            }
            None => {
                mark_eligible_lanes_failed(lanes, "campaign scorecard lacks results");
                return Ok(Some(runner_environment));
            }
        };
        (Some(runner_environment), results)
    } else {
        (None, Vec::new())
    };

    let mut by_eval = BTreeMap::new();
    let mut structural_errors = Vec::new();
    for (index, row) in results.iter().enumerate() {
        let Some(row) = row.as_object() else {
            structural_errors.push(format!("scorecard result row {index} is not an object"));
            continue;
        };
        let Some(eval_id) = row
            .get("eval_id")
            .and_then(serde_json::Value::as_str)
            .filter(|value| !value.trim().is_empty())
        else {
            structural_errors.push(format!(
                "scorecard result row {index} lacks a non-empty string eval_id"
            ));
            continue;
        };
        if !expected_eval_ids.contains(eval_id) {
            structural_errors.push(format!(
                "scorecard contains unexpected eval result {eval_id:?}"
            ));
            continue;
        }
        if by_eval.contains_key(eval_id) {
            structural_errors.push(format!(
                "scorecard contains duplicate eval result {eval_id:?}"
            ));
            continue;
        }
        let expected_count = expected_benchmark_counts.get(eval_id).copied();
        let validation = ay_bench::runner::preflight_eval_benchmark_inventory(eval_id)
            .map_err(|error| {
                format!(
                    "cannot revalidate the exact current corpus selection for eval {eval_id:?}: {error:#}"
                )
            })
            .and_then(|expected_inventory| {
                validate_scorecard_row_for_run(
                    repo,
                    row,
                    eval_id,
                    profile,
                    runner_environment.as_ref(),
                    expected_count,
                    &expected_inventory,
                )
            });
        by_eval.insert(eval_id.to_string(), validation);
    }

    if !structural_errors.is_empty() {
        mark_eligible_lanes_failed(lanes, &structural_errors.join("; "));
        return Ok(runner_environment);
    }

    for lane in lanes.iter_mut().filter(|lane| lane.status == "eligible") {
        match by_eval.get(&lane.eval_id) {
            Some(Err(error)) => {
                lane.status = "failed".to_string();
                lane.reason = error.clone();
            }
            Some(Ok(evidence)) => {
                lane.status = "passed".to_string();
                lane.reason =
                    "typed scorecard, per-instance verdict, host provenance, and enforced _oom_guard envelope gates passed; proxy evidence only".to_string();
                lane.benchmark_count = Some(evidence.benchmark_count);
                lane.score_competition = Some(evidence.score_competition.clone());
                lane.score = Some(evidence.score.clone());
                lane.solve_summary = Some(evidence.solve_summary.clone());
                lane.evidence_counts = Some(evidence.evidence_counts.clone());
                lane.verdict_evidence_classification =
                    Some(VERDICT_EVIDENCE_CLASSIFICATION.to_string());
                lane.reference_solvers = evidence.reference_solvers.clone();
                lane.results_path = Some(evidence.results_path.clone());
                lane.native_results = Some(evidence.native_results.clone());
                lane.corpus = Some(evidence.corpus.clone());
                lane.enforced_envelope = Some(evidence.enforced_envelope.clone());
            }
            None => {
                lane.status = "failed".to_string();
                lane.reason = run_error
                    .unwrap_or("evaluation produced no scorecard row")
                    .to_string();
            }
        }
    }
    Ok(runner_environment)
}

fn mark_eligible_lanes_failed(lanes: &mut [LanePacket], reason: &str) {
    for lane in lanes.iter_mut().filter(|lane| lane.status == "eligible") {
        lane.status = "failed".to_string();
        lane.reason = reason.to_string();
    }
}

fn validate_scorecard_row(
    row: &serde_json::Map<String, serde_json::Value>,
    eval_id: &str,
) -> std::result::Result<ValidatedScorecardRow, String> {
    match row.get("error") {
        None | Some(serde_json::Value::Null) => {}
        Some(serde_json::Value::String(error)) if !error.trim().is_empty() => {
            return Err(format!("benchmark runner reported an error: {error}"));
        }
        Some(serde_json::Value::String(_)) => {
            return Err("benchmark runner emitted an empty error field".to_string());
        }
        Some(_) => {
            return Err("benchmark runner error field is not a string or null".to_string());
        }
    }

    let expected_competition = expected_score_competition(eval_id)
        .ok_or_else(|| format!("cannot determine score competition for eval {eval_id:?}"))?;
    let competition = row
        .get("competition")
        .and_then(serde_json::Value::as_str)
        .filter(|value| !value.trim().is_empty())
        .ok_or_else(|| "scorecard row lacks a non-empty string competition".to_string())?;
    if competition != expected_competition {
        return Err(format!(
            "scorecard competition {competition:?} does not match eval {eval_id:?} ({expected_competition})"
        ));
    }

    let score = row
        .get("score")
        .cloned()
        .ok_or_else(|| "scorecard row lacks score".to_string())?;
    let solve_summary =
        solve_summary_for_score(&score, competition).map_err(|errors| errors.join("; "))?;
    let evidence_value = row
        .get("evidence")
        .cloned()
        .ok_or_else(|| "scorecard row lacks per-instance evidence summary".to_string())?;
    let evidence_errors = evidence_shape_errors(Some(&evidence_value));
    if !evidence_errors.is_empty() {
        return Err(evidence_errors.join("; "));
    }
    let evidence = serde_json::from_value::<ScorecardEvidence>(evidence_value)
        .map_err(|error| format!("scorecard evidence has an invalid shape: {error}"))?;
    Ok(ValidatedScorecardRow {
        competition: competition.to_string(),
        score,
        solve_summary,
        evidence,
    })
}

fn validate_scorecard_row_for_run(
    repo: &Path,
    row: &serde_json::Map<String, serde_json::Value>,
    eval_id: &str,
    profile: &Profile,
    runner_environment: Option<&RunnerEnvironmentEvidence>,
    expected_benchmark_count: Option<usize>,
    expected_inventory: &ay_bench::runner::EvalBenchmarkInventory,
) -> std::result::Result<ValidatedLaneEvidence, String> {
    let validated_row = validate_scorecard_row(row, eval_id)?;
    let runner_environment = runner_environment
        .ok_or_else(|| "campaign scorecard lacks environment evidence".to_string())?;
    let score_total_u64 = validated_row.solve_summary.total;
    let score_total = usize::try_from(score_total_u64)
        .map_err(|_| "scorecard score total exceeds this host".to_string())?;
    if validated_row.evidence.total != score_total_u64 {
        return Err(format!(
            "scorecard evidence total {} does not match score total {score_total}",
            validated_row.evidence.total
        ));
    }
    validate_expected_score_scope(
        &validated_row.competition,
        &validated_row.score,
        expected_inventory,
    )?;
    let native = validate_native_lane_evidence(
        repo,
        &validated_row.evidence.results_path,
        profile,
        runner_environment,
        expected_benchmark_count,
        score_total,
        &validated_row.competition,
        &validated_row.score,
        &validated_row.evidence,
        expected_inventory,
    )?;
    let expected_domain = expected_native_domain(&validated_row.competition).ok_or_else(|| {
        format!(
            "unsupported score competition {:?}",
            validated_row.competition
        )
    })?;
    if native.corpus.domain != expected_domain {
        return Err(format!(
            "native results domain {:?} does not match score competition {:?} ({expected_domain})",
            native.corpus.domain, validated_row.competition
        ));
    }
    Ok(ValidatedLaneEvidence {
        score_competition: validated_row.competition,
        score: validated_row.score,
        solve_summary: validated_row.solve_summary,
        evidence_counts: EvidenceCountsPacket {
            verified: validated_row.evidence.verified,
            wrong: validated_row.evidence.wrong,
            unverified_definitive: validated_row.evidence.unverified_definitive,
            non_definitive: validated_row.evidence.non_definitive,
            total: validated_row.evidence.total,
        },
        reference_solvers: native.reference_solvers,
        results_path: native.results_path,
        benchmark_count: native.benchmark_count,
        native_results: native.native_results,
        corpus: native.corpus,
        enforced_envelope: native.enforced_envelope,
    })
}

fn validate_expected_score_scope(
    competition: &str,
    score: &serde_json::Value,
    expected: &ay_bench::runner::EvalBenchmarkInventory,
) -> std::result::Result<(), String> {
    if competition != expected.competition {
        return Err(format!(
            "score competition {competition:?} does not match exact eval competition {:?}",
            expected.competition
        ));
    }
    let observed = match competition {
        "SAT-COMP" => None,
        "SMT-COMP" => Some(
            serde_json::from_value::<SmtScoreFields>(score.clone())
                .map_err(|error| format!("read SMT score scope: {error}"))?
                .division,
        ),
        "CHC-COMP" | "HWMCC" => Some(
            serde_json::from_value::<ChcScoreFields>(score.clone())
                .map_err(|error| format!("read {competition} score scope: {error}"))?
                .track,
        ),
        other => return Err(format!("unsupported score competition {other:?}")),
    };
    if observed != expected.score_scope {
        return Err(format!(
            "score scope {:?} does not match exact eval scope {:?}",
            observed, expected.score_scope
        ));
    }
    Ok(())
}

fn validate_native_lane_evidence(
    repo: &Path,
    results_path: &str,
    profile: &Profile,
    runner_environment: &RunnerEnvironmentEvidence,
    expected_benchmark_count: Option<usize>,
    score_total: usize,
    competition: &str,
    score: &serde_json::Value,
    evidence: &ScorecardEvidence,
    expected_inventory: &ay_bench::runner::EvalBenchmarkInventory,
) -> std::result::Result<ValidatedNativeLaneEvidence, String> {
    let requested_path = Path::new(results_path);
    let path = if requested_path.is_absolute() {
        requested_path.to_path_buf()
    } else {
        repo.join(requested_path)
    };
    let (document, native_results) = read_native_evidence_with_identity(&path)?;
    validate_runner_environment(&document.environment)?;
    if document.environment != *runner_environment {
        return Err(
            "native results environment does not match the campaign scorecard environment"
                .to_string(),
        );
    }
    if document.settings.benchmark_count != score_total {
        return Err(format!(
            "native results benchmark_count {} does not match score total {score_total}",
            document.settings.benchmark_count
        ));
    }
    if let Some(expected) = expected_benchmark_count {
        if document.settings.benchmark_count != expected {
            return Err(format!(
                "native results benchmark_count {} does not match preflight count {expected}",
                document.settings.benchmark_count
            ));
        }
    }
    validate_reviewer_full_native_settings(&document.settings)?;
    validate_native_per_instance_evidence(&document, competition, score, evidence)?;
    validate_native_eval_binding(&document, expected_inventory)?;
    if (document.settings.timeout_sec - profile.timeout_sec).abs() > f64::EPSILON {
        return Err(format!(
            "native results timeout {} does not match profile timeout {}",
            document.settings.timeout_sec, profile.timeout_sec
        ));
    }
    let plan = &document.settings.resource_plan;
    if plan.requested_jobs != profile.max_jobs || plan.jobs != profile.max_jobs {
        return Err(format!(
            "native results jobs requested/admitted {}/{} do not match profile max_jobs {}",
            plan.requested_jobs, plan.jobs, profile.max_jobs
        ));
    }
    if plan.memlimit_mb_per_child == 0 || plan.memlimit_mb_per_child > profile.per_child_memory_mib
    {
        return Err(format!(
            "native results memory envelope {} MiB exceeds profile cap {} MiB",
            plan.memlimit_mb_per_child, profile.per_child_memory_mib
        ));
    }
    if plan.nbcore_per_child == 0 || plan.nbcore_per_child > profile.per_child_cores {
        return Err(format!(
            "native results core envelope {} exceeds profile cap {}",
            plan.nbcore_per_child, profile.per_child_cores
        ));
    }
    if document.settings.resource_enforcement != ay_bench::ENFORCEMENT_AY_MEMORY_RSS_V1 {
        return Err(format!(
            "native results use unexpected resource enforcement {:?}",
            document.settings.resource_enforcement
        ));
    }
    let expected_planner = repo.join("scripts/_oom_guard.py");
    let actual_planner = Path::new(&plan.planner);
    let planner_matches = match (
        fs::canonicalize(&expected_planner),
        fs::canonicalize(actual_planner),
    ) {
        (Ok(expected), Ok(actual)) => expected == actual,
        _ => actual_planner == expected_planner,
    };
    if !planner_matches {
        return Err(format!(
            "native results resource planner {} is not {}",
            actual_planner.display(),
            expected_planner.display()
        ));
    }
    let effective_envelope = ay_bench::effective_execution_envelope(
        plan,
        &document.settings.resource_enforcement,
        document.settings.timeout_sec,
    )
    .map_err(|error| format!("native results resource envelope is invalid: {error}"))?;
    let corpus = validate_native_corpus_identity(&document.settings, expected_inventory)?;
    let reference_solvers = validate_native_reference_solvers(
        &document.references,
        plan,
        document.settings.timeout_sec,
    )?;

    Ok(ValidatedNativeLaneEvidence {
        results_path: path.display().to_string(),
        benchmark_count: document.settings.benchmark_count,
        native_results,
        corpus,
        reference_solvers,
        enforced_envelope: EnforcedEnvelopePacket {
            timeout_sec: document.settings.timeout_sec,
            resource_plan: plan.clone(),
            resource_enforcement: document.settings.resource_enforcement,
            effective_envelope,
        },
    })
}

fn validate_reviewer_full_native_settings(
    settings: &NativeSettingsEvidence,
) -> std::result::Result<(), String> {
    if settings.runs != 1 {
        return Err(format!(
            "native results contain {} benchmark repetitions, but reviewer-full executes exactly one",
            settings.runs
        ));
    }
    if settings.shard.is_some() {
        return Err(
            "native results contain shard metadata, but reviewer-full executes the complete selection"
                .to_string(),
        );
    }
    Ok(())
}

fn validate_native_eval_binding(
    document: &NativeEvidenceDocument,
    expected: &ay_bench::runner::EvalBenchmarkInventory,
) -> std::result::Result<(), String> {
    if document.settings.domain != expected.domain {
        return Err(format!(
            "native results domain {:?} does not match eval inventory domain {:?}",
            document.settings.domain, expected.domain
        ));
    }
    if document.items.len() != expected.items.len() {
        return Err(format!(
            "native results contain {} items, but the exact current eval selection contains {}",
            document.items.len(),
            expected.items.len()
        ));
    }
    if !valid_sha256_identity(&expected.content_inventory_sha256) {
        return Err("current eval inventory has an invalid content SHA-256".to_string());
    }

    let recorded_root = Path::new(&document.settings.benchmarks_dir);
    if !recorded_root.is_absolute() {
        return Err(format!(
            "native results benchmarks_dir is not absolute: {}",
            recorded_root.display()
        ));
    }
    let canonical_recorded_root = fs::canonicalize(recorded_root).map_err(|error| {
        format!(
            "canonicalize native results benchmarks_dir {}: {error}",
            recorded_root.display()
        )
    })?;
    let expected_root = Path::new(&expected.canonical_benchmarks_dir);
    if canonical_recorded_root != expected_root {
        return Err(format!(
            "native results benchmarks_dir {} resolves to {}, expected exact eval root {}",
            recorded_root.display(),
            canonical_recorded_root.display(),
            expected_root.display()
        ));
    }

    for (index, ((item, prepared), expected_item)) in document
        .items
        .iter()
        .zip(&document.preprocessing)
        .zip(&expected.items)
        .enumerate()
    {
        if item.file != expected_item.benchmark_id {
            return Err(format!(
                "native result item {index} has benchmark ID {:?}, expected {:?}",
                item.file, expected_item.benchmark_id
            ));
        }
        if item.benchmark_path != expected_item.canonical_path {
            return Err(format!(
                "native result item {:?} has source path {:?}, expected exact current path {:?}",
                item.file, item.benchmark_path, expected_item.canonical_path
            ));
        }
        if item.benchmark_content_hash.as_deref() != Some(expected_item.source_sha256.as_str()) {
            return Err(format!(
                "native result item {:?} source SHA-256 does not match the exact current eval source",
                item.file
            ));
        }
        if prepared.source_hash != expected_item.source_sha256
            || prepared.source_bytes != expected_item.source_size_bytes
        {
            return Err(format!(
                "native preprocessing identity {:?} does not match the exact current eval source bytes",
                item.file
            ));
        }
    }
    Ok(())
}

fn validate_native_per_instance_evidence(
    document: &NativeEvidenceDocument,
    competition: &str,
    score: &serde_json::Value,
    evidence: &ScorecardEvidence,
) -> std::result::Result<(), String> {
    let expected_count = document.settings.benchmark_count;
    if document.items.len() != expected_count {
        return Err(format!(
            "native results contain {} per-instance items, expected {expected_count}",
            document.items.len()
        ));
    }
    if document.preprocessing.len() != expected_count {
        return Err(format!(
            "native results contain {} preprocessing identities, expected {expected_count}",
            document.preprocessing.len()
        ));
    }
    if document.settings.runs == 0 {
        return Err("native results settings contain zero benchmark repetitions".to_string());
    }

    let mut item_ids = BTreeSet::new();
    let mut source_paths = BTreeSet::new();
    let mut preprocessing_ids = BTreeSet::new();
    for (index, (item, prepared)) in document
        .items
        .iter()
        .zip(&document.preprocessing)
        .enumerate()
    {
        if item.file.is_empty() {
            return Err(format!(
                "native result item {index} has an empty benchmark ID"
            ));
        }
        if !item_ids.insert(item.file.as_str()) {
            return Err(format!(
                "native results repeat benchmark ID {:?}",
                item.file
            ));
        }
        if item.benchmark_path.is_empty() {
            return Err(format!(
                "native result item {:?} has an empty benchmark source path",
                item.file
            ));
        }
        if !source_paths.insert(item.benchmark_path.as_str()) {
            return Err(format!(
                "native results repeat benchmark source path {:?}",
                item.benchmark_path
            ));
        }
        if prepared.benchmark_path.is_empty() {
            return Err(format!(
                "native preprocessing identity {index} has an empty benchmark ID"
            ));
        }
        if !preprocessing_ids.insert(prepared.benchmark_path.as_str()) {
            return Err(format!(
                "native preprocessing repeats benchmark ID {:?}",
                prepared.benchmark_path
            ));
        }
        if item.file != prepared.benchmark_path {
            return Err(format!(
                "native result item {:?} does not match preprocessing identity {:?} at index {index}",
                item.file, prepared.benchmark_path
            ));
        }

        let benchmark_hash = item.benchmark_content_hash.as_deref().ok_or_else(|| {
            format!(
                "native result item {:?} lacks benchmark_content_hash",
                item.file
            )
        })?;
        validate_required_sha256(benchmark_hash, "benchmark_content_hash", &item.file)?;
        validate_required_sha256(
            &prepared.source_hash,
            "preprocessing source_hash",
            &item.file,
        )?;
        if benchmark_hash != prepared.source_hash {
            return Err(format!(
                "native result item {:?} benchmark_content_hash does not match preprocessing source_hash",
                item.file
            ));
        }

        let solver_input_hash = item
            .solver_input_hash
            .as_deref()
            .ok_or_else(|| format!("native result item {:?} lacks solver_input_hash", item.file))?;
        validate_required_sha256(solver_input_hash, "solver_input_hash", &item.file)?;
        validate_required_sha256(
            &prepared.solver_input_hash,
            "preprocessing solver_input_hash",
            &item.file,
        )?;
        if solver_input_hash != prepared.solver_input_hash {
            return Err(format!(
                "native result item {:?} solver_input_hash does not match preprocessing solver_input_hash",
                item.file
            ));
        }
        if !matches!(
            item.solver_input_path.as_deref(),
            Some(path) if !path.is_empty()
        ) {
            return Err(format!(
                "native result item {:?} lacks a non-empty solver_input_path",
                item.file
            ));
        }

        validate_native_result(&item.result, "AY result", &item.file)?;
        match (item.expected_source.as_str(), item.expected.as_deref()) {
            ("unknown", None) => {}
            ("header" | "path" | "header+path", Some("sat" | "unsat")) => {}
            ("header" | "path" | "header+path", None) => {
                return Err(format!(
                    "native result item {:?} has authoritative expected source {:?} without a verdict",
                    item.file, item.expected_source
                ));
            }
            ("unknown", Some(_)) => {
                return Err(format!(
                    "native result item {:?} has an expected verdict from unknown source",
                    item.file
                ));
            }
            (_, Some(expected)) => {
                return Err(format!(
                    "native result item {:?} has unsupported expected verdict/source {:?}/{:?}",
                    item.file, expected, item.expected_source
                ));
            }
            (_, None) => {
                return Err(format!(
                    "native result item {:?} has unsupported expected source {:?}",
                    item.file, item.expected_source
                ));
            }
        }
        if !item.time_sec.is_finite() || item.time_sec < 0.0 {
            return Err(format!(
                "native result item {:?} has invalid wall time {}",
                item.file, item.time_sec
            ));
        }
        if !item.cpu_time_sec.is_finite() || item.cpu_time_sec < 0.0 {
            return Err(format!(
                "native result item {:?} has invalid CPU time {}",
                item.file, item.cpu_time_sec
            ));
        }
    }

    let comparison_index = validate_native_reference_comparisons(document)?;
    let recomputed_score = recompute_native_score(
        competition,
        score,
        &document.items,
        document.settings.timeout_sec,
    )?;
    if recomputed_score != *score {
        return Err(format!(
            "native per-instance score does not exactly match scorecard score: recomputed {recomputed_score}, scorecard {score}"
        ));
    }

    let mut classified = EvidenceCountsPacket {
        verified: 0,
        wrong: 0,
        unverified_definitive: 0,
        non_definitive: 0,
        total: u64::try_from(document.items.len())
            .map_err(|_| "native per-instance count exceeds u64".to_string())?,
    };
    for item in &document.items {
        let agreements = comparison_index.get(&item.file);
        let verifier = if agreements
            .is_some_and(|values| values.iter().any(|agreement| agreement == "disagree"))
        {
            0
        } else if agreements
            .is_some_and(|values| values.iter().any(|agreement| agreement == "agree"))
        {
            1
        } else if matches!(
            item.expected_source.as_str(),
            "header" | "path" | "header+path"
        ) && item
            .expected
            .as_deref()
            .is_some_and(|expected| expected == item.result)
        {
            1
        } else if matches!(item.result.as_str(), "sat" | "unsat")
            && matches!(
                item.expected_source.as_str(),
                "header" | "path" | "header+path"
            )
        {
            0
        } else {
            -1
        };
        match verifier {
            1 => classified.verified += 1,
            0 => classified.wrong += 1,
            _ if matches!(item.result.as_str(), "sat" | "unsat") => {
                classified.unverified_definitive += 1;
            }
            _ => classified.non_definitive += 1,
        }
    }
    let reported = EvidenceCountsPacket {
        verified: evidence.verified,
        wrong: evidence.wrong,
        unverified_definitive: evidence.unverified_definitive,
        non_definitive: evidence.non_definitive,
        total: evidence.total,
    };
    if classified != reported {
        return Err(format!(
            "native per-instance verdict classification {:?} does not match scorecard evidence {:?}",
            classified, reported
        ));
    }
    Ok(())
}

fn validate_required_sha256(
    value: &str,
    field: &str,
    benchmark_id: &str,
) -> std::result::Result<(), String> {
    if !valid_sha256_identity(value) {
        return Err(format!(
            "native result item {benchmark_id:?} has noncanonical {field} {value:?}"
        ));
    }
    Ok(())
}

fn validate_native_result(
    result: &str,
    label: &str,
    benchmark_id: &str,
) -> std::result::Result<(), String> {
    if !matches!(
        result,
        "sat" | "unsat" | "unknown" | "timeout" | "memout" | "error"
    ) {
        return Err(format!(
            "native result item {benchmark_id:?} has unsupported {label} {result:?}"
        ));
    }
    Ok(())
}

fn native_agreement(ay: &str, reference: &str) -> &'static str {
    let ay_definitive = matches!(ay, "sat" | "unsat");
    let reference_definitive = matches!(reference, "sat" | "unsat");
    match (ay_definitive, reference_definitive) {
        (true, true) if ay == reference => "agree",
        (true, true) => "disagree",
        (true, false) => "ay_only",
        (false, true) => "ref_only",
        (false, false) => "both_unknown",
    }
}

fn validate_native_reference_comparisons(
    document: &NativeEvidenceDocument,
) -> std::result::Result<BTreeMap<String, Vec<String>>, String> {
    if document.references.is_empty() {
        if document.comparisons.is_some() || document.reference_comparisons.is_some() {
            return Err(
                "native results contain comparison rows without reference solver summaries"
                    .to_string(),
            );
        }
        return Ok(BTreeMap::new());
    }

    let groups = document.reference_comparisons.as_deref().ok_or_else(|| {
        "native results lack per-instance reference_comparisons for declared reference solvers"
            .to_string()
    })?;
    if groups.len() != document.references.len() {
        return Err(format!(
            "native results contain {} reference comparison groups for {} reference solver summaries",
            groups.len(),
            document.references.len()
        ));
    }
    let legacy = document.comparisons.as_deref().ok_or_else(|| {
        "native results lack the actual-schema first-reference comparisons field".to_string()
    })?;
    if groups.first().map(|first| first.items.as_slice()) != Some(legacy) {
        return Err(
            "native results legacy comparisons do not match the first reference comparison group"
                .to_string(),
        );
    }

    let item_by_id = document
        .items
        .iter()
        .map(|item| (item.file.as_str(), item))
        .collect::<BTreeMap<_, _>>();
    let mut comparison_index = document
        .items
        .iter()
        .map(|item| (item.file.clone(), Vec::new()))
        .collect::<BTreeMap<_, _>>();
    let mut reference_names = BTreeSet::new();
    for (group, summary) in groups.iter().zip(&document.references) {
        if group.reference_solver != summary.reference_solver {
            return Err(format!(
                "native reference comparison group {:?} does not match summary {:?}",
                group.reference_solver, summary.reference_solver
            ));
        }
        if !reference_names.insert(group.reference_solver.as_str()) {
            return Err(format!(
                "native results repeat reference comparison group {:?}",
                group.reference_solver
            ));
        }
        if group.items.len() != document.items.len() {
            return Err(format!(
                "native reference comparison group {:?} contains {} items, expected {}",
                group.reference_solver,
                group.items.len(),
                document.items.len()
            ));
        }
        let mut seen = BTreeSet::new();
        let mut agree = 0_u64;
        let mut disagree = 0_u64;
        let mut ay_only = 0_u64;
        let mut ref_only = 0_u64;
        for comparison in &group.items {
            if !seen.insert(comparison.file.as_str()) {
                return Err(format!(
                    "native reference comparison group {:?} repeats benchmark ID {:?}",
                    group.reference_solver, comparison.file
                ));
            }
            let item = item_by_id.get(comparison.file.as_str()).ok_or_else(|| {
                format!(
                    "native reference comparison group {:?} contains unknown benchmark ID {:?}",
                    group.reference_solver, comparison.file
                )
            })?;
            if comparison.ay_result != item.result {
                return Err(format!(
                    "native reference comparison for {:?} reports AY result {:?}, expected {:?}",
                    comparison.file, comparison.ay_result, item.result
                ));
            }
            let item_solver_hash = item.solver_input_hash.as_deref().ok_or_else(|| {
                format!("native result item {:?} lacks solver_input_hash", item.file)
            })?;
            validate_required_sha256(
                &comparison.solver_input_hash,
                "reference comparison solver_input_hash",
                &comparison.file,
            )?;
            if comparison.solver_input_hash != item_solver_hash {
                return Err(format!(
                    "native reference comparison for {:?} uses a different solver_input_hash",
                    comparison.file
                ));
            }
            validate_native_result(&comparison.ref_result, "reference result", &comparison.file)?;
            if comparison.reference_runs.is_empty() {
                return Err(format!(
                    "native reference comparison for {:?} has no reference run evidence",
                    comparison.file
                ));
            }
            let expected_runs = usize::try_from(document.settings.runs)
                .map_err(|_| "native benchmark repetition count exceeds usize".to_string())?;
            if comparison.reference_runs.len() != expected_runs {
                return Err(format!(
                    "native reference comparison for {:?} contains {} runs, expected {expected_runs}",
                    comparison.file,
                    comparison.reference_runs.len()
                ));
            }
            for run in &comparison.reference_runs {
                validate_native_result(&run.result, "reference run result", &comparison.file)?;
                if run.solver_input_path.is_empty() {
                    return Err(format!(
                        "native reference run for {:?} has an empty solver input path",
                        comparison.file
                    ));
                }
                validate_required_sha256(
                    &run.solver_input_hash,
                    "reference run solver_input_hash",
                    &comparison.file,
                )?;
                validate_required_sha256(
                    &run.stdout_sha256,
                    "reference run stdout_sha256",
                    &comparison.file,
                )?;
                validate_required_sha256(
                    &run.stderr_sha256,
                    "reference run stderr_sha256",
                    &comparison.file,
                )?;
                if run.solver_input_hash != item_solver_hash {
                    return Err(format!(
                        "native reference run for {:?} uses a different solver_input_hash",
                        comparison.file
                    ));
                }
                if Some(run.solver_input_path.as_str()) != item.solver_input_path.as_deref() {
                    return Err(format!(
                        "native reference run for {:?} uses a different solver_input_path",
                        comparison.file
                    ));
                }
            }
            let first_run_result = comparison.reference_runs[0].result.as_str();
            let expected_ref_result = if comparison
                .reference_runs
                .iter()
                .all(|run| run.result == first_run_result)
            {
                first_run_result
            } else {
                "error"
            };
            if comparison.ref_result != expected_ref_result {
                return Err(format!(
                    "native reference comparison for {:?} reports representative result {:?}, but its retained runs require {expected_ref_result:?}",
                    comparison.file, comparison.ref_result
                ));
            }
            let expected_agreement = native_agreement(&comparison.ay_result, expected_ref_result);
            if comparison.agreement != expected_agreement {
                return Err(format!(
                    "native reference comparison for {:?} has agreement {:?}, expected {expected_agreement:?}",
                    comparison.file, comparison.agreement
                ));
            }
            match comparison.agreement.as_str() {
                "agree" => agree += 1,
                "disagree" => disagree += 1,
                "ay_only" => ay_only += 1,
                "ref_only" => ref_only += 1,
                "both_unknown" => {}
                _ => unreachable!("agreement was recomputed above"),
            }
            comparison_index
                .get_mut(&comparison.file)
                .ok_or_else(|| {
                    format!(
                        "native reference comparison group {:?} contains unknown benchmark ID {:?}",
                        group.reference_solver, comparison.file
                    )
                })?
                .push(comparison.agreement.clone());
        }
        if agree != summary.agree
            || disagree != summary.disagree
            || ay_only != summary.ay_only
            || ref_only != summary.ref_only
        {
            return Err(format!(
                "native reference comparison counters for {:?} ({agree}/{disagree}/{ay_only}/{ref_only}) do not match summary ({}/{}/{}/{})",
                group.reference_solver,
                summary.agree,
                summary.disagree,
                summary.ay_only,
                summary.ref_only
            ));
        }
    }
    Ok(comparison_index)
}

fn native_scoring_items(items: &[NativeResultItemEvidence]) -> Vec<ay_bench::scoring::ResultItem> {
    items
        .iter()
        .map(|item| ay_bench::scoring::ResultItem {
            file: Some(item.file.clone()),
            expected: item.expected.clone(),
            result: Some(item.result.clone()),
            time_sec: Some(item.time_sec),
            cpu_time_sec: Some(item.cpu_time_sec),
            exit_code: None,
            correct: None,
        })
        .collect()
}

fn recompute_native_score(
    competition: &str,
    score: &serde_json::Value,
    items: &[NativeResultItemEvidence],
    timeout_sec: f64,
) -> std::result::Result<serde_json::Value, String> {
    let items = native_scoring_items(items);
    let recomputed = match competition {
        "SAT-COMP" => serde_json::to_value(ay_bench::scoring::score_sat(&items, timeout_sec)),
        "SMT-COMP" => {
            let typed = serde_json::from_value::<SmtScoreFields>(score.clone())
                .map_err(|error| format!("read SMT score metadata for recomputation: {error}"))?;
            serde_json::to_value(ay_bench::scoring::score_smt(
                &items,
                timeout_sec,
                &typed.division,
            ))
        }
        "CHC-COMP" => {
            let typed = serde_json::from_value::<ChcScoreFields>(score.clone())
                .map_err(|error| format!("read CHC score metadata for recomputation: {error}"))?;
            serde_json::to_value(ay_bench::scoring::score_chc(
                &items,
                timeout_sec,
                &typed.track,
            ))
        }
        "HWMCC" => {
            let typed = serde_json::from_value::<ChcScoreFields>(score.clone())
                .map_err(|error| format!("read HWMCC score metadata for recomputation: {error}"))?;
            serde_json::to_value(ay_bench::scoring::score_hwmcc(
                &items,
                timeout_sec,
                &typed.track,
            ))
        }
        other => {
            return Err(format!(
                "cannot recompute unsupported competition {other:?}"
            ))
        }
    }
    .map_err(|error| format!("serialize recomputed native score: {error}"))?;
    Ok(recomputed)
}

struct DigestingReader<R> {
    inner: R,
    hasher: Sha256,
    size_bytes: u64,
}

impl<R> DigestingReader<R> {
    fn new(inner: R) -> Self {
        Self {
            inner,
            hasher: Sha256::new(),
            size_bytes: 0,
        }
    }

    fn identity(&self) -> NativeResultsIdentityPacket {
        NativeResultsIdentityPacket {
            sha256: format!("sha256:{:x}", self.hasher.clone().finalize()),
            size_bytes: self.size_bytes,
        }
    }
}

impl<R: std::io::Read> std::io::Read for DigestingReader<R> {
    fn read(&mut self, buffer: &mut [u8]) -> std::io::Result<usize> {
        let read = self.inner.read(buffer)?;
        let read_u64 = u64::try_from(read).map_err(|_| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "native results read length exceeds u64",
            )
        })?;
        self.size_bytes = self.size_bytes.checked_add(read_u64).ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "native results size exceeds u64",
            )
        })?;
        self.hasher.update(&buffer[..read]);
        Ok(read)
    }
}

fn read_native_evidence_with_identity(
    path: &Path,
) -> std::result::Result<(NativeEvidenceDocument, NativeResultsIdentityPacket), String> {
    let path_metadata = fs::symlink_metadata(path).map_err(|error| {
        format!(
            "inspect native results evidence {}: {error}",
            path.display()
        )
    })?;
    if !path_metadata.file_type().is_file() || path_metadata.file_type().is_symlink() {
        return Err(format!(
            "native results evidence is not a non-symlink regular file: {}",
            path.display()
        ));
    }
    let file = fs::File::open(path)
        .map_err(|error| format!("open native results evidence {}: {error}", path.display()))?;
    let metadata_before = file
        .metadata()
        .map_err(|error| format!("stat native results evidence {}: {error}", path.display()))?;
    let modified_before = metadata_before.modified().ok();
    let mut reader = DigestingReader::new(BufReader::new(file));
    let document: NativeEvidenceDocument = serde_json::from_reader(&mut reader)
        .map_err(|error| format!("parse native results evidence {}: {error}", path.display()))?;
    std::io::copy(&mut reader, &mut std::io::sink())
        .map_err(|error| format!("finish hashing native results {}: {error}", path.display()))?;
    let metadata_after =
        reader.inner.get_ref().metadata().map_err(|error| {
            format!("restat native results evidence {}: {error}", path.display())
        })?;
    let identity = reader.identity();
    if metadata_before.len() != metadata_after.len()
        || metadata_after.len() != identity.size_bytes
        || modified_before
            .zip(metadata_after.modified().ok())
            .is_some_and(|(before, after)| before != after)
    {
        return Err(format!(
            "native results evidence changed while validating: {}",
            path.display()
        ));
    }
    if !valid_sha256_identity(&identity.sha256) || identity.size_bytes == 0 {
        return Err(format!(
            "native results evidence has an invalid file identity: {}",
            path.display()
        ));
    }
    Ok((document, identity))
}

fn validate_native_corpus_identity(
    settings: &NativeSettingsEvidence,
    expected: &ay_bench::runner::EvalBenchmarkInventory,
) -> std::result::Result<CorpusIdentityPacket, String> {
    if settings.benchmarks_dir.trim().is_empty() {
        return Err("native results benchmarks_dir is empty".to_string());
    }
    if settings.domain.trim().is_empty() {
        return Err("native results domain is empty".to_string());
    }
    if settings.benchmark_count == 0 {
        return Err("native results benchmark_count is zero".to_string());
    }
    if let Some(shard) = &settings.shard {
        validate_native_shard_identity(shard, settings.benchmark_count)?;
    }
    if !valid_sha256_identity(&expected.content_inventory_sha256) {
        return Err("native results current corpus inventory SHA-256 is invalid".to_string());
    }
    Ok(CorpusIdentityPacket {
        benchmarks_dir: settings.benchmarks_dir.clone(),
        domain: settings.domain.clone(),
        benchmark_count: settings.benchmark_count,
        content_inventory_sha256: expected.content_inventory_sha256.clone(),
        shard: settings.shard.clone(),
    })
}

fn validate_native_reference_solvers(
    references: &[NativeReferenceEvidence],
    resource_plan: &ay_bench::ResourcePlan,
    timeout_sec: f64,
) -> std::result::Result<Vec<ReferenceSolverProvenancePacket>, String> {
    let expected_envelope = ay_bench::effective_execution_envelope(
        resource_plan,
        ay_bench::ENFORCEMENT_RSS_WATCHDOG_V1,
        timeout_sec,
    )
    .map_err(|error| format!("reference solver resource envelope is invalid: {error}"))?;
    let mut names = BTreeSet::new();
    let mut paths = BTreeSet::new();
    let mut packets = Vec::with_capacity(references.len());
    for reference in references {
        if reference.reference_solver.trim().is_empty()
            || reference.reference_solver_version.trim().is_empty()
            || reference.reference_solver_build_version.trim().is_empty()
            || reference.reference_solver_build_commit.trim().is_empty()
            || reference
                .reference_solver_build_datetime_utc
                .trim()
                .is_empty()
            || reference.reference_solver_build_stamp.trim().is_empty()
        {
            return Err("native reference solver contains an empty provenance field".to_string());
        }
        if !names.insert(reference.reference_solver.as_str()) {
            return Err(format!(
                "native results repeat reference solver name {:?}",
                reference.reference_solver
            ));
        }
        if !valid_sha256_identity(&reference.reference_solver_sha256)
            || reference.reference_solver_size_bytes == 0
        {
            return Err(format!(
                "native reference solver {:?} has an invalid file identity",
                reference.reference_solver
            ));
        }
        let recorded_path = Path::new(&reference.reference_solver_path);
        if !recorded_path.is_absolute() {
            return Err(format!(
                "native reference solver {:?} path is not absolute",
                reference.reference_solver
            ));
        }
        let canonical = fs::canonicalize(recorded_path).map_err(|error| {
            format!(
                "canonicalize native reference solver {:?} {}: {error}",
                reference.reference_solver,
                recorded_path.display()
            )
        })?;
        if canonical != recorded_path {
            return Err(format!(
                "native reference solver {:?} path is not canonical: {}",
                reference.reference_solver,
                recorded_path.display()
            ));
        }
        if !is_executable_file(&canonical) {
            return Err(format!(
                "native reference solver {:?} is missing, non-regular, or non-executable: {}",
                reference.reference_solver,
                canonical.display()
            ));
        }
        if !paths.insert(canonical.clone()) {
            return Err(format!(
                "native results repeat reference solver path {}",
                canonical.display()
            ));
        }
        let (observed_sha256, observed_size) = file_identity(&canonical, "native reference solver")
            .map_err(|error| format!("authenticate native reference solver: {error:#}"))?;
        if observed_sha256 != reference.reference_solver_sha256
            || observed_size != reference.reference_solver_size_bytes
        {
            return Err(format!(
                "native reference solver {:?} changed after execution",
                reference.reference_solver
            ));
        }
        if reference.reference_resource_enforcement != ay_bench::ENFORCEMENT_RSS_WATCHDOG_V1 {
            return Err(format!(
                "native reference solver {:?} uses unexpected resource enforcement {:?}",
                reference.reference_solver, reference.reference_resource_enforcement
            ));
        }
        if reference.reference_resource_envelope != expected_envelope {
            return Err(format!(
                "native reference solver {:?} resource envelope does not match the candidate envelope",
                reference.reference_solver
            ));
        }
        packets.push(ReferenceSolverProvenancePacket {
            name: reference.reference_solver.clone(),
            canonical_path: canonical.display().to_string(),
            sha256: reference.reference_solver_sha256.clone(),
            size_bytes: reference.reference_solver_size_bytes,
            version: reference.reference_solver_version.clone(),
            build_version: reference.reference_solver_build_version.clone(),
            build_commit: reference.reference_solver_build_commit.clone(),
            build_datetime_utc: reference.reference_solver_build_datetime_utc.clone(),
            build_stamp: reference.reference_solver_build_stamp.clone(),
            resource_enforcement: reference.reference_resource_enforcement.clone(),
            resource_envelope: reference.reference_resource_envelope.clone(),
        });
    }
    Ok(packets)
}

fn validate_native_shard_identity(
    shard: &NativeShardIdentityPacket,
    benchmark_count: usize,
) -> std::result::Result<(), String> {
    if shard.shard_size == 0
        || shard.shard_count == 0
        || shard.corpus_benchmark_count == 0
        || shard.selected_benchmark_count == 0
    {
        return Err("native results shard contains a zero count".to_string());
    }
    if shard.shard_index >= shard.shard_count
        || shard.requested_index % shard.shard_count != shard.shard_index
    {
        return Err("native results shard indices are inconsistent".to_string());
    }
    let expected_shard_count = (shard.corpus_benchmark_count - 1) / shard.shard_size + 1;
    if shard.shard_count != expected_shard_count {
        return Err("native results shard_count is inconsistent with its corpus".to_string());
    }
    let start = shard
        .shard_index
        .checked_mul(shard.shard_size)
        .ok_or_else(|| "native results shard start overflows".to_string())?;
    let end = start
        .checked_add(shard.shard_size)
        .map(|value| value.min(shard.corpus_benchmark_count))
        .ok_or_else(|| "native results shard end overflows".to_string())?;
    let expected_selected = end
        .checked_sub(start)
        .ok_or_else(|| "native results shard range is invalid".to_string())?;
    if shard.selected_benchmark_count != expected_selected
        || shard.selected_benchmark_count != benchmark_count
    {
        return Err("native results shard selected count is inconsistent".to_string());
    }
    if shard.selector != "sorted-normalized-id-contiguous-v1" {
        return Err("native results shard selector is unsupported".to_string());
    }
    if !valid_sha256_identity(&shard.corpus_path_inventory_sha256) {
        return Err("native results shard has an invalid corpus inventory SHA-256".to_string());
    }
    Ok(())
}

fn valid_sha256_identity(value: &str) -> bool {
    let digest = value.strip_prefix("sha256:").unwrap_or_default();
    digest.len() == 64
        && digest
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
}

fn validate_runner_environment(
    environment: &RunnerEnvironmentEvidence,
) -> std::result::Result<(), String> {
    if environment.timestamp.trim().is_empty()
        || environment.git_commit.trim().is_empty()
        || environment.ay_path.trim().is_empty()
        || environment.ay_sha256.trim().is_empty()
        || environment.ay_version.trim().is_empty()
        || environment.ay_build_version.trim().is_empty()
        || environment.ay_build_commit.trim().is_empty()
        || environment.ay_build_datetime_utc.trim().is_empty()
        || environment.ay_build_stamp.trim().is_empty()
        || environment.hostname.trim().is_empty()
        || environment.os.trim().is_empty()
        || environment.arch.trim().is_empty()
        || environment.cpu_model.trim().is_empty()
    {
        return Err("runner environment contains an empty provenance field".to_string());
    }
    if environment.ay_size_bytes == 0 || environment.cpu_count == 0 || environment.memory_bytes == 0
    {
        return Err("runner environment contains a zero machine/binary field".to_string());
    }
    if !valid_full_git_commit(&environment.git_commit) {
        return Err("runner environment contains an invalid source git commit".to_string());
    }
    if environment.git_dirty != Some(false) || !environment.comparable_git_state {
        return Err(
            "runner environment was captured from a dirty, unknown, or non-comparable git state"
                .to_string(),
        );
    }
    let sha256 = environment
        .ay_sha256
        .strip_prefix("sha256:")
        .unwrap_or_default();
    if sha256.len() != 64
        || !sha256
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    {
        return Err("runner environment contains an invalid AY SHA-256".to_string());
    }
    if !environment
        .load_avg
        .iter()
        .all(|value| value.is_finite() && *value >= 0.0)
    {
        return Err("runner environment load averages are invalid".to_string());
    }
    Ok(())
}

fn validate_candidate_binding(
    expected: &CandidatePacket,
    observed: &CandidatePacket,
    environment: &RunnerEnvironmentEvidence,
) -> std::result::Result<(), String> {
    if expected.git_dirty {
        return Err("candidate source checkout was dirty before execution".to_string());
    }
    if observed.git_dirty {
        return Err("candidate source checkout became dirty during execution".to_string());
    }
    if !valid_full_git_commit(&expected.git_commit) {
        return Err("candidate source commit is not an exact 40-hex commit".to_string());
    }
    if expected.git_commit != observed.git_commit {
        return Err(format!(
            "candidate source commit changed during execution (expected {}, found {})",
            expected.git_commit, observed.git_commit
        ));
    }
    if expected.ay_path != observed.ay_path {
        return Err(format!(
            "candidate canonical path changed during execution (expected {}, found {})",
            expected.ay_path, observed.ay_path
        ));
    }
    if expected.ay_sha256.is_none() || expected.ay_sha256 != observed.ay_sha256 {
        return Err(format!(
            "candidate SHA-256 changed during execution (expected {:?}, found {:?})",
            expected.ay_sha256, observed.ay_sha256
        ));
    }
    if expected.ay_size_bytes.is_none() || expected.ay_size_bytes != observed.ay_size_bytes {
        return Err(format!(
            "candidate size changed during execution (expected {:?}, found {:?})",
            expected.ay_size_bytes, observed.ay_size_bytes
        ));
    }
    let Some(expected_build_commit) = expected.ay_build_commit.as_deref() else {
        return Err("candidate AY version output lacks build.commit".to_string());
    };
    if expected.ay_build_commit != observed.ay_build_commit {
        return Err(format!(
            "candidate AY build commit changed during execution (expected {:?}, found {:?})",
            expected.ay_build_commit, observed.ay_build_commit
        ));
    }
    if expected_build_commit != expected.git_commit {
        return Err(format!(
            "candidate AY build commit {} does not exactly match source commit {}",
            expected_build_commit, expected.git_commit
        ));
    }
    if environment.git_commit != expected.git_commit {
        return Err(format!(
            "runner source commit {} does not match candidate source commit {}",
            environment.git_commit, expected.git_commit
        ));
    }
    if environment.git_dirty != Some(false) || !environment.comparable_git_state {
        return Err("runner environment is dirty, unknown, or marked non-comparable".to_string());
    }
    if environment.ay_path != expected.ay_path {
        return Err(format!(
            "runner AY path {} does not match candidate canonical path {}",
            environment.ay_path, expected.ay_path
        ));
    }
    if Some(environment.ay_sha256.as_str()) != expected.ay_sha256.as_deref() {
        return Err(format!(
            "runner AY SHA-256 {} does not match candidate {:?}",
            environment.ay_sha256, expected.ay_sha256
        ));
    }
    if Some(environment.ay_size_bytes) != expected.ay_size_bytes {
        return Err(format!(
            "runner AY size {} does not match candidate {:?}",
            environment.ay_size_bytes, expected.ay_size_bytes
        ));
    }
    if environment.ay_build_commit != expected_build_commit {
        return Err(format!(
            "runner AY build commit {} does not match candidate build commit {}",
            environment.ay_build_commit, expected_build_commit
        ));
    }
    Ok(())
}

fn valid_full_git_commit(value: &str) -> bool {
    value.len() == 40
        && value
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
}

fn expected_score_competition(eval_id: &str) -> Option<&'static str> {
    if eval_id.starts_with("sat-") || eval_id.starts_with("satcomp-") {
        Some("SAT-COMP")
    } else if eval_id.starts_with("smt-") {
        Some("SMT-COMP")
    } else if eval_id.starts_with("chc-") || eval_id.starts_with("chccomp-") {
        Some("CHC-COMP")
    } else if eval_id.starts_with("hwmcc-") {
        Some("HWMCC")
    } else {
        None
    }
}

fn expected_native_domain(competition: &str) -> Option<&'static str> {
    match competition {
        "SAT-COMP" => Some("sat"),
        "SMT-COMP" => Some("smt"),
        "CHC-COMP" => Some("chc"),
        "HWMCC" => Some("hwmcc"),
        _ => None,
    }
}

#[cfg(test)]
fn score_shape_errors(score: Option<&serde_json::Value>, competition: Option<&str>) -> Vec<String> {
    let Some(score) = score else {
        return vec!["scorecard row lacks score".to_string()];
    };
    let Some(competition) = competition else {
        return vec!["scorecard row lacks competition".to_string()];
    };
    solve_summary_for_score(score, competition)
        .map(|_| Vec::new())
        .unwrap_or_else(|errors| errors)
}

fn solve_summary_for_score(
    score: &serde_json::Value,
    competition: &str,
) -> std::result::Result<SolveSummaryPacket, Vec<String>> {
    let (solved, total, errors) = match competition {
        "SAT-COMP" => match serde_json::from_value::<SatScoreFields>(score.clone()) {
            Ok(score) => {
                let errors = validate_sat_score(&score);
                (score.solved, score.total, errors)
            }
            Err(error) => {
                return Err(vec![format!(
                    "SAT score has incomplete or mistyped fields: {error}"
                )]);
            }
        },
        "SMT-COMP" => match serde_json::from_value::<SmtScoreFields>(score.clone()) {
            Ok(score) => {
                let errors = validate_smt_score(&score);
                (score.solved, score.total, errors)
            }
            Err(error) => {
                return Err(vec![format!(
                    "SMT score has incomplete or mistyped fields: {error}"
                )]);
            }
        },
        "CHC-COMP" | "HWMCC" => match serde_json::from_value::<ChcScoreFields>(score.clone()) {
            Ok(score) => {
                let errors = validate_chc_score(&score, competition);
                (score.solved, score.total, errors)
            }
            Err(error) => {
                return Err(vec![format!(
                    "{competition} score has incomplete or mistyped fields: {error}"
                )]);
            }
        },
        other => return Err(vec![format!("unsupported score competition {other:?}")]),
    };
    if !errors.is_empty() {
        return Err(errors);
    }
    let solve_rate = solved as f64 / total as f64;
    if !solve_rate.is_finite() || !(0.0..=1.0).contains(&solve_rate) {
        return Err(vec!["score solve rate is not a valid number".to_string()]);
    }
    Ok(SolveSummaryPacket {
        solved,
        total,
        solve_rate,
    })
}

fn evidence_shape_errors(evidence: Option<&serde_json::Value>) -> Vec<String> {
    let Some(evidence) = evidence else {
        return vec!["scorecard row lacks per-instance evidence summary".to_string()];
    };
    let evidence = match serde_json::from_value::<ScorecardEvidence>(evidence.clone()) {
        Ok(evidence) => evidence,
        Err(error) => {
            return vec![format!("scorecard evidence has an invalid shape: {error}")];
        }
    };
    let mut errors = Vec::new();
    if evidence.results_path.trim().is_empty() {
        errors.push("scorecard evidence results_path is empty".to_string());
    } else if !Path::new(&evidence.results_path).is_file() {
        errors.push(format!(
            "scorecard evidence results_path is missing: {}",
            evidence.results_path
        ));
    }
    if evidence.total == 0 {
        errors.push("scorecard evidence total must be positive".to_string());
    }
    let classified = evidence
        .verified
        .checked_add(evidence.wrong)
        .and_then(|value| value.checked_add(evidence.unverified_definitive))
        .and_then(|value| value.checked_add(evidence.non_definitive));
    if classified != Some(evidence.total) {
        errors.push("scorecard evidence counts do not sum to total".to_string());
    }
    if evidence.wrong != 0 {
        errors.push(format!(
            "scorecard evidence contains {} wrong answer(s)",
            evidence.wrong
        ));
    }
    if evidence.unverified_definitive != 0 {
        errors.push(format!(
            "scorecard evidence contains {} unverified definitive answer(s)",
            evidence.unverified_definitive
        ));
    }
    errors
}

fn validate_sat_score(score: &SatScoreFields) -> Vec<String> {
    let mut errors = common_score_errors(
        score.total,
        score.solved,
        score.solved_sat,
        score.solved_unsat,
        &score.wrong_answers,
    );
    if score.solved.checked_add(score.unsolved) != Some(score.total) {
        errors.push("SAT solved and unsolved counts do not sum to total".to_string());
    }
    if score.wrong != 0 {
        errors.push("SAT score has a nonzero wrong count".to_string());
    }
    if score.disqualified {
        errors.push("SAT score is disqualified".to_string());
    }
    require_finite(score.par2_total, "par2_total", false, &mut errors);
    require_finite(score.par2_avg, "par2_avg", false, &mut errors);
    require_finite(score.timeout_sec, "timeout_sec", true, &mut errors);
    if score.total > 0 && score.par2_total.is_finite() && score.par2_avg.is_finite() {
        let expected_average = score.par2_total / score.total as f64;
        if (expected_average - score.par2_avg).abs() > 0.0011 {
            errors.push("SAT par2_avg is inconsistent with par2_total and total".to_string());
        }
    }
    errors
}

fn validate_smt_score(score: &SmtScoreFields) -> Vec<String> {
    let mut errors = common_score_errors(
        score.total,
        score.solved,
        score.solved_sat,
        score.solved_unsat,
        &score.wrong_answers,
    );
    if score.errors != 0 {
        errors.push("SMT score has a nonzero error count".to_string());
    }
    if !score.sound {
        errors.push("SMT score is not sound".to_string());
    }
    if score.division.trim().is_empty() {
        errors.push("SMT score division is empty".to_string());
    }
    if score.solved.checked_add(score.timeout_count).is_none()
        || score.solved + score.timeout_count > score.total
    {
        errors.push("SMT solved and timeout counts exceed total".to_string());
    }
    require_finite(score.wall_time, "wall_time", false, &mut errors);
    require_finite(score.cpu_time, "cpu_time", false, &mut errors);
    errors
}

fn validate_chc_score(score: &ChcScoreFields, competition: &str) -> Vec<String> {
    let mut errors = common_score_errors(
        score.total,
        score.solved,
        score.solved_sat,
        score.solved_unsat,
        &score.wrong_answers,
    );
    if score.solved.checked_add(score.unsolved) != Some(score.total) {
        errors.push(format!(
            "{competition} solved and unsolved counts do not sum to total"
        ));
    }
    if score.wrong != 0 {
        errors.push(format!("{competition} score has a nonzero wrong count"));
    }
    if score.track.trim().is_empty() {
        errors.push(format!("{competition} score track is empty"));
    }
    require_finite(score.cpu_time, "cpu_time", false, &mut errors);
    require_finite(score.timeout_sec, "timeout_sec", true, &mut errors);
    errors
}

fn common_score_errors(
    total: u64,
    solved: u64,
    solved_sat: u64,
    solved_unsat: u64,
    wrong_answers: &[serde_json::Value],
) -> Vec<String> {
    let mut errors = Vec::new();
    if total == 0 {
        errors.push("score total must be positive".to_string());
    }
    if solved > total {
        errors.push("score solved exceeds total".to_string());
    }
    if solved_sat.checked_add(solved_unsat) != Some(solved) {
        errors.push("score solved subtype counts do not sum to solved".to_string());
    }
    if !wrong_answers.is_empty() {
        errors.push("score wrong_answers must be an empty array".to_string());
    }
    errors
}

fn require_finite(value: f64, field: &str, positive: bool, errors: &mut Vec<String>) {
    if !value.is_finite() || if positive { value <= 0.0 } else { value < 0.0 } {
        errors.push(format!("score field {field} is not a valid number"));
    }
}

fn track_packets(loaded: &LoadedCampaign, lanes: &[LanePacket]) -> Vec<TrackPacket> {
    let lane_by_id = lanes
        .iter()
        .map(|lane| (lane.lane_id.as_str(), lane))
        .collect::<BTreeMap<_, _>>();
    loaded
        .catalog
        .tracks
        .iter()
        .map(|track| {
            let event_id = format!("{}-{}", track.competition, track.edition);
            let event = &loaded.events[&event_id];
            let track_lanes = loaded
                .lanes
                .iter()
                .filter(|lane| lane.competition_refs.iter().any(|id| id == &track.id))
                .filter_map(|lane| lane_by_id.get(lane.id.as_str()).copied())
                .collect::<Vec<_>>();
            let passed = track_lanes.iter().any(|lane| lane.status == "passed");
            let failed = track_lanes.iter().any(|lane| lane.status == "failed");
            let planned = track_lanes.iter().any(|lane| lane.status == "eligible");
            let (disposition, reason) = if failed {
                (
                    "failed",
                    "At least one relevant executable proxy lane failed; inspect every referenced lane packet, including any that passed.",
                )
            } else if passed {
                (
                    "executed-proxy",
                    "Every executed relevant local proxy lane completed. The lanes are not exact track replays and their scores are not admitted.",
                )
            } else if planned {
                (
                    "planned-proxy",
                    "One or more relevant proxy lanes passed local preflight and would run under this profile; plan mode did not launch solvers.",
                )
            } else if event.local_run_support == "not-applicable" {
                ("not-applicable", event.reason.as_str())
            } else if event.corpus_status == "unavailable" {
                ("blocked-unavailable", event.reason.as_str())
            } else if event.local_run_support == "unsupported" {
                ("blocked-unsupported", event.reason.as_str())
            } else if !track_lanes.is_empty() {
                (
                    "blocked-local-preflight",
                    "Every relevant registered lane is disabled or missing a local prerequisite.",
                )
            } else {
                ("blocked-no-recipe", event.reason.as_str())
            };
            TrackPacket {
                track_id: track.id.clone(),
                competition: track.competition.clone(),
                edition: track.edition,
                event_id,
                execution_disposition: disposition.to_string(),
                official_replay_status: "blocked".to_string(),
                score_admitted: false,
                underpowered_vs_official: format!(
                    "manifest-baseline-{}; runtime-host-recorded-but-official-match-not-verified",
                    event.official_machine_status
                ),
                reason: reason.to_string(),
                lane_ids: track_lanes
                    .iter()
                    .map(|lane| lane.lane_id.clone())
                    .collect(),
            }
        })
        .collect()
}

fn coverage_packet(
    loaded: &LoadedCampaign,
    lanes: &[LanePacket],
    tracks: &[TrackPacket],
) -> CampaignCoveragePacket {
    CampaignCoveragePacket {
        declared_tracks: loaded.catalog.tracks.len(),
        accounted_tracks: tracks.len(),
        declared_lanes: loaded.lanes.len(),
        eligible_lanes: lanes
            .iter()
            .filter(|lane| lane.status == "eligible")
            .count(),
        blocked_lanes: lanes.iter().filter(|lane| lane.status == "blocked").count(),
        passed_lanes: lanes.iter().filter(|lane| lane.status == "passed").count(),
        failed_lanes: lanes.iter().filter(|lane| lane.status == "failed").count(),
    }
}

fn requested_envelope_packet(repo: &Path, profile: &Profile) -> RequestedEnvelopePacket {
    RequestedEnvelopePacket {
        timeout_sec: profile.timeout_sec,
        max_jobs: profile.max_jobs,
        per_child_memory_mib: profile.per_child_memory_mib,
        per_child_cores: profile.per_child_cores,
        cpu_policy: profile.cpu_policy.clone(),
        oom_guard_required: profile.oom_guard_required,
        guard_script: repo.join("scripts/_oom_guard.py").display().to_string(),
    }
}

fn runtime_host_packet() -> RuntimeHostPacket {
    let cpuinfo = fs::read_to_string("/proc/cpuinfo").ok();
    let (cgroup_v2_path, cgroup_v2_dir) = cgroup_v2_location()
        .map(|(path, directory)| (Some(path), Some(directory)))
        .unwrap_or((None, None));
    let cgroup_value = |name: &str| {
        cgroup_v2_dir
            .as_ref()
            .and_then(|directory| read_trimmed(&directory.join(name)))
    };
    RuntimeHostPacket {
        evidence_source: "runtime-procfs-and-rust-standard-library",
        hostname: read_trimmed(Path::new("/proc/sys/kernel/hostname"))
            .or_else(|| std::env::var("HOSTNAME").ok())
            .unwrap_or_else(|| "unknown".to_string()),
        os: std::env::consts::OS,
        arch: std::env::consts::ARCH,
        cpu_model: cpuinfo
            .as_deref()
            .and_then(cpu_model_from_cpuinfo)
            .unwrap_or_else(|| std::env::consts::ARCH.to_string()),
        system_logical_cpu_count: cpuinfo.as_deref().and_then(logical_cpu_count),
        scheduler_available_cpu_count: std::thread::available_parallelism()
            .ok()
            .map(std::num::NonZeroUsize::get),
        physical_core_count: cpuinfo.as_deref().and_then(physical_core_count),
        memory_total_bytes: proc_meminfo_kib("MemTotal").and_then(|kib| kib.checked_mul(1024)),
        swap_total_bytes: proc_meminfo_kib("SwapTotal").and_then(|kib| kib.checked_mul(1024)),
        cgroup_v2_path,
        cgroup_memory_max: cgroup_value("memory.max"),
        cgroup_memory_high: cgroup_value("memory.high"),
        cgroup_swap_max: cgroup_value("memory.swap.max"),
        cgroup_cpu_max: cgroup_value("cpu.max"),
        cgroup_cpuset_effective: cgroup_value("cpuset.cpus.effective"),
        official_hardware_match_verified: false,
    }
}

fn read_trimmed(path: &Path) -> Option<String> {
    fs::read_to_string(path)
        .ok()
        .map(|value| value.trim().to_string())
        .filter(|value| !value.is_empty())
}

fn proc_meminfo_kib(key: &str) -> Option<u64> {
    let body = fs::read_to_string("/proc/meminfo").ok()?;
    body.lines().find_map(|line| {
        let (field, value) = line.split_once(':')?;
        if field != key {
            return None;
        }
        value.split_whitespace().next()?.parse().ok()
    })
}

fn cpu_model_from_cpuinfo(cpuinfo: &str) -> Option<String> {
    for key in ["model name", "Hardware", "Processor"] {
        if let Some(value) = cpuinfo.lines().find_map(|line| {
            let (field, value) = line.split_once(':')?;
            (field.trim() == key)
                .then(|| value.trim().to_string())
                .filter(|value| !value.is_empty())
        }) {
            return Some(value);
        }
    }
    None
}

fn logical_cpu_count(cpuinfo: &str) -> Option<usize> {
    let count = cpuinfo
        .lines()
        .filter(|line| {
            line.split_once(':')
                .is_some_and(|(field, _)| field.trim() == "processor")
        })
        .count();
    (count > 0).then_some(count)
}

fn physical_core_count(cpuinfo: &str) -> Option<usize> {
    let mut cores = BTreeSet::new();
    for record in cpuinfo.split("\n\n") {
        let mut physical_id = None;
        let mut core_id = None;
        for line in record.lines() {
            let Some((field, value)) = line.split_once(':') else {
                continue;
            };
            match field.trim() {
                "physical id" => physical_id = Some(value.trim()),
                "core id" => core_id = Some(value.trim()),
                _ => {}
            }
        }
        if let (Some(physical_id), Some(core_id)) = (physical_id, core_id) {
            cores.insert((physical_id.to_string(), core_id.to_string()));
        }
    }
    (!cores.is_empty()).then_some(cores.len())
}

fn cgroup_v2_location() -> Option<(String, PathBuf)> {
    let body = fs::read_to_string("/proc/self/cgroup").ok()?;
    let path = body.lines().find_map(|line| line.strip_prefix("0::"))?;
    let mut directory = PathBuf::from("/sys/fs/cgroup");
    for component in Path::new(path).components() {
        if let std::path::Component::Normal(component) = component {
            directory.push(component);
        }
    }
    Some((path.to_string(), directory))
}

fn load_toml<T: for<'de> Deserialize<'de>>(repo: &Path, path: &Path) -> Result<T> {
    let path = resolve_input(repo, path);
    let body = fs::read_to_string(&path).with_context(|| format!("read {}", path.display()))?;
    toml::from_str(&body).with_context(|| format!("parse {}", path.display()))
}

fn resolve_input(repo: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        repo.join(path)
    }
}

fn resolve_output(repo: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        repo.join(path)
    }
}

fn resolve_ay(repo: &Path, requested: Option<PathBuf>) -> Result<PathBuf> {
    let path = match requested {
        Some(path) if path.is_absolute() => path,
        Some(path) => repo.join(path),
        None => std::env::current_exe().context("resolve running AY executable")?,
    };
    if !is_executable_file(&path) {
        bail!(
            "AY candidate is missing, not a regular file, or not executable: {}",
            path.display()
        );
    }
    Ok(path)
}

fn find_repo_root() -> Result<PathBuf> {
    let mut starts = Vec::new();
    if let Ok(cwd) = std::env::current_dir() {
        starts.push(cwd);
    }
    if let Ok(executable) = std::env::current_exe() {
        if let Some(parent) = executable.parent() {
            starts.push(parent.to_path_buf());
        }
    }
    for start in starts {
        for ancestor in start.ancestors() {
            if ancestor.join(DEFAULT_CATALOG).is_file()
                && ancestor.join("scripts/_oom_guard.py").is_file()
            {
                return Ok(ancestor.to_path_buf());
            }
        }
    }
    bail!("could not locate AY repository root")
}

fn is_executable_file(path: &Path) -> bool {
    if !path.is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        fs::metadata(path)
            .map(|metadata| metadata.permissions().mode() & 0o111 != 0)
            .unwrap_or(false)
    }
    #[cfg(not(unix))]
    {
        true
    }
}

fn tool_available(tool: &str) -> bool {
    std::env::var_os("PATH").is_some_and(|paths| {
        std::env::split_paths(&paths).any(|directory| is_executable_file(&directory.join(tool)))
    })
}

fn candidate_packet(repo: &Path, ay: Option<&Path>) -> Result<CandidatePacket> {
    let commit = git_output(repo, &["rev-parse", "HEAD"]).unwrap_or_else(|_| "unknown".to_string());
    let dirty = git_output(repo, &["status", "--porcelain", "--untracked-files=normal"])
        .map(|output| !output.is_empty())
        .unwrap_or(true);
    let (ay_path, ay_sha256, ay_size_bytes, ay_build_commit) = if let Some(path) = ay {
        let canonical = fs::canonicalize(path)
            .with_context(|| format!("canonicalize campaign candidate {}", path.display()))?;
        let (sha256, size_bytes) = candidate_file_identity(&canonical)?;
        let build_commit = candidate_build_commit(repo, &canonical)?;
        (
            canonical.display().to_string(),
            Some(sha256),
            Some(size_bytes),
            build_commit,
        )
    } else {
        ("(plan-only)".to_string(), None, None, None)
    };
    Ok(CandidatePacket {
        ay_path,
        ay_sha256,
        ay_size_bytes,
        ay_build_commit,
        git_commit: commit,
        git_dirty: dirty,
    })
}

fn candidate_file_identity(path: &Path) -> Result<(String, u64)> {
    file_identity(path, "campaign candidate")
}

fn file_identity(path: &Path, purpose: &str) -> Result<(String, u64)> {
    let mut file =
        fs::File::open(path).with_context(|| format!("open {purpose} {}", path.display()))?;
    let metadata = file
        .metadata()
        .with_context(|| format!("stat {purpose} {}", path.display()))?;
    if !metadata.file_type().is_file() {
        bail!("{purpose} is not a regular file: {}", path.display());
    }
    let mut hasher = Sha256::new();
    let mut size_bytes = 0_u64;
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let read = file
            .read(&mut buffer)
            .with_context(|| format!("hash {purpose} {}", path.display()))?;
        if read == 0 {
            break;
        }
        size_bytes = size_bytes
            .checked_add(read as u64)
            .ok_or_else(|| anyhow!("{purpose} size overflow"))?;
        hasher.update(&buffer[..read]);
    }
    let metadata_after = file
        .metadata()
        .with_context(|| format!("restat {purpose} {}", path.display()))?;
    if metadata.len() != metadata_after.len() || metadata.len() != size_bytes {
        bail!("{purpose} changed while hashing: {}", path.display());
    }
    Ok((format!("sha256:{:x}", hasher.finalize()), size_bytes))
}

fn candidate_build_commit(repo: &Path, ay: &Path) -> Result<Option<String>> {
    let output = Command::new(ay)
        .arg("--version")
        .current_dir(repo)
        .stdin(Stdio::null())
        .output()
        .with_context(|| format!("probe campaign candidate version {}", ay.display()))?;
    if !output.status.success() {
        return Ok(None);
    }
    let bytes = if output.stdout.is_empty() {
        output.stderr
    } else {
        output.stdout
    };
    let text = String::from_utf8(bytes).context("campaign candidate version is not UTF-8")?;
    Ok(text.lines().find_map(|line| {
        line.trim()
            .strip_prefix("build.commit=")
            .map(str::trim)
            .filter(|value| !value.is_empty())
            .map(str::to_string)
    }))
}

fn git_output(repo: &Path, args: &[&str]) -> Result<String> {
    let output = Command::new("git")
        .current_dir(repo)
        .args(args)
        .output()
        .context("invoke git")?;
    if !output.status.success() {
        bail!("git {} exited with {}", args.join(" "), output.status);
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

fn unix_time() -> Result<u64> {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .context("system clock precedes Unix epoch")
        .map(|duration| duration.as_secs())
}

fn write_or_print(repo: &Path, output: Option<&Path>, packet: &CampaignPacket) -> Result<()> {
    if let Some(output) = output {
        write_json_atomic(&resolve_output(repo, output), packet)
    } else {
        println!("{}", serde_json::to_string_pretty(packet)?);
        Ok(())
    }
}

fn write_json_atomic(path: &Path, packet: &CampaignPacket) -> Result<()> {
    let parent = path
        .parent()
        .ok_or_else(|| anyhow!("campaign output {} has no parent", path.display()))?;
    fs::create_dir_all(parent)
        .with_context(|| format!("create campaign output {}", parent.display()))?;
    let temporary = parent.join(format!(
        ".{}.tmp.{}",
        path.file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("campaign"),
        std::process::id()
    ));
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)
        .with_context(|| format!("create temporary campaign packet {}", temporary.display()))?;
    serde_json::to_writer_pretty(&mut file, packet).context("serialize campaign packet")?;
    file.write_all(b"\n").context("finish campaign packet")?;
    file.sync_all().context("sync campaign packet")?;
    drop(file);
    fs::rename(&temporary, path).with_context(|| {
        format!(
            "publish campaign packet {} -> {}",
            temporary.display(),
            path.display()
        )
    })?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn campaign_run_help_names_only_executable_profile() {
        let mut command = CampaignArgs::augment_args(clap::Command::new("campaign"));
        let run = command
            .find_subcommand_mut("run")
            .expect("campaign run subcommand");
        let help = run.render_long_help().to_string();
        assert!(help.contains("Only reviewer-full"));
        assert!(help.contains("all other declared profiles remain declarative"));
        assert!(!help.contains("Only non-official profiles"));
    }

    fn repository() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    fn campaign_files() -> CampaignFiles {
        CampaignFiles {
            catalog: PathBuf::from(DEFAULT_CATALOG),
            assets: PathBuf::from(DEFAULT_ASSETS),
            corpora: PathBuf::from(DEFAULT_CORPORA),
            lanes: PathBuf::from(DEFAULT_LANES),
            profiles: PathBuf::from(DEFAULT_PROFILES),
        }
    }

    #[test]
    fn executable_profile_rejects_reviewer_full_alias() {
        let repo = repository();
        let mut profile = LoadedCampaign::load(&repo, &campaign_files(), "reviewer-full")
            .expect("load reviewer-full campaign profile")
            .profile;
        profile.id = "reviewer-full-alias".to_string();

        let error = validate_executable_profile(&profile)
            .expect_err("profile aliases must remain declarative")
            .to_string();
        assert!(
            error.contains("supports only reviewer-full"),
            "unexpected error: {error}"
        );
    }

    fn test_runner_environment() -> RunnerEnvironmentEvidence {
        RunnerEnvironmentEvidence {
            timestamp: "2026-07-24T00:00:00Z".to_string(),
            git_commit: "0123456789012345678901234567890123456789".to_string(),
            git_dirty: Some(false),
            comparable_git_state: true,
            ay_path: "/tmp/ay".to_string(),
            ay_sha256: format!("sha256:{}", "a".repeat(64)),
            ay_size_bytes: 1,
            ay_version: "ay test".to_string(),
            ay_build_version: "test".to_string(),
            ay_build_commit: "0123456789012345678901234567890123456789".to_string(),
            ay_build_datetime_utc: "2026-07-24T00:00:00Z".to_string(),
            ay_build_stamp: "test".to_string(),
            hostname: "reviewer".to_string(),
            os: "linux".to_string(),
            arch: "x86_64".to_string(),
            cpu_model: "test cpu".to_string(),
            cpu_count: 2,
            memory_bytes: 8 * 1024 * 1024 * 1024,
            load_avg: [0.0, 0.0, 0.0],
        }
    }

    fn test_candidate_packet() -> CandidatePacket {
        CandidatePacket {
            ay_path: "/tmp/ay".to_string(),
            ay_sha256: Some(format!("sha256:{}", "a".repeat(64))),
            ay_size_bytes: Some(1),
            ay_build_commit: Some("0123456789012345678901234567890123456789".to_string()),
            git_commit: "0123456789012345678901234567890123456789".to_string(),
            git_dirty: false,
        }
    }

    fn test_eligible_lane(eval_id: &str, benchmark_count: usize) -> LanePacket {
        LanePacket {
            lane_id: "test-lane".to_string(),
            eval_id: eval_id.to_string(),
            evidence_class: "proxy".to_string(),
            status: "eligible".to_string(),
            reason: String::new(),
            benchmark_count: Some(benchmark_count),
            score_competition: None,
            score: None,
            solve_summary: None,
            evidence_counts: None,
            verdict_evidence_classification: None,
            reference_solvers: Vec::new(),
            results_path: None,
            native_results: None,
            corpus: None,
            enforced_envelope: None,
        }
    }

    fn test_native_document() -> NativeEvidenceDocument {
        let items = vec![
            NativeResultItemEvidence {
                file: "sat/a.cnf".to_string(),
                benchmark_path: "/corpus/sat/a.cnf".to_string(),
                benchmark_content_hash: Some(format!("sha256:{}", "a".repeat(64))),
                solver_input_hash: Some(format!("sha256:{}", "d".repeat(64))),
                solver_input_path: Some("/private/sat/a.cnf".to_string()),
                expected: Some("sat".to_string()),
                expected_source: "path".to_string(),
                result: "sat".to_string(),
                time_sec: 1.0,
                cpu_time_sec: 0.9,
            },
            NativeResultItemEvidence {
                file: "unsat/b.cnf".to_string(),
                benchmark_path: "/corpus/unsat/b.cnf".to_string(),
                benchmark_content_hash: Some(format!("sha256:{}", "b".repeat(64))),
                solver_input_hash: Some(format!("sha256:{}", "e".repeat(64))),
                solver_input_path: Some("/private/unsat/b.cnf".to_string()),
                expected: Some("unsat".to_string()),
                expected_source: "path".to_string(),
                result: "unsat".to_string(),
                time_sec: 1.0,
                cpu_time_sec: 0.8,
            },
            NativeResultItemEvidence {
                file: "sat/c.cnf".to_string(),
                benchmark_path: "/corpus/sat/c.cnf".to_string(),
                benchmark_content_hash: Some(format!("sha256:{}", "c".repeat(64))),
                solver_input_hash: Some(format!("sha256:{}", "f".repeat(64))),
                solver_input_path: Some("/private/sat/c.cnf".to_string()),
                expected: Some("sat".to_string()),
                expected_source: "path".to_string(),
                result: "timeout".to_string(),
                time_sec: 60.0,
                cpu_time_sec: 59.0,
            },
        ];
        let preprocessing = items
            .iter()
            .map(|item| NativeInputPreparationEvidence {
                benchmark_path: item.file.clone(),
                source_hash: item
                    .benchmark_content_hash
                    .clone()
                    .expect("test benchmark hash"),
                solver_input_hash: item.solver_input_hash.clone().expect("test solver hash"),
                source_bytes: 1,
            })
            .collect();
        NativeEvidenceDocument {
            environment: test_runner_environment(),
            items,
            preprocessing,
            settings: NativeSettingsEvidence {
                benchmarks_dir: "benchmarks/sat/test".to_string(),
                timeout_sec: 60.0,
                domain: "sat".to_string(),
                benchmark_count: 3,
                runs: 1,
                resource_plan: ay_bench::ResourcePlan {
                    requested_jobs: 1,
                    jobs: 1,
                    memlimit_mb_per_child: 1024,
                    nbcore_per_child: 1,
                    headroom_mb: 256,
                    planner: repository()
                        .join("scripts/_oom_guard.py")
                        .display()
                        .to_string(),
                },
                resource_enforcement: ay_bench::ENFORCEMENT_AY_MEMORY_RSS_V1.to_string(),
                shard: None,
            },
            comparisons: None,
            reference_comparisons: None,
            references: Vec::new(),
        }
    }

    fn materialize_test_inventory(
        document: &mut NativeEvidenceDocument,
        root: &Path,
    ) -> ay_bench::runner::EvalBenchmarkInventory {
        fs::create_dir_all(root).expect("create test corpus root");
        let canonical_root = fs::canonicalize(root).expect("canonical test corpus root");
        let mut expected_items = Vec::with_capacity(document.items.len());
        for (index, (item, prepared)) in document
            .items
            .iter_mut()
            .zip(&mut document.preprocessing)
            .enumerate()
        {
            let path = canonical_root.join(&item.file);
            fs::create_dir_all(path.parent().expect("test benchmark parent"))
                .expect("create test benchmark parent");
            let contents = format!("c test benchmark {index}\np cnf 1 1\n1 0\n");
            fs::write(&path, contents.as_bytes()).expect("write test benchmark");
            let canonical_path = fs::canonicalize(&path).expect("canonical test benchmark");
            let source_sha256 = format!("sha256:{:x}", Sha256::digest(contents.as_bytes()));
            let source_size_bytes = contents.len() as u64;
            item.benchmark_path = canonical_path.display().to_string();
            item.benchmark_content_hash = Some(source_sha256.clone());
            prepared.source_hash = source_sha256.clone();
            prepared.source_bytes = source_size_bytes;
            expected_items.push(ay_bench::runner::EvalBenchmarkIdentity {
                benchmark_id: item.file.clone(),
                canonical_path: canonical_path.display().to_string(),
                source_sha256,
                source_size_bytes,
            });
        }
        document.settings.benchmarks_dir = canonical_root.display().to_string();
        ay_bench::runner::EvalBenchmarkInventory {
            benchmarks_dir: canonical_root.display().to_string(),
            canonical_benchmarks_dir: canonical_root.display().to_string(),
            domain: document.settings.domain.clone(),
            competition: "SAT-COMP".to_string(),
            score_scope: None,
            content_inventory_sha256: format!("sha256:{}", "9".repeat(64)),
            items: expected_items,
        }
    }

    fn test_native_document_for_sat_inventory(
        inventory: &ay_bench::runner::EvalBenchmarkInventory,
    ) -> NativeEvidenceDocument {
        assert_eq!(inventory.domain, "sat");
        assert!(!inventory.items.is_empty());
        let last = inventory.items.len() - 1;
        let items = inventory
            .items
            .iter()
            .enumerate()
            .map(|(index, expected)| {
                let expected_verdict = if expected.benchmark_id.starts_with("unsat/")
                    || expected.benchmark_id.contains("/unsat/")
                {
                    "unsat"
                } else {
                    "sat"
                };
                NativeResultItemEvidence {
                    file: expected.benchmark_id.clone(),
                    benchmark_path: expected.canonical_path.clone(),
                    benchmark_content_hash: Some(expected.source_sha256.clone()),
                    solver_input_hash: Some(expected.source_sha256.clone()),
                    solver_input_path: Some(format!("/private/{index}.cnf")),
                    expected: Some(expected_verdict.to_string()),
                    expected_source: "path".to_string(),
                    result: if index == last {
                        "timeout".to_string()
                    } else {
                        expected_verdict.to_string()
                    },
                    time_sec: if index == last { 60.0 } else { 1.0 },
                    cpu_time_sec: if index == last { 59.0 } else { 0.9 },
                }
            })
            .collect::<Vec<_>>();
        let preprocessing = inventory
            .items
            .iter()
            .map(|expected| NativeInputPreparationEvidence {
                benchmark_path: expected.benchmark_id.clone(),
                source_hash: expected.source_sha256.clone(),
                solver_input_hash: expected.source_sha256.clone(),
                source_bytes: expected.source_size_bytes,
            })
            .collect();
        let mut document = test_native_document();
        document.items = items;
        document.preprocessing = preprocessing;
        document.settings.benchmarks_dir = inventory.benchmarks_dir.clone();
        document.settings.domain = inventory.domain.clone();
        document.settings.benchmark_count = inventory.items.len();
        document
    }

    fn test_native_sat_score(document: &NativeEvidenceDocument) -> serde_json::Value {
        recompute_native_score(
            "SAT-COMP",
            &serde_json::Value::Null,
            &document.items,
            document.settings.timeout_sec,
        )
        .expect("recompute test SAT score")
    }

    fn test_scorecard_evidence(results_path: &Path) -> ScorecardEvidence {
        ScorecardEvidence {
            results_path: results_path.display().to_string(),
            verified: 2,
            wrong: 0,
            unverified_definitive: 0,
            non_definitive: 1,
            total: 3,
        }
    }

    #[test]
    fn native_per_instance_evidence_rejects_truncated_items() {
        let mut document = test_native_document();
        let score = test_native_sat_score(&document);
        let evidence = test_scorecard_evidence(Path::new("/tmp/results.json"));
        document.items.pop();

        let error = validate_native_per_instance_evidence(&document, "SAT-COMP", &score, &evidence)
            .expect_err("truncated items must fail");
        assert!(
            error.contains("2 per-instance items"),
            "unexpected error: {error}"
        );
    }

    #[test]
    fn native_per_instance_evidence_rejects_duplicate_identities() {
        let mut document = test_native_document();
        let score = test_native_sat_score(&document);
        let evidence = test_scorecard_evidence(Path::new("/tmp/results.json"));
        let duplicate = document.items[0].file.clone();
        document.items[1].file = duplicate;

        let error = validate_native_per_instance_evidence(&document, "SAT-COMP", &score, &evidence)
            .expect_err("duplicate benchmark IDs must fail");
        assert!(
            error.contains("repeat benchmark ID"),
            "unexpected error: {error}"
        );
    }

    #[test]
    fn native_per_instance_evidence_rejects_inconsistent_score_and_counts() {
        let document = test_native_document();
        let score = test_native_sat_score(&document);
        let mut evidence = test_scorecard_evidence(Path::new("/tmp/results.json"));
        evidence.verified = 1;
        evidence.non_definitive = 2;

        let error = validate_native_per_instance_evidence(&document, "SAT-COMP", &score, &evidence)
            .expect_err("inconsistent verdict counts must fail");
        assert!(
            error.contains("does not match scorecard evidence"),
            "unexpected error: {error}"
        );

        let evidence = test_scorecard_evidence(Path::new("/tmp/results.json"));
        let mut inconsistent_score = score;
        inconsistent_score["solved"] = serde_json::json!(1);
        let error = validate_native_per_instance_evidence(
            &document,
            "SAT-COMP",
            &inconsistent_score,
            &evidence,
        )
        .expect_err("inconsistent score must fail");
        assert!(
            error.contains("does not exactly match scorecard score"),
            "unexpected error: {error}"
        );
    }

    #[test]
    fn native_per_instance_evidence_requires_canonical_content_hashes() {
        let scorecard_evidence = test_scorecard_evidence(Path::new("/tmp/results.json"));

        let mut missing = test_native_document();
        let score = test_native_sat_score(&missing);
        missing.items[0].benchmark_content_hash = None;
        let error = validate_native_per_instance_evidence(
            &missing,
            "SAT-COMP",
            &score,
            &scorecard_evidence,
        )
        .expect_err("missing benchmark hash must fail");
        assert!(
            error.contains("lacks benchmark_content_hash"),
            "unexpected error: {error}"
        );

        let mut uppercase = test_native_document();
        let score = test_native_sat_score(&uppercase);
        let noncanonical = format!("sha256:{}", "A".repeat(64));
        uppercase.items[0].benchmark_content_hash = Some(noncanonical.clone());
        uppercase.preprocessing[0].source_hash = noncanonical;
        let error = validate_native_per_instance_evidence(
            &uppercase,
            "SAT-COMP",
            &score,
            &scorecard_evidence,
        )
        .expect_err("noncanonical benchmark hash must fail");
        assert!(
            error.contains("noncanonical benchmark_content_hash"),
            "unexpected error: {error}"
        );

        let mut bad_solver_hash = test_native_document();
        let score = test_native_sat_score(&bad_solver_hash);
        bad_solver_hash.items[0].solver_input_hash = Some("sha256:short".to_string());
        bad_solver_hash.preprocessing[0].solver_input_hash = "sha256:short".to_string();
        let error = validate_native_per_instance_evidence(
            &bad_solver_hash,
            "SAT-COMP",
            &score,
            &scorecard_evidence,
        )
        .expect_err("noncanonical solver input hash must fail");
        assert!(
            error.contains("noncanonical solver_input_hash"),
            "unexpected error: {error}"
        );
    }

    #[test]
    fn reviewer_full_native_settings_reject_repetitions_and_shards() {
        let mut settings = test_native_document().settings;
        assert!(validate_reviewer_full_native_settings(&settings).is_ok());

        settings.runs = 2;
        assert!(validate_reviewer_full_native_settings(&settings)
            .unwrap_err()
            .contains("exactly one"));

        settings.runs = 1;
        settings.shard = Some(NativeShardIdentityPacket {
            requested_index: 0,
            shard_index: 0,
            shard_size: 3,
            shard_count: 1,
            corpus_benchmark_count: 3,
            selected_benchmark_count: 3,
            corpus_path_inventory_sha256: format!("sha256:{}", "a".repeat(64)),
            selector: "sorted-normalized-id-contiguous-v1".to_string(),
        });
        assert!(validate_reviewer_full_native_settings(&settings)
            .unwrap_err()
            .contains("complete selection"));
    }

    #[test]
    fn native_eval_binding_rejects_same_count_substitutions() {
        let directory = tempfile::tempdir().expect("tempdir");
        let mut document = test_native_document();
        let inventory = materialize_test_inventory(&mut document, directory.path());
        assert!(validate_native_eval_binding(&document, &inventory).is_ok());

        document.items.swap(0, 1);
        let error = validate_native_eval_binding(&document, &inventory)
            .expect_err("reordered or substituted corpus rows must fail");
        assert!(
            error.contains("benchmark ID"),
            "unexpected corpus binding error: {error}"
        );
        document.items.swap(0, 1);

        document.items[0].benchmark_content_hash = Some(format!("sha256:{}", "7".repeat(64)));
        let error = validate_native_eval_binding(&document, &inventory)
            .expect_err("same-count content substitution must fail");
        assert!(
            error.contains("exact current eval source"),
            "unexpected corpus hash error: {error}"
        );
    }

    #[test]
    fn reference_comparison_result_must_follow_retained_runs() {
        let mut document = test_native_document();
        document.items.truncate(1);
        document.preprocessing.truncate(1);
        document.settings.benchmark_count = 1;
        let item = &document.items[0];
        let solver_input_hash = item
            .solver_input_hash
            .clone()
            .expect("test solver input hash");
        let comparison = NativeComparisonItemEvidence {
            file: item.file.clone(),
            solver_input_hash: solver_input_hash.clone(),
            ay_result: "sat".to_string(),
            ref_result: "sat".to_string(),
            agreement: "agree".to_string(),
            reference_runs: vec![NativeReferenceRunEvidence {
                result: "unsat".to_string(),
                solver_input_path: item
                    .solver_input_path
                    .clone()
                    .expect("test solver input path"),
                solver_input_hash,
                stdout_sha256: format!("sha256:{}", "0".repeat(64)),
                stderr_sha256: format!("sha256:{}", "1".repeat(64)),
            }],
        };
        document.comparisons = Some(vec![comparison.clone()]);
        document.reference_comparisons = Some(vec![NativeReferenceComparisonEvidence {
            reference_solver: "reference".to_string(),
            items: vec![comparison],
        }]);
        document.references = vec![NativeReferenceEvidence {
            reference_solver: "reference".to_string(),
            reference_solver_path: "/tmp/reference".to_string(),
            reference_solver_sha256: format!("sha256:{}", "2".repeat(64)),
            reference_solver_size_bytes: 1,
            reference_solver_version: "reference test".to_string(),
            reference_solver_build_version: "test".to_string(),
            reference_solver_build_commit: "unknown".to_string(),
            reference_solver_build_datetime_utc: "unknown".to_string(),
            reference_solver_build_stamp: "reference test".to_string(),
            reference_resource_enforcement: ay_bench::ENFORCEMENT_RSS_WATCHDOG_V1.to_string(),
            reference_resource_envelope: "test".to_string(),
            agree: 1,
            disagree: 0,
            ay_only: 0,
            ref_only: 0,
        }];

        let error = validate_native_reference_comparisons(&document)
            .expect_err("comparison result must be derived from retained runs");
        assert!(
            error.contains("retained runs require \"unsat\""),
            "unexpected reference reconciliation error: {error}"
        );
    }

    #[test]
    fn candidate_binding_requires_exact_clean_source_and_binary_identity() {
        let candidate = test_candidate_packet();
        let observed = candidate.clone();
        let environment = test_runner_environment();
        assert!(validate_candidate_binding(&candidate, &observed, &environment).is_ok());

        let mut stale_binary = candidate.clone();
        stale_binary.ay_build_commit = Some("1123456789012345678901234567890123456789".to_string());
        assert!(
            validate_candidate_binding(&stale_binary, &stale_binary, &environment)
                .unwrap_err()
                .contains("does not exactly match source commit")
        );

        let mut changed_binary = observed.clone();
        changed_binary.ay_sha256 = Some(format!("sha256:{}", "b".repeat(64)));
        assert!(
            validate_candidate_binding(&candidate, &changed_binary, &environment)
                .unwrap_err()
                .contains("SHA-256 changed")
        );

        let mut dirty_candidate = candidate.clone();
        dirty_candidate.git_dirty = true;
        assert!(
            validate_candidate_binding(&dirty_candidate, &dirty_candidate, &environment)
                .unwrap_err()
                .contains("dirty before execution")
        );
    }

    #[test]
    fn candidate_binding_rejects_mismatched_native_environment() {
        let candidate = test_candidate_packet();
        let mut environment = test_runner_environment();

        environment.git_commit = "1123456789012345678901234567890123456789".to_string();
        assert!(
            validate_candidate_binding(&candidate, &candidate, &environment)
                .unwrap_err()
                .contains("runner source commit")
        );

        environment = test_runner_environment();
        environment.ay_path = "/tmp/other-ay".to_string();
        assert!(
            validate_candidate_binding(&candidate, &candidate, &environment)
                .unwrap_err()
                .contains("runner AY path")
        );

        environment = test_runner_environment();
        environment.ay_sha256 = format!("sha256:{}", "b".repeat(64));
        assert!(
            validate_candidate_binding(&candidate, &candidate, &environment)
                .unwrap_err()
                .contains("runner AY SHA-256")
        );

        environment = test_runner_environment();
        environment.ay_build_commit = "1123456789012345678901234567890123456789".to_string();
        assert!(
            validate_candidate_binding(&candidate, &candidate, &environment)
                .unwrap_err()
                .contains("runner AY build commit")
        );

        environment = test_runner_environment();
        environment.git_dirty = Some(true);
        assert!(
            validate_candidate_binding(&candidate, &candidate, &environment)
                .unwrap_err()
                .contains("runner environment is dirty")
        );

        environment = test_runner_environment();
        environment.comparable_git_state = false;
        assert!(
            validate_candidate_binding(&candidate, &candidate, &environment)
                .unwrap_err()
                .contains("marked non-comparable")
        );
    }

    #[test]
    fn runner_environment_requires_clean_comparable_full_commit() {
        let mut environment = test_runner_environment();
        assert!(validate_runner_environment(&environment).is_ok());

        environment.git_dirty = Some(true);
        assert!(validate_runner_environment(&environment)
            .unwrap_err()
            .contains("dirty, unknown, or non-comparable"));

        environment = test_runner_environment();
        environment.comparable_git_state = false;
        assert!(validate_runner_environment(&environment)
            .unwrap_err()
            .contains("dirty, unknown, or non-comparable"));

        environment = test_runner_environment();
        environment.git_commit = "0123456789ab".to_string();
        assert!(validate_runner_environment(&environment)
            .unwrap_err()
            .contains("invalid source git commit"));
    }

    #[test]
    fn invalid_runner_provenance_fails_lanes_and_remains_in_packet() {
        let directory = tempfile::tempdir().expect("tempdir");
        let scorecard = directory.path().join("scorecard.json");
        let mut environment = test_runner_environment();
        environment.git_dirty = Some(true);
        fs::write(
            &scorecard,
            serde_json::to_vec(&serde_json::json!({
                "environment": environment,
                "mode": "dev",
                "results": [],
            }))
            .expect("serialize scorecard"),
        )
        .expect("write scorecard");
        let mut lanes = vec![LanePacket {
            lane_id: "sat".to_string(),
            eval_id: "sat-continuous-canary".to_string(),
            evidence_class: "proxy".to_string(),
            status: "eligible".to_string(),
            reason: String::new(),
            benchmark_count: Some(1),
            score_competition: None,
            score: None,
            solve_summary: None,
            evidence_counts: None,
            verdict_evidence_classification: None,
            reference_solvers: Vec::new(),
            results_path: None,
            native_results: None,
            corpus: None,
            enforced_envelope: None,
        }];
        let repo = repository();
        let loaded = LoadedCampaign::load(&repo, &campaign_files(), "reviewer-full").unwrap();
        let retained =
            apply_scorecard_status(&repo, &scorecard, &mut lanes, &loaded.profile, None, None)
                .expect("validate scorecard")
                .expect("retain invalid environment for diagnostics");
        assert_eq!(retained.git_dirty, Some(true));
        assert_eq!(lanes[0].status, "failed");
        assert!(lanes[0]
            .reason
            .contains("dirty, unknown, or non-comparable"));
    }

    #[cfg(unix)]
    #[test]
    fn candidate_packet_records_canonical_hash_and_build_commit() {
        use std::os::unix::fs::{symlink, PermissionsExt as _};

        let directory = tempfile::tempdir().expect("tempdir");
        let binary = directory.path().join("ay-real");
        let requested = directory.path().join("ay");
        let commit = "0123456789012345678901234567890123456789";
        fs::write(
            &binary,
            format!("#!/bin/sh\nprintf '%s\\n' 'ay test' 'build.commit={commit}'\n"),
        )
        .expect("write fake AY");
        fs::set_permissions(&binary, fs::Permissions::from_mode(0o755))
            .expect("make fake AY executable");
        symlink(&binary, &requested).expect("symlink fake AY");

        let packet = candidate_packet(directory.path(), Some(&requested)).expect("packet");
        let bytes = fs::read(&binary).expect("read fake AY");
        assert_eq!(
            packet.ay_path,
            fs::canonicalize(&binary)
                .expect("canonical fake AY")
                .display()
                .to_string()
        );
        assert_eq!(
            packet.ay_sha256.as_deref(),
            Some(format!("sha256:{:x}", Sha256::digest(bytes)).as_str())
        );
        assert_eq!(
            packet.ay_size_bytes,
            Some(fs::metadata(&binary).unwrap().len())
        );
        assert_eq!(packet.ay_build_commit.as_deref(), Some(commit));
    }

    #[test]
    fn reviewer_plan_emits_every_track_without_admitting_scores() {
        let repo = repository();
        let loaded = LoadedCampaign::load(&repo, &campaign_files(), "reviewer-full").unwrap();
        let lanes = plan_lanes(&repo, &loaded.lanes);
        let tracks = track_packets(&loaded, &lanes);
        assert_eq!(tracks.len(), 832);
        assert!(tracks.iter().all(|track| !track.score_admitted));
        assert!(tracks
            .iter()
            .all(|track| track.official_replay_status == "blocked"));
        assert!(
            tracks
                .iter()
                .any(|track| track.execution_disposition == "planned-proxy"),
            "eligible plan lanes must not be mislabeled as preflight-blocked"
        );
        let coverage = coverage_packet(&loaded, &lanes, &tracks);
        assert_eq!(coverage.declared_tracks, coverage.accounted_tracks);
        assert_eq!(
            coverage.declared_lanes,
            coverage.eligible_lanes + coverage.blocked_lanes
        );
    }

    #[test]
    fn lane_plan_enforces_declared_minimum_benchmark_count() {
        let lane = Lane {
            id: "undersized".to_string(),
            kind: "rolling".to_string(),
            eval_id: "sat-continuous-canary".to_string(),
            enabled: true,
            requires_paths: Vec::new(),
            requires_tools: Vec::new(),
            min_benchmarks: usize::MAX,
            competition_refs: Vec::new(),
            blocked_reason: None,
        };
        let packets = plan_lanes(&repository(), &[lane]);
        assert_eq!(packets[0].status, "blocked");
        assert!(packets[0].reason.contains("lane requires at least"));
    }

    #[cfg(unix)]
    #[test]
    fn tool_probe_rejects_non_executable_regular_files() {
        use std::os::unix::fs::PermissionsExt as _;

        let directory = tempfile::tempdir().expect("tempdir");
        let path = directory.path().join("tool");
        fs::write(&path, "#!/bin/sh\n").expect("write tool");
        fs::set_permissions(&path, fs::Permissions::from_mode(0o644))
            .expect("make tool non-executable");
        assert!(!is_executable_file(&path));
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755))
            .expect("make tool executable");
        assert!(is_executable_file(&path));
    }

    #[test]
    fn scorecard_correctness_gate_fails_closed() {
        assert!(!score_shape_errors(None, Some("SAT-COMP")).is_empty());
        assert!(!score_shape_errors(Some(&serde_json::json!({})), Some("SAT-COMP")).is_empty());
        let score = serde_json::json!({
            "par2_total": 1.0,
            "par2_avg": 1.0,
            "solved": 1,
            "solved_sat": 1,
            "solved_unsat": 0,
            "unsolved": 0,
            "wrong": 0,
            "disqualified": false,
            "total": 1,
            "timeout_sec": 60.0,
            "wrong_answers": [],
        });
        assert!(score_shape_errors(Some(&score), Some("SAT-COMP")).is_empty());
        let mut bad = score.clone();
        bad["wrong"] = serde_json::json!(1);
        assert!(!score_shape_errors(Some(&bad), Some("SAT-COMP")).is_empty());

        let mut missing = score.clone();
        missing
            .as_object_mut()
            .expect("score object")
            .remove("disqualified");
        assert!(!score_shape_errors(Some(&missing), Some("SAT-COMP")).is_empty());

        let mut mistyped = score.clone();
        mistyped["wrong"] = serde_json::json!("0");
        assert!(!score_shape_errors(Some(&mistyped), Some("SAT-COMP")).is_empty());

        let mut inconsistent = score;
        inconsistent["par2_avg"] = serde_json::json!(2.0);
        assert!(!score_shape_errors(Some(&inconsistent), Some("SAT-COMP")).is_empty());
    }

    #[test]
    fn scorecard_rejects_missing_empty_and_mistyped_smt_soundness() {
        let score = serde_json::json!({
            "division": "QF_LIA",
            "errors": 0,
            "solved": 1,
            "wall_time": 0.25,
            "cpu_time": 0.2,
            "total": 1,
            "solved_sat": 1,
            "solved_unsat": 0,
            "timeout_count": 0,
            "sound": true,
            "wrong_answers": [],
        });
        assert!(score_shape_errors(Some(&score), Some("SMT-COMP")).is_empty());

        let mut missing = score.clone();
        missing
            .as_object_mut()
            .expect("score object")
            .remove("sound");
        assert!(!score_shape_errors(Some(&missing), Some("SMT-COMP")).is_empty());

        let mut mistyped = score.clone();
        mistyped["sound"] = serde_json::json!("true");
        assert!(!score_shape_errors(Some(&mistyped), Some("SMT-COMP")).is_empty());

        let mut empty = score;
        empty["division"] = serde_json::json!("  ");
        assert!(!score_shape_errors(Some(&empty), Some("SMT-COMP")).is_empty());
    }

    #[test]
    fn score_scope_is_bound_to_the_exact_eval() {
        let mut inventory = ay_bench::runner::EvalBenchmarkInventory {
            benchmarks_dir: "/corpus".to_string(),
            canonical_benchmarks_dir: "/corpus".to_string(),
            domain: "smt".to_string(),
            competition: "SMT-COMP".to_string(),
            score_scope: Some("QF_LRA".to_string()),
            content_inventory_sha256: format!("sha256:{}", "a".repeat(64)),
            items: Vec::new(),
        };
        let score = serde_json::json!({
            "division": "QF_LIA",
            "errors": 0,
            "solved": 1,
            "wall_time": 0.25,
            "cpu_time": 0.2,
            "total": 1,
            "solved_sat": 1,
            "solved_unsat": 0,
            "timeout_count": 0,
            "sound": true,
            "wrong_answers": [],
        });
        let error = validate_expected_score_scope("SMT-COMP", &score, &inventory)
            .expect_err("a score from another division must fail");
        assert!(
            error.contains("exact eval scope"),
            "unexpected score scope error: {error}"
        );

        inventory.score_scope = Some("QF_LIA".to_string());
        assert!(validate_expected_score_scope("SMT-COMP", &score, &inventory).is_ok());
    }

    #[test]
    fn scorecard_evidence_rejects_wrong_and_unverified_definitive_answers() {
        let directory = tempfile::tempdir().expect("tempdir");
        let results = directory.path().join("results.json");
        fs::write(&results, b"{}\n").expect("write results");
        let evidence = serde_json::json!({
            "results_path": results,
            "verified": 2,
            "wrong": 0,
            "unverified_definitive": 0,
            "non_definitive": 1,
            "total": 3,
        });
        assert!(evidence_shape_errors(Some(&evidence)).is_empty());

        let mut wrong = evidence.clone();
        wrong["verified"] = serde_json::json!(1);
        wrong["wrong"] = serde_json::json!(1);
        assert!(!evidence_shape_errors(Some(&wrong)).is_empty());

        let mut unverified = evidence;
        unverified["verified"] = serde_json::json!(1);
        unverified["unverified_definitive"] = serde_json::json!(1);
        assert!(!evidence_shape_errors(Some(&unverified)).is_empty());
        assert!(!evidence_shape_errors(None).is_empty());
    }

    #[test]
    fn scorecard_row_rejects_wrong_domain_and_malformed_error() {
        let row = serde_json::json!({
            "eval_id": "sat-continuous-canary",
            "competition": "SMT-COMP",
            "score": {
                "division": "QF_LIA",
                "errors": 0,
                "solved": 1,
                "wall_time": 0.25,
                "cpu_time": 0.2,
                "total": 1,
                "solved_sat": 1,
                "solved_unsat": 0,
                "timeout_count": 0,
                "sound": true,
                "wrong_answers": [],
            },
        });
        assert!(validate_scorecard_row(
            row.as_object().expect("row object"),
            "sat-continuous-canary"
        )
        .is_err());

        let mut malformed_error = row;
        malformed_error["competition"] = serde_json::json!("SAT-COMP");
        malformed_error["error"] = serde_json::json!({"message": "failed"});
        assert!(validate_scorecard_row(
            malformed_error.as_object().expect("row object"),
            "sat-continuous-canary"
        )
        .is_err());
    }

    #[test]
    fn duplicate_scorecard_rows_fail_the_lane() {
        let directory = tempfile::tempdir().expect("tempdir");
        let scorecard = directory.path().join("scorecard.json");
        let score = serde_json::json!({
            "par2_total": 1.0,
            "par2_avg": 1.0,
            "solved": 1,
            "solved_sat": 1,
            "solved_unsat": 0,
            "unsolved": 0,
            "wrong": 0,
            "disqualified": false,
            "total": 1,
            "timeout_sec": 60.0,
            "wrong_answers": [],
        });
        let row = serde_json::json!({
            "eval_id": "sat-continuous-canary",
            "competition": "SAT-COMP",
            "score": score,
        });
        fs::write(
            &scorecard,
            serde_json::to_vec(&serde_json::json!({
                "environment": test_runner_environment(),
                "mode": "dev",
                "results": [row.clone(), row],
            }))
            .expect("serialize scorecard"),
        )
        .expect("write scorecard");
        let mut lanes = vec![LanePacket {
            lane_id: "sat".to_string(),
            eval_id: "sat-continuous-canary".to_string(),
            evidence_class: "proxy".to_string(),
            status: "eligible".to_string(),
            reason: String::new(),
            benchmark_count: Some(1),
            score_competition: None,
            score: None,
            solve_summary: None,
            evidence_counts: None,
            verdict_evidence_classification: None,
            reference_solvers: Vec::new(),
            results_path: None,
            native_results: None,
            corpus: None,
            enforced_envelope: None,
        }];

        let repo = repository();
        let loaded = LoadedCampaign::load(&repo, &campaign_files(), "reviewer-full").unwrap();
        apply_scorecard_status(&repo, &scorecard, &mut lanes, &loaded.profile, None, None)
            .expect("validate scorecard");
        assert_eq!(lanes[0].status, "failed");
        assert!(lanes[0].reason.contains("duplicate eval result"));
    }

    #[test]
    fn passed_lane_retains_score_counts_result_identity_and_corpus() {
        let repo = repository();
        let loaded = LoadedCampaign::load(&repo, &campaign_files(), "reviewer-full").unwrap();
        let environment = test_runner_environment();
        let directory = tempfile::tempdir().expect("tempdir");
        let results = directory.path().join("results.json");
        let reference = directory.path().join("reference-solver");
        fs::write(&reference, b"reference solver test binary\n").expect("write reference solver");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            fs::set_permissions(&reference, fs::Permissions::from_mode(0o755))
                .expect("make reference solver executable");
        }
        let reference = fs::canonicalize(reference).expect("canonical reference solver");
        let (reference_sha256, reference_size_bytes) =
            candidate_file_identity(&reference).expect("reference identity");
        let resource_plan = ay_bench::ResourcePlan {
            requested_jobs: 1,
            jobs: 1,
            memlimit_mb_per_child: loaded.profile.per_child_memory_mib,
            nbcore_per_child: loaded.profile.per_child_cores,
            headroom_mb: 1024,
            planner: repo.join("scripts/_oom_guard.py").display().to_string(),
        };
        let reference_resource_envelope = ay_bench::effective_execution_envelope(
            &resource_plan,
            ay_bench::ENFORCEMENT_RSS_WATCHDOG_V1,
            loaded.profile.timeout_sec,
        )
        .expect("reference resource envelope");
        let inventory =
            ay_bench::runner::preflight_eval_benchmark_inventory("sat-continuous-canary")
                .expect("preflight exact SAT canary inventory");
        let benchmark_count = inventory.items.len();
        let verified_count =
            u64::try_from(benchmark_count - 1).expect("test benchmark count fits u64");
        let total_count = u64::try_from(benchmark_count).expect("test benchmark count fits u64");
        let mut native_document = test_native_document_for_sat_inventory(&inventory);
        native_document.environment = environment;
        native_document.settings.timeout_sec = loaded.profile.timeout_sec;
        native_document.settings.resource_plan = resource_plan.clone();
        let comparison_items = native_document
            .items
            .iter()
            .map(|item| {
                let solver_input_hash = item
                    .solver_input_hash
                    .clone()
                    .expect("test solver input hash");
                NativeComparisonItemEvidence {
                    file: item.file.clone(),
                    solver_input_hash: solver_input_hash.clone(),
                    ay_result: item.result.clone(),
                    ref_result: item.result.clone(),
                    agreement: native_agreement(&item.result, &item.result).to_string(),
                    reference_runs: vec![NativeReferenceRunEvidence {
                        result: item.result.clone(),
                        solver_input_path: item
                            .solver_input_path
                            .clone()
                            .expect("test solver input path"),
                        solver_input_hash,
                        stdout_sha256: format!("sha256:{}", "0".repeat(64)),
                        stderr_sha256: format!("sha256:{}", "0".repeat(64)),
                    }],
                }
            })
            .collect::<Vec<_>>();
        native_document.comparisons = Some(comparison_items.clone());
        native_document.reference_comparisons = Some(vec![NativeReferenceComparisonEvidence {
            reference_solver: "test-reference".to_string(),
            items: comparison_items,
        }]);
        native_document.references = vec![NativeReferenceEvidence {
            reference_solver: "test-reference".to_string(),
            reference_solver_path: reference.display().to_string(),
            reference_solver_sha256: reference_sha256.clone(),
            reference_solver_size_bytes: reference_size_bytes,
            reference_solver_version: "test-reference 1.0".to_string(),
            reference_solver_build_version: "1.0".to_string(),
            reference_solver_build_commit: "unknown".to_string(),
            reference_solver_build_datetime_utc: "unknown".to_string(),
            reference_solver_build_stamp: "test-reference 1.0".to_string(),
            reference_resource_enforcement: ay_bench::ENFORCEMENT_RSS_WATCHDOG_V1.to_string(),
            reference_resource_envelope: reference_resource_envelope.clone(),
            agree: verified_count,
            disagree: 0,
            ay_only: 0,
            ref_only: 0,
        }];
        let score = test_native_sat_score(&native_document);
        let native_bytes = serde_json::to_vec(&native_document).expect("serialize native evidence");
        fs::write(&results, &native_bytes).expect("write native evidence");

        let scorecard = directory.path().join("scorecard.json");
        fs::write(
            &scorecard,
            serde_json::to_vec(&serde_json::json!({
                "environment": test_runner_environment(),
                "mode": "dev",
                "results": [{
                    "eval_id": "sat-continuous-canary",
                    "competition": "SAT-COMP",
                    "score": score.clone(),
                    "evidence": {
                        "results_path": results,
                        "verified": verified_count,
                        "wrong": 0,
                        "unverified_definitive": 0,
                        "non_definitive": 1,
                        "total": total_count,
                    },
                }],
            }))
            .expect("serialize scorecard"),
        )
        .expect("write scorecard");

        let mut lanes = vec![test_eligible_lane("sat-continuous-canary", benchmark_count)];
        apply_scorecard_status(&repo, &scorecard, &mut lanes, &loaded.profile, None, None)
            .expect("validate scorecard");
        let lane = &lanes[0];
        assert_eq!(lane.status, "passed");
        assert_eq!(lane.evidence_class, "proxy");
        assert_eq!(
            lane.verdict_evidence_classification.as_deref(),
            Some(VERDICT_EVIDENCE_CLASSIFICATION)
        );
        assert_eq!(lane.score_competition.as_deref(), Some("SAT-COMP"));
        assert_eq!(lane.score.as_ref(), Some(&score));
        assert_eq!(
            lane.solve_summary,
            Some(SolveSummaryPacket {
                solved: verified_count,
                total: total_count,
                solve_rate: verified_count as f64 / total_count as f64,
            })
        );
        assert_eq!(
            lane.evidence_counts,
            Some(EvidenceCountsPacket {
                verified: verified_count,
                wrong: 0,
                unverified_definitive: 0,
                non_definitive: 1,
                total: total_count,
            })
        );
        assert_eq!(
            lane.native_results,
            Some(NativeResultsIdentityPacket {
                sha256: format!("sha256:{:x}", Sha256::digest(&native_bytes)),
                size_bytes: native_bytes.len() as u64,
            })
        );
        assert_eq!(
            lane.corpus,
            Some(CorpusIdentityPacket {
                benchmarks_dir: inventory.benchmarks_dir,
                domain: "sat".to_string(),
                benchmark_count,
                content_inventory_sha256: inventory.content_inventory_sha256,
                shard: None,
            })
        );
        assert_eq!(
            lane.reference_solvers,
            vec![ReferenceSolverProvenancePacket {
                name: "test-reference".to_string(),
                canonical_path: reference.display().to_string(),
                sha256: reference_sha256,
                size_bytes: reference_size_bytes,
                version: "test-reference 1.0".to_string(),
                build_version: "1.0".to_string(),
                build_commit: "unknown".to_string(),
                build_datetime_utc: "unknown".to_string(),
                build_stamp: "test-reference 1.0".to_string(),
                resource_enforcement: ay_bench::ENFORCEMENT_RSS_WATCHDOG_V1.to_string(),
                resource_envelope: reference_resource_envelope,
            }]
        );
    }

    #[test]
    fn score_and_corpus_digests_fail_closed() {
        let non_finite = SatScoreFields {
            par2_total: f64::NAN,
            par2_avg: 1.0,
            solved: 1,
            solved_sat: 1,
            solved_unsat: 0,
            unsolved: 0,
            wrong: 0,
            disqualified: false,
            total: 1,
            timeout_sec: 60.0,
            wrong_answers: Vec::new(),
        };
        assert!(validate_sat_score(&non_finite)
            .iter()
            .any(|error| error.contains("par2_total")));

        let shard = NativeShardIdentityPacket {
            requested_index: 0,
            shard_index: 0,
            shard_size: 3,
            shard_count: 2,
            corpus_benchmark_count: 5,
            selected_benchmark_count: 3,
            corpus_path_inventory_sha256: format!("sha256:{}", "a".repeat(64)),
            selector: "sorted-normalized-id-contiguous-v1".to_string(),
        };
        assert!(validate_native_shard_identity(&shard, 3).is_ok());

        let mut malformed = shard;
        malformed.corpus_path_inventory_sha256 = "sha256:not-a-digest".to_string();
        assert!(validate_native_shard_identity(&malformed, 3)
            .unwrap_err()
            .contains("invalid corpus inventory SHA-256"));
        assert!(!valid_sha256_identity(&format!(
            "sha256:{}",
            "A".repeat(64)
        )));
    }

    #[test]
    fn reference_solver_provenance_requires_exact_identity_and_enforcement() {
        let directory = tempfile::tempdir().expect("tempdir");
        let solver = directory.path().join("reference-solver");
        fs::write(&solver, b"reference solver test binary\n").expect("write solver");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            fs::set_permissions(&solver, fs::Permissions::from_mode(0o755))
                .expect("make solver executable");
        }
        let solver = fs::canonicalize(solver).expect("canonical solver");
        let (sha256, size_bytes) = candidate_file_identity(&solver).expect("reference identity");
        let plan = ay_bench::ResourcePlan {
            requested_jobs: 1,
            jobs: 1,
            memlimit_mb_per_child: 1024,
            nbcore_per_child: 1,
            headroom_mb: 256,
            planner: "scripts/_oom_guard.py".to_string(),
        };
        let envelope = ay_bench::effective_execution_envelope(
            &plan,
            ay_bench::ENFORCEMENT_RSS_WATCHDOG_V1,
            60.0,
        )
        .expect("reference envelope");
        let mut reference = NativeReferenceEvidence {
            reference_solver: "test-reference".to_string(),
            reference_solver_path: solver.display().to_string(),
            reference_solver_sha256: sha256,
            reference_solver_size_bytes: size_bytes,
            reference_solver_version: "test-reference 1.0".to_string(),
            reference_solver_build_version: "1.0".to_string(),
            reference_solver_build_commit: "unknown".to_string(),
            reference_solver_build_datetime_utc: "unknown".to_string(),
            reference_solver_build_stamp: "test-reference 1.0".to_string(),
            reference_resource_enforcement: ay_bench::ENFORCEMENT_RSS_WATCHDOG_V1.to_string(),
            reference_resource_envelope: envelope,
            agree: 0,
            disagree: 0,
            ay_only: 0,
            ref_only: 0,
        };
        assert!(validate_native_reference_solvers(&[reference.clone()], &plan, 60.0).is_ok());

        reference.reference_resource_enforcement =
            ay_bench::ENFORCEMENT_AY_MEMORY_RSS_V1.to_string();
        assert!(validate_native_reference_solvers(&[reference], &plan, 60.0)
            .unwrap_err()
            .contains("unexpected resource enforcement"));
    }

    #[test]
    fn native_evidence_requires_the_exact_guarded_profile_envelope() {
        let repo = repository();
        let loaded = LoadedCampaign::load(&repo, &campaign_files(), "reviewer-full").unwrap();
        let environment = test_runner_environment();
        let directory = tempfile::tempdir().expect("tempdir");
        let results = directory.path().join("results.json");
        let evidence = |enforcement: &str| {
            let mut document = test_native_document();
            document.environment = environment.clone();
            document.settings.timeout_sec = loaded.profile.timeout_sec;
            document.settings.resource_plan = ay_bench::ResourcePlan {
                requested_jobs: 1,
                jobs: 1,
                memlimit_mb_per_child: loaded.profile.per_child_memory_mib,
                nbcore_per_child: loaded.profile.per_child_cores,
                headroom_mb: 1024,
                planner: repo.join("scripts/_oom_guard.py").display().to_string(),
            };
            document.settings.resource_enforcement = enforcement.to_string();
            document
        };
        let mut valid_document = evidence(ay_bench::ENFORCEMENT_AY_MEMORY_RSS_V1);
        let inventory =
            materialize_test_inventory(&mut valid_document, &directory.path().join("corpus"));
        let score = test_native_sat_score(&valid_document);
        let scorecard_evidence = test_scorecard_evidence(&results);
        fs::write(
            &results,
            serde_json::to_vec(&valid_document).expect("serialize native evidence"),
        )
        .expect("write native evidence");
        let validated = validate_native_lane_evidence(
            &repo,
            results.to_str().expect("UTF-8 path"),
            &loaded.profile,
            &environment,
            Some(3),
            3,
            "SAT-COMP",
            &score,
            &scorecard_evidence,
            &inventory,
        )
        .expect("valid guarded evidence");
        assert_eq!(validated.benchmark_count, 3);
        assert!(validated
            .enforced_envelope
            .effective_envelope
            .contains("oom-guard-v2:jobs=1"));

        let mut invalid_document = evidence("legacy-unenforced");
        let invalid_inventory =
            materialize_test_inventory(&mut invalid_document, &directory.path().join("corpus"));
        fs::write(
            &results,
            serde_json::to_vec(&invalid_document).expect("serialize bad evidence"),
        )
        .expect("write bad native evidence");
        assert!(validate_native_lane_evidence(
            &repo,
            results.to_str().expect("UTF-8 path"),
            &loaded.profile,
            &environment,
            Some(3),
            3,
            "SAT-COMP",
            &score,
            &scorecard_evidence,
            &invalid_inventory,
        )
        .is_err());
    }

    #[test]
    fn parses_runtime_cpu_topology_without_guessing() {
        let cpuinfo = "\
processor : 0
physical id : 0
core id : 0
model name : Reviewer CPU

processor : 1
physical id : 0
core id : 0
model name : Reviewer CPU

processor : 2
physical id : 0
core id : 1
model name : Reviewer CPU
";
        assert_eq!(logical_cpu_count(cpuinfo), Some(3));
        assert_eq!(physical_core_count(cpuinfo), Some(2));
        assert_eq!(
            cpu_model_from_cpuinfo(cpuinfo).as_deref(),
            Some("Reviewer CPU")
        );
    }
}
