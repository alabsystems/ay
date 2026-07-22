// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay competition-jit` subcommands.
//!
//! This first-class CLI surface owns the matrix checks, promotion gate, release
//! validation, hot-input packet generation, and bounded ROI probe runner.

use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::{Args, Subcommand, ValueEnum};
use serde_json::{json, Value};

use crate::competition_jit_gate;
use crate::competition_jit_hot_inputs;
use crate::competition_jit_probe;
use crate::competition_jit_release;

/// Competition JIT matrix, gate, release, and ROI probe subcommands.
#[derive(Subcommand)]
pub(crate) enum CompetitionJitCommand {
    /// JIT mode matrix inspection and validation.
    #[command(subcommand)]
    Matrix(matrix::MatrixCommand),

    /// Emit known external code generation ROI hot-input probe commands.
    HotInputs(hot_inputs::HotInputsArgs),

    /// Run the fail-closed competition JIT promotion gate.
    Gate(gate::GateArgs),

    /// Competition JIT release report and package validation.
    #[command(subcommand)]
    Release(release::ReleaseCommand),

    /// Run bounded stats-aware ROI probes for JIT candidates.
    Probe(probe::ProbeArgs),
}

/// Entry point for `ay competition-jit` subcommands.
pub(crate) fn run(command: CompetitionJitCommand) -> Result<()> {
    match command {
        CompetitionJitCommand::Matrix(command) => match command {
            matrix::MatrixCommand::Check(args) => matrix::check(args),
        },
        CompetitionJitCommand::HotInputs(args) => hot_inputs::run(args),
        CompetitionJitCommand::Gate(args) => gate::run(args),
        CompetitionJitCommand::Release(command) => match command {
            release::ReleaseCommand::Validate(args) => release::validate(args),
        },
        CompetitionJitCommand::Probe(args) => probe::run(args),
    }
}

#[derive(Clone, Copy, Debug, ValueEnum)]
pub(crate) enum Track {
    Sat,
    Smt,
    Pb,
    Chc,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
pub(crate) enum JitMode {
    Off,
    Current,
    SolverProgram,
    ProfileOnly,
}

impl Track {
    fn as_str(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Smt => "smt",
            Self::Pb => "pb",
            Self::Chc => "chc",
        }
    }
}

impl JitMode {
    fn as_str(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::Current => "current",
            Self::SolverProgram => "solver-program",
            Self::ProfileOnly => "profile-only",
        }
    }
}

fn repo_root() -> PathBuf {
    competition_jit_probe::default_repo_root()
}

fn write_json(value: &Value) -> Result<()> {
    println!("{}", serde_json::to_string_pretty(value)?);
    Ok(())
}

pub(crate) mod matrix {
    use super::*;

    #[derive(Subcommand)]
    pub(crate) enum MatrixCommand {
        /// Validate the checked-in JIT mode matrix and schema contract.
        Check(CheckArgs),
    }

    #[derive(Args)]
    pub(crate) struct CheckArgs {
        /// JIT mode matrix JSON.
        #[arg(long, default_value = "competition/jit_mode_matrix.json")]
        pub(crate) matrix: PathBuf,

        /// JIT mode matrix JSON schema.
        #[arg(long, default_value = "competition/jit_mode_matrix.schema.json")]
        pub(crate) schema: PathBuf,

        /// Restrict checks to one competition track.
        #[arg(long, value_enum)]
        pub(crate) track: Option<Track>,

        /// Emit machine-readable JSON.
        #[arg(long)]
        pub(crate) json: bool,
    }

    pub(crate) fn check(args: CheckArgs) -> Result<()> {
        let root = repo_root();
        let matrix_path = if args.matrix.is_absolute() {
            args.matrix.clone()
        } else {
            root.join(&args.matrix)
        };
        let schema_path = if args.schema.is_absolute() {
            args.schema.clone()
        } else {
            root.join(&args.schema)
        };
        let matrix = competition_jit_gate::load_matrix(&matrix_path)?;
        if !schema_path.is_file() {
            anyhow::bail!("matrix schema does not exist: {}", schema_path.display());
        }
        if let Some(track) = args.track {
            if !matrix.tracks.contains_key(track.as_str()) {
                anyhow::bail!("matrix does not define track {}", track.as_str());
            }
        }

        let matrix_display = competition_jit_probe::display_path(&matrix_path, &root);
        let schema_display = competition_jit_probe::display_path(&schema_path, &root);
        if args.json {
            let payload = json!({
                "schema": "ay.competition-jit-matrix-check/v1",
                "status": "pass",
                "matrix": matrix_display,
                "matrix_schema": schema_display,
                "version": matrix.version,
                "modes": matrix.modes.keys().cloned().collect::<Vec<_>>(),
                "tracks": matrix.tracks.keys().cloned().collect::<Vec<_>>(),
            });
            write_json(&payload)
        } else {
            println!(
                "competition-jit matrix check: status=pass matrix={} tracks={} modes={}",
                matrix_display,
                matrix.tracks.len(),
                matrix.modes.len()
            );
            Ok(())
        }
    }
}

pub(crate) mod hot_inputs {
    use super::*;

    #[derive(Args)]
    pub(crate) struct HotInputsArgs {
        /// Emit only one artifact; may be repeated.
        #[arg(long = "artifact", num_args = 1)]
        pub(crate) artifacts: Vec<String>,

        /// Optional ay binary path for emitted probe commands.
        #[arg(long)]
        pub(crate) ay: Option<PathBuf>,

        /// Directory used by emitted probe report paths.
        #[arg(long, default_value = "the development design notes")]
        pub(crate) report_dir: PathBuf,

        /// Solver timeout passed to generated probes, in milliseconds.
        #[arg(long, default_value_t = 1000)]
        pub(crate) timeout_ms: u64,

        /// Per-probe wall-clock timeout in seconds.
        #[arg(long, default_value_t = 2.0)]
        pub(crate) wall_timeout_s: f64,

        /// Overall probe timeout in seconds.
        #[arg(long, default_value_t = 30.0)]
        pub(crate) overall_timeout_s: f64,

        /// Omit --fail-on-gate-fail from emitted probe commands.
        #[arg(long)]
        pub(crate) no_fail_on_gate_fail: bool,

        /// Emit a JSON packet.
        #[arg(long)]
        pub(crate) json: bool,
    }

    pub(crate) fn run(args: HotInputsArgs) -> Result<()> {
        let options = competition_jit_hot_inputs::HotInputCommandOptions {
            artifacts: args.artifacts,
            ay: args.ay,
            report_dir: args.report_dir,
            timeout_ms: args.timeout_ms,
            wall_timeout_s: args.wall_timeout_s,
            overall_timeout_s: args.overall_timeout_s,
            fail_on_gate_fail: !args.no_fail_on_gate_fail,
        };
        let packet = competition_jit_hot_inputs::build_packet_with_root(&options, &repo_root())?;
        if args.json {
            print!("{}", competition_jit_hot_inputs::json_output(&packet)?);
        } else {
            print!("{}", competition_jit_hot_inputs::shell_output(&packet));
        }
        Ok(())
    }
}

pub(crate) mod gate {
    use super::*;

    #[derive(Args)]
    pub(crate) struct GateArgs {
        /// JIT mode matrix JSON.
        #[arg(long, default_value = "competition/jit_mode_matrix.json")]
        pub(crate) matrix: PathBuf,

        /// Competition track.
        #[arg(long, value_enum)]
        pub(crate) track: Option<Track>,

        /// Artifact ID from the mode matrix.
        #[arg(long)]
        pub(crate) artifact: Option<String>,

        /// Candidate mode being gated.
        #[arg(long, value_enum)]
        pub(crate) candidate_mode: Option<JitMode>,

        /// Baseline JSON summary or ay-bench results.json.
        #[arg(long)]
        pub(crate) baseline: Option<PathBuf>,

        /// Candidate JSON summary or ay-bench results.json.
        #[arg(long)]
        pub(crate) candidate: Option<PathBuf>,

        /// Combined comparison JSON with baseline/candidate totals.
        #[arg(long)]
        pub(crate) comparison: Option<PathBuf>,

        /// Self-contained external code generation promotion smoke JSON.
        #[arg(long)]
        pub(crate) smoke_input: Option<PathBuf>,

        /// Validate candidate summary JIT metadata and required counters.
        #[arg(long)]
        pub(crate) require_summary_metadata: bool,

        /// Write compact JIT mode metadata JSON.
        #[arg(long)]
        pub(crate) metadata_out: Option<PathBuf>,

        /// Validate one per-track package/replay release report JSON.
        #[arg(long)]
        pub(crate) release_report: Option<PathBuf>,

        /// Emit machine-readable decision JSON.
        #[arg(long)]
        pub(crate) json: bool,
    }

    pub(crate) fn run(args: GateArgs) -> Result<()> {
        if let Some(report) = args.release_report {
            let release_args = release::ValidateArgs {
                reports: vec![report],
                out_dir: PathBuf::from("target/competition-jit-release/reports"),
                tracks: Vec::new(),
                json: args.json,
            };
            return release::validate(release_args);
        }

        let root = repo_root();
        let matrix_path = if args.matrix.is_absolute() {
            args.matrix.clone()
        } else {
            root.join(&args.matrix)
        };
        let matrix_value = competition_jit_probe::load_matrix(&matrix_path)?;
        let matrix = competition_jit_gate::load_matrix(&matrix_path)?;

        let gate_input = load_gate_comparison(&args)?;
        let comparison = gate_input.comparison;
        let gate_inputs = comparison.get("gate_inputs").and_then(Value::as_object);
        let track = args
            .track
            .map(Track::as_str)
            .map(str::to_string)
            .or_else(|| {
                gate_inputs
                    .and_then(|inputs| inputs.get("track"))
                    .and_then(Value::as_str)
                    .map(str::to_string)
            })
            .or_else(|| {
                comparison
                    .get("track")
                    .and_then(Value::as_str)
                    .map(str::to_string)
            })
            .context(
                "--track is required when the comparison does not include gate_inputs.track",
            )?;
        let artifact_id = args
            .artifact
            .or_else(|| {
                gate_inputs
                    .and_then(|inputs| inputs.get("artifact_id"))
                    .and_then(Value::as_str)
                    .map(str::to_string)
            })
            .or_else(|| comparison.get("artifact").and_then(Value::as_str).map(str::to_string))
            .context("--artifact is required when the comparison does not include gate_inputs.artifact_id")?;
        let artifact = competition_jit_probe::find_artifact(&matrix_value, &track, &artifact_id)?;
        let candidate_mode = args
            .candidate_mode
            .map(JitMode::as_str)
            .map(str::to_string)
            .or_else(|| {
                gate_inputs
                    .and_then(|inputs| inputs.get("candidate_mode"))
                    .and_then(Value::as_str)
                    .map(str::to_string)
            })
            .or_else(|| {
                comparison
                    .get("candidate_mode")
                    .and_then(Value::as_str)
                    .map(str::to_string)
            })
            .or_else(|| {
                comparison
                    .get("candidate")
                    .and_then(competition_jit_gate::summary_candidate_mode)
            });
        let application_counter = artifact
            .get("application_counter")
            .and_then(Value::as_str)
            .context("artifact is missing application_counter")?;
        if args.require_summary_metadata || gate_input.require_summary_metadata {
            validate_candidate_summary_metadata(
                &comparison,
                &track,
                &artifact_id,
                candidate_mode.as_deref(),
                application_counter,
            )?;
        }
        let (install_counter, apply_counter) = competition_jit_probe::native_dispatch_counter_keys(
            &artifact,
            candidate_mode.as_deref().unwrap_or("profile-only"),
        );
        let baseline = competition_jit_gate::normalize_gate_metrics(
            &comparison,
            competition_jit_gate::MetricNormalizationOptions {
                role: Some("baseline"),
                application_counter_key: Some(application_counter),
                native_install_counter_key: install_counter.as_deref(),
                native_apply_counter_key: apply_counter.as_deref(),
            },
        );
        let candidate = competition_jit_gate::normalize_gate_metrics(
            &comparison,
            competition_jit_gate::MetricNormalizationOptions {
                role: Some("candidate"),
                application_counter_key: Some(application_counter),
                native_install_counter_key: install_counter.as_deref(),
                native_apply_counter_key: apply_counter.as_deref(),
            },
        );
        let decision = competition_jit_gate::evaluate_gate(
            &matrix,
            &track,
            &artifact_id,
            baseline,
            candidate,
            candidate_mode.as_deref(),
        )?;
        if let Some(path) = args.metadata_out {
            let metadata = competition_jit_gate::gate_decision_to_json_value(&decision);
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::write(
                &path,
                format!("{}\n", serde_json::to_string_pretty(&metadata)?),
            )?;
        }
        if args.json {
            print!(
                "{}",
                competition_jit_gate::gate_decision_to_json_string(&decision)?
            );
        } else {
            println!(
                "competition-jit gate: status={} track={} artifact={} candidate={} recommended={} native_dispatch={}",
                decision.status,
                decision.track,
                decision.artifact,
                decision.candidate_mode,
                decision.recommended_mode,
                decision.native_dispatch
            );
            for failure in &decision.failures {
                println!("  failure {}: {}", failure.kind, failure.detail);
            }
        }
        Ok(())
    }

    struct GateComparisonInput {
        comparison: Value,
        require_summary_metadata: bool,
    }

    fn load_gate_comparison(args: &GateArgs) -> Result<GateComparisonInput> {
        match (
            args.comparison.as_ref(),
            args.smoke_input.as_ref(),
            args.baseline.as_ref(),
            args.candidate.as_ref(),
        ) {
            (Some(path), None, None, None) => {
                Ok(GateComparisonInput {
                    comparison: competition_jit_gate::load_json_object(path).with_context(
                        || format!("load gate comparison {}", path.display()),
                    )?,
                    require_summary_metadata: false,
                })
            }
            (None, Some(path), None, None) => {
                let smoke =
                    competition_jit_gate::load_json_object(path)
                        .with_context(|| format!("load smoke input {}", path.display()))?;
                let mut comparison = smoke
                    .get("comparison")
                    .cloned()
                    .filter(Value::is_object)
                    .context("--smoke-input must contain a comparison object")?;
                if let Some(comparison_object) = comparison.as_object_mut() {
                    for field in ["track", "artifact", "candidate_mode"] {
                        if !comparison_object.contains_key(field) {
                            if let Some(value) = smoke.get(field) {
                                comparison_object.insert(field.to_string(), value.clone());
                            }
                        }
                    }
                }
                Ok(GateComparisonInput {
                    comparison,
                    require_summary_metadata: smoke
                        .get("require_summary_metadata")
                        .and_then(Value::as_bool)
                        .unwrap_or(false),
                })
            }
            (Some(_), Some(_), _, _) | (Some(_), None, Some(_), _) | (Some(_), None, _, Some(_))
            | (None, Some(_), Some(_), _) | (None, Some(_), _, Some(_)) => {
                anyhow::bail!(
                    "use exactly one input form: --comparison, --smoke-input, or --baseline/--candidate"
                )
            }
            (None, None, Some(baseline), Some(candidate)) => Ok(GateComparisonInput {
                comparison: json!({
                    "baseline": competition_jit_gate::load_json_object(baseline).with_context(|| {
                        format!("load baseline summary {}", baseline.display())
                    })?,
                    "candidate": competition_jit_gate::load_json_object(candidate).with_context(|| {
                        format!("load candidate summary {}", candidate.display())
                    })?,
                }),
                require_summary_metadata: false,
            }),
            (None, None, Some(_), None) | (None, None, None, Some(_)) => {
                anyhow::bail!("--baseline and --candidate must be provided together")
            }
            (None, None, None, None) => anyhow::bail!(
                "competition-jit gate requires --comparison, --smoke-input, --release-report, or --baseline and --candidate"
            ),
        }
    }

    fn validate_candidate_summary_metadata(
        comparison: &Value,
        track: &str,
        artifact: &str,
        candidate_mode: Option<&str>,
        application_counter: &str,
    ) -> Result<()> {
        let candidate = comparison
            .get("candidate")
            .and_then(Value::as_object)
            .context("--require-summary-metadata requires a candidate summary object")?;
        let metadata = candidate
            .get("competition_jit")
            .and_then(Value::as_object)
            .context("candidate summary is missing competition_jit metadata")?;

        let schema_version = metadata.get("schema_version").and_then(Value::as_i64);
        if schema_version != Some(1) {
            anyhow::bail!(
                "candidate competition_jit.schema_version must be 1, got {}",
                metadata
                    .get("schema_version")
                    .map(Value::to_string)
                    .unwrap_or_else(|| "missing".to_string())
            );
        }
        require_metadata_string(metadata, "track", track)?;
        let metadata_artifact = metadata
            .get("artifact_id")
            .or_else(|| metadata.get("artifact"))
            .and_then(Value::as_str);
        if metadata_artifact != Some(artifact) {
            anyhow::bail!(
                "candidate competition_jit.artifact must be {artifact:?}, got {metadata_artifact:?}"
            );
        }
        if let Some(candidate_mode) = candidate_mode {
            require_metadata_string(metadata, "candidate_mode", candidate_mode)?;
        }
        let counter_key = metadata
            .get("application_counter")
            .and_then(application_counter_key);
        if counter_key != Some(application_counter) {
            anyhow::bail!(
                "candidate competition_jit.application_counter must be {application_counter:?}, got {counter_key:?}"
            );
        }
        Ok(())
    }

    fn require_metadata_string(
        metadata: &serde_json::Map<String, Value>,
        field: &str,
        expected: &str,
    ) -> Result<()> {
        let actual = metadata.get(field).and_then(Value::as_str);
        if actual == Some(expected) {
            Ok(())
        } else {
            anyhow::bail!("candidate competition_jit.{field} must be {expected:?}, got {actual:?}")
        }
    }

    fn application_counter_key(value: &Value) -> Option<&str> {
        match value {
            Value::String(text) => Some(text.as_str()),
            Value::Object(object) => object.get("key").and_then(Value::as_str),
            _ => None,
        }
    }
}

pub(crate) mod release {
    use super::*;

    #[derive(Subcommand)]
    pub(crate) enum ReleaseCommand {
        /// Validate competition JIT release reports and package smoke inputs.
        Validate(ValidateArgs),
    }

    #[derive(Args)]
    pub(crate) struct ValidateArgs {
        /// Release report JSON to validate; may be repeated.
        #[arg(long = "report", num_args = 1)]
        pub(crate) reports: Vec<PathBuf>,

        /// Directory for sat/smt/pb/chc release reports.
        #[arg(long, default_value = "target/competition-jit-release/reports")]
        pub(crate) out_dir: PathBuf,

        /// Track to validate; may be repeated. Defaults to all tracks.
        #[arg(long = "track", value_enum, num_args = 1)]
        pub(crate) tracks: Vec<Track>,

        /// Emit machine-readable JSON.
        #[arg(long)]
        pub(crate) json: bool,
    }

    pub(crate) fn validate(args: ValidateArgs) -> Result<()> {
        let root = repo_root();
        let options = competition_jit_release::ReleaseReportOptions::new(
            root.clone(),
            root.join("competition/jit_mode_matrix.json"),
        );
        let reports = if args.reports.is_empty() {
            let tracks = if args.tracks.is_empty() {
                vec![Track::Sat, Track::Smt, Track::Pb, Track::Chc]
            } else {
                args.tracks.clone()
            };
            tracks
                .into_iter()
                .map(|track| args.out_dir.join(format!("{}.json", track.as_str())))
                .collect::<Vec<_>>()
        } else {
            args.reports.clone()
        };

        let mut summaries = Vec::new();
        for report in &reports {
            let summary = competition_jit_release::validate_release_report(
                &options,
                report,
                &competition_jit_release::RecomputedGateModule,
            )?;
            summaries.push(json!({
                "schema": summary.schema,
                "status": summary.status,
                "release_status": summary.release_status,
                "track": summary.track,
                "artifact": summary.artifact,
                "candidate_mode": summary.candidate_mode,
                "recommended_mode": summary.recommended_mode,
                "native_dispatch": summary.native_dispatch,
                "package": summary.package,
                "replay": summary.replay,
                "report": competition_jit_probe::display_path(report, &root),
            }));
        }

        if args.json {
            write_json(&json!({
                "schema": "ay.competition-jit-release-validation/v1",
                "status": "pass",
                "reports": summaries,
            }))
        } else {
            for summary in summaries {
                println!(
                    "competition-jit release validate: status=pass report={} track={} release_status={}",
                    summary["report"].as_str().unwrap_or(""),
                    summary["track"].as_str().unwrap_or(""),
                    summary["release_status"].as_str().unwrap_or("")
                );
            }
            Ok(())
        }
    }
}

pub(crate) mod probe {
    use super::*;

    #[derive(Args)]
    pub(crate) struct ProbeArgs {
        /// Competition track.
        #[arg(long, value_enum)]
        pub(crate) track: Track,

        /// JIT matrix artifact ID; defaults to the first track artifact.
        #[arg(long)]
        pub(crate) artifact: Option<String>,

        /// JIT mode matrix JSON.
        #[arg(long, default_value = "competition/jit_mode_matrix.json")]
        pub(crate) matrix: PathBuf,

        /// ay binary path.
        #[arg(long)]
        pub(crate) ay: Option<PathBuf>,

        /// Probe input path; may be repeated.
        #[arg(long = "probe", num_args = 1)]
        pub(crate) probes: Vec<PathBuf>,

        /// Maximum number of default probes to run.
        #[arg(long, default_value_t = 8)]
        pub(crate) max_probes: usize,

        /// Solver timeout passed to ay, in milliseconds.
        #[arg(long, default_value_t = 1000)]
        pub(crate) timeout_ms: u64,

        /// Per-probe wall-clock timeout in seconds.
        #[arg(long, default_value_t = 2.0)]
        pub(crate) wall_timeout_s: f64,

        /// Grace period after timeout before killing ay.
        #[arg(long, default_value_t = 0.5)]
        pub(crate) kill_grace_s: f64,

        /// Overall probe timeout in seconds.
        #[arg(long, default_value_t = 30.0)]
        pub(crate) overall_timeout_s: f64,

        /// Baseline JIT mode.
        #[arg(long, default_value = "off")]
        pub(crate) baseline_mode: String,

        /// Candidate JIT mode.
        #[arg(long, value_enum)]
        pub(crate) candidate_mode: Option<JitMode>,

        /// SAT variant passed to ay for DIMACS probes.
        #[arg(long, default_value = "default")]
        pub(crate) sat_variant: String,

        /// Pass --native for PB probes.
        #[arg(long)]
        pub(crate) pb_native: bool,

        /// Extra ay argument before the probe path; may be repeated.
        #[arg(long = "ay-arg", num_args = 1, allow_hyphen_values = true)]
        pub(crate) ay_args: Vec<String>,

        /// Print commands without executing probes.
        #[arg(long)]
        pub(crate) dry_run: bool,

        /// Emit machine-readable JSON.
        #[arg(long)]
        pub(crate) json: bool,

        /// Write JSON report to this path.
        #[arg(long)]
        pub(crate) out: Option<PathBuf>,

        /// Exit non-zero when the gate fails.
        #[arg(long)]
        pub(crate) fail_on_gate_fail: bool,
    }

    pub(crate) fn run(args: ProbeArgs) -> Result<()> {
        let root = repo_root();
        let options = competition_jit_probe::RoiProbeOptions {
            root: root.clone(),
            track: args.track.as_str().to_string(),
            artifact: args.artifact,
            matrix: if args.matrix.is_absolute() {
                args.matrix
            } else {
                root.join(args.matrix)
            },
            ay: args.ay,
            probes: args.probes,
            max_probes: args.max_probes,
            timeout_ms: args.timeout_ms,
            wall_timeout_s: args.wall_timeout_s,
            kill_grace_s: args.kill_grace_s,
            overall_timeout_s: args.overall_timeout_s,
            baseline_mode: args.baseline_mode,
            candidate_mode: args.candidate_mode.map(JitMode::as_str).map(str::to_string),
            sat_variant: args.sat_variant,
            pb_native: args.pb_native,
            ay_args: args.ay_args,
            dry_run: args.dry_run,
        };
        let report = competition_jit_probe::run_probe(&options)?;
        if let Some(path) = args.out {
            competition_jit_probe::write_json_report(&path, &report)?;
        }
        if args.json {
            print!("{}", competition_jit_probe::report_json_output(&report)?);
        } else {
            print!("{}", competition_jit_probe::human_report(&report));
        }
        if args.fail_on_gate_fail && report.get("status").and_then(Value::as_str) == Some("fail") {
            anyhow::bail!("competition-jit probe gate failed");
        }
        Ok(())
    }
}
