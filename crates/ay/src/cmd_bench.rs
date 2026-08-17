// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay bench` subcommand — competition-standard benchmarking.
//!
//! Routes to the ay-bench library crate for actual execution.

use std::path::PathBuf;

use clap::{Subcommand, ValueEnum};

#[cfg(any(feature = "bench", test))]
use crate::stats_output;

/// Bench subcommands.
#[derive(Subcommand)]
pub(crate) enum BenchCommand {
    /// Run benchmarks and produce competition-standard scores.
    ///
    /// By default uses short dev timeouts for fast iteration.
    /// Pass --competition to use official competition timeouts:
    ///   SAT-COMP: 5000s, SMT-COMP: 1200s, CHC-COMP: 1800s
    Run {
        /// Eval IDs to run (e.g., chccomp-2025-extra-small-lia)
        eval_ids: Vec<String>,

        /// Run all registered evals
        #[arg(long)]
        all: bool,

        /// Run all evals for a specific competition domain
        #[arg(long, value_enum)]
        domain: Option<Domain>,

        /// Use competition-standard timeouts
        #[arg(long)]
        competition: bool,

        /// Path to AY binary
        ///
        /// Defaults to the currently running `ay` executable so stamped
        /// wrapper paths like `target/user/release/ay bench run ...` do not
        /// silently benchmark a different binary.
        #[arg(long)]
        ay: Option<PathBuf>,

        /// Override timeout (seconds)
        #[arg(long)]
        timeout: Option<f64>,

        /// Write combined scorecard JSON
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Override number of runs per benchmark; omitted uses the eval registry.
        #[arg(long, value_parser = clap::value_parser!(u32).range(1..))]
        runs: Option<u32>,

        /// Zero-based deterministic corpus shard cursor.
        #[arg(long, requires = "shard_size")]
        shard_index: Option<usize>,

        /// Maximum benchmarks in this invocation (1..=4096).
        #[arg(long, requires = "shard_index", value_parser = parse_shard_size)]
        shard_size: Option<usize>,

        /// Reference solver for comparison as name=path; repeatable, e.g.
        /// --reference-solver kissat=reference/kissat-sc2025/build/kissat.
        ///
        /// A bare PATH is accepted and named by its file stem (back-compat
        /// with the old single flag). A bare NAME with no '=' or path
        /// separator resolves via the tool registry (`ay tool which NAME`)
        #[arg(long = "reference-solver", num_args = 1, value_name = "[NAME=]PATH")]
        reference_solvers: Vec<String>,

        /// Stamp a comparison run class into results.json.
        ///
        /// `bench compare run` sets and VERIFIES this itself; a manually
        /// stamped class is recorded as unverified. Unstamped runs carry no
        /// class and must not be quoted as one
        #[arg(long, value_enum, value_name = "CLASS")]
        run_class: Option<RunClass>,

        /// Minimal output
        #[arg(short, long)]
        quiet: bool,

        /// Compute proof-complexity features for each benchmark and
        /// attach them to the persistent results store.
        #[arg(long)]
        with_features: bool,

        /// SAT-COMP track label to record with SAT benchmark results.
        #[arg(long)]
        sat_track: Option<String>,

        /// SAT-COMP AI-class label to record with SAT benchmark results.
        #[arg(long)]
        sat_ai_class: Option<String>,

        /// SAT solver variant to pass through to ay for SAT benchmark runs.
        #[arg(long)]
        sat_variant: Option<String>,
    },

    /// Compare AY against a competition's field under labeled run classes
    Compare(crate::cmd_bench_compare::BenchCompareArgs),

    /// Plan or run the catalog-complete external-reviewer campaign.
    #[cfg(feature = "bench")]
    Campaign(crate::cmd_bench_campaign::CampaignArgs),

    /// Score existing results JSON.
    Score {
        /// Results JSON file
        results_file: PathBuf,

        /// Competition scoring method
        #[arg(long, value_enum)]
        scoring: ScoringMethod,

        /// Timeout used during the run (seconds)
        #[arg(long)]
        timeout: Option<f64>,

        /// SMT-COMP division name
        #[arg(long)]
        division: Option<String>,

        /// CHC-COMP track name
        #[arg(long)]
        track: Option<String>,

        /// Assert competition-standard timeout
        #[arg(long)]
        standard: bool,

        /// Output full score as JSON
        #[arg(long)]
        json: bool,
    },

    /// Print proof-complexity structural features for a single benchmark
    /// file as JSON.
    ///
    /// Supports DIMACS CNF inputs today; other formats will error.
    Features {
        /// Path to the benchmark file (currently `.cnf`/`.dimacs`).
        file: PathBuf,
    },

    /// List all registered evals.
    List,

    /// Print competition scoring methodology.
    Standards,

    /// Run the first-class SAT-COMP delta gate with reference solvers.
    ///
    /// This is the maintained Rust replacement for SAT hard-tail Python
    /// wrappers: it records provenance, runs AY and references, parses SAT
    /// status lines, scores PAR-2, and writes compact durable artifacts.
    SatDelta {
        /// CSV manifest with local_path/path plus optional result/family/category columns.
        #[arg(long)]
        manifest: Option<PathBuf>,

        /// Benchmark root for the built-in hard-tail preset when --manifest is omitted.
        #[arg(long, default_value = "benchmarks/sat/satcomp2024-sample")]
        benchmark_root: PathBuf,

        /// Output directory for report artifacts.
        #[arg(long)]
        out_dir: PathBuf,

        /// Path to AY binary.
        #[arg(long)]
        ay: Option<PathBuf>,

        /// Environment variable for AY solver runs as KEY=VALUE. Repeatable.
        #[arg(long = "ay-env", num_args = 1)]
        ay_env: Vec<String>,

        /// Reference solver as name=path. Repeatable, e.g. --reference-solver kissat=reference/kissat/build/kissat.
        #[arg(long = "reference-solver", num_args = 1)]
        reference_solvers: Vec<String>,

        /// Per-row wall-clock timeout in seconds.
        #[arg(long, default_value = "20")]
        timeout: f64,

        /// SAT variant passed to `ay solve`.
        #[arg(long, default_value = "default")]
        sat_variant: String,

        /// Proof format passed to `ay solve`.
        #[arg(long, default_value = "lrat")]
        proof_format: String,

        /// Proof checker path recorded in provenance.
        #[arg(long)]
        proof_checker: Option<PathBuf>,

        /// Allow and explicitly label dirty-source evidence.
        #[arg(long)]
        allow_dirty: bool,

        /// Fail if any row is wrong or invalid.
        #[arg(long)]
        fail_on_wrong: bool,

        /// Fail if AY loses solved count or PAR-2 to any reference.
        #[arg(long)]
        fail_on_ay_ref_loss: bool,

        /// Fail if the requested AY BCP true-tail relocation gate is not exercised.
        #[arg(long)]
        require_bcp_relocation_exercise: bool,

        /// Fail if the requested AY BCP SEARCH in-place watch scan route is not exercised.
        #[arg(long)]
        require_bcp_search_inplace_watch_scan_exercise: bool,

        /// Fail if the requested AY dense-mutex focused restart route is not exercised.
        #[arg(long)]
        require_dense_mutex_focused_restart_gate_exercise: bool,
    },

    /// Run the native CHC completion gate for CHC-COMP-shaped evidence.
    ///
    /// Loads workbench JSON or CHC-COMP `.set` manifests, runs AY with CHC
    /// stats JSON enabled, scores solved/PAR-2, checks validation and route
    /// telemetry, and writes admission artifacts.
    ChcGate {
        /// Workbench JSON, CSV/TSV, eval YAML, or CHC-COMP `.set` manifest.
        #[arg(long)]
        manifest: Option<PathBuf>,

        /// Benchmark root or CATEGORY=ROOT; recursively discovers *.smt2 files.
        #[arg(long = "root", num_args = 1)]
        roots: Vec<String>,

        /// Use repo-local CHC recovery sample cases.
        #[arg(long)]
        sample: bool,

        /// Output directory for CHC gate artifacts.
        #[arg(long)]
        out_dir: PathBuf,

        /// Path to AY binary.
        #[arg(long)]
        ay: Option<PathBuf>,

        /// Per-row wall-clock timeout in seconds.
        #[arg(long)]
        timeout: f64,

        /// Baseline summary JSON for solved/PAR-2 regression checks.
        #[arg(long)]
        baseline: Option<PathBuf>,

        /// Override or label the manifest category.
        #[arg(long)]
        category: Option<String>,

        /// Require all 11 core CHC categories to appear.
        #[arg(long)]
        require_all_categories: bool,

        /// Require at least one row to exercise this route counter. Repeatable.
        #[arg(long = "require-route-counter", num_args = 1)]
        require_route_counters: Vec<String>,

        /// Allow and explicitly label dirty-source evidence as non-promotable.
        #[arg(long)]
        allow_dirty: bool,

        /// Fail if any row is wrong.
        #[arg(long)]
        fail_on_wrong: bool,

        /// Fail if any row is invalid or lacks mandatory validation telemetry.
        #[arg(long)]
        fail_on_invalid: bool,

        /// Minimum solved-count delta versus baseline.
        #[arg(long, default_value = "0")]
        min_solved_delta: isize,

        /// Maximum allowed PAR-2 regression percentage versus baseline.
        #[arg(long, default_value = "0")]
        max_par2_regression_pct: f64,
    },

    /// Generate or validate a fail-closed SAT-COMP mirror manifest.
    ///
    /// By default this requires every compressed benchmark file to have a
    /// definitive SAT/UNSAT label and exits non-zero with a structured report
    /// if any label is missing, stale, duplicate, or unknown.
    SatMirrorManifest {
        /// SAT-COMP mirror root. Defaults to $SATCOMP_OFFICIAL_MIRROR or
        /// ~/win-all-software-proof-competitions.
        #[arg(long)]
        mirror_root: Option<PathBuf>,

        /// Competition year under benchmarks/sat/<year>.
        #[arg(long, default_value = "2024")]
        year: String,

        /// Explicit compressed benchmark directory.
        #[arg(long)]
        benchmarks_dir: Option<PathBuf>,

        /// Explicit expected-result labels CSV.
        #[arg(long)]
        labels_csv: Option<PathBuf>,

        /// Explicit official-unknown labels CSV.
        ///
        /// Rows in this file may materialize as `unknown` without using the
        /// broad `--allow-unknown` inventory escape hatch.
        #[arg(long)]
        official_unknowns_csv: Option<PathBuf>,

        /// Optional official metadata CSV with "hash filename family author".
        #[arg(long)]
        metadata_csv: Option<PathBuf>,

        /// Required compressed benchmark count.
        #[arg(long, default_value = "400")]
        expected_count: usize,

        /// Write CSV manifest on success.
        #[arg(long)]
        out_csv: Option<PathBuf>,

        /// Write JSON details manifest on success.
        #[arg(long)]
        out_json: Option<PathBuf>,

        /// Always write a JSON completeness report.
        #[arg(long)]
        report_json: Option<PathBuf>,

        /// Materialize missing/unknown labels as unknown for inventory only.
        #[arg(long)]
        allow_unknown: bool,
    },

    /// Diff persisted bench results between two commits.
    ///
    /// Reads the SQLite store at `.ay-bench/results.sqlite` (written by
    /// `ay-bench run`) and reports regressions, improvements, and slowdowns
    /// between the two revisions. Exits non-zero if any regression is
    /// detected so commit hooks / CI can block bad changes.
    Diff {
        /// Base revision (default: HEAD~10). Accepts any `git rev-parse`-able input.
        #[arg(long, default_value = "HEAD~10")]
        base: String,

        /// Head revision (default: HEAD). Accepts any `git rev-parse`-able input.
        #[arg(long, default_value = "HEAD")]
        head: String,

        /// Only diff the given eval (e.g. `chccomp-2025-extra-small-lia`).
        #[arg(long)]
        eval: Option<String>,

        /// Output format.
        #[arg(long, value_enum, default_value_t = DiffFormat::Table)]
        format: DiffFormat,

        /// Slowdown threshold in percent (runtime delta flagged above this).
        #[arg(long, default_value = "20.0")]
        slowdown_threshold_pct: f64,
    },

    /// Harvest a reference solver's results across a corpus to build the
    /// differential-suite baseline.
    ///
    /// Writes rows to `.ay-bench/baselines.sqlite` keyed by
    /// `(corpus, benchmark_path, solver)`. Each row records the reference
    /// solver's answer (sat/unsat/unknown/timeout/error), wall-clock runtime,
    /// exit code, and the benchmark's declared expected status.
    Harvest {
        /// Corpus name used as the baseline store key (e.g. "qfuf-neq").
        #[arg(long)]
        corpus: String,

        /// Directory containing the benchmark files (recurses into subdirs).
        #[arg(long)]
        dir: PathBuf,

        /// Reference solver binary: bare name (looked up via PATH) or absolute path.
        #[arg(long, default_value = "z3")]
        solver: String,

        /// Per-benchmark wall-clock timeout in seconds.
        #[arg(long, default_value = "30")]
        timeout: f64,

        /// Parallelism (0 = num CPUs).
        #[arg(long, default_value = "0")]
        jobs: usize,

        /// Maximum number of benchmarks to harvest (0 = no limit).
        #[arg(long, default_value = "0")]
        limit: usize,

        /// File extensions to include (comma-separated, no leading dot).
        #[arg(long, default_value = "smt2,cnf")]
        extensions: String,
    },

    /// Verify an AY results.json against a previously harvested reference
    /// baseline, flagging any `sound_bug` classification (ay disagrees with
    /// the reference on a definite sat/unsat answer).
    ///
    /// Exits non-zero iff at least one sound-bug disagreement is found.
    Verify {
        /// Corpus name in the baseline store.
        #[arg(long)]
        corpus: String,

        /// AY results JSON (from `ay bench run ... -o results.json`).
        #[arg(long)]
        results: PathBuf,

        /// Reference solver to compare against (matches baseline row's solver).
        #[arg(long, default_value = "z3")]
        reference_solver: String,

        /// Emit the report as JSON instead of a human-readable table.
        #[arg(long)]
        json: bool,
    },

    /// Cross-verify a baseline corpus across 2-3 reference solvers and flag
    /// benchmarks where the solvers disagree with each other (`ref_wrong`
    /// rule).
    ///
    /// Reads rows from `.ay-bench/baselines.sqlite` (populated by
    /// `ay bench harvest`) — no solver is invoked. Exits non-zero iff at
    /// least one benchmark is classified as `dispute` (two reference
    /// solvers returned different definite answers).
    CrossVerify {
        /// Corpus name in the baseline store.
        #[arg(long)]
        corpus: String,

        /// Comma-separated reference solver short names to cross-check
        /// (e.g. `z3,golem` or `z3,golem,cvc5`). Must match the `solver`
        /// column in the baseline store. At least two distinct entries.
        #[arg(long)]
        solvers: String,

        /// Emit the report as JSON instead of a human-readable table.
        #[arg(long)]
        json: bool,
    },
}

#[derive(Clone, Copy, ValueEnum)]
pub(crate) enum DiffFormat {
    Table,
    Json,
    /// GitHub-flavored markdown (suitable for PR comments).
    Markdown,
}

#[derive(Clone, ValueEnum)]
pub(crate) enum Domain {
    /// SAT Competition (PAR-2 scoring)
    Sat,
    /// SMT-COMP (lexicographic scoring)
    Smt,
    /// CHC-COMP (solved count + CPU tiebreaker)
    Chc,
    /// HWMCC (solved count + CPU tiebreaker)
    Hwmcc,
}

impl std::fmt::Display for Domain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sat => write!(f, "sat"),
            Self::Smt => write!(f, "smt"),
            Self::Chc => write!(f, "chc"),
            Self::Hwmcc => write!(f, "hwmcc"),
        }
    }
}

/// Comparison run class recorded by `bench run --run-class`.
///
/// A number never travels without its class. Plain `bench run` only STAMPS
/// the class (plus a host fingerprint) into results.json; verification
/// against cited official specs belongs to `bench compare check`/`run`.
#[derive(Clone, Copy, ValueEnum)]
pub(crate) enum RunClass {
    /// Local run on hardware matching the cited official machine specs
    Replay,
    /// Developer machine, specs recorded; verdicts meaningful, timings weak
    Laptop,
}

impl std::fmt::Display for RunClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Replay => write!(f, "replay"),
            Self::Laptop => write!(f, "laptop"),
        }
    }
}

#[cfg(any(feature = "bench", test))]
fn report_json_with_build(mut value: serde_json::Value) -> serde_json::Value {
    if let serde_json::Value::Object(map) = &mut value {
        map.insert(
            "ay_build".to_string(),
            stats_output::BUILD_PROVENANCE.json_value(),
        );
    }
    value
}

#[cfg(any(feature = "bench", test))]
fn resolve_bench_ay_path(ay: Option<PathBuf>) -> anyhow::Result<PathBuf> {
    use anyhow::Context as _;

    match ay {
        Some(path) => Ok(path),
        None => std::env::current_exe().context("resolve current ay executable for `bench run`"),
    }
}

#[allow(clippy::enum_variant_names)]
#[derive(Clone, ValueEnum)]
pub(crate) enum ScoringMethod {
    /// SAT Competition PAR-2
    SatComp,
    /// SMT-COMP lexicographic
    SmtComp,
    /// CHC-COMP solved count
    ChcComp,
    /// HWMCC solved count
    HwmccComp,
}

// Keep CLI parsing available in `cli`-only builds where the optional
// `ay-bench` dependency is intentionally absent. The execution layer repeats
// this fail-closed bound in `ay_bench::native::MAX_NATIVE_SHARD_SIZE`.
const MAX_NATIVE_SHARD_SIZE: usize = 4096;

#[cfg(feature = "bench")]
const _: () = assert!(MAX_NATIVE_SHARD_SIZE == ay_bench::native::MAX_NATIVE_SHARD_SIZE);

fn parse_shard_size(value: &str) -> Result<usize, String> {
    let parsed = value
        .parse::<usize>()
        .map_err(|_| format!("invalid shard size {value:?}"))?;
    if (1..=MAX_NATIVE_SHARD_SIZE).contains(&parsed) {
        Ok(parsed)
    } else {
        Err(format!(
            "shard size must be in 1..={MAX_NATIVE_SHARD_SIZE}, got {parsed}"
        ))
    }
}

/// Entry point for `ay bench` subcommands.
#[cfg(not(feature = "bench"))]
pub(crate) fn run(_command: BenchCommand) -> anyhow::Result<()> {
    anyhow::bail!("ay bench was built without benchmark support; rebuild with --features bench")
}

/// Entry point for `ay bench` subcommands.
#[cfg(feature = "bench")]
pub(crate) fn run(command: BenchCommand) -> anyhow::Result<()> {
    match command {
        BenchCommand::Compare(args) => crate::cmd_bench_compare::run(args),
        BenchCommand::Campaign(args) => crate::cmd_bench_campaign::run(args),
        BenchCommand::Run {
            eval_ids,
            all,
            domain,
            competition,
            ay,
            timeout,
            output,
            runs,
            shard_index,
            shard_size,
            reference_solvers,
            run_class,
            quiet,
            with_features,
            sat_track,
            sat_ai_class,
            sat_variant,
        } => {
            let ay = resolve_bench_ay_path(ay)?;
            let reference_solvers = parse_run_reference_solvers(
                reference_solvers,
                &ay_bench::runner::repo_root_public(),
            )?;
            ay_bench::runner::cmd_run(ay_bench::runner::RunArgs {
                eval_ids,
                all,
                domain: domain.map(|d| d.to_string()),
                competition,
                ay,
                timeout,
                output,
                runs,
                shard_index,
                shard_size,
                reference_solvers,
                run_class: run_class.map(|c| c.to_string()),
                quiet,
                with_features,
                sat_track,
                sat_ai_class,
                sat_variant,
                resource_memory_cap_mib: None,
                resource_core_cap: None,
            })?;
            Ok(())
        }
        BenchCommand::Score {
            results_file,
            scoring,
            timeout,
            division,
            track,
            standard,
            json,
        } => {
            let method = match scoring {
                ScoringMethod::SatComp => ay_bench::scoring::Competition::SatComp,
                ScoringMethod::SmtComp => ay_bench::scoring::Competition::SmtComp,
                ScoringMethod::ChcComp => ay_bench::scoring::Competition::ChcComp,
                ScoringMethod::HwmccComp => ay_bench::scoring::Competition::HwmccComp,
            };
            ay_bench::scoring::cmd_score(ay_bench::scoring::ScoreArgs {
                results_file,
                method,
                timeout,
                division,
                track,
                standard,
                json,
            })?;
            Ok(())
        }
        BenchCommand::Features { file } => {
            ay_bench::features::cmd_features(file)?;
            Ok(())
        }
        BenchCommand::List => {
            ay_bench::runner::cmd_list()?;
            Ok(())
        }
        BenchCommand::Standards => {
            ay_bench::scoring::print_standards();
            Ok(())
        }
        BenchCommand::SatDelta {
            manifest,
            benchmark_root,
            out_dir,
            ay,
            ay_env,
            reference_solvers,
            timeout,
            sat_variant,
            proof_format,
            proof_checker,
            allow_dirty,
            fail_on_wrong,
            fail_on_ay_ref_loss,
            require_bcp_relocation_exercise,
            require_bcp_search_inplace_watch_scan_exercise,
            require_dense_mutex_focused_restart_gate_exercise,
        } => {
            let ay = resolve_bench_ay_path(ay)?;
            let ay_env = parse_ay_env(ay_env)?;
            let refs = parse_reference_solvers(reference_solvers)?;
            ay_bench::sat_delta::cmd_sat_delta(ay_bench::sat_delta::SatDeltaArgs {
                manifest,
                benchmark_root,
                out_dir,
                ay,
                ay_env,
                reference_solvers: refs,
                timeout_sec: timeout,
                sat_variant,
                proof_format,
                proof_checker,
                allow_dirty,
                fail_on_wrong,
                fail_on_ay_ref_loss,
                require_bcp_relocation_exercise,
                require_bcp_search_inplace_watch_scan_exercise,
                require_dense_mutex_focused_restart_gate_exercise,
            })?;
            Ok(())
        }
        BenchCommand::ChcGate {
            manifest,
            roots,
            sample,
            out_dir,
            ay,
            timeout,
            baseline,
            category,
            require_all_categories,
            require_route_counters,
            allow_dirty,
            fail_on_wrong,
            fail_on_invalid,
            min_solved_delta,
            max_par2_regression_pct,
        } => {
            let ay = resolve_bench_ay_path(ay)?;
            ay_bench::chc_gate::cmd_chc_gate(ay_bench::chc_gate::ChcGateArgs {
                manifest,
                roots,
                sample,
                out_dir,
                ay,
                timeout_sec: timeout,
                baseline,
                category,
                require_all_categories,
                require_route_counters,
                allow_dirty,
                fail_on_wrong,
                fail_on_invalid,
                min_solved_delta,
                max_par2_regression_pct,
            })?;
            Ok(())
        }
        BenchCommand::SatMirrorManifest {
            mirror_root,
            year,
            benchmarks_dir,
            labels_csv,
            official_unknowns_csv,
            metadata_csv,
            expected_count,
            out_csv,
            out_json,
            report_json,
            allow_unknown,
        } => {
            ay_bench::sat_mirror_manifest::cmd_sat_mirror_manifest(
                ay_bench::sat_mirror_manifest::SatMirrorManifestArgs {
                    mirror_root,
                    year,
                    benchmarks_dir,
                    labels_csv,
                    official_unknowns_csv,
                    metadata_csv,
                    expected_count,
                    out_csv,
                    out_json,
                    report_json,
                    allow_unknown,
                },
            )?;
            Ok(())
        }
        BenchCommand::Diff {
            base,
            head,
            eval,
            format,
            slowdown_threshold_pct,
        } => {
            let fmt = match format {
                DiffFormat::Table => ay_bench::runner::DiffFormat::Table,
                DiffFormat::Json => ay_bench::runner::DiffFormat::Json,
                DiffFormat::Markdown => ay_bench::runner::DiffFormat::Markdown,
            };
            let has_regressions = ay_bench::runner::cmd_diff(ay_bench::runner::DiffArgs {
                base,
                head,
                eval,
                format: fmt,
                slowdown_threshold_pct,
            })?;
            if has_regressions {
                // Non-zero exit so commit hooks / CI can block on regressions.
                std::process::exit(1);
            }
            Ok(())
        }
        BenchCommand::Harvest {
            corpus,
            dir,
            solver,
            timeout,
            jobs,
            limit,
            extensions,
        } => {
            let exts: Vec<String> = extensions
                .split(',')
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .map(|s| s.trim_start_matches('.').to_string())
                .collect();
            ay_bench::harvest::cmd_harvest(ay_bench::harvest::HarvestArgs {
                corpus,
                benchmarks_dir: dir,
                solver,
                timeout_s: timeout,
                jobs,
                limit,
                extensions: exts,
                store_path: None,
            })?;
            Ok(())
        }
        BenchCommand::Verify {
            corpus,
            results,
            reference_solver,
            json,
        } => {
            let report = ay_bench::harvest::cmd_verify(ay_bench::harvest::VerifyArgs {
                corpus,
                results_file: results,
                reference_solver,
                baseline_store: None,
                json,
            })?;
            if json {
                let text = serde_json::to_string_pretty(&report_json_with_build(
                    serde_json::to_value(&report)?,
                ))?;
                println!("{text}");
            } else {
                println!("{}", stats_output::BUILD_PROVENANCE.human_banner());
                print!("{}", ay_bench::harvest::render_verify_table(&report));
            }
            if report.has_failures() {
                std::process::exit(1);
            }
            Ok(())
        }
        BenchCommand::CrossVerify {
            corpus,
            solvers,
            json,
        } => {
            let solver_list: Vec<String> = solvers
                .split(',')
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .map(str::to_string)
                .collect();
            let report = ay_bench::cross_verify::cmd_cross_verify(
                ay_bench::cross_verify::CrossVerifyArgs {
                    corpus,
                    solvers: solver_list,
                    baseline_store: None,
                    json,
                },
            )?;
            if json {
                let text = serde_json::to_string_pretty(&report_json_with_build(
                    serde_json::to_value(&report)?,
                ))?;
                println!("{text}");
            } else {
                println!("{}", stats_output::BUILD_PROVENANCE.human_banner());
                print!("{}", ay_bench::cross_verify::render_cross_table(&report));
            }
            if report.has_failures() {
                std::process::exit(1);
            }
            Ok(())
        }
    }
}

#[cfg(any(feature = "bench", test))]
fn parse_reference_solvers(raw: Vec<String>) -> anyhow::Result<Vec<(String, PathBuf)>> {
    raw.into_iter()
        .map(|entry| {
            let (name, path) = entry.split_once('=').ok_or_else(|| {
                anyhow::anyhow!("--reference-solver must be name=path, got {entry:?}")
            })?;
            if name.trim().is_empty() || path.trim().is_empty() {
                return Err(anyhow::anyhow!(
                    "--reference-solver must have non-empty name and path, got {entry:?}"
                ));
            }
            Ok((name.trim().to_string(), PathBuf::from(path.trim())))
        })
        .collect()
}

/// Tool registry consulted when a `bench run --reference-solver` value is a
/// bare NAME. Kept as data under `ay tool`'s ownership; this module only
/// reads it for resolution.
#[cfg(any(feature = "bench", test))]
const REFERENCE_TOOLS_MANIFEST: &str = "reference/tools.toml";

/// Parse repeatable `bench run --reference-solver [NAME=]PATH` values.
///
/// Three forms per value:
///   - `NAME=PATH` — explicit pair (delegates to [`parse_reference_solvers`],
///     the `sat-delta` parser).
///   - bare PATH (contains a path separator) — named from its file name;
///     byte-compatible with the old single `--reference-solver PATH` flag,
///     including paths whose directories contain `=`.
///   - bare NAME (no `=`, no separator) — resolved via reference/tools.toml
///     (`$AY_TOOL_<NAME>` override, install target, extra paths); when
///     unresolved the bare name is kept so $PATH lookup happens at spawn
///     time, exactly as the old flag behaved.
#[cfg(any(feature = "bench", test))]
fn parse_run_reference_solvers(
    raw: Vec<String>,
    repo_root: &std::path::Path,
) -> anyhow::Result<Vec<(String, PathBuf)>> {
    raw.into_iter()
        .map(|entry| {
            let has_separator = |s: &str| s.contains('/') || s.contains(std::path::MAIN_SEPARATOR);
            if let Some((name, _)) = entry.split_once('=') {
                if !has_separator(name) {
                    let mut parsed = parse_reference_solvers(vec![entry])?;
                    return Ok(parsed.remove(0));
                }
            }
            if has_separator(&entry) {
                let path = PathBuf::from(&entry);
                return Ok((reference_display_name(&path), path));
            }
            let name = entry.trim().to_string();
            if name.is_empty() {
                return Err(anyhow::anyhow!(
                    "--reference-solver must be [NAME=]PATH, got {entry:?}"
                ));
            }
            let path = resolve_reference_solver_name(&name, repo_root);
            Ok((name, path))
        })
        .collect()
}

/// Legacy display name for a reference solver path — the naming the single
/// `--reference-solver PATH` flag recorded into results.json.
#[cfg(any(feature = "bench", test))]
fn reference_display_name(path: &std::path::Path) -> String {
    path.file_name()
        .map(|n| n.to_string_lossy().to_string())
        .unwrap_or_else(|| path.display().to_string())
}

/// `$AY_TOOL_<NAME>` env-override key: name uppercased, non-alphanumerics
/// mapped to `_` (the fixed resolution-order contract shared with `ay tool`).
#[cfg(any(feature = "bench", test))]
fn reference_tool_env_key(name: &str) -> String {
    let mapped: String = name
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() {
                c.to_ascii_uppercase()
            } else {
                '_'
            }
        })
        .collect();
    format!("AY_TOOL_{mapped}")
}

/// Resolve a bare reference-solver NAME: `$AY_TOOL_<NAME>` override, then the
/// tool registry's install target and fallback paths, then the bare name
/// itself (left for $PATH resolution when the solver is spawned).
#[cfg(any(feature = "bench", test))]
fn resolve_reference_solver_name(name: &str, repo_root: &std::path::Path) -> PathBuf {
    if let Some(path) = std::env::var_os(reference_tool_env_key(name)) {
        return PathBuf::from(path);
    }
    resolve_reference_solver_via_registry(name, repo_root).unwrap_or_else(|| PathBuf::from(name))
}

/// Minimal reader over reference/tools.toml — resolution fields only.
/// `ay tool` owns the full schema, validation, and installs.
#[cfg(any(feature = "bench", test))]
#[derive(serde::Deserialize)]
struct ReferenceToolsDoc {
    #[serde(default)]
    tool: Vec<ReferenceToolEntry>,
}

#[cfg(any(feature = "bench", test))]
#[derive(serde::Deserialize)]
struct ReferenceToolEntry {
    name: String,
    #[serde(default)]
    bin: Option<String>,
    #[serde(default)]
    install_to: Option<String>,
    #[serde(default)]
    extra_paths: Vec<String>,
}

#[cfg(any(feature = "bench", test))]
fn resolve_reference_solver_via_registry(
    name: &str,
    repo_root: &std::path::Path,
) -> Option<PathBuf> {
    let manifest = repo_root.join(REFERENCE_TOOLS_MANIFEST);
    let text = std::fs::read_to_string(&manifest).ok()?;
    let doc: ReferenceToolsDoc = toml::from_str(&text).ok()?;
    let entry = doc.tool.into_iter().find(|t| t.name == name)?;

    let mut candidates = Vec::new();
    if let Some(install_to) = entry.install_to.as_deref() {
        let target = expand_reference_path(install_to, repo_root);
        // Directory targets (e.g. install_to="reference/cadical",
        // bin="build/cadical") resolve through `bin`; file targets
        // (e.g. install_to="~/.local/bin/drat-trim") resolve directly.
        if let Some(bin) = entry.bin.as_deref() {
            candidates.push(target.join(bin));
        }
        candidates.push(target);
    }
    for extra in &entry.extra_paths {
        candidates.push(expand_reference_path(extra, repo_root));
    }
    candidates.into_iter().find(|c| c.is_file())
}

#[cfg(any(feature = "bench", test))]
fn expand_reference_path(raw: &str, repo_root: &std::path::Path) -> PathBuf {
    if let Some(rest) = raw.strip_prefix("~/") {
        if let Some(home) = std::env::var_os("HOME") {
            return PathBuf::from(home).join(rest);
        }
    }
    let path = PathBuf::from(raw);
    if path.is_absolute() {
        path
    } else {
        repo_root.join(path)
    }
}

#[cfg(any(feature = "bench", test))]
fn parse_ay_env(raw: Vec<String>) -> anyhow::Result<Vec<(String, String)>> {
    raw.into_iter()
        .map(|entry| {
            let (key, value) = entry
                .split_once('=')
                .ok_or_else(|| anyhow::anyhow!("--ay-env must be KEY=VALUE, got {entry:?}"))?;
            if key.is_empty() {
                return Err(anyhow::anyhow!(
                    "--ay-env must have a non-empty key, got {entry:?}"
                ));
            }
            if key.contains('\0') || value.contains('\0') {
                return Err(anyhow::anyhow!(
                    "--ay-env cannot contain NUL bytes, got {entry:?}"
                ));
            }
            Ok((key.to_string(), value.to_string()))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_report_json_with_build_injects_top_level_provenance() {
        let report = serde_json::json!({
            "corpus": "sample",
            "total": 1,
        });
        let wrapped = report_json_with_build(report);

        assert_eq!(wrapped["corpus"], "sample");
        assert_eq!(
            wrapped["ay_build"]["stamp"],
            stats_output::BUILD_PROVENANCE.stamp
        );
        assert_eq!(
            wrapped["ay_build"]["version"],
            stats_output::BUILD_PROVENANCE.version
        );
    }

    #[test]
    fn test_resolve_bench_ay_path_prefers_explicit_override() {
        let explicit = PathBuf::from("/tmp/custom-ay");
        let resolved =
            resolve_bench_ay_path(Some(explicit.clone())).expect("resolve explicit ay path");
        assert_eq!(resolved, explicit);
    }

    #[test]
    fn test_resolve_bench_ay_path_defaults_to_current_executable() {
        let resolved = resolve_bench_ay_path(None).expect("resolve current ay path");
        assert!(
            resolved.is_absolute(),
            "bench run default should resolve to the invoked ay executable path"
        );
        assert!(
            resolved
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("ay")),
            "bench run default should resolve to the running ay binary: {}",
            resolved.display()
        );
    }

    #[test]
    fn test_parse_ay_env_preserves_key_value_pairs() {
        let parsed = parse_ay_env(vec![
            "AY_SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION=1".to_string(),
            "AY_EMPTY=".to_string(),
        ])
        .unwrap();

        assert_eq!(
            parsed,
            vec![
                (
                    "AY_SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION".to_string(),
                    "1".to_string()
                ),
                ("AY_EMPTY".to_string(), String::new()),
            ]
        );
    }

    #[test]
    fn test_parse_ay_env_rejects_missing_equals() {
        let err = parse_ay_env(vec!["AY_SAT_FLAG".to_string()]).unwrap_err();

        assert!(err.to_string().contains("--ay-env must be KEY=VALUE"));
    }

    // --- bench run --reference-solver [NAME=]PATH parsing ---

    #[test]
    fn test_parse_run_reference_solvers_name_path_form() {
        let root = tempfile::tempdir().expect("tempdir");
        let parsed = parse_run_reference_solvers(
            vec!["kissat=reference/kissat-sc2025/build/kissat".to_string()],
            root.path(),
        )
        .unwrap();

        assert_eq!(
            parsed,
            vec![(
                "kissat".to_string(),
                PathBuf::from("reference/kissat-sc2025/build/kissat"),
            )]
        );
    }

    #[test]
    fn test_parse_run_reference_solvers_bare_path_form_keeps_legacy_naming() {
        let root = tempfile::tempdir().expect("tempdir");
        let parsed = parse_run_reference_solvers(
            vec!["reference/cadical/build/cadical".to_string()],
            root.path(),
        )
        .unwrap();

        assert_eq!(
            parsed,
            vec![(
                "cadical".to_string(),
                PathBuf::from("reference/cadical/build/cadical"),
            )]
        );
    }

    #[test]
    fn test_parse_run_reference_solvers_bare_path_with_equals_in_directory() {
        // The old single flag accepted any path; directories containing '='
        // must not be split as NAME=PATH.
        let root = tempfile::tempdir().expect("tempdir");
        let parsed =
            parse_run_reference_solvers(vec!["runs/width=15/fake-z3".to_string()], root.path())
                .unwrap();

        assert_eq!(
            parsed,
            vec![(
                "fake-z3".to_string(),
                PathBuf::from("runs/width=15/fake-z3")
            )]
        );
    }

    #[test]
    fn test_parse_run_reference_solvers_bare_name_falls_back_to_path_lookup() {
        // No tools registry under this root: the bare name is kept so the
        // solver spawn resolves it on $PATH, exactly like the old flag.
        let root = tempfile::tempdir().expect("tempdir");
        let parsed =
            parse_run_reference_solvers(vec!["no-such-registered-tool".to_string()], root.path())
                .unwrap();

        assert_eq!(
            parsed,
            vec![(
                "no-such-registered-tool".to_string(),
                PathBuf::from("no-such-registered-tool"),
            )]
        );
    }

    #[test]
    fn test_parse_run_reference_solvers_bare_name_resolves_via_tool_registry() {
        let root = tempfile::tempdir().expect("tempdir");
        let install_dir = root.path().join("reference").join("fake-solver");
        std::fs::create_dir_all(install_dir.join("build")).expect("mkdir install tree");
        let binary = install_dir.join("build").join("fake-solver");
        std::fs::write(&binary, "#!/bin/sh\n").expect("write fake binary");
        std::fs::write(
            root.path().join(REFERENCE_TOOLS_MANIFEST),
            "schema_version = 1\n\n\
             [[tool]]\n\
             name = \"fake-solver\"\n\
             kind = \"reference-solver\"\n\
             bin = \"build/fake-solver\"\n\
             install_to = \"reference/fake-solver\"\n",
        )
        .expect("write tools manifest");

        let parsed =
            parse_run_reference_solvers(vec!["fake-solver".to_string()], root.path()).unwrap();

        assert_eq!(parsed, vec![("fake-solver".to_string(), binary)]);
    }

    #[test]
    fn test_parse_run_reference_solvers_registry_file_target_and_extra_paths() {
        let root = tempfile::tempdir().expect("tempdir");
        let extra = root.path().join("elsewhere").join("fake-checker");
        std::fs::create_dir_all(extra.parent().unwrap()).expect("mkdir extra");
        std::fs::create_dir_all(root.path().join("reference")).expect("mkdir manifest parent");
        std::fs::write(&extra, "#!/bin/sh\n").expect("write fake binary");
        std::fs::create_dir_all(root.path().join("reference")).expect("mkdir reference");
        std::fs::write(
            root.path().join(REFERENCE_TOOLS_MANIFEST),
            format!(
                "schema_version = 1\n\n\
                 [[tool]]\n\
                 name = \"fake-checker\"\n\
                 bin = \"fake-checker\"\n\
                 install_to = \"reference/not-installed\"\n\
                 extra_paths = [{:?}]\n",
                extra.display().to_string(),
            ),
        )
        .expect("write tools manifest");

        let parsed =
            parse_run_reference_solvers(vec!["fake-checker".to_string()], root.path()).unwrap();

        assert_eq!(parsed, vec![("fake-checker".to_string(), extra)]);
    }

    #[test]
    fn test_parse_run_reference_solvers_preserves_order_and_mixed_forms() {
        let root = tempfile::tempdir().expect("tempdir");
        let parsed = parse_run_reference_solvers(
            vec![
                "kissat=reference/kissat/build/kissat".to_string(),
                "reference/cadical/build/cadical".to_string(),
            ],
            root.path(),
        )
        .unwrap();

        assert_eq!(
            parsed,
            vec![
                (
                    "kissat".to_string(),
                    PathBuf::from("reference/kissat/build/kissat"),
                ),
                (
                    "cadical".to_string(),
                    PathBuf::from("reference/cadical/build/cadical"),
                ),
            ]
        );
    }

    #[test]
    fn test_parse_run_reference_solvers_rejects_empty_name_or_path() {
        let root = tempfile::tempdir().expect("tempdir");

        let err =
            parse_run_reference_solvers(vec!["=only-path".to_string()], root.path()).unwrap_err();
        assert!(err
            .to_string()
            .contains("--reference-solver must have non-empty name and path"));

        let err =
            parse_run_reference_solvers(vec!["kissat=".to_string()], root.path()).unwrap_err();
        assert!(err
            .to_string()
            .contains("--reference-solver must have non-empty name and path"));
    }

    #[test]
    fn test_reference_tool_env_key_uppercases_and_maps_non_alnum() {
        assert_eq!(reference_tool_env_key("drat-trim"), "AY_TOOL_DRAT_TRIM");
        assert_eq!(reference_tool_env_key("z3"), "AY_TOOL_Z3");
        assert_eq!(
            reference_tool_env_key("kissat-sc2025"),
            "AY_TOOL_KISSAT_SC2025"
        );
    }
}
