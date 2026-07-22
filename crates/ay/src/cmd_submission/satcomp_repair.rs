// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-COMP repair diagnostics owned by the Rust submission/preflight CLI.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File};
use std::io::{Cursor, Write};
mod neighborhood;
mod solver_runner;
mod source_frame_audit;
mod witness;

use self::neighborhood::{grow_free_vars, grow_neighborhoods, write_flip_cnf, write_reduced_cnf};
use self::solver_runner::{
    falsified_clause_ids, parse_solver_model, run_solver, run_version, verify_drat,
    write_dimacs_model,
};
use self::source_frame_audit::run_source_frame_audit;
use self::witness::run_witness_audit;

use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{bail, Context, Result};
use ay_sat::dimacs_core::{parse_dimacs_events, DimacsEvent, DimacsRecordRef};
use clap::{Args, Subcommand};
use serde_json::{json, Value as JsonValue};

use super::{display_path_for_report, make_temp_dir, sha256_file};
use crate::build_info::BUILD_INFO;

const DEFAULT_TARGET_CNF: &str =
    "benchmarks/sat/satcomp2024-sample/c5ae0ec49de0959cd14431ce851c14f8-Circuit_multiplier22.cnf.xz";
const DEFAULT_W210_LEDGERS: &[&str] = &[
    "the development design notes",
    "the development design notes",
    "the development design notes",
];
const DEFAULT_SOURCE_FRAME_ROWS: &str = "the development design notes";
const DEFAULT_MISSING_SOURCE_FRAME_ROWS: &str = "the development design notes";
const DEFAULT_SOURCE_HOOK_TARGETS: &str = "the development design notes";
const DEFAULT_COMPONENT_SOURCE_HOOKS: &str = "the development design notes";
const DEFAULT_W210_SIDE_EFFECT_REPORT: &str =
    "target/satcomp-circuit-repair-probes/w210-source-frame-choice-side-effect-topk2.json";
const SATCOMP_MODEL_CHECK_SCHEMA: &str = "ay.satcomp-model-check/v1";
const ALLOWED_SOURCE_FRAME_FAMILIES: &[&str] = &[
    "forced_gate_replay_bridge",
    "w210_frontier",
    "w210_scc_choice",
];
const DEFAULT_OUTPUT_DIR: &str = "target/satcomp-circuit-repair-probes";
const MAX_WITNESS_XOR_ARITY: usize = 5;
const MAX_BACKFILL_FRONTIER_REPORT_BYTES: u64 = 64 * 1024 * 1024;

/// Rust-owned SAT-COMP repair diagnostic commands.
// clap subcommand enum: constructed once at CLI parse; boxing arg fields would
// break the derive and buys nothing at this scale.
#[allow(clippy::large_enum_variant)]
#[derive(Subcommand)]
pub(crate) enum SatCompRepairCommand {
    /// Check W210 residual-neighborhood repair surfaces.
    #[command(name = "radius-surface")]
    RadiusSurface(RadiusSurfaceOptions),
    /// Flip selected outside-radius W210 values one at a time.
    #[command(name = "outside-single-flip")]
    OutsideSingleFlip(OutsideSingleFlipOptions),
    /// Probe selected outside-radius component windows.
    #[command(name = "component-window")]
    ComponentWindow(ComponentWindowOptions),
    /// Validate a complete assignment against the original DIMACS CNF.
    #[command(name = "assignment-audit")]
    AssignmentAudit(AssignmentAuditOptions),
    /// Greedily search assignment value deltas against the original DIMACS CNF.
    #[command(name = "assignment-local-search")]
    AssignmentLocalSearch(AssignmentLocalSearchOptions),
    /// Produce a fail-closed full-CNF objective model candidate from W210 state.
    #[command(name = "full-cnf-objective-producer")]
    FullCnfObjectiveProducer(FullCnfObjectiveProducerOptions),
    /// Recover backfill frontier clauses introduced by local-search side effects.
    #[command(name = "introduced-clause-backfill-frontier")]
    IntroducedClauseBackfillFrontier(IntroducedClauseBackfillFrontierOptions),
    /// Materialize candidate variables from an introduced-clause backfill frontier.
    #[command(name = "introduced-clause-backfill-candidates")]
    IntroducedClauseBackfillCandidates(IntroducedClauseBackfillCandidatesOptions),
    /// Search introduced-clause backfill candidates without granting solver authority.
    #[command(name = "introduced-clause-backfill-search")]
    IntroducedClauseBackfillSearch(IntroducedClauseBackfillSearchOptions),
    /// Extract residual anchors from source-frame side-effect diagnostics.
    #[command(name = "residual-side-effect-backbone")]
    ResidualSideEffectBackbone(ResidualSideEffectBackboneOptions),
    /// Probe frontier-assisted reduced-CNF model materialization around a target residual.
    #[command(name = "frontier-assisted-model-materializer")]
    FrontierAssistedModelMaterializer(FrontierAssistedModelMaterializerOptions),
    /// Recover and classify exact circuit witness clauses.
    #[command(name = "witness-audit")]
    WitnessAudit(WitnessAuditOptions),
    /// Validate source-frame repair rows against the original DIMACS.
    #[command(name = "source-frame-audit")]
    SourceFrameAudit(SourceFrameAuditOptions),
}

#[derive(Args, Clone)]
struct CommonOptions {
    /// Original DIMACS CNF, optionally .xz/.gz/.bz2 compressed.
    #[arg(long, default_value = DEFAULT_TARGET_CNF)]
    target_cnf: PathBuf,
    /// W210 TSV ledger with original_var/value columns; repeatable.
    #[arg(long = "w210-ledger", value_name = "PATH")]
    w210_ledgers: Vec<PathBuf>,
    /// ay binary used to solve reduced CNFs. Defaults to the current executable.
    #[arg(long)]
    ay_bin: Option<PathBuf>,
    /// Per-solver-command timeout in seconds.
    #[arg(long, default_value_t = 120)]
    timeout_sec: u64,
    /// Evidence JSON output path.
    #[arg(long)]
    output: Option<PathBuf>,
    /// Reduced-CNF work directory.
    #[arg(long)]
    work_dir: Option<PathBuf>,
    /// Keep reduced CNFs and proofs after the run.
    #[arg(long)]
    retain_work: bool,
}

#[derive(Args, Clone)]
pub(crate) struct RadiusSurfaceOptions {
    #[command(flatten)]
    common: CommonOptions,
    /// Maximum residual-neighborhood radius.
    #[arg(long, default_value_t = 3)]
    max_radius: usize,
}

#[derive(Args, Clone)]
pub(crate) struct OutsideSingleFlipOptions {
    #[command(flatten)]
    common: CommonOptions,
    /// Residual-neighborhood radius kept free.
    #[arg(long, default_value_t = 3)]
    radius: usize,
    /// Limit candidate count after deterministic ordering.
    #[arg(long)]
    candidate_limit: Option<usize>,
    /// Comma/space-separated one-based vars or ranges, e.g. 50,97-99.
    #[arg(long)]
    candidate_vars: Option<String>,
}

#[derive(Args, Clone)]
pub(crate) struct ComponentWindowOptions {
    #[command(flatten)]
    common: CommonOptions,
    /// Seed TSV value-delta file applied before computing residual windows; repeatable.
    #[arg(long = "seed-set-file")]
    seed_set_files: Vec<PathBuf>,
    /// Residual-neighborhood radius kept free.
    #[arg(long, default_value_t = 3)]
    radius: usize,
    /// Window as NAME=VAR[,VAR...] or NAME=START-END; repeatable.
    #[arg(long = "window")]
    windows: Vec<String>,
    /// Generate deterministic outside-radius windows by increasing free-var count.
    #[arg(long)]
    auto_low_free_windows: bool,
    /// Maximum window size generated by `--auto-low-free-windows`.
    #[arg(long, default_value_t = 2)]
    auto_window_max_size: usize,
    /// Generate windows from component hook representative hitting sets.
    #[arg(long)]
    auto_component_hitting_windows: bool,
    /// Generate component combinations whose source families cover every required family.
    #[arg(long)]
    auto_component_family_windows: bool,
    /// Component source-hook target TSV for `--auto-component-hitting-windows`.
    #[arg(long, default_value = DEFAULT_COMPONENT_SOURCE_HOOKS)]
    component_hook_targets: PathBuf,
    /// Limit selected window count after deterministic ordering.
    #[arg(long)]
    window_limit: Option<usize>,
}

#[derive(Args, Clone)]
pub(crate) struct AssignmentAuditOptions {
    #[command(flatten)]
    common: CommonOptions,
    /// DIMACS model/stdout file with `v ...` assignment lines. Defaults to W210 ledgers.
    #[arg(long)]
    dimacs_model: Option<PathBuf>,
    /// Flip one-based variables or ranges after loading the assignment, e.g. 50,97-99.
    #[arg(long = "flip")]
    flips: Vec<String>,
    /// TSV/text file listing one-based variables to flip; repeatable.
    #[arg(long = "flip-file")]
    flip_files: Vec<PathBuf>,
    /// TSV file with original_var and candidate_value/value/set_value columns to apply.
    #[arg(long = "set-file")]
    set_files: Vec<PathBuf>,
}

#[derive(Args, Clone)]
pub(crate) struct AssignmentLocalSearchOptions {
    #[command(flatten)]
    common: CommonOptions,
    /// Seed TSV value-delta file applied before local search; repeatable.
    #[arg(long = "seed-set-file")]
    seed_set_files: Vec<PathBuf>,
    /// Candidate variables as comma/space-separated one-based vars or ranges.
    #[arg(long)]
    candidate_vars: Option<String>,
    /// TSV/text file listing one-based candidate variables; repeatable.
    #[arg(long = "candidate-file")]
    candidate_files: Vec<PathBuf>,
    /// Use variables from the seed residual clauses when no explicit candidates are supplied.
    #[arg(long)]
    residual_candidates: bool,
    /// Limit candidate variables after deterministic ordering.
    #[arg(long)]
    candidate_limit: Option<usize>,
    /// Maximum greedy flip rounds.
    #[arg(long, default_value_t = 4)]
    rounds: usize,
    /// Maximum greedy pair-flip rounds after single-flip descent stalls.
    #[arg(long, default_value_t = 0)]
    pair_rounds: usize,
    /// Limit pair-search candidates after deterministic ordering.
    #[arg(long)]
    pair_candidate_limit: Option<usize>,
    /// Maximum greedy correlated group-flip rounds after pair search stalls.
    #[arg(long, default_value_t = 0)]
    group_rounds: usize,
    /// Maximum exact component-family group-flip rounds after pair search stalls.
    #[arg(long, default_value_t = 0)]
    component_family_rounds: usize,
    /// Limit exact component-family groups after deterministic ordering.
    #[arg(long)]
    component_family_group_limit: Option<usize>,
    /// Maximum source-frame required-value overlay rounds after pair search stalls.
    #[arg(long, default_value_t = 0)]
    source_frame_value_rounds: usize,
    /// Limit source-frame required-value overlays after deterministic ordering.
    #[arg(long)]
    source_frame_value_limit: Option<usize>,
    /// Maximum source-frame literal-choice beam rounds after required-value overlays.
    #[arg(long, default_value_t = 0)]
    source_frame_choice_rounds: usize,
    /// Limit source-frame literal-choice candidate rows after deterministic ordering.
    #[arg(long)]
    source_frame_choice_limit: Option<usize>,
    /// Beam width for source-frame literal-choice search.
    #[arg(long, default_value_t = 1024)]
    source_frame_choice_beam_width: usize,
    /// Keep all non-worsening source-frame choices plus top K worsening choices per clause.
    #[arg(
        long,
        alias = "source-frame-choice-side-effect-top-k-per-clause",
        value_name = "K"
    )]
    source_frame_choice_side_effect_top_per_clause: Option<usize>,
    /// Real source-frame input rows for `--source-frame-value-rounds`.
    #[arg(long, default_value = DEFAULT_SOURCE_FRAME_ROWS)]
    source_frame_rows: PathBuf,
    /// Current remaining-clause value ledger to feed current-residual source-frame choice search.
    #[arg(
        long = "source-frame-choice-current-remaining-clause-value-ledger",
        alias = "source-frame-choice-remaining-clause-ledger",
        value_name = "PATH"
    )]
    source_frame_choice_current_remaining_clause_value_ledger: Option<PathBuf>,
    /// Add generic choices from the current residual clauses and recompute them each choice round.
    #[arg(long)]
    source_frame_choice_dynamic_residual_choices: bool,
    /// Allow a nonempty neutral source-frame choice when no strict improvement exists.
    #[arg(long)]
    source_frame_choice_accept_neutral: bool,
    /// Component source-hook target TSV for `--component-family-rounds`.
    #[arg(long, default_value = DEFAULT_COMPONENT_SOURCE_HOOKS)]
    component_hook_targets: PathBuf,
    /// Number of variables flipped together in correlated group search.
    #[arg(long, default_value_t = 3)]
    group_size: usize,
    /// Sliding candidate window size used to build correlated group templates.
    #[arg(long, default_value_t = 12)]
    group_window_size: usize,
    /// Limit group-search candidates after deterministic ordering.
    #[arg(long)]
    group_candidate_limit: Option<usize>,
    /// Variables of which each group must include at least `--group-require-count`.
    #[arg(long)]
    group_require_vars: Option<String>,
    /// TSV/text file listing variables of which each group must include at least `--group-require-count`.
    #[arg(long = "group-require-file")]
    group_require_files: Vec<PathBuf>,
    /// Minimum required-variable count for each group when a required set is supplied.
    #[arg(long, default_value_t = 1)]
    group_require_count: usize,
    /// Maximum unique group templates evaluated per group-search round.
    #[arg(long, default_value_t = 25_000)]
    group_evaluation_limit: usize,
}

#[derive(Args, Clone)]
pub(crate) struct FullCnfObjectiveProducerOptions {
    #[command(flatten)]
    common: CommonOptions,
    /// Maximum strict full-CNF source-frame literal-choice rounds.
    #[arg(long, default_value_t = 4)]
    source_frame_choice_rounds: usize,
    /// Limit source-frame literal-choice candidate rows after deterministic ordering.
    #[arg(long)]
    source_frame_choice_limit: Option<usize>,
    /// Beam width for source-frame literal-choice search.
    #[arg(long, default_value_t = 1024)]
    source_frame_choice_beam_width: usize,
    /// Keep all non-worsening source-frame choices plus top K worsening choices per clause.
    #[arg(
        long,
        alias = "source-frame-choice-side-effect-top-k-per-clause",
        value_name = "K"
    )]
    source_frame_choice_side_effect_top_per_clause: Option<usize>,
    /// Real source-frame input rows.
    #[arg(long, default_value = DEFAULT_SOURCE_FRAME_ROWS)]
    source_frame_rows: PathBuf,
    /// Current remaining-clause value ledger to feed current-residual source-frame choice search.
    #[arg(
        long = "source-frame-choice-current-remaining-clause-value-ledger",
        alias = "source-frame-choice-remaining-clause-ledger",
        value_name = "PATH"
    )]
    source_frame_choice_current_remaining_clause_value_ledger: Option<PathBuf>,
    /// Add generic choices from the current residual clauses and recompute them each choice round.
    #[arg(long)]
    source_frame_choice_dynamic_residual_choices: bool,
    /// Allow an unseen nonempty neutral full-CNF residual move as a diagnostic plateau bridge.
    #[arg(long)]
    source_frame_choice_accept_neutral: bool,
    /// Optional retained SAT model stdout path, emitted only after residual count reaches zero.
    #[arg(long, value_name = "PATH")]
    model_stdout_output: Option<PathBuf>,
    /// Retained `ay check model --json` verdict path for the emitted model stdout.
    #[arg(long, value_name = "PATH")]
    checker_verdict_json: Option<PathBuf>,
    /// Exit status from the retained model-check command.
    #[arg(long)]
    checker_exit_status: Option<i32>,
    /// Exact retained checker command argv; repeat the flag once per argv cell.
    #[arg(long = "checker-command", value_name = "ARG")]
    checker_command: Vec<String>,
}

#[derive(Args, Clone)]
pub(crate) struct IntroducedClauseBackfillFrontierOptions {
    /// Original DIMACS CNF, optionally .xz/.gz/.bz2 compressed.
    #[arg(long, default_value = DEFAULT_TARGET_CNF)]
    target_cnf: PathBuf,
    /// assignment-local-search JSON report containing source-frame choice side-effect summaries.
    #[arg(
        long = "assignment-local-search-report",
        alias = "local-search-report",
        alias = "report",
        value_name = "PATH"
    )]
    assignment_local_search_report: PathBuf,
    /// Evidence JSON output path.
    #[arg(long)]
    output: Option<PathBuf>,
    /// Optional TSV output path for one row per unique introduced clause.
    #[arg(long = "tsv-output", alias = "output-tsv", value_name = "PATH")]
    tsv_output: Option<PathBuf>,
}

#[derive(Args, Clone)]
pub(crate) struct IntroducedClauseBackfillCandidatesOptions {
    /// introduced-clause-backfill-frontier JSON report.
    #[arg(
        long = "frontier-report",
        alias = "introduced-clause-backfill-frontier",
        alias = "report",
        value_name = "PATH"
    )]
    frontier_report: PathBuf,
    /// Evidence JSON output path.
    #[arg(long)]
    output: Option<PathBuf>,
    /// Optional TSV output path compatible with assignment-local-search --candidate-file.
    #[arg(
        long = "candidate-var-tsv-output",
        alias = "candidate-tsv-output",
        alias = "candidate-output",
        alias = "candidate-file-output",
        value_name = "PATH"
    )]
    candidate_var_tsv_output: Option<PathBuf>,
    /// Optional TSV output path with one window row per introduced clause.
    #[arg(
        long = "clause-window-tsv-output",
        alias = "window-tsv-output",
        value_name = "PATH"
    )]
    clause_window_tsv_output: Option<PathBuf>,
}

#[derive(Args, Clone)]
pub(crate) struct IntroducedClauseBackfillSearchOptions {
    #[command(flatten)]
    common: CommonOptions,
    /// Seed TSV value-delta file applied before introduced-clause backfill search; repeatable.
    #[arg(long = "seed-set-file")]
    seed_set_files: Vec<PathBuf>,
    /// introduced-clause-backfill-candidates JSON report.
    #[arg(
        long = "candidates-report",
        alias = "introduced-clause-backfill-candidates",
        alias = "report",
        value_name = "PATH"
    )]
    candidates_report: PathBuf,
    /// Maximum source candidate variables materialized from the candidates report.
    #[arg(long, default_value_t = 256)]
    source_candidate_limit: usize,
    /// Maximum clause-window variables materialized from the candidates report.
    #[arg(long, default_value_t = 128)]
    window_var_limit: usize,
    /// Include W210 variables outside the residual-neighborhood radius as extra candidates.
    #[arg(long)]
    include_outside_radius_vars: bool,
    /// W210 residual-neighborhood radius whose complement is eligible.
    #[arg(long, default_value_t = 3)]
    outside_radius: usize,
    /// Maximum outside-radius-only variables materialized after deterministic ordering.
    #[arg(long, default_value_t = 128)]
    outside_radius_var_limit: usize,
    /// Maximum greedy flip rounds over the materialized candidate set.
    #[arg(long, default_value_t = 4)]
    rounds: usize,
    /// Maximum greedy pair-flip rounds after single-flip descent stalls.
    #[arg(long, default_value_t = 1)]
    pair_rounds: usize,
    /// Limit pair-search candidates after deterministic source-first ordering.
    #[arg(long, default_value_t = 64)]
    pair_candidate_limit: usize,
    /// Maximum correlated group-flip rounds after pair search stalls.
    #[arg(long, default_value_t = 0)]
    group_rounds: usize,
    /// Number of variables flipped together in correlated group search.
    #[arg(long, default_value_t = 3)]
    group_size: usize,
    /// Sliding candidate window size used to build correlated group templates.
    #[arg(long, default_value_t = 12)]
    group_window_size: usize,
    /// Limit group-search candidates after deterministic source-first ordering.
    #[arg(long, default_value_t = 64)]
    group_candidate_limit: usize,
    /// Maximum unique group templates evaluated per group-search round.
    #[arg(long, default_value_t = 25_000)]
    group_evaluation_limit: usize,
}

#[derive(Args, Clone)]
pub(crate) struct ResidualSideEffectBackboneOptions {
    /// Original DIMACS CNF, optionally .xz/.gz/.bz2 compressed.
    #[arg(long, default_value = DEFAULT_TARGET_CNF)]
    target_cnf: PathBuf,
    /// assignment-local-search JSON report containing source-frame side-effect summaries.
    #[arg(
        long = "side-effect-report",
        alias = "assignment-local-search-report",
        alias = "report",
        default_value = DEFAULT_W210_SIDE_EFFECT_REPORT,
        value_name = "PATH"
    )]
    side_effect_report: PathBuf,
    /// Optional introduced-clause-backfill-frontier JSON report derived from the same side-effect report.
    #[arg(
        long = "frontier-report",
        alias = "introduced-clause-backfill-frontier",
        value_name = "PATH"
    )]
    frontier_report: Option<PathBuf>,
    /// Evidence JSON output path.
    #[arg(long)]
    output: Option<PathBuf>,
}

#[derive(Args, Clone)]
pub(crate) struct FrontierAssistedModelMaterializerOptions {
    #[command(flatten)]
    common: CommonOptions,
    /// assignment-local-search JSON report containing source-frame choice side-effect summaries.
    #[arg(
        long = "side-effect-report",
        alias = "assignment-local-search-report",
        value_name = "PATH"
    )]
    side_effect_report: PathBuf,
    /// introduced-clause-backfill-frontier JSON report derived from the same side-effect report.
    #[arg(
        long = "frontier-report",
        alias = "introduced-clause-backfill-frontier",
        value_name = "PATH"
    )]
    frontier_report: PathBuf,
    /// Seed TSV value-delta file applied before computing residual radius variables; repeatable.
    #[arg(long = "seed-set-file")]
    seed_set_files: Vec<PathBuf>,
    /// One-based residual clause this diagnostic is centered on. Defaults to Circuit_multiplier22 6507.
    #[arg(long = "target-residual-clause", default_value_t = 6507)]
    target_residual_clause: usize,
    /// Residual-neighborhood radius kept free before frontier windows are added.
    #[arg(long, default_value_t = 3)]
    radius: usize,
    /// Maximum outside-radius frontier variables selected after deterministic ranking.
    #[arg(long = "frontier-candidate-limit", default_value_t = 64)]
    frontier_candidate_limit: usize,
    /// Number of selected frontier variables freed together per reduced-CNF window.
    #[arg(long = "window-size", default_value_t = 2)]
    window_size: usize,
    /// Maximum frontier windows solved.
    #[arg(long = "window-limit", default_value_t = 8)]
    window_limit: usize,
}

#[derive(Args, Clone)]
pub(crate) struct WitnessAuditOptions {
    #[command(flatten)]
    common: CommonOptions,
}

#[derive(Args, Clone)]
pub(crate) struct SourceFrameAuditOptions {
    #[command(flatten)]
    common: CommonOptions,
    /// Real source-frame input rows to validate.
    #[arg(long, default_value = DEFAULT_SOURCE_FRAME_ROWS)]
    source_frame_rows: PathBuf,
    /// Diagnostic missing-source rows that must remain non-materialized.
    #[arg(long, default_value = DEFAULT_MISSING_SOURCE_FRAME_ROWS)]
    missing_source_rows: PathBuf,
    /// Residual-clause source-hook target TSV.
    #[arg(long, default_value = DEFAULT_SOURCE_HOOK_TARGETS)]
    residual_hook_targets: PathBuf,
    /// Component source-hook target TSV.
    #[arg(long, default_value = DEFAULT_COMPONENT_SOURCE_HOOKS)]
    component_hook_targets: PathBuf,
    /// Overlay accepted source-frame values onto the complete W210 assignment and validate it.
    #[arg(long)]
    w210_overlay: bool,
}

#[derive(Clone, Debug)]
struct RawFormula {
    num_vars: usize,
    clauses: Vec<Vec<i32>>,
}

#[derive(Clone, Debug)]
struct Window {
    name: String,
    one_based_vars: Vec<usize>,
}

#[derive(Clone, Debug)]
struct WindowSelection {
    windows: Vec<Window>,
    source: &'static str,
    auto_low_free_candidate_windows: Option<usize>,
    auto_component_hitting_candidate_windows: Option<usize>,
    component_hitting_windows: Vec<ComponentHittingWindow>,
    auto_component_family_candidate_windows: Option<usize>,
    component_family_windows: Vec<ComponentFamilyWindow>,
    component_hook_targets: Option<PathBuf>,
}

#[derive(Clone, Debug)]
struct ComponentHittingWindow {
    component_id: usize,
    name: String,
    one_based_vars: Vec<usize>,
    min_variable_hitting_set_size: usize,
    diagnostic_missing_literal_rows: usize,
    clause_count: usize,
    one_based_clause_ids: Vec<usize>,
    source_frame_class: String,
    covered_real_source_families: String,
    construction_action: String,
}

#[derive(Clone, Debug)]
struct ComponentFamilyWindow {
    component_ids: Vec<usize>,
    name: String,
    one_based_vars: Vec<usize>,
    covered_real_source_families: Vec<String>,
    source_frame_classes: Vec<String>,
    diagnostic_missing_literal_rows: usize,
    covered_clause_count: usize,
    one_based_clause_ids: Vec<usize>,
    component_count: usize,
}

#[derive(Clone, Debug, Default)]
struct ComponentFamilyGroupSelection {
    groups: Vec<Vec<usize>>,
    windows: Vec<ComponentFamilyWindow>,
    candidate_count: Option<usize>,
    component_hook_targets: Option<PathBuf>,
}

#[derive(Clone, Debug, Default)]
struct SourceFrameValueSelection {
    overlays: Vec<SourceFrameValueOverlay>,
    candidate_count: Option<usize>,
    component_hook_targets: Option<PathBuf>,
    source_frame_rows: Option<PathBuf>,
    source_frame_parse_errors: usize,
    source_frame_parse_error_samples: Vec<String>,
}

#[derive(Clone, Debug)]
struct SourceFrameValueOverlay {
    window: ComponentFamilyWindow,
    assignments: Vec<(usize, bool)>,
    source_rows_seen: usize,
    valid_binding_rows: usize,
    invalid_binding_rows: usize,
    duplicate_same_required_values: usize,
    conflicting_required_values: usize,
    conflicting_one_based_vars: Vec<usize>,
    source_frame_row_id_samples: Vec<String>,
}

#[derive(Clone, Debug, Default)]
struct SourceFrameChoiceSelection {
    rows_by_clause: BTreeMap<usize, Vec<SourceFrameChoiceRow>>,
    candidate_row_count: Option<usize>,
    selected_row_count: usize,
    side_effect_prune_input_rows: Option<usize>,
    side_effect_prune_kept_rows: Option<usize>,
    side_effect_prune_non_worsening_rows: usize,
    side_effect_prune_top_per_clause_rows: usize,
    side_effect_prune_pruned_rows: Option<usize>,
    source_frame_rows: Option<PathBuf>,
    remaining_clause_ledger: Option<PathBuf>,
    remaining_clause_rows_seen: usize,
    remaining_clause_choice_rows: usize,
    dynamic_residual_choice_clause_count: usize,
    dynamic_residual_choice_rows: usize,
    source_frame_parse_errors: usize,
    source_frame_parse_error_samples: Vec<String>,
    remaining_clause_parse_errors: usize,
    remaining_clause_parse_error_samples: Vec<String>,
}

#[derive(Clone, Debug)]
struct SourceFrameChoiceRow {
    source_frame_row_id: String,
    clause_id_one_based: usize,
    literal_index_one_based: usize,
    var: usize,
    required_value: bool,
}

#[derive(Clone, Debug, Default)]
struct SourceFrameChoiceState {
    assignments: BTreeMap<usize, bool>,
    row_ids: Vec<String>,
    clause_ids: Vec<usize>,
}

#[derive(Clone, Debug)]
struct CommandResult {
    command: Vec<String>,
    exit_code: Option<i32>,
    timed_out: bool,
    wall_time_ms: u128,
    stdout: String,
    stderr: String,
}

impl CommandResult {
    fn json(&self) -> JsonValue {
        json!({
            "command": self.command,
            "exit_code": self.exit_code,
            "timed_out": self.timed_out,
            "wall_time_ms": self.wall_time_ms,
            "stdout": self.stdout,
            "stderr": self.stderr,
        })
    }
}

#[derive(Clone, Debug)]
struct WitnessGate {
    kind: &'static str,
    output: usize,
    inputs: Vec<i32>,
    defining_clauses: Vec<usize>,
    negated_output: bool,
}

#[derive(Clone, Debug)]
struct TsvTable {
    path: PathBuf,
    header: Vec<String>,
    rows: Vec<BTreeMap<String, String>>,
}

#[derive(Clone, Debug)]
struct SourceFrameRow {
    source_frame_row_id: String,
    clause_id_one_based: usize,
    literal_index_one_based: usize,
    lit: i32,
    var_one_based: usize,
    source_family: String,
    source_value: Option<bool>,
    required_value_to_satisfy_literal: bool,
}

#[derive(Clone, Debug, Default)]
struct SourceFrameParsedRows {
    rows: Vec<SourceFrameRow>,
    parse_errors: usize,
    parse_error_samples: Vec<String>,
}

#[derive(Clone, Debug, Default)]
struct SourceFrameRowAudit {
    rows_seen: usize,
    rows_accepted: usize,
    rows_rejected: usize,
    unsupported_family: usize,
    var_out_of_range: usize,
    literal_var_mismatch: usize,
    clause_out_of_range: usize,
    literal_index_out_of_range: usize,
    literal_index_mismatch: usize,
    literal_missing_from_clause: usize,
    required_value_mismatch: usize,
    parse_errors: usize,
    conflicts: usize,
    source_value_satisfies_literal: usize,
    source_value_falsifies_literal: usize,
}

#[derive(Clone, Debug)]
struct BackfillFrontierRow {
    round: usize,
    top_candidate_rank: usize,
    introduced_clause_id_one_based: usize,
    original_clause_lits: Vec<i32>,
    original_clause_vars: Vec<usize>,
    candidate_one_based_set_values: Vec<(usize, bool)>,
    candidate_one_based_vars: Vec<usize>,
    source_frame_row_ids: Vec<String>,
    candidate_one_based_clause_ids: Vec<usize>,
    candidate_residual_falsified_clause_count: Option<usize>,
    net_residual_delta: Option<isize>,
    introduced_residual_count: Option<usize>,
    affected_one_based_clause_ids: Vec<usize>,
    cleared_one_based_clause_ids: Vec<usize>,
}

#[derive(Clone, Debug, Default)]
struct BackfillFrontierReport {
    rows: Vec<BackfillFrontierRow>,
    source_frame_choice_rounds_seen: usize,
    top_candidates_seen: usize,
    top_candidates_with_side_effect_summary: usize,
    top_candidates_with_introductions: usize,
}

#[derive(Clone, Debug)]
struct BackfillCandidateClause {
    one_based_clause_id: usize,
    original_clause_lits: Vec<i32>,
    original_clause_vars: Vec<usize>,
    introducing_candidate_vars: Vec<usize>,
    already_introducing_candidate_vars: Vec<usize>,
    new_backfill_vars: Vec<usize>,
    source_frame_row_id_samples: Vec<String>,
    occurrence_count: usize,
}

#[derive(Clone, Debug, Default)]
struct BackfillCandidateReport {
    clauses: Vec<BackfillCandidateClause>,
    candidate_vars: BTreeSet<usize>,
    candidate_var_occurrences: usize,
    candidate_var_occurrence_counts: BTreeMap<usize, usize>,
    candidate_clause_pairs: BTreeSet<(usize, usize)>,
    window_vars: BTreeSet<usize>,
    introducing_candidate_vars: BTreeSet<usize>,
    already_introducing_candidate_vars: BTreeSet<usize>,
    new_backfill_vars: BTreeSet<usize>,
    introducing_candidate_vars_outside_clause_vars: BTreeSet<usize>,
}

#[derive(Clone, Debug)]
struct FrontierMaterializerLedgerRow {
    one_based_var: usize,
    current_value: bool,
    outside_radius: bool,
    frontier_occurrences: usize,
    source_tags: BTreeSet<String>,
    anchor_ids: BTreeSet<String>,
    related_clause_ids: BTreeSet<usize>,
    score: usize,
}

#[derive(Clone, Debug)]
struct ResidualSideEffectAnchor {
    anchor_id: String,
    round: usize,
    top_candidate_rank: usize,
    source_frame_row_ids: Vec<String>,
    candidate_one_based_clause_ids: Vec<usize>,
    one_based_set_values: Vec<(usize, bool)>,
    candidate_residual_falsified_clause_count: Option<usize>,
    candidate_residual_one_based_clause_ids: Vec<usize>,
    net_residual_delta: Option<isize>,
    affected_one_based_clause_ids: Vec<usize>,
    cleared_round_start_residual_one_based_clause_ids: Vec<usize>,
    cleared_baseline_residual_one_based_clause_ids: Vec<usize>,
    retained_baseline_residual_one_based_clause_ids: Vec<usize>,
    introduced_residual_one_based_clause_ids: Vec<usize>,
}

#[derive(Clone, Debug, Default)]
struct ResidualSideEffectBackbone {
    baseline_residual_one_based_clause_ids: BTreeSet<usize>,
    top_candidates_seen: usize,
    top_candidates_with_side_effect_summary: usize,
    anchors: Vec<ResidualSideEffectAnchor>,
    residual_to_anchor_ids: BTreeMap<usize, Vec<String>>,
    unique_affected_one_based_clause_ids: BTreeSet<usize>,
    unique_introduced_residual_one_based_clause_ids: BTreeSet<usize>,
}

#[derive(Clone, Debug)]
struct ResidualSideEffectFrontierSummary {
    path: PathBuf,
    sha256: String,
    source_repo_head: String,
    assignment_local_search_report_sha256: String,
    unique_introduced_one_based_clause_ids: BTreeSet<usize>,
}

pub(crate) fn run(command: SatCompRepairCommand) -> Result<()> {
    match command {
        SatCompRepairCommand::RadiusSurface(opts) => run_radius_surface(opts),
        SatCompRepairCommand::OutsideSingleFlip(opts) => run_outside_single_flip(opts),
        SatCompRepairCommand::ComponentWindow(opts) => run_component_window(opts),
        SatCompRepairCommand::AssignmentAudit(opts) => run_assignment_audit(opts),
        SatCompRepairCommand::AssignmentLocalSearch(opts) => run_assignment_local_search(opts),
        SatCompRepairCommand::FullCnfObjectiveProducer(opts) => {
            run_full_cnf_objective_producer(opts)
        }
        SatCompRepairCommand::IntroducedClauseBackfillFrontier(opts) => {
            run_introduced_clause_backfill_frontier(opts)
        }
        SatCompRepairCommand::IntroducedClauseBackfillCandidates(opts) => {
            run_introduced_clause_backfill_candidates(opts)
        }
        SatCompRepairCommand::IntroducedClauseBackfillSearch(opts) => {
            run_introduced_clause_backfill_search(opts)
        }
        SatCompRepairCommand::ResidualSideEffectBackbone(opts) => {
            run_residual_side_effect_backbone(opts)
        }
        SatCompRepairCommand::FrontierAssistedModelMaterializer(opts) => {
            run_frontier_assisted_model_materializer(opts)
        }
        SatCompRepairCommand::WitnessAudit(opts) => run_witness_audit(opts),
        SatCompRepairCommand::SourceFrameAudit(opts) => run_source_frame_audit(opts),
    }
}

fn run_assignment_audit(opts: AssignmentAuditOptions) -> Result<()> {
    let root = repo_root()?;
    let common = opts.common;
    let target_cnf = resolve_path(&root, &common.target_cnf);
    let formula = parse_dimacs_path(&target_cnf)?;
    let output = output_path(&root, &common, "assignment-audit")?;
    let (mut assignment, assignment_source, assignment_stats, ledgers) = if let Some(path) =
        opts.dimacs_model
    {
        let path = resolve_path(&root, &path);
        let (assignment, stats) = parse_dimacs_model_path(&path, formula.num_vars)?;
        (
            assignment,
            json!({
                "kind": "dimacs_model",
                "path": display_path_for_report(&path, &root),
                "sha256": sha256_file(&path)?,
            }),
            stats,
            Vec::new(),
        )
    } else {
        let ledgers = ledger_paths(&root, &common);
        let (assignment, stats) = parse_w210_assignment(formula.num_vars, &ledgers)?;
        (
            assignment,
            json!({
                "kind": "w210_value_ledgers",
                "paths": ledgers.iter().map(|path| display_path_for_report(path, &root)).collect::<Vec<_>>(),
            }),
            stats,
            ledgers,
        )
    };

    let flipped_vars = apply_assignment_flips(
        &root,
        formula.num_vars,
        &mut assignment,
        &opts.flips,
        &opts.flip_files,
    )?;
    let set_values =
        apply_assignment_sets(&root, formula.num_vars, &mut assignment, &opts.set_files)?;
    let residual_ids = residual_clause_ids(&formula.clauses, &assignment);
    let residual_one_based: Vec<usize> = residual_ids.iter().map(|idx| idx + 1).collect();
    let residual_samples =
        residual_clause_samples(&formula.clauses, &assignment, &residual_ids, 16);
    let valid_model = residual_ids.is_empty();
    let payload = json!({
        "schema": "ay.satcomp-circuit-assignment-audit/v1",
        "issue": 9424,
        "scoreboard_row": "Circuit_multiplier22",
        "source": diagnostic_source_json(
            git_head(&root),
            "Diagnostic-only Rust SAT-COMP submission/preflight CLI assignment audit. No route, SAT stdout, model-output, proof, solved-count, PAR-2, or SAT-COMP authority is granted.",
        ),
        "input": {
            "path": display_path_for_report(&target_cnf, &root),
            "sha256": sha256_file(&target_cnf)?,
            "num_vars": formula.num_vars,
            "num_clauses": formula.clauses.len(),
        },
        "assignment": {
            "source": assignment_source,
            "stats": assignment_stats,
            "complete": assignment.len() == formula.num_vars,
            "assigned_vars": assignment.len(),
            "one_based_flipped_vars": flipped_vars.iter().map(|var| var + 1).collect::<Vec<_>>(),
            "flipped_var_count": flipped_vars.len(),
            "flip_files": opts.flip_files.iter().map(|path| display_path_for_report(&resolve_path(&root, path), &root)).collect::<Vec<_>>(),
            "one_based_set_values": set_values.iter().map(|(var, value)| json!({"var": var + 1, "value": value})).collect::<Vec<_>>(),
            "set_var_count": set_values.len(),
            "set_files": opts.set_files.iter().map(|path| display_path_for_report(&resolve_path(&root, path), &root)).collect::<Vec<_>>(),
        },
        "w210_ledgers": {
            "paths": ledgers.iter().map(|path| display_path_for_report(path, &root)).collect::<Vec<_>>(),
        },
        "residual": {
            "zero_based_clause_ids": &residual_ids,
            "one_based_clause_ids": residual_one_based,
            "count": residual_ids.len(),
            "samples": residual_samples,
        },
        "verdict": {
            "original_dimacs_valid_model": valid_model,
            "complete_original_dimacs_valid_model_found": valid_model,
            "route_admitted": false,
            "sat_output_authority": false,
            "model_output_authority": false,
            "proof_output_authority": false,
            "sat_comp_progress_claim": false,
            "blocker": if valid_model {
                "Assignment validates against the original DIMACS, but this audit does not admit a solver route or grant SAT/model authority."
            } else {
                "Assignment does not satisfy the original DIMACS; residual clauses remain."
            },
        },
    });
    write_json(&output, &payload)?;
    println!("{}", serde_json::to_string(&payload["verdict"])?);
    Ok(())
}

fn run_assignment_local_search(opts: AssignmentLocalSearchOptions) -> Result<()> {
    let root = repo_root()?;
    let common = opts.common.clone();
    if opts.source_frame_choice_dynamic_residual_choices && opts.source_frame_choice_rounds == 0 {
        bail!(
            "assignment-local-search --source-frame-choice-dynamic-residual-choices requires --source-frame-choice-rounds"
        );
    }
    if opts.source_frame_choice_accept_neutral && opts.source_frame_choice_rounds == 0 {
        bail!(
            "assignment-local-search --source-frame-choice-accept-neutral requires --source-frame-choice-rounds"
        );
    }
    let target_cnf = resolve_path(&root, &common.target_cnf);
    let formula = parse_dimacs_path(&target_cnf)?;
    let ledgers = ledger_paths(&root, &common);
    let (w210_assignment, ledger_stats) = parse_w210_assignment(formula.num_vars, &ledgers)?;
    let w210_residual = residual_clause_ids(&formula.clauses, &w210_assignment);
    let mut assignment = w210_assignment.clone();
    let seed_set_values = apply_assignment_sets(
        &root,
        formula.num_vars,
        &mut assignment,
        &opts.seed_set_files,
    )?;
    let seed_residual = residual_clause_ids(&formula.clauses, &assignment);
    let candidates = local_search_candidates(
        &root,
        formula.num_vars,
        &formula.clauses,
        &seed_residual,
        &opts,
    )?;
    let output = output_path(&root, &common, "assignment-local-search")?;
    let best_set_path = output.with_file_name(format!(
        "{}-best-set.tsv",
        output
            .file_stem()
            .and_then(|value| value.to_str())
            .unwrap_or("assignment-local-search")
    ));

    let mut current_residual = seed_residual.clone();
    let mut rounds = Vec::new();
    let mut evaluated_flips = 0usize;
    for round_idx in 0..opts.rounds {
        let current_count = current_residual.len();
        let mut best_var = None;
        let mut best_residual = current_residual.clone();
        let mut top = Vec::new();
        for &var in &candidates {
            let mut trial = assignment.clone();
            trial[var] = !trial[var];
            let residual = residual_clause_ids(&formula.clauses, &trial);
            evaluated_flips += 1;
            top.push((residual.len(), var, residual.clone()));
            let better_tie = match best_var {
                Some(best) => var < best,
                None => true,
            };
            if residual.len() < best_residual.len()
                || (residual.len() == best_residual.len() && better_tie)
            {
                best_var = Some(var);
                best_residual = residual;
            }
        }
        top.sort_by_key(|(count, var, _)| (*count, *var));
        let top_candidates: Vec<_> = top
            .iter()
            .take(16)
            .map(|(count, var, residual)| {
                json!({
                    "one_based_var": var + 1,
                    "residual_falsified_clause_count": count,
                    "residual_falsified_one_based_clause_ids": residual.iter().take(32).map(|idx| idx + 1).collect::<Vec<_>>(),
                })
            })
            .collect();
        let improved = best_residual.len() < current_count;
        let selected_var = if improved { best_var } else { None };
        if let Some(var) = selected_var {
            assignment[var] = !assignment[var];
            current_residual = best_residual.clone();
        }
        rounds.push(json!({
            "round": round_idx + 1,
            "starting_residual_falsified_clause_count": current_count,
            "selected_one_based_var": selected_var.map(|var| var + 1),
            "selected_new_value": selected_var.map(|var| assignment[var]),
            "ending_residual_falsified_clause_count": if improved { best_residual.len() } else { current_count },
            "improved": improved,
            "top_candidates": top_candidates,
        }));
        if !improved {
            break;
        }
    }

    let pair_candidates =
        pair_search_candidates(&candidates, opts.pair_candidate_limit, opts.pair_rounds > 0)?;
    let mut pair_rounds = Vec::new();
    let mut evaluated_pair_flips = 0usize;
    if opts.pair_rounds > 0 && pair_candidates.len() < 2 {
        bail!("assignment-local-search pair candidate set must contain at least two variables");
    }
    for round_idx in 0..opts.pair_rounds {
        let current_count = current_residual.len();
        let mut best_pair = None;
        let mut best_residual = current_residual.clone();
        let mut top = Vec::new();
        for i in 0..pair_candidates.len() {
            for j in i + 1..pair_candidates.len() {
                let a = pair_candidates[i];
                let b = pair_candidates[j];
                let mut trial = assignment.clone();
                trial[a] = !trial[a];
                trial[b] = !trial[b];
                let residual = residual_clause_ids(&formula.clauses, &trial);
                evaluated_pair_flips += 1;
                top.push((residual.len(), a, b, residual.clone()));
                let better_tie = match best_pair {
                    Some((best_a, best_b)) => (a, b) < (best_a, best_b),
                    None => true,
                };
                if residual.len() < best_residual.len()
                    || (residual.len() == best_residual.len() && better_tie)
                {
                    best_pair = Some((a, b));
                    best_residual = residual;
                }
            }
        }
        top.sort_by_key(|(count, a, b, _)| (*count, *a, *b));
        let top_candidates: Vec<_> = top
            .iter()
            .take(16)
            .map(|(count, a, b, residual)| {
                json!({
                    "one_based_vars": [a + 1, b + 1],
                    "residual_falsified_clause_count": count,
                    "residual_falsified_one_based_clause_ids": residual.iter().take(32).map(|idx| idx + 1).collect::<Vec<_>>(),
                })
            })
            .collect();
        let improved = best_residual.len() < current_count;
        let selected_pair = if improved { best_pair } else { None };
        if let Some((a, b)) = selected_pair {
            assignment[a] = !assignment[a];
            assignment[b] = !assignment[b];
            current_residual = best_residual.clone();
        }
        pair_rounds.push(json!({
            "round": round_idx + 1,
            "starting_residual_falsified_clause_count": current_count,
            "selected_one_based_vars": selected_pair.map(|(a, b)| vec![a + 1, b + 1]),
            "selected_new_values": selected_pair.map(|(a, b)| vec![assignment[a], assignment[b]]),
            "ending_residual_falsified_clause_count": if improved { best_residual.len() } else { current_count },
            "improved": improved,
            "top_candidates": top_candidates,
        }));
        if !improved {
            break;
        }
    }

    let source_frame_value_selection = source_frame_value_selection(&root, &formula, &opts)?;
    if opts.source_frame_value_rounds > 0 && source_frame_value_selection.overlays.is_empty() {
        bail!("assignment-local-search source-frame value overlay set is empty");
    }
    let mut source_frame_value_rounds = Vec::new();
    let mut evaluated_source_frame_value_overlays = 0usize;
    let source_frame_value_conflicting_overlays = source_frame_value_selection
        .overlays
        .iter()
        .filter(|overlay| overlay.conflicting_required_values > 0)
        .count();
    for round_idx in 0..opts.source_frame_value_rounds {
        let current_count = current_residual.len();
        let mut best_overlay_idx = None;
        let mut best_residual = current_residual.clone();
        let mut top = Vec::new();
        for (overlay_idx, overlay) in source_frame_value_selection.overlays.iter().enumerate() {
            let trial = assignment_after_required_value_overlay(&assignment, overlay);
            let residual = residual_clause_ids(&formula.clauses, &trial);
            evaluated_source_frame_value_overlays += 1;
            top.push((residual.len(), overlay_idx, residual));
            let better_tie = match best_overlay_idx {
                Some(best_idx) => overlay_idx < best_idx,
                None => true,
            };
            if top.last().expect("just pushed").0 < best_residual.len()
                || (top.last().expect("just pushed").0 == best_residual.len() && better_tie)
            {
                best_overlay_idx = Some(overlay_idx);
                best_residual = top.last().expect("just pushed").2.clone();
            }
        }
        top.sort_by_key(|(count, overlay_idx, _)| (*count, *overlay_idx));
        let top_candidates: Vec<_> = top
            .iter()
            .take(16)
            .map(|(count, overlay_idx, residual)| {
                let overlay = &source_frame_value_selection.overlays[*overlay_idx];
                json!({
                    "name": &overlay.window.name,
                    "component_ids": &overlay.window.component_ids,
                    "one_based_set_values": overlay.assignments.iter().map(|(var, value)| json!({"var": var + 1, "value": value})).collect::<Vec<_>>(),
                    "source_rows_seen": overlay.source_rows_seen,
                    "valid_binding_rows": overlay.valid_binding_rows,
                    "conflicting_required_values": overlay.conflicting_required_values,
                    "residual_falsified_clause_count": count,
                    "residual_falsified_one_based_clause_ids": residual.iter().take(32).map(|idx| idx + 1).collect::<Vec<_>>(),
                })
            })
            .collect();
        let improved = best_residual.len() < current_count;
        let selected_overlay_idx = if improved { best_overlay_idx } else { None };
        if let Some(overlay_idx) = selected_overlay_idx {
            apply_required_value_overlay(
                &mut assignment,
                &source_frame_value_selection.overlays[overlay_idx],
            );
            current_residual = best_residual.clone();
        }
        source_frame_value_rounds.push(json!({
            "round": round_idx + 1,
            "starting_residual_falsified_clause_count": current_count,
            "selected_overlay_name": selected_overlay_idx.map(|idx| source_frame_value_selection.overlays[idx].window.name.clone()),
            "selected_component_ids": selected_overlay_idx.map(|idx| source_frame_value_selection.overlays[idx].window.component_ids.clone()),
            "selected_one_based_set_values": selected_overlay_idx.map(|idx| source_frame_value_selection.overlays[idx].assignments.iter().map(|(var, value)| json!({"var": var + 1, "value": value})).collect::<Vec<_>>()),
            "ending_residual_falsified_clause_count": if improved { current_residual.len() } else { current_count },
            "improved": improved,
            "top_candidates": top_candidates,
        }));
        if !improved {
            break;
        }
    }

    if opts.source_frame_choice_rounds > 0 && opts.source_frame_choice_beam_width == 0 {
        bail!("assignment-local-search source-frame-choice-beam-width must be positive");
    }
    let mut source_frame_choice_current_selection =
        if opts.source_frame_choice_dynamic_residual_choices {
            SourceFrameChoiceSelection::default()
        } else {
            source_frame_choice_selection(&root, &formula, &assignment, &current_residual, &opts)?
        };
    if opts.source_frame_choice_rounds > 0
        && !opts.source_frame_choice_dynamic_residual_choices
        && source_frame_choice_current_selection
            .rows_by_clause
            .is_empty()
    {
        bail!("assignment-local-search source-frame choice set is empty");
    }
    let mut source_frame_choice_rounds = Vec::new();
    let mut evaluated_source_frame_choice_states = 0usize;
    let mut source_frame_choice_dynamic_rounds = 0usize;
    let mut source_frame_choice_dynamic_generated_rows = 0usize;
    let mut source_frame_choice_dynamic_generated_clauses = 0usize;
    let mut source_frame_choice_neutral_selections = 0usize;
    let mut source_frame_choice_seen_residuals = BTreeSet::new();
    source_frame_choice_seen_residuals.insert(current_residual.clone());
    for round_idx in 0..opts.source_frame_choice_rounds {
        if opts.source_frame_choice_dynamic_residual_choices {
            source_frame_choice_current_selection = source_frame_choice_selection(
                &root,
                &formula,
                &assignment,
                &current_residual,
                &opts,
            )?;
            source_frame_choice_dynamic_rounds += 1;
            source_frame_choice_dynamic_generated_rows +=
                source_frame_choice_current_selection.dynamic_residual_choice_rows;
            source_frame_choice_dynamic_generated_clauses +=
                source_frame_choice_current_selection.dynamic_residual_choice_clause_count;
        }
        if source_frame_choice_current_selection
            .rows_by_clause
            .is_empty()
        {
            if round_idx == 0 {
                bail!("assignment-local-search source-frame choice set is empty");
            }
            break;
        }
        let round_start_residual = current_residual.clone();
        let current_count = round_start_residual.len();
        let search = source_frame_choice_beam_search(
            &formula,
            &assignment,
            &source_frame_choice_current_selection,
            opts.source_frame_choice_beam_width,
            opts.source_frame_choice_accept_neutral,
            if opts.source_frame_choice_accept_neutral {
                Some(&source_frame_choice_seen_residuals)
            } else {
                None
            },
        );
        evaluated_source_frame_choice_states += search.evaluated_states;
        let strict_improved = search.best_residual.len() < current_count;
        let selected_residual_seen_before =
            source_frame_choice_seen_residuals.contains(&search.best_residual);
        let neutral_accepted = !strict_improved
            && opts.source_frame_choice_accept_neutral
            && search.best_residual.len() == current_count
            && !search.best_state.assignments.is_empty()
            && !selected_residual_seen_before;
        let accepted = strict_improved || neutral_accepted;
        if accepted {
            apply_source_frame_choice_state(&mut assignment, &search.best_state);
            current_residual = search.best_residual.clone();
            source_frame_choice_seen_residuals.insert(current_residual.clone());
        }
        if neutral_accepted {
            source_frame_choice_neutral_selections += 1;
        }
        let selected_side_effect_summary = if accepted {
            let affected = source_frame_choice_affected_clause_ids(
                &search.best_state,
                &source_frame_choice_occurrences(&formula),
            );
            Some(source_frame_choice_side_effect_summary(
                &round_start_residual,
                &search.best_residual,
                &affected,
            ))
        } else {
            None
        };
        source_frame_choice_rounds.push(json!({
            "round": round_idx + 1,
            "dynamic_current_residual_choices": opts.source_frame_choice_dynamic_residual_choices,
            "choices_regenerated_from_current_residual": opts.source_frame_choice_dynamic_residual_choices && round_idx > 0,
            "dynamic_residual_choice_clause_count": source_frame_choice_current_selection.dynamic_residual_choice_clause_count,
            "dynamic_residual_choice_rows": source_frame_choice_current_selection.dynamic_residual_choice_rows,
            "candidate_row_count": source_frame_choice_current_selection.candidate_row_count,
            "selected_row_count": source_frame_choice_current_selection.selected_row_count,
            "starting_residual_falsified_clause_count": current_count,
            "starting_residual_falsified_one_based_clause_ids": round_start_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
            "ending_residual_falsified_clause_count": if accepted { current_residual.len() } else { current_count },
            "ending_residual_falsified_one_based_clause_ids": if accepted {
                current_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>()
            } else {
                round_start_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>()
            },
            "improved": strict_improved,
            "strict_improvement": strict_improved,
            "neutral_accepted": neutral_accepted,
            "applied_non_worsening": neutral_accepted,
            "accepted": accepted,
            "selected_residual_seen_before": selected_residual_seen_before,
            "clauses_with_choices": source_frame_choice_current_selection.rows_by_clause.len(),
            "selected_source_frame_row_ids": if accepted { Some(search.best_state.row_ids.clone()) } else { None },
            "selected_one_based_set_values": if accepted { Some(source_frame_choice_state_set_values(&search.best_state)) } else { None },
            "selected_clause_ids": if accepted { Some(search.best_state.clause_ids.clone()) } else { None },
            "selected_side_effect_summary": selected_side_effect_summary.clone(),
            "side_effect_summary": selected_side_effect_summary,
            "beam_final_width": search.final_width,
            "evaluated_states": search.evaluated_states,
            "top_candidates": search.top_candidates,
            "authority": diagnostic_authority_json(),
        }));
        if !accepted {
            break;
        }
    }

    let component_family_selection =
        component_family_group_selection(&root, formula.num_vars, &opts)?;
    if opts.component_family_rounds > 0 && component_family_selection.groups.is_empty() {
        bail!("assignment-local-search component-family group set is empty");
    }
    let mut component_family_scorer =
        AssignmentResidualScorer::new(formula.num_vars, &formula.clauses);
    let mut component_family_rounds = Vec::new();
    let mut evaluated_component_family_group_flips = 0usize;
    let mut evaluated_component_family_group_affected_clauses = 0usize;
    for round_idx in 0..opts.component_family_rounds {
        let current_count = current_residual.len();
        let current_residual_flags = residual_flags(formula.clauses.len(), &current_residual);
        let mut best_group_idx = None;
        let mut best_residual_count = current_count;
        let mut top = Vec::new();
        for (group_idx, group) in component_family_selection.groups.iter().enumerate() {
            let score = component_family_scorer.flip_group_residual_count(
                &assignment,
                group,
                &current_residual_flags,
                current_count,
            );
            evaluated_component_family_group_flips += 1;
            evaluated_component_family_group_affected_clauses += score.affected_clause_count;
            top.push((score.residual_count, group_idx));
            let better_tie = match best_group_idx {
                Some(best_idx) => group_idx < best_idx,
                None => true,
            };
            if score.residual_count < best_residual_count
                || (score.residual_count == best_residual_count && better_tie)
            {
                best_group_idx = Some(group_idx);
                best_residual_count = score.residual_count;
            }
        }
        top.sort_by_key(|(count, group_idx)| (*count, *group_idx));
        let top_candidates: Vec<_> = top
            .iter()
            .take(16)
            .map(|(count, group_idx)| {
                let group = &component_family_selection.groups[*group_idx];
                let window = &component_family_selection.windows[*group_idx];
                let residual =
                    residual_clause_ids_after_group_flip(&formula.clauses, &assignment, group);
                debug_assert_eq!(*count, residual.len());
                json!({
                    "name": &window.name,
                    "component_ids": &window.component_ids,
                    "one_based_vars": group.iter().map(|var| var + 1).collect::<Vec<_>>(),
                    "residual_falsified_clause_count": count,
                    "residual_falsified_one_based_clause_ids": residual.iter().take(32).map(|idx| idx + 1).collect::<Vec<_>>(),
                })
            })
            .collect();
        let improved = best_residual_count < current_count;
        let selected_group_idx = if improved { best_group_idx } else { None };
        if let Some(group_idx) = selected_group_idx {
            for &var in &component_family_selection.groups[group_idx] {
                assignment[var] = !assignment[var];
            }
            current_residual = residual_clause_ids(&formula.clauses, &assignment);
            debug_assert_eq!(best_residual_count, current_residual.len());
        }
        component_family_rounds.push(json!({
            "round": round_idx + 1,
            "starting_residual_falsified_clause_count": current_count,
            "selected_group_name": selected_group_idx.map(|idx| component_family_selection.windows[idx].name.clone()),
            "selected_component_ids": selected_group_idx.map(|idx| component_family_selection.windows[idx].component_ids.clone()),
            "selected_one_based_vars": selected_group_idx.map(|idx| component_family_selection.groups[idx].iter().map(|var| var + 1).collect::<Vec<_>>()),
            "selected_new_values": selected_group_idx.map(|idx| component_family_selection.groups[idx].iter().map(|var| assignment[*var]).collect::<Vec<_>>()),
            "ending_residual_falsified_clause_count": if improved { current_residual.len() } else { current_count },
            "improved": improved,
            "top_candidates": top_candidates,
        }));
        if !improved {
            break;
        }
    }

    let group_candidates = group_search_candidates(
        &candidates,
        opts.group_candidate_limit,
        opts.group_rounds > 0,
    )?;
    let group_required_vars = group_required_vars(&root, formula.num_vars, &opts)?;
    let group_templates = if opts.group_rounds > 0 {
        windowed_group_templates(
            &group_candidates,
            opts.group_size,
            opts.group_window_size,
            &group_required_vars,
            opts.group_require_count,
            opts.group_evaluation_limit,
        )?
    } else {
        GroupTemplates::default()
    };
    if opts.group_rounds > 0 && group_templates.groups.is_empty() {
        bail!("assignment-local-search group candidate set did not produce any groups");
    }
    let mut group_scorer = AssignmentResidualScorer::new(formula.num_vars, &formula.clauses);
    let mut group_rounds = Vec::new();
    let mut evaluated_group_flips = 0usize;
    let mut evaluated_group_affected_clauses = 0usize;
    for round_idx in 0..opts.group_rounds {
        let current_count = current_residual.len();
        let current_residual_flags = residual_flags(formula.clauses.len(), &current_residual);
        let mut best_group: Option<Vec<usize>> = None;
        let mut best_residual_count = current_count;
        let mut top = Vec::new();
        for group in &group_templates.groups {
            let score = group_scorer.flip_group_residual_count(
                &assignment,
                group,
                &current_residual_flags,
                current_count,
            );
            evaluated_group_flips += 1;
            evaluated_group_affected_clauses += score.affected_clause_count;
            top.push((score.residual_count, group.clone()));
            let better_tie = match &best_group {
                Some(best) => group < best,
                None => true,
            };
            if score.residual_count < best_residual_count
                || (score.residual_count == best_residual_count && better_tie)
            {
                best_group = Some(group.clone());
                best_residual_count = score.residual_count;
            }
        }
        top.sort_by(|(left_count, left_group), (right_count, right_group)| {
            left_count
                .cmp(right_count)
                .then_with(|| left_group.cmp(right_group))
        });
        let top_candidates: Vec<_> = top
            .iter()
            .take(16)
            .map(|(count, group)| {
                let residual =
                    residual_clause_ids_after_group_flip(&formula.clauses, &assignment, group);
                debug_assert_eq!(*count, residual.len());
                json!({
                    "one_based_vars": group.iter().map(|var| var + 1).collect::<Vec<_>>(),
                    "residual_falsified_clause_count": count,
                    "residual_falsified_one_based_clause_ids": residual.iter().take(32).map(|idx| idx + 1).collect::<Vec<_>>(),
                })
            })
            .collect();
        let improved = best_residual_count < current_count;
        let selected_group = if improved { best_group } else { None };
        if let Some(group) = &selected_group {
            for &var in group {
                assignment[var] = !assignment[var];
            }
            current_residual = residual_clause_ids(&formula.clauses, &assignment);
            debug_assert_eq!(best_residual_count, current_residual.len());
        }
        group_rounds.push(json!({
            "round": round_idx + 1,
            "starting_residual_falsified_clause_count": current_count,
            "selected_one_based_vars": selected_group.as_ref().map(|group| group.iter().map(|var| var + 1).collect::<Vec<_>>()),
            "selected_new_values": selected_group.as_ref().map(|group| group.iter().map(|var| assignment[*var]).collect::<Vec<_>>()),
            "ending_residual_falsified_clause_count": if improved { current_residual.len() } else { current_count },
            "improved": improved,
            "top_candidates": top_candidates,
        }));
        if !improved {
            break;
        }
    }

    let best_delta = assignment_delta_from_base(&w210_assignment, &assignment);
    write_set_tsv(&best_set_path, &w210_assignment, &best_delta)?;
    let valid_model = current_residual.is_empty();
    let component_family_group_hook_targets = component_family_selection
        .component_hook_targets
        .as_ref()
        .map(|path| artifact_json(path, &root))
        .transpose()?;
    let source_frame_value_component_hook_targets = source_frame_value_selection
        .component_hook_targets
        .as_ref()
        .map(|path| artifact_json(path, &root))
        .transpose()?;
    let source_frame_value_rows_artifact = source_frame_value_selection
        .source_frame_rows
        .as_ref()
        .map(|path| artifact_json(path, &root))
        .transpose()?;
    let source_frame_choice_rows_artifact = source_frame_choice_current_selection
        .source_frame_rows
        .as_ref()
        .map(|path| artifact_json(path, &root))
        .transpose()?;
    let source_frame_choice_remaining_clause_ledger_artifact =
        source_frame_choice_current_selection
            .remaining_clause_ledger
            .as_ref()
            .map(|path| artifact_json(path, &root))
            .transpose()?;
    let mut search_payload = json!({
        "rounds_requested": opts.rounds,
        "rounds_run": rounds.len(),
        "candidate_count": candidates.len(),
        "residual_candidates": opts.residual_candidates,
        "candidate_limit": opts.candidate_limit,
        "evaluated_flips": evaluated_flips,
        "rounds": rounds,
        "pair_rounds_requested": opts.pair_rounds,
        "pair_rounds_run": pair_rounds.len(),
        "pair_candidate_count": pair_candidates.len(),
        "pair_candidate_limit": opts.pair_candidate_limit,
        "evaluated_pair_flips": evaluated_pair_flips,
        "pair_rounds": pair_rounds,
    });
    search_payload["source_frame_value_rounds_requested"] = json!(opts.source_frame_value_rounds);
    search_payload["source_frame_value_rounds_run"] = json!(source_frame_value_rounds.len());
    search_payload["source_frame_value_limit"] = json!(opts.source_frame_value_limit);
    search_payload["source_frame_value_candidate_windows"] =
        json!(source_frame_value_selection.candidate_count);
    search_payload["source_frame_value_selected_overlays"] = json!(source_frame_value_selection
        .candidate_count
        .map(|_| source_frame_value_selection.overlays.len()));
    search_payload["source_frame_value_pruned_by_limit"] = json!(source_frame_value_selection
        .candidate_count
        .map(|count| count.saturating_sub(source_frame_value_selection.overlays.len())));
    search_payload["source_frame_value_component_hook_targets"] =
        json!(source_frame_value_component_hook_targets);
    search_payload["source_frame_value_rows"] = json!(source_frame_value_rows_artifact);
    search_payload["source_frame_value_parse_errors"] =
        json!(source_frame_value_selection.source_frame_parse_errors);
    search_payload["source_frame_value_conflicting_overlays"] =
        json!(source_frame_value_conflicting_overlays);
    search_payload["source_frame_value_parse_error_samples"] =
        json!(&source_frame_value_selection.source_frame_parse_error_samples);
    search_payload["source_frame_value_overlays"] = json!(source_frame_value_selection
        .overlays
        .iter()
        .map(source_frame_value_overlay_json)
        .collect::<Vec<_>>());
    search_payload["evaluated_source_frame_value_overlays"] =
        json!(evaluated_source_frame_value_overlays);
    search_payload["source_frame_value_rounds"] = json!(source_frame_value_rounds);
    search_payload["source_frame_choice_rounds_requested"] = json!(opts.source_frame_choice_rounds);
    search_payload["source_frame_choice_rounds_run"] = json!(source_frame_choice_rounds.len());
    search_payload["source_frame_choice_limit"] = json!(opts.source_frame_choice_limit);
    search_payload["source_frame_choice_beam_width"] = json!(opts.source_frame_choice_beam_width);
    search_payload["source_frame_choice_side_effect_top_per_clause"] =
        json!(opts.source_frame_choice_side_effect_top_per_clause);
    search_payload["source_frame_choice_side_effect_pruning_authority"] = json!("diagnostic_only");
    search_payload["source_frame_choice_dynamic_residual_choices"] =
        json!(opts.source_frame_choice_dynamic_residual_choices);
    search_payload["source_frame_choice_accept_neutral"] =
        json!(opts.source_frame_choice_accept_neutral);
    search_payload["source_frame_choice_dynamic_rounds"] =
        json!(source_frame_choice_dynamic_rounds);
    search_payload["source_frame_choice_dynamic_generated_rows"] =
        json!(source_frame_choice_dynamic_generated_rows);
    search_payload["source_frame_choice_dynamic_generated_clause_count"] =
        json!(source_frame_choice_dynamic_generated_clauses);
    search_payload["source_frame_choice_neutral_selections"] =
        json!(source_frame_choice_neutral_selections);
    search_payload["source_frame_choice_seen_residual_state_count"] =
        json!(source_frame_choice_seen_residuals.len());
    search_payload["source_frame_choice_candidate_rows"] =
        json!(source_frame_choice_current_selection.candidate_row_count);
    search_payload["source_frame_choice_selected_rows"] =
        json!(source_frame_choice_current_selection.selected_row_count);
    search_payload["source_frame_choice_side_effect_prune_input_rows"] =
        json!(source_frame_choice_current_selection.side_effect_prune_input_rows);
    search_payload["source_frame_choice_side_effect_prune_kept_rows"] =
        json!(source_frame_choice_current_selection.side_effect_prune_kept_rows);
    search_payload["source_frame_choice_side_effect_prune_non_worsening_rows"] =
        json!(source_frame_choice_current_selection.side_effect_prune_non_worsening_rows);
    search_payload["source_frame_choice_side_effect_prune_top_per_clause_rows"] =
        json!(source_frame_choice_current_selection.side_effect_prune_top_per_clause_rows);
    search_payload["source_frame_choice_side_effect_prune_pruned_rows"] =
        json!(source_frame_choice_current_selection.side_effect_prune_pruned_rows);
    search_payload["source_frame_choice_rows"] = json!(source_frame_choice_rows_artifact);
    search_payload["source_frame_choice_remaining_clause_ledger"] =
        json!(source_frame_choice_remaining_clause_ledger_artifact);
    search_payload["source_frame_choice_remaining_clause_ledger_authority"] =
        json!("diagnostic_only");
    search_payload["source_frame_choice_remaining_clause_rows_seen"] =
        json!(source_frame_choice_current_selection.remaining_clause_rows_seen);
    search_payload["source_frame_choice_remaining_clause_choice_rows"] =
        json!(source_frame_choice_current_selection.remaining_clause_choice_rows);
    search_payload["source_frame_choice_dynamic_residual_choice_rows"] =
        json!(source_frame_choice_current_selection.dynamic_residual_choice_rows);
    search_payload["source_frame_choice_dynamic_residual_choice_clause_count"] =
        json!(source_frame_choice_current_selection.dynamic_residual_choice_clause_count);
    search_payload["source_frame_choice_parse_errors"] =
        json!(source_frame_choice_current_selection.source_frame_parse_errors);
    search_payload["source_frame_choice_parse_error_samples"] =
        json!(&source_frame_choice_current_selection.source_frame_parse_error_samples);
    search_payload["source_frame_choice_remaining_clause_parse_errors"] =
        json!(source_frame_choice_current_selection.remaining_clause_parse_errors);
    search_payload["source_frame_choice_remaining_clause_parse_error_samples"] =
        json!(&source_frame_choice_current_selection.remaining_clause_parse_error_samples);
    search_payload["source_frame_choice_clauses_with_choices"] =
        json!(source_frame_choice_current_selection.rows_by_clause.len());
    search_payload["evaluated_source_frame_choice_states"] =
        json!(evaluated_source_frame_choice_states);
    search_payload["source_frame_choice_rounds"] = json!(source_frame_choice_rounds);
    search_payload["component_family_rounds_requested"] = json!(opts.component_family_rounds);
    search_payload["component_family_rounds_run"] = json!(component_family_rounds.len());
    search_payload["component_family_group_limit"] = json!(opts.component_family_group_limit);
    search_payload["component_family_group_candidate_windows"] =
        json!(component_family_selection.candidate_count);
    search_payload["component_family_group_selected_windows"] = json!(component_family_selection
        .candidate_count
        .map(|_| component_family_selection.groups.len()));
    search_payload["component_family_group_pruned_by_limit"] = json!(component_family_selection
        .candidate_count
        .map(|count| count.saturating_sub(component_family_selection.groups.len())));
    search_payload["component_family_group_hook_targets"] =
        json!(component_family_group_hook_targets);
    search_payload["component_family_groups"] = json!(component_family_selection
        .windows
        .iter()
        .map(component_family_window_json)
        .collect::<Vec<_>>());
    search_payload["evaluated_component_family_group_flips"] =
        json!(evaluated_component_family_group_flips);
    search_payload["evaluated_component_family_group_affected_clauses"] =
        json!(evaluated_component_family_group_affected_clauses);
    search_payload["component_family_group_rounds"] = json!(component_family_rounds);
    search_payload["group_rounds_requested"] = json!(opts.group_rounds);
    search_payload["group_rounds_run"] = json!(group_rounds.len());
    search_payload["group_size"] = json!(opts.group_size);
    search_payload["group_window_size"] = json!(opts.group_window_size);
    search_payload["group_candidate_count"] = json!(group_candidates.len());
    search_payload["group_candidate_limit"] = json!(opts.group_candidate_limit);
    search_payload["group_required_var_count"] = json!(group_required_vars.len());
    search_payload["group_required_min_count"] = json!(opts.group_require_count);
    search_payload["group_required_one_based_vars"] = json!(group_required_vars
        .iter()
        .map(|var| var + 1)
        .collect::<Vec<_>>());
    search_payload["group_evaluation_limit"] = json!(opts.group_evaluation_limit);
    search_payload["group_template_count"] = json!(group_templates.groups.len());
    search_payload["group_templates_truncated"] = json!(group_templates.truncated);
    search_payload["evaluated_group_flips"] = json!(evaluated_group_flips);
    search_payload["evaluated_group_affected_clauses"] = json!(evaluated_group_affected_clauses);
    search_payload["group_scoring"] = json!("incremental_affected_clause_delta");
    search_payload["group_rounds"] = json!(group_rounds);
    let payload = json!({
        "schema": "ay.satcomp-circuit-assignment-local-search/v1",
        "issue": 9424,
        "scoreboard_row": "Circuit_multiplier22",
        "source": diagnostic_source_json(
            git_head(&root),
            "Diagnostic-only Rust SAT-COMP submission/preflight CLI assignment local search. No route, SAT stdout, model-output, proof, solved-count, PAR-2, or SAT-COMP authority is granted.",
        ),
        "input": {
            "path": display_path_for_report(&target_cnf, &root),
            "sha256": sha256_file(&target_cnf)?,
            "num_vars": formula.num_vars,
            "num_clauses": formula.clauses.len(),
        },
        "w210_ledgers": {
            "paths": ledgers.iter().map(|path| display_path_for_report(path, &root)).collect::<Vec<_>>(),
            "stats": ledger_stats,
        },
        "seed": {
            "set_files": opts.seed_set_files.iter().map(|path| display_path_for_report(&resolve_path(&root, path), &root)).collect::<Vec<_>>(),
            "one_based_set_values": seed_set_values.iter().map(|(var, value)| json!({"var": var + 1, "value": value})).collect::<Vec<_>>(),
            "set_var_count": seed_set_values.len(),
            "residual_falsified_clause_count": seed_residual.len(),
            "residual_falsified_one_based_clause_ids": seed_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
        },
        "baseline_w210": {
            "residual_falsified_clause_count": w210_residual.len(),
            "residual_falsified_one_based_clause_ids": w210_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
        },
        "search": search_payload,
        "best": {
            "residual_falsified_clause_count": current_residual.len(),
            "residual_falsified_one_based_clause_ids": current_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
            "original_dimacs_valid_model": valid_model,
            "changed_from_w210_var_count": best_delta.len(),
            "one_based_set_values": best_delta.iter().map(|(var, value)| json!({"var": var + 1, "value": value})).collect::<Vec<_>>(),
            "set_file": display_path_for_report(&best_set_path, &root),
            "set_file_sha256": sha256_file(&best_set_path)?,
        },
        "authority": diagnostic_authority_json(),
        "verdict": {
            "original_dimacs_valid_model": valid_model,
            "complete_original_dimacs_valid_model_found": valid_model,
            "route_admitted": false,
            "sat_output_authority": false,
            "model_output_authority": false,
            "proof_output_authority": false,
            "solver_verdict_authority": false,
            "sat_comp_progress_claim": false,
            "blocker": if valid_model {
                "Local search found an assignment that validates against the original DIMACS, but this diagnostic does not admit a solver route or grant SAT/model authority."
            } else {
                "Local search did not find an original-DIMACS-valid model; residual clauses remain."
            },
        },
    });
    write_json(&output, &payload)?;
    println!("{}", serde_json::to_string(&payload["verdict"])?);
    Ok(())
}

fn run_full_cnf_objective_producer(opts: FullCnfObjectiveProducerOptions) -> Result<()> {
    let root = repo_root()?;
    let common = opts.common.clone();
    if opts.source_frame_choice_rounds > 0 && opts.source_frame_choice_beam_width == 0 {
        bail!("full-cnf-objective-producer --source-frame-choice-beam-width must be positive");
    }
    if opts.source_frame_choice_rounds > 0 && opts.source_frame_choice_limit.is_none() {
        bail!(
            "full-cnf-objective-producer --source-frame-choice-rounds requires --source-frame-choice-limit"
        );
    }
    let target_cnf = resolve_path(&root, &common.target_cnf);
    let formula = parse_dimacs_path(&target_cnf)?;
    let ledgers = ledger_paths(&root, &common);
    let (w210_assignment, ledger_stats) = parse_w210_assignment(formula.num_vars, &ledgers)?;
    let baseline_residual = residual_clause_ids(&formula.clauses, &w210_assignment);
    let mut assignment = w210_assignment.clone();
    let mut current_residual = baseline_residual.clone();
    let output = output_path(&root, &common, "full-cnf-objective-producer")?;
    let best_set_path = output.with_file_name(format!(
        "{}-best-set.tsv",
        output
            .file_stem()
            .and_then(|value| value.to_str())
            .unwrap_or("full-cnf-objective-producer")
    ));
    let local_search_opts = full_cnf_objective_local_search_options(&opts, common);
    let mut rounds = Vec::new();
    let mut stop_reason = "round_limit".to_string();
    let mut evaluated_source_frame_choice_states = 0usize;
    let mut dynamic_rounds = 0usize;
    let mut dynamic_generated_rows = 0usize;
    let mut dynamic_generated_clause_count = 0usize;
    let mut neutral_selections = 0usize;
    let mut seen_residuals = BTreeSet::new();
    seen_residuals.insert(current_residual.clone());
    let retained_update_policy = if opts.source_frame_choice_accept_neutral {
        "strict_full_cnf_improvement_or_unseen_neutral_bridge"
    } else {
        "strict_full_cnf_improvement_only"
    };

    for round_idx in 0..opts.source_frame_choice_rounds {
        let selection = source_frame_choice_selection(
            &root,
            &formula,
            &assignment,
            &current_residual,
            &local_search_opts,
        )?;
        if selection.rows_by_clause.is_empty() {
            stop_reason = "source_frame_choice_set_empty".to_string();
            rounds.push(json!({
                "round": round_idx + 1,
                "full_cnf_objective": true,
                "starting_residual_falsified_clause_count": current_residual.len(),
                "starting_residual_falsified_one_based_clause_ids": current_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
                "candidate_row_count": selection.candidate_row_count,
                "selected_row_count": selection.selected_row_count,
                "accepted": false,
                "strict_full_cnf_improvement": false,
                "blocker": "source_frame_choice_set_empty",
            }));
            break;
        }
        if opts.source_frame_choice_dynamic_residual_choices {
            dynamic_rounds += 1;
            dynamic_generated_rows += selection.dynamic_residual_choice_rows;
            dynamic_generated_clause_count += selection.dynamic_residual_choice_clause_count;
        }
        let round_start_residual = current_residual.clone();
        let search = source_frame_choice_beam_search(
            &formula,
            &assignment,
            &selection,
            opts.source_frame_choice_beam_width,
            opts.source_frame_choice_accept_neutral,
            opts.source_frame_choice_accept_neutral
                .then_some(&seen_residuals),
        );
        evaluated_source_frame_choice_states += search.evaluated_states;
        let update_decision = full_cnf_update_decision(
            &round_start_residual,
            &search.best_residual,
            search.best_state.assignments.is_empty(),
            opts.source_frame_choice_accept_neutral,
            &seen_residuals,
        );
        let accepted = update_decision.accepted;
        let selected_side_effect_summary = if accepted {
            let affected = source_frame_choice_affected_clause_ids(
                &search.best_state,
                &source_frame_choice_occurrences(&formula),
            );
            Some(source_frame_choice_side_effect_summary(
                &round_start_residual,
                &search.best_residual,
                &affected,
            ))
        } else {
            None
        };
        if accepted {
            apply_source_frame_choice_state(&mut assignment, &search.best_state);
            current_residual = search.best_residual.clone();
            seen_residuals.insert(current_residual.clone());
            if update_decision.neutral_bridge {
                neutral_selections += 1;
            }
        }
        rounds.push(json!({
            "round": round_idx + 1,
            "full_cnf_objective": true,
            "retained_update_policy": retained_update_policy,
            "dynamic_current_residual_choices": opts.source_frame_choice_dynamic_residual_choices,
            "dynamic_residual_choice_clause_count": selection.dynamic_residual_choice_clause_count,
            "dynamic_residual_choice_rows": selection.dynamic_residual_choice_rows,
            "source_frame_choice_accept_neutral": opts.source_frame_choice_accept_neutral,
            "candidate_row_count": selection.candidate_row_count,
            "selected_row_count": selection.selected_row_count,
            "side_effect_prune_input_rows": selection.side_effect_prune_input_rows,
            "side_effect_prune_kept_rows": selection.side_effect_prune_kept_rows,
            "side_effect_prune_non_worsening_rows": selection.side_effect_prune_non_worsening_rows,
            "side_effect_prune_top_per_clause_rows": selection.side_effect_prune_top_per_clause_rows,
            "side_effect_prune_pruned_rows": selection.side_effect_prune_pruned_rows,
            "starting_residual_falsified_clause_count": round_start_residual.len(),
            "starting_residual_falsified_one_based_clause_ids": round_start_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
            "ending_residual_falsified_clause_count": if accepted { current_residual.len() } else { round_start_residual.len() },
            "ending_residual_falsified_one_based_clause_ids": if accepted {
                current_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>()
            } else {
                round_start_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>()
            },
            "accepted": accepted,
            "strict_full_cnf_improvement": update_decision.strict_improvement,
            "neutral_full_cnf_bridge": update_decision.neutral_bridge,
            "selected_source_frame_row_ids": if accepted { Some(search.best_state.row_ids.clone()) } else { None },
            "selected_one_based_set_values": if accepted { Some(source_frame_choice_state_set_values(&search.best_state)) } else { None },
            "selected_clause_ids": if accepted { Some(search.best_state.clause_ids.clone()) } else { None },
            "selected_side_effect_summary": selected_side_effect_summary,
            "beam_final_width": search.final_width,
            "evaluated_states": search.evaluated_states,
            "top_candidates": search.top_candidates,
            "authority": diagnostic_authority_json(),
        }));
        if current_residual.is_empty() {
            stop_reason = "zero_residual_candidate".to_string();
            break;
        }
        if !accepted {
            stop_reason = if opts.source_frame_choice_accept_neutral {
                "no_strict_or_unseen_neutral_full_cnf_update"
            } else {
                "no_strict_full_cnf_improvement"
            }
            .to_string();
            break;
        }
    }

    if opts.source_frame_choice_rounds == 0 {
        stop_reason = "no_rounds_requested".to_string();
    }
    let best_delta = assignment_delta_from_base(&w210_assignment, &assignment);
    write_set_tsv(&best_set_path, &w210_assignment, &best_delta)?;
    let valid_model = current_residual.is_empty();
    let model_stdout_artifact =
        maybe_emit_full_cnf_model_stdout(&root, &opts, valid_model, &assignment)?;
    let checker_evidence = full_cnf_checker_evidence_json(
        &root,
        &opts,
        &formula,
        &target_cnf,
        model_stdout_artifact.as_ref(),
        valid_model,
    )?;
    let checker_valid = checker_evidence
        .get("valid_for_authority")
        .and_then(JsonValue::as_bool)
        .unwrap_or(false);
    let verdict = full_cnf_objective_verdict_json(valid_model, checker_valid);
    let payload = json!({
        "schema": "ay.satcomp-circuit-full-cnf-objective-producer/v1",
        "issue": 9424,
        "scoreboard_row": "Circuit_multiplier22",
        "source": diagnostic_source_json(
            git_head(&root),
            "Diagnostic-only full-CNF objective producer. W159/W210 assignment is a seed only; no Main route, proof, solved-count, PAR-2, or SAT-COMP authority is granted.",
        ),
        "input": {
            "path": display_path_for_report(&target_cnf, &root),
            "sha256": sha256_file(&target_cnf)?,
            "num_vars": formula.num_vars,
            "num_clauses": formula.clauses.len(),
        },
        "w210_seed": {
            "paths": ledgers.iter().map(|path| display_path_for_report(path, &root)).collect::<Vec<_>>(),
            "stats": ledger_stats,
            "seed_authority": "diagnostic_only",
        },
        "baseline_w210": {
            "residual_falsified_clause_count": baseline_residual.len(),
            "residual_falsified_one_based_clause_ids": baseline_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
        },
        "search": {
            "source_frame_choice_rounds_requested": opts.source_frame_choice_rounds,
            "source_frame_choice_rounds_run": rounds.len(),
            "source_frame_choice_limit": opts.source_frame_choice_limit,
            "source_frame_choice_beam_width": opts.source_frame_choice_beam_width,
            "source_frame_choice_side_effect_top_per_clause": opts.source_frame_choice_side_effect_top_per_clause,
            "source_frame_choice_dynamic_residual_choices": opts.source_frame_choice_dynamic_residual_choices,
            "source_frame_choice_accept_neutral": opts.source_frame_choice_accept_neutral,
            "source_frame_choice_dynamic_rounds": dynamic_rounds,
            "source_frame_choice_dynamic_generated_rows": dynamic_generated_rows,
            "source_frame_choice_dynamic_generated_clause_count": dynamic_generated_clause_count,
            "source_frame_choice_neutral_selections": neutral_selections,
            "source_frame_choice_seen_residual_state_count": seen_residuals.len(),
            "evaluated_source_frame_choice_states": evaluated_source_frame_choice_states,
            "retained_update_policy": retained_update_policy,
            "objective": "all_original_dimacs_clauses",
            "stop_reason": stop_reason,
            "rounds": rounds,
        },
        "best": {
            "residual_falsified_clause_count": current_residual.len(),
            "residual_falsified_one_based_clause_ids": current_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
            "original_dimacs_valid_model_candidate": valid_model,
            "changed_from_w210_var_count": best_delta.len(),
            "one_based_set_values": best_delta.iter().map(|(var, value)| json!({"var": var + 1, "value": value})).collect::<Vec<_>>(),
            "set_file": display_path_for_report(&best_set_path, &root),
            "set_file_sha256": sha256_file(&best_set_path)?,
            "model_stdout": model_stdout_artifact,
        },
        "checker_evidence": checker_evidence,
        "authority": {
            "diagnostic_only": true,
            "route_admitted": false,
            "sat_output_authority": verdict["sat_output_authority"],
            "model_output_authority": verdict["model_output_authority"],
            "proof_output_authority": false,
            "solver_verdict_authority": verdict["solver_verdict_authority"],
            "sat_comp_progress_claim": false,
            "authority_requires_retained_original_dimacs_model_check": true,
        },
        "verdict": verdict,
    });
    write_json(&output, &payload)?;
    println!("{}", serde_json::to_string(&payload["verdict"])?);
    Ok(())
}

fn full_cnf_objective_local_search_options(
    opts: &FullCnfObjectiveProducerOptions,
    common: CommonOptions,
) -> AssignmentLocalSearchOptions {
    AssignmentLocalSearchOptions {
        common,
        seed_set_files: Vec::new(),
        candidate_vars: None,
        candidate_files: Vec::new(),
        residual_candidates: false,
        candidate_limit: None,
        rounds: 0,
        pair_rounds: 0,
        pair_candidate_limit: None,
        group_rounds: 0,
        component_family_rounds: 0,
        component_family_group_limit: None,
        source_frame_value_rounds: 0,
        source_frame_value_limit: None,
        source_frame_choice_rounds: opts.source_frame_choice_rounds,
        source_frame_choice_limit: opts.source_frame_choice_limit,
        source_frame_choice_beam_width: opts.source_frame_choice_beam_width,
        source_frame_choice_side_effect_top_per_clause: opts
            .source_frame_choice_side_effect_top_per_clause,
        source_frame_rows: opts.source_frame_rows.clone(),
        source_frame_choice_current_remaining_clause_value_ledger: opts
            .source_frame_choice_current_remaining_clause_value_ledger
            .clone(),
        source_frame_choice_dynamic_residual_choices: opts
            .source_frame_choice_dynamic_residual_choices,
        source_frame_choice_accept_neutral: opts.source_frame_choice_accept_neutral,
        component_hook_targets: PathBuf::from(DEFAULT_COMPONENT_SOURCE_HOOKS),
        group_size: 3,
        group_window_size: 12,
        group_candidate_limit: None,
        group_require_vars: None,
        group_require_files: Vec::new(),
        group_require_count: 1,
        group_evaluation_limit: 25_000,
    }
}

fn full_cnf_retains_strict_update(
    current_residual_count: usize,
    candidate_residual_count: usize,
    candidate_empty: bool,
) -> bool {
    !candidate_empty && candidate_residual_count < current_residual_count
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FullCnfUpdateDecision {
    accepted: bool,
    strict_improvement: bool,
    neutral_bridge: bool,
}

fn full_cnf_update_decision(
    current_residual: &[usize],
    candidate_residual: &[usize],
    candidate_empty: bool,
    accept_neutral: bool,
    seen_residuals: &BTreeSet<Vec<usize>>,
) -> FullCnfUpdateDecision {
    let strict_improvement = full_cnf_retains_strict_update(
        current_residual.len(),
        candidate_residual.len(),
        candidate_empty,
    );
    let neutral_bridge = !candidate_empty
        && accept_neutral
        && candidate_residual.len() == current_residual.len()
        && candidate_residual != current_residual
        && !seen_residuals.contains(candidate_residual);
    FullCnfUpdateDecision {
        accepted: strict_improvement || neutral_bridge,
        strict_improvement,
        neutral_bridge,
    }
}

fn full_cnf_objective_verdict_json(valid_model: bool, checker_valid: bool) -> JsonValue {
    let authority = valid_model && checker_valid;
    json!({
        "original_dimacs_valid_model_candidate": valid_model,
        "complete_original_dimacs_valid_model_found": valid_model,
        "retained_original_dimacs_model_check_valid": checker_valid,
        "route_admitted": false,
        "sat_output_authority": authority,
        "model_output_authority": authority,
        "proof_output_authority": false,
        "solver_verdict_authority": authority,
        "sat_comp_progress_claim": false,
        "blocker": if valid_model {
            if checker_valid {
                "Original-DIMACS model candidate has retained checker evidence; this diagnostic still does not admit a Main route."
            } else {
                "Original-DIMACS model candidate requires retained ay check model --json evidence before SAT/model authority."
            }
        } else {
            "Full-CNF objective producer did not find an original-DIMACS-valid model; residual clauses remain."
        },
    })
}

fn maybe_emit_full_cnf_model_stdout(
    root: &Path,
    opts: &FullCnfObjectiveProducerOptions,
    valid_model: bool,
    assignment: &[bool],
) -> Result<Option<JsonValue>> {
    if !valid_model {
        return Ok(None);
    }
    let Some(path) = &opts.model_stdout_output else {
        return Ok(None);
    };
    let path = resolve_path(root, path);
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&path, render_satcomp_model_stdout(assignment))
        .with_context(|| format!("failed to write model stdout '{}'", path.display()))?;
    Ok(Some(json!({
        "path": display_path_for_report(&path, root),
        "sha256": sha256_file(&path)?,
    })))
}

fn render_satcomp_model_stdout(assignment: &[bool]) -> String {
    let mut stdout = String::from("s SATISFIABLE\nv");
    for (idx, value) in assignment.iter().enumerate() {
        let lit = if *value {
            (idx + 1) as isize
        } else {
            -((idx + 1) as isize)
        };
        stdout.push(' ');
        stdout.push_str(&lit.to_string());
    }
    stdout.push_str(" 0\n");
    stdout
}

fn full_cnf_checker_evidence_json(
    root: &Path,
    opts: &FullCnfObjectiveProducerOptions,
    formula: &RawFormula,
    target_cnf: &Path,
    model_stdout_artifact: Option<&JsonValue>,
    valid_model: bool,
) -> Result<JsonValue> {
    let mut blockers = Vec::new();
    if !valid_model {
        blockers.push("residual_nonzero".to_string());
    }
    let model_stdout_path = model_stdout_artifact
        .and_then(|artifact| artifact.get("path"))
        .and_then(JsonValue::as_str);
    let model_stdout_sha256 = model_stdout_artifact
        .and_then(|artifact| artifact.get("sha256"))
        .and_then(JsonValue::as_str);
    if valid_model && model_stdout_path.is_none() {
        blockers.push("model_stdout_not_retained".to_string());
    }
    let checker_path = opts
        .checker_verdict_json
        .as_ref()
        .map(|path| resolve_path(root, path));
    if valid_model && checker_path.is_none() {
        blockers.push("checker_verdict_json_missing".to_string());
    }
    if valid_model && opts.checker_exit_status != Some(0) {
        blockers.push("checker_exit_status_not_zero".to_string());
    }
    if valid_model && opts.checker_command.is_empty() {
        blockers.push("checker_command_missing".to_string());
    }

    let mut checker_artifact = JsonValue::Null;
    if let Some(path) = checker_path {
        let raw = fs::read_to_string(&path)
            .with_context(|| format!("failed to read checker verdict '{}'", path.display()))?;
        let parsed: JsonValue = serde_json::from_str(&raw)
            .with_context(|| format!("failed to parse checker verdict '{}'", path.display()))?;
        checker_artifact = json!({
            "path": display_path_for_report(&path, root),
            "sha256": sha256_file(&path)?,
        });
        if parsed.get("schema").and_then(JsonValue::as_str) != Some(SATCOMP_MODEL_CHECK_SCHEMA) {
            blockers.push("checker_schema_mismatch".to_string());
        }
        let formula_path = parsed.get("formula").and_then(JsonValue::as_str);
        if !formula_path.is_some_and(|path| full_cnf_reported_path_matches(root, path, target_cnf))
        {
            blockers.push("checker_formula_path_mismatch".to_string());
        }
        let stdout_path = parsed.get("stdout").and_then(JsonValue::as_str);
        match (stdout_path, model_stdout_path) {
            (Some(reported), Some(expected)) => {
                let expected = resolve_path(root, Path::new(expected));
                if !full_cnf_reported_path_matches(root, reported, &expected) {
                    blockers.push("checker_stdout_path_mismatch".to_string());
                }
            }
            _ if valid_model => blockers.push("checker_stdout_path_missing".to_string()),
            _ => {}
        }
        if parsed.get("model_status").and_then(JsonValue::as_str) != Some("valid") {
            blockers.push("checker_model_status_not_valid".to_string());
        }
        if parsed.get("valid").and_then(JsonValue::as_bool) != Some(true) {
            blockers.push("checker_valid_false".to_string());
        }
        if parsed.get("num_vars").and_then(JsonValue::as_u64) != Some(formula.num_vars as u64) {
            blockers.push("checker_num_vars_mismatch".to_string());
        }
        if parsed.get("clauses_checked").and_then(JsonValue::as_u64)
            != Some(formula.clauses.len() as u64)
        {
            blockers.push("checker_clauses_checked_mismatch".to_string());
        }
        if !parsed
            .get("first_unsatisfied_clause")
            .is_some_and(JsonValue::is_null)
        {
            blockers.push("checker_first_unsatisfied_clause_present".to_string());
        }
    }

    Ok(json!({
        "required_for_authority": true,
        "valid_for_authority": blockers.is_empty(),
        "blockers": blockers,
        "retained_formula": {
            "path": display_path_for_report(target_cnf, root),
            "sha256": sha256_file(target_cnf)?,
        },
        "retained_model_stdout": {
            "path": model_stdout_path,
            "sha256": model_stdout_sha256,
        },
        "retained_checker_verdict": checker_artifact,
        "checker_command": &opts.checker_command,
        "checker_exit_status": opts.checker_exit_status,
    }))
}

fn full_cnf_reported_path_matches(root: &Path, reported: &str, expected: &Path) -> bool {
    let reported = Path::new(reported);
    let resolved = if reported.is_absolute() {
        reported.to_path_buf()
    } else {
        root.join(reported)
    };
    resolved == expected
}

fn run_introduced_clause_backfill_frontier(
    opts: IntroducedClauseBackfillFrontierOptions,
) -> Result<()> {
    let root = repo_root()?;
    let target_cnf = resolve_path(&root, &opts.target_cnf);
    let report_path = resolve_path(&root, &opts.assignment_local_search_report);
    let output = opts
        .output
        .as_ref()
        .map(|path| resolve_path(&root, path))
        .unwrap_or_else(|| {
            root.join(DEFAULT_OUTPUT_DIR)
                .join("introduced-clause-backfill-frontier.json")
        });
    let formula = parse_dimacs_path(&target_cnf)?;
    let report_size = fs::metadata(&report_path)
        .with_context(|| {
            format!(
                "failed to stat assignment-local-search report '{}'",
                report_path.display()
            )
        })?
        .len();
    if report_size > MAX_BACKFILL_FRONTIER_REPORT_BYTES {
        bail!(
            "assignment-local-search report '{}' is too large: {} bytes exceeds {}",
            report_path.display(),
            report_size,
            MAX_BACKFILL_FRONTIER_REPORT_BYTES
        );
    }
    let report_bytes = fs::read(&report_path).with_context(|| {
        format!(
            "failed to read assignment-local-search report '{}'",
            report_path.display()
        )
    })?;
    let report_json: JsonValue = serde_json::from_slice(&report_bytes).with_context(|| {
        format!(
            "failed to parse assignment-local-search report JSON '{}'",
            report_path.display()
        )
    })?;
    let current_repo_head = git_head(&root)
        .context("introduced-clause-backfill-frontier could not determine current git HEAD")?;
    let target_sha256 = sha256_file(&target_cnf)?;
    validate_assignment_local_search_report_for_backfill(
        &report_json,
        &formula,
        &target_sha256,
        &current_repo_head,
    )?;
    let frontier = collect_introduced_clause_backfill_frontier(&formula, &report_json)?;

    let tsv_output = opts
        .tsv_output
        .as_ref()
        .map(|path| -> Result<PathBuf> {
            let path = resolve_path(&root, path);
            write_backfill_frontier_tsv(&path, &frontier.rows)?;
            Ok(path)
        })
        .transpose()?;
    let tsv_artifact = tsv_output
        .as_ref()
        .map(|path| artifact_json(path, &root))
        .transpose()?;

    let unique_introduced_clause_ids: BTreeSet<usize> = frontier
        .rows
        .iter()
        .map(|row| row.introduced_clause_id_one_based)
        .collect();
    let frontier_clause_vars: BTreeSet<usize> = frontier
        .rows
        .iter()
        .flat_map(|row| row.original_clause_vars.iter().copied())
        .collect();
    let candidate_vars: BTreeSet<usize> = frontier
        .rows
        .iter()
        .flat_map(|row| row.candidate_one_based_vars.iter().copied())
        .collect();
    let introduced_clauses = json!({
        "source_frame_choice_rounds_seen": frontier.source_frame_choice_rounds_seen,
        "top_candidates_seen": frontier.top_candidates_seen,
        "top_candidates_with_side_effect_summary": frontier.top_candidates_with_side_effect_summary,
        "top_candidates_with_introductions": frontier.top_candidates_with_introductions,
        "seen_clause_references": frontier.rows.len(),
        "deduped_duplicate_clause_references": frontier.rows.len().saturating_sub(unique_introduced_clause_ids.len()),
        "unique_clause_count": unique_introduced_clause_ids.len(),
        "one_based_clause_ids": unique_introduced_clause_ids.iter().copied().collect::<Vec<_>>(),
        "introduced_clause_occurrences": frontier.rows.len(),
        "unique_introduced_clause_count": unique_introduced_clause_ids.len(),
        "unique_introduced_one_based_clause_ids": unique_introduced_clause_ids.iter().copied().collect::<Vec<_>>(),
        "frontier_clause_var_count": frontier_clause_vars.len(),
        "frontier_clause_one_based_vars": frontier_clause_vars.iter().copied().collect::<Vec<_>>(),
        "candidate_var_count": candidate_vars.len(),
        "candidate_one_based_vars": candidate_vars.iter().copied().collect::<Vec<_>>(),
        "clauses": backfill_frontier_clause_groups(&frontier.rows),
        "occurrences": frontier.rows.iter().map(backfill_frontier_row_json).collect::<Vec<_>>(),
        "rows": frontier.rows.iter().map(backfill_frontier_row_json).collect::<Vec<_>>(),
    });
    let payload = json!({
        "schema": "ay.satcomp-circuit-introduced-clause-backfill-frontier/v1",
        "issue": 9424,
        "scoreboard_row": "Circuit_multiplier22",
        "source": diagnostic_source_json(
            Some(current_repo_head.clone()),
            "Diagnostic-only Rust SAT-COMP submission/preflight CLI introduced-clause frontier audit. No route, SAT stdout, model-output, proof, solved-count, PAR-2, or SAT-COMP authority is granted.",
        ),
        "input": {
            "path": display_path_for_report(&target_cnf, &root),
            "sha256": target_sha256,
            "num_vars": formula.num_vars,
            "num_clauses": formula.clauses.len(),
        },
        "assignment_local_search_report": {
            "path": display_path_for_report(&report_path, &root),
            "sha256": sha256_file(&report_path)?,
            "schema": report_json.get("schema").cloned().unwrap_or(JsonValue::Null),
            "repo_head": report_json.pointer("/source/repo_head").cloned().unwrap_or(JsonValue::Null),
            "ay_build": report_json.pointer("/source/ay_build").cloned().unwrap_or(JsonValue::Null),
            "repo_head_matches_current": true,
        },
        "introduced_clauses": introduced_clauses.clone(),
        "frontier": introduced_clauses,
        "artifacts": {
            "tsv_output": tsv_artifact,
        },
        "authority": {
            "classification": "diagnostic_only",
            "route_admitted": false,
            "sat_output_authority": false,
            "model_output_authority": false,
            "proof_output_authority": false,
            "solver_verdict_authority": false,
            "sat_comp_progress_claim": false,
        },
        "verdict": {
            "diagnostic_only": true,
            "introduced_clause_frontier_recovered": !frontier.rows.is_empty(),
            "route_admitted": false,
            "sat_output_authority": false,
            "model_output_authority": false,
            "proof_output_authority": false,
            "solver_verdict_authority": false,
            "sat_comp_progress_claim": false,
            "blocker": "Introduced-clause backfill frontier is diagnostic only; it recovers CNF clauses and candidate variables but does not solve, emit a model/proof, or authorize a SAT-COMP route.",
        },
    });
    write_json(&output, &payload)?;
    println!("{}", serde_json::to_string(&payload["verdict"])?);
    Ok(())
}

fn run_introduced_clause_backfill_candidates(
    opts: IntroducedClauseBackfillCandidatesOptions,
) -> Result<()> {
    let root = repo_root()?;
    let report_path = resolve_path(&root, &opts.frontier_report);
    let output = opts
        .output
        .as_ref()
        .map(|path| resolve_path(&root, path))
        .unwrap_or_else(|| {
            root.join(DEFAULT_OUTPUT_DIR)
                .join("introduced-clause-backfill-candidates.json")
        });
    let report_size = fs::metadata(&report_path)
        .with_context(|| {
            format!(
                "failed to stat introduced-clause-backfill-frontier report '{}'",
                report_path.display()
            )
        })?
        .len();
    if report_size > MAX_BACKFILL_FRONTIER_REPORT_BYTES {
        bail!(
            "introduced-clause-backfill-frontier report '{}' is too large: {} bytes exceeds {}",
            report_path.display(),
            report_size,
            MAX_BACKFILL_FRONTIER_REPORT_BYTES
        );
    }
    let report_bytes = fs::read(&report_path).with_context(|| {
        format!(
            "failed to read introduced-clause-backfill-frontier report '{}'",
            report_path.display()
        )
    })?;
    let report_json: JsonValue = serde_json::from_slice(&report_bytes).with_context(|| {
        format!(
            "failed to parse introduced-clause-backfill-frontier report JSON '{}'",
            report_path.display()
        )
    })?;
    let current_repo_head = git_head(&root)
        .context("introduced-clause-backfill-candidates could not determine current git HEAD")?;
    let (num_vars, num_clauses) =
        validate_introduced_clause_backfill_frontier_report_for_candidates(
            &report_json,
            &current_repo_head,
        )?;
    let candidates =
        collect_introduced_clause_backfill_candidates(&report_json, num_vars, num_clauses)?;

    let candidate_var_tsv_output = opts
        .candidate_var_tsv_output
        .as_ref()
        .map(|path| -> Result<PathBuf> {
            let path = resolve_path(&root, path);
            write_backfill_candidate_var_tsv(&path, &candidates)?;
            Ok(path)
        })
        .transpose()?;
    let candidate_var_tsv_artifact = candidate_var_tsv_output
        .as_ref()
        .map(|path| artifact_json(path, &root))
        .transpose()?;
    let clause_window_tsv_output = opts
        .clause_window_tsv_output
        .as_ref()
        .map(|path| -> Result<PathBuf> {
            let path = resolve_path(&root, path);
            write_backfill_clause_window_tsv(&path, &candidates.clauses)?;
            Ok(path)
        })
        .transpose()?;
    let clause_window_tsv_artifact = clause_window_tsv_output
        .as_ref()
        .map(|path| artifact_json(path, &root))
        .transpose()?;

    let introduced_clause_ids: BTreeSet<usize> = candidates
        .clauses
        .iter()
        .map(|clause| clause.one_based_clause_id)
        .collect();
    let candidate_summary = json!({
        "source": "introduced_clauses occurrence candidate_one_based_vars",
        "introduced_clause_count": candidates.clauses.len(),
        "introduced_one_based_clause_ids": introduced_clause_ids.iter().copied().collect::<Vec<_>>(),
        "candidate_var_count": candidates.candidate_vars.len(),
        "candidate_one_based_vars": candidates.candidate_vars.iter().copied().collect::<Vec<_>>(),
        "candidate_var_occurrences": candidates.candidate_var_occurrences,
        "candidate_clause_pair_count": candidates.candidate_clause_pairs.len(),
        "introducing_candidate_var_count": candidates.introducing_candidate_vars.len(),
        "introducing_candidate_one_based_vars": candidates.introducing_candidate_vars.iter().copied().collect::<Vec<_>>(),
        "already_introducing_candidate_var_count": candidates.already_introducing_candidate_vars.len(),
        "already_introducing_candidate_one_based_vars": candidates.already_introducing_candidate_vars.iter().copied().collect::<Vec<_>>(),
        "new_backfill_var_count": candidates.new_backfill_vars.len(),
        "new_backfill_one_based_vars": candidates.new_backfill_vars.iter().copied().collect::<Vec<_>>(),
        "introducing_candidate_vars_outside_introduced_clause_var_count": candidates.introducing_candidate_vars_outside_clause_vars.len(),
        "introducing_candidate_vars_outside_introduced_clause_one_based_vars": candidates.introducing_candidate_vars_outside_clause_vars.iter().copied().collect::<Vec<_>>(),
        "clauses": candidates.clauses.iter().map(backfill_candidate_clause_json).collect::<Vec<_>>(),
        "clause_windows": candidates.clauses.iter().map(backfill_candidate_clause_json).collect::<Vec<_>>(),
    });
    let counts = json!({
        "frontier_clause_occurrences": candidates.clauses.iter().map(|clause| clause.occurrence_count).sum::<usize>(),
        "deduped_duplicate_clause_references": candidates.clauses.iter().map(|clause| clause.occurrence_count.saturating_sub(1)).sum::<usize>(),
        "unique_introduced_clause_count": candidates.clauses.len(),
        "candidate_var_count": candidates.candidate_vars.len(),
        "candidate_var_occurrences": candidates.candidate_var_occurrences,
        "candidate_clause_pair_count": candidates.candidate_clause_pairs.len(),
        "clause_window_count": candidates.clauses.len(),
        "clause_window_var_count": candidates.window_vars.len(),
        "window_var_count": candidates.window_vars.len(),
        "new_backfill_var_count": candidates.new_backfill_vars.len(),
    });
    let clause_windows = json!({
        "one_based_clause_ids": introduced_clause_ids.iter().copied().collect::<Vec<_>>(),
        "window_var_count": candidates.window_vars.len(),
        "window_one_based_vars": candidates.window_vars.iter().copied().collect::<Vec<_>>(),
        "clauses": candidates.clauses.iter().map(backfill_candidate_clause_json).collect::<Vec<_>>(),
    });
    let payload = json!({
        "schema": "ay.satcomp-circuit-introduced-clause-backfill-candidates/v1",
        "issue": 9424,
        "scoreboard_row": "Circuit_multiplier22",
        "source": diagnostic_source_json(
            Some(current_repo_head.clone()),
            "Diagnostic-only Rust SAT-COMP submission/preflight CLI introduced-clause backfill candidate materializer. No route, SAT stdout, model-output, proof, solved-count, PAR-2, or SAT-COMP authority is granted.",
        ),
        "input": report_json.get("input").cloned().unwrap_or(JsonValue::Null),
        "introduced_clause_backfill_frontier": {
            "path": display_path_for_report(&report_path, &root),
            "sha256": sha256_file(&report_path)?,
            "schema": report_json.get("schema").cloned().unwrap_or(JsonValue::Null),
            "repo_head": report_json.pointer("/source/repo_head").cloned().unwrap_or(JsonValue::Null),
            "ay_build": report_json.pointer("/source/ay_build").cloned().unwrap_or(JsonValue::Null),
            "assignment_local_search_report": report_json.get("assignment_local_search_report").cloned().unwrap_or(JsonValue::Null),
        },
        "counts": counts,
        "candidates": candidate_summary,
        "clause_windows": clause_windows,
        "artifacts": {
            "candidate_var_tsv_output": candidate_var_tsv_artifact,
            "clause_window_tsv_output": clause_window_tsv_artifact,
        },
        "authority": {
            "classification": "diagnostic_only",
            "route_admitted": false,
            "sat_output_authority": false,
            "model_output_authority": false,
            "proof_output_authority": false,
            "solver_verdict_authority": false,
            "sat_comp_progress_claim": false,
        },
        "verdict": {
            "diagnostic_only": true,
            "candidate_vars_recovered": !candidates.candidate_vars.is_empty(),
            "candidate_vars_source": "introduced_clauses occurrence candidate_one_based_vars",
            "route_admitted": false,
            "sat_output_authority": false,
            "model_output_authority": false,
            "proof_output_authority": false,
            "solver_verdict_authority": false,
            "sat_comp_progress_claim": false,
            "blocker": "Introduced-clause backfill candidates are diagnostic only; they materialize source candidate variables and bounded clause windows for follow-up search but do not solve, emit a model/proof, or authorize a SAT-COMP route.",
        },
    });
    write_json(&output, &payload)?;
    println!("{}", serde_json::to_string(&payload["verdict"])?);
    Ok(())
}

fn run_introduced_clause_backfill_search(
    opts: IntroducedClauseBackfillSearchOptions,
) -> Result<()> {
    if opts.source_candidate_limit == 0 {
        bail!("introduced-clause-backfill-search --source-candidate-limit must be positive");
    }
    if opts.window_var_limit == 0 {
        bail!("introduced-clause-backfill-search --window-var-limit must be positive");
    }
    if opts.include_outside_radius_vars && opts.outside_radius_var_limit == 0 {
        bail!(
            "introduced-clause-backfill-search --outside-radius-var-limit must be positive when --include-outside-radius-vars is set"
        );
    }
    if opts.pair_rounds > 0 && opts.pair_candidate_limit < 2 {
        bail!(
            "introduced-clause-backfill-search --pair-candidate-limit must be at least 2 when --pair-rounds is positive"
        );
    }
    if opts.group_rounds > 0 && opts.group_candidate_limit < opts.group_size {
        bail!(
            "introduced-clause-backfill-search --group-candidate-limit must be at least --group-size when --group-rounds is positive"
        );
    }

    let root = repo_root()?;
    let common = opts.common.clone();
    let target_cnf = resolve_path(&root, &common.target_cnf);
    let report_path = resolve_path(&root, &opts.candidates_report);
    let output = output_path(&root, &common, "introduced-clause-backfill-search")?;
    let best_set_path = output.with_file_name(format!(
        "{}-best-set.tsv",
        output
            .file_stem()
            .and_then(|value| value.to_str())
            .unwrap_or("introduced-clause-backfill-search")
    ));

    let formula = parse_dimacs_path(&target_cnf)?;
    let report_size = fs::metadata(&report_path)
        .with_context(|| {
            format!(
                "failed to stat introduced-clause-backfill-candidates report '{}'",
                report_path.display()
            )
        })?
        .len();
    if report_size > MAX_BACKFILL_FRONTIER_REPORT_BYTES {
        bail!(
            "introduced-clause-backfill-candidates report '{}' is too large: {} bytes exceeds {}",
            report_path.display(),
            report_size,
            MAX_BACKFILL_FRONTIER_REPORT_BYTES
        );
    }
    let report_bytes = fs::read(&report_path).with_context(|| {
        format!(
            "failed to read introduced-clause-backfill-candidates report '{}'",
            report_path.display()
        )
    })?;
    let report_json: JsonValue = serde_json::from_slice(&report_bytes).with_context(|| {
        format!(
            "failed to parse introduced-clause-backfill-candidates report JSON '{}'",
            report_path.display()
        )
    })?;
    let target_sha256 = sha256_file(&target_cnf)?;
    let current_repo_head = git_head(&root)
        .context("introduced-clause-backfill-search could not determine current git HEAD")?;
    let candidates = validate_introduced_clause_backfill_candidates_report_for_search(
        &report_json,
        &formula,
        &target_sha256,
        &current_repo_head,
    )?;

    let ledgers = ledger_paths(&root, &common);
    let (w210_assignment, ledger_stats) = parse_w210_assignment(formula.num_vars, &ledgers)?;
    let w210_residual = residual_clause_ids(&formula.clauses, &w210_assignment);
    let mut assignment = w210_assignment.clone();
    let seed_set_values = apply_assignment_sets(
        &root,
        formula.num_vars,
        &mut assignment,
        &opts.seed_set_files,
    )?;
    let seed_residual = residual_clause_ids(&formula.clauses, &assignment);
    let seed_delta = assignment_delta_from_base(&w210_assignment, &assignment);

    let selected_source_vars: Vec<_> = candidates
        .candidate_vars
        .iter()
        .copied()
        .take(opts.source_candidate_limit)
        .collect();
    let source_var_set = candidates.candidate_vars.clone();
    let window_only_vars: BTreeSet<_> = candidates
        .window_vars
        .difference(&source_var_set)
        .copied()
        .collect();
    let selected_window_vars: Vec<_> = window_only_vars
        .iter()
        .copied()
        .take(opts.window_var_limit)
        .collect();
    let selected_outside_radius_vars;
    let selected_outside_radius_var_set;
    let outside_radius_free_var_count;
    let outside_radius_var_count;
    let outside_radius_one_based_vars;
    let outside_radius_only_var_count;
    let outside_radius_only_one_based_vars;
    let outside_radius_window_overlap_vars;
    let outside_radius_vars_truncated;
    if opts.include_outside_radius_vars {
        let radius_free_vars = grow_free_vars(
            formula.num_vars,
            &formula.clauses,
            &seed_residual,
            opts.outside_radius,
        );
        let outside_radius_vars: BTreeSet<_> = (0..formula.num_vars)
            .filter(|var| !radius_free_vars.contains(var))
            .map(|var| var + 1)
            .collect();
        let outside_radius_only_vars: BTreeSet<_> = outside_radius_vars
            .difference(&candidates.window_vars)
            .copied()
            .collect();
        let outside_radius_window_overlap: Vec<_> = outside_radius_vars
            .intersection(&candidates.window_vars)
            .copied()
            .collect();
        selected_outside_radius_vars = outside_radius_only_vars
            .iter()
            .copied()
            .take(opts.outside_radius_var_limit)
            .collect::<Vec<_>>();
        selected_outside_radius_var_set = selected_outside_radius_vars
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        outside_radius_free_var_count = Some(radius_free_vars.len());
        outside_radius_var_count = Some(outside_radius_vars.len());
        outside_radius_one_based_vars =
            Some(outside_radius_vars.iter().copied().collect::<Vec<_>>());
        outside_radius_only_var_count = Some(outside_radius_only_vars.len());
        outside_radius_only_one_based_vars =
            Some(outside_radius_only_vars.iter().copied().collect::<Vec<_>>());
        outside_radius_window_overlap_vars = Some(outside_radius_window_overlap);
        outside_radius_vars_truncated = Some(
            outside_radius_only_vars
                .len()
                .saturating_sub(selected_outside_radius_vars.len()),
        );
    } else {
        selected_outside_radius_vars = Vec::new();
        selected_outside_radius_var_set = BTreeSet::new();
        outside_radius_free_var_count = None::<usize>;
        outside_radius_var_count = None::<usize>;
        outside_radius_one_based_vars = None::<Vec<usize>>;
        outside_radius_only_var_count = None::<usize>;
        outside_radius_only_one_based_vars = None::<Vec<usize>>;
        outside_radius_window_overlap_vars = None::<Vec<usize>>;
        outside_radius_vars_truncated = None::<usize>;
    }
    let mut selected_candidate_vars = selected_source_vars.clone();
    selected_candidate_vars.extend(selected_window_vars.iter().copied());
    selected_candidate_vars.extend(selected_outside_radius_vars.iter().copied());
    ensure_unique_usizes(
        &selected_candidate_vars,
        "introduced-clause-backfill-search materialized candidates",
    )?;
    if selected_candidate_vars.is_empty() {
        bail!("introduced-clause-backfill-search materialized candidate set is empty");
    }
    let search_candidates: Vec<usize> = selected_candidate_vars
        .iter()
        .map(|one_based| one_based - 1)
        .collect();

    let mut current_residual = seed_residual.clone();

    let mut rounds = Vec::new();
    let mut evaluated_flips = 0usize;
    for round_idx in 0..opts.rounds {
        let current_count = current_residual.len();
        let mut best_var = None;
        let mut best_residual = current_residual.clone();
        let mut top = Vec::new();
        for &var in &search_candidates {
            let mut trial = assignment.clone();
            trial[var] = !trial[var];
            let residual = residual_clause_ids(&formula.clauses, &trial);
            evaluated_flips += 1;
            top.push((residual.len(), var, residual.clone()));
            let better_tie = match best_var {
                Some(best) => var < best,
                None => true,
            };
            if residual.len() < best_residual.len()
                || (residual.len() == best_residual.len() && better_tie)
            {
                best_var = Some(var);
                best_residual = residual;
            }
        }
        top.sort_by_key(|(count, var, _)| (*count, *var));
        let top_candidates: Vec<_> = top
            .iter()
            .take(16)
            .map(|(count, var, residual)| {
                json!({
                    "one_based_var": var + 1,
                    "source_kind": backfill_search_candidate_source_kind(
                        *var + 1,
                        &source_var_set,
                        &window_only_vars,
                        &selected_outside_radius_var_set,
                    ),
                    "residual_falsified_clause_count": count,
                    "residual_falsified_one_based_clause_ids": residual.iter().take(32).map(|idx| idx + 1).collect::<Vec<_>>(),
                })
            })
            .collect();
        let improved = best_residual.len() < current_count;
        let selected_var = if improved { best_var } else { None };
        if let Some(var) = selected_var {
            assignment[var] = !assignment[var];
            current_residual = best_residual.clone();
        }
        rounds.push(json!({
            "round": round_idx + 1,
            "starting_residual_falsified_clause_count": current_count,
            "selected_one_based_var": selected_var.map(|var| var + 1),
            "selected_source_kind": selected_var.map(|var| {
                backfill_search_candidate_source_kind(
                    var + 1,
                    &source_var_set,
                    &window_only_vars,
                    &selected_outside_radius_var_set,
                )
            }),
            "selected_new_value": selected_var.map(|var| assignment[var]),
            "ending_residual_falsified_clause_count": if improved { best_residual.len() } else { current_count },
            "improved": improved,
            "top_candidates": top_candidates,
        }));
        if !improved {
            break;
        }
    }

    let pair_candidates = pair_search_candidates(
        &search_candidates,
        Some(opts.pair_candidate_limit),
        opts.pair_rounds > 0,
    )?;
    if opts.pair_rounds > 0 && pair_candidates.len() < 2 {
        bail!("introduced-clause-backfill-search pair candidate set must contain at least two variables");
    }
    let mut pair_rounds = Vec::new();
    let mut evaluated_pair_flips = 0usize;
    for round_idx in 0..opts.pair_rounds {
        let current_count = current_residual.len();
        let mut best_pair = None;
        let mut best_residual = current_residual.clone();
        let mut top = Vec::new();
        for i in 0..pair_candidates.len() {
            for j in i + 1..pair_candidates.len() {
                let a = pair_candidates[i];
                let b = pair_candidates[j];
                let mut trial = assignment.clone();
                trial[a] = !trial[a];
                trial[b] = !trial[b];
                let residual = residual_clause_ids(&formula.clauses, &trial);
                evaluated_pair_flips += 1;
                top.push((residual.len(), a, b, residual.clone()));
                let better_tie = match best_pair {
                    Some((best_a, best_b)) => (a, b) < (best_a, best_b),
                    None => true,
                };
                if residual.len() < best_residual.len()
                    || (residual.len() == best_residual.len() && better_tie)
                {
                    best_pair = Some((a, b));
                    best_residual = residual;
                }
            }
        }
        top.sort_by_key(|(count, a, b, _)| (*count, *a, *b));
        let top_candidates: Vec<_> = top
            .iter()
            .take(16)
            .map(|(count, a, b, residual)| {
                json!({
                    "one_based_vars": [a + 1, b + 1],
                    "source_kinds": [
                        backfill_search_candidate_source_kind(
                            *a + 1,
                            &source_var_set,
                            &window_only_vars,
                            &selected_outside_radius_var_set,
                        ),
                        backfill_search_candidate_source_kind(
                            *b + 1,
                            &source_var_set,
                            &window_only_vars,
                            &selected_outside_radius_var_set,
                        ),
                    ],
                    "residual_falsified_clause_count": count,
                    "residual_falsified_one_based_clause_ids": residual.iter().take(32).map(|idx| idx + 1).collect::<Vec<_>>(),
                })
            })
            .collect();
        let improved = best_residual.len() < current_count;
        let selected_pair = if improved { best_pair } else { None };
        if let Some((a, b)) = selected_pair {
            assignment[a] = !assignment[a];
            assignment[b] = !assignment[b];
            current_residual = best_residual.clone();
        }
        pair_rounds.push(json!({
            "round": round_idx + 1,
            "starting_residual_falsified_clause_count": current_count,
            "selected_one_based_vars": selected_pair.map(|(a, b)| vec![a + 1, b + 1]),
            "selected_source_kinds": selected_pair.map(|(a, b)| {
                vec![
                    backfill_search_candidate_source_kind(
                        a + 1,
                        &source_var_set,
                        &window_only_vars,
                        &selected_outside_radius_var_set,
                    ),
                    backfill_search_candidate_source_kind(
                        b + 1,
                        &source_var_set,
                        &window_only_vars,
                        &selected_outside_radius_var_set,
                    ),
                ]
            }),
            "selected_new_values": selected_pair.map(|(a, b)| vec![assignment[a], assignment[b]]),
            "ending_residual_falsified_clause_count": if improved { best_residual.len() } else { current_count },
            "improved": improved,
            "top_candidates": top_candidates,
        }));
        if !improved {
            break;
        }
    }

    let group_candidates = group_search_candidates(
        &search_candidates,
        Some(opts.group_candidate_limit),
        opts.group_rounds > 0,
    )?;
    let group_templates = if opts.group_rounds > 0 {
        windowed_group_templates(
            &group_candidates,
            opts.group_size,
            opts.group_window_size,
            &BTreeSet::new(),
            0,
            opts.group_evaluation_limit,
        )?
    } else {
        GroupTemplates::default()
    };
    if opts.group_rounds > 0 && group_templates.groups.is_empty() {
        bail!("introduced-clause-backfill-search group candidate set did not produce any groups");
    }
    let mut group_scorer = AssignmentResidualScorer::new(formula.num_vars, &formula.clauses);
    let mut group_rounds = Vec::new();
    let mut evaluated_group_flips = 0usize;
    let mut evaluated_group_affected_clauses = 0usize;
    for round_idx in 0..opts.group_rounds {
        let current_count = current_residual.len();
        let current_residual_flags = residual_flags(formula.clauses.len(), &current_residual);
        let mut best_group: Option<Vec<usize>> = None;
        let mut best_residual_count = current_count;
        let mut top = Vec::new();
        for group in &group_templates.groups {
            let score = group_scorer.flip_group_residual_count(
                &assignment,
                group,
                &current_residual_flags,
                current_count,
            );
            evaluated_group_flips += 1;
            evaluated_group_affected_clauses += score.affected_clause_count;
            top.push((score.residual_count, group.clone()));
            let better_tie = match &best_group {
                Some(best) => group < best,
                None => true,
            };
            if score.residual_count < best_residual_count
                || (score.residual_count == best_residual_count && better_tie)
            {
                best_group = Some(group.clone());
                best_residual_count = score.residual_count;
            }
        }
        top.sort_by(|(left_count, left_group), (right_count, right_group)| {
            left_count
                .cmp(right_count)
                .then_with(|| left_group.cmp(right_group))
        });
        let top_candidates: Vec<_> = top
            .iter()
            .take(16)
            .map(|(count, group)| {
                let residual =
                    residual_clause_ids_after_group_flip(&formula.clauses, &assignment, group);
                debug_assert_eq!(*count, residual.len());
                json!({
                    "one_based_vars": group.iter().map(|var| var + 1).collect::<Vec<_>>(),
                    "source_kinds": group.iter().map(|var| {
                        backfill_search_candidate_source_kind(
                            *var + 1,
                            &source_var_set,
                            &window_only_vars,
                            &selected_outside_radius_var_set,
                        )
                    }).collect::<Vec<_>>(),
                    "residual_falsified_clause_count": count,
                    "residual_falsified_one_based_clause_ids": residual.iter().take(32).map(|idx| idx + 1).collect::<Vec<_>>(),
                })
            })
            .collect();
        let improved = best_residual_count < current_count;
        let selected_group = if improved { best_group } else { None };
        if let Some(group) = &selected_group {
            for &var in group {
                assignment[var] = !assignment[var];
            }
            current_residual = residual_clause_ids(&formula.clauses, &assignment);
            debug_assert_eq!(best_residual_count, current_residual.len());
        }
        group_rounds.push(json!({
            "round": round_idx + 1,
            "starting_residual_falsified_clause_count": current_count,
            "selected_one_based_vars": selected_group.as_ref().map(|group| group.iter().map(|var| var + 1).collect::<Vec<_>>()),
            "selected_source_kinds": selected_group.as_ref().map(|group| group.iter().map(|var| {
                backfill_search_candidate_source_kind(
                    *var + 1,
                    &source_var_set,
                    &window_only_vars,
                    &selected_outside_radius_var_set,
                )
            }).collect::<Vec<_>>()),
            "selected_new_values": selected_group.as_ref().map(|group| group.iter().map(|var| assignment[*var]).collect::<Vec<_>>()),
            "ending_residual_falsified_clause_count": if improved { current_residual.len() } else { current_count },
            "improved": improved,
            "top_candidates": top_candidates,
        }));
        if !improved {
            break;
        }
    }

    let best_delta = assignment_delta_from_base(&w210_assignment, &assignment);
    write_set_tsv(&best_set_path, &w210_assignment, &best_delta)?;
    let valid_model = current_residual.is_empty();
    let introduced_clause_ids: BTreeSet<_> = candidates
        .clauses
        .iter()
        .map(|clause| clause.one_based_clause_id)
        .collect();
    let search_payload = json!({
        "engine": "assignment-local-search-inprocess",
        "authority": "diagnostic_only",
        "rounds_requested": opts.rounds,
        "rounds_run": rounds.len(),
        "candidate_count": search_candidates.len(),
        "evaluated_flips": evaluated_flips,
        "rounds": rounds,
        "pair_rounds_requested": opts.pair_rounds,
        "pair_rounds_run": pair_rounds.len(),
        "pair_candidate_count": pair_candidates.len(),
        "pair_candidate_limit": opts.pair_candidate_limit,
        "evaluated_pair_flips": evaluated_pair_flips,
        "pair_rounds": pair_rounds,
        "group_rounds_requested": opts.group_rounds,
        "group_rounds_run": group_rounds.len(),
        "group_size": opts.group_size,
        "group_window_size": opts.group_window_size,
        "group_candidate_count": group_candidates.len(),
        "group_candidate_limit": opts.group_candidate_limit,
        "group_evaluation_limit": opts.group_evaluation_limit,
        "group_template_count": group_templates.groups.len(),
        "group_templates_truncated": group_templates.truncated,
        "evaluated_group_flips": evaluated_group_flips,
        "evaluated_group_affected_clauses": evaluated_group_affected_clauses,
        "group_scoring": "incremental_affected_clause_delta",
        "group_rounds": group_rounds,
    });
    let seed_payload = json!({
        "enabled": !opts.seed_set_files.is_empty(),
        "set_files": opts.seed_set_files.iter().map(|path| display_path_for_report(&resolve_path(&root, path), &root)).collect::<Vec<_>>(),
        "one_based_set_values": seed_set_values.iter().map(|(var, value)| json!({"var": var + 1, "value": value})).collect::<Vec<_>>(),
        "set_var_count": seed_set_values.len(),
        "changed_from_w210_var_count": seed_delta.len(),
        "one_based_changed_from_w210_vars": seed_delta.iter().map(|(var, value)| json!({"var": var + 1, "value": value})).collect::<Vec<_>>(),
        "residual_falsified_clause_count": seed_residual.len(),
        "residual_falsified_one_based_clause_ids": seed_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
    });
    let input_payload = json!({
        "path": display_path_for_report(&target_cnf, &root),
        "sha256": target_sha256,
        "num_vars": formula.num_vars,
        "num_clauses": formula.clauses.len(),
    });
    let candidates_report_payload = json!({
        "path": display_path_for_report(&report_path, &root),
        "sha256": sha256_file(&report_path)?,
        "schema": report_json.get("schema").cloned().unwrap_or(JsonValue::Null),
        "repo_head": report_json.pointer("/source/repo_head").cloned().unwrap_or(JsonValue::Null),
    });
    let w210_ledgers_payload = json!({
        "paths": ledgers.iter().map(|path| display_path_for_report(path, &root)).collect::<Vec<_>>(),
        "stats": ledger_stats,
    });
    let materialized_candidates_payload = json!({
        "source": "introduced-clause-backfill-candidates JSON report",
        "source_candidate_limit": opts.source_candidate_limit,
        "source_candidate_count": candidates.candidate_vars.len(),
        "selected_source_candidate_count": selected_source_vars.len(),
        "source_candidates_truncated": candidates.candidate_vars.len().saturating_sub(selected_source_vars.len()),
        "selected_source_candidate_one_based_vars": selected_source_vars,
        "window_var_limit": opts.window_var_limit,
        "window_var_count": candidates.window_vars.len(),
        "window_only_var_count": window_only_vars.len(),
        "selected_window_only_var_count": selected_window_vars.len(),
        "window_only_vars_truncated": window_only_vars.len().saturating_sub(selected_window_vars.len()),
        "window_vars_truncated": window_only_vars.len().saturating_sub(selected_window_vars.len()),
        "selected_window_only_one_based_vars": selected_window_vars,
        "include_outside_radius_vars": opts.include_outside_radius_vars,
        "outside_radius": opts.outside_radius,
        "outside_radius_var_limit": opts.outside_radius_var_limit,
        "outside_radius_w210_residual_falsified_clause_count": w210_residual.len(),
        "outside_radius_w210_residual_one_based_clause_ids": w210_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
        "outside_radius_residual_source": "seed_assignment",
        "outside_radius_seed_residual_falsified_clause_count": seed_residual.len(),
        "outside_radius_seed_residual_one_based_clause_ids": seed_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
        "outside_radius_free_var_count": outside_radius_free_var_count,
        "outside_radius_var_count": outside_radius_var_count,
        "one_based_outside_radius_vars": outside_radius_one_based_vars,
        "outside_radius_only_var_count": outside_radius_only_var_count,
        "one_based_outside_radius_only_vars": outside_radius_only_one_based_vars,
        "outside_radius_window_overlap_var_count": outside_radius_window_overlap_vars.as_ref().map(Vec::len),
        "outside_radius_window_overlap_one_based_vars": outside_radius_window_overlap_vars,
        "selected_outside_radius_only_var_count": selected_outside_radius_vars.len(),
        "outside_radius_vars_truncated": outside_radius_vars_truncated,
        "selected_outside_radius_only_one_based_vars": selected_outside_radius_vars,
        "selected_candidate_count": selected_candidate_vars.len(),
        "selected_candidate_one_based_vars": selected_candidate_vars,
        "introduced_clause_count": candidates.clauses.len(),
        "introduced_one_based_clause_ids": introduced_clause_ids.iter().copied().collect::<Vec<_>>(),
        "clause_windows": candidates.clauses.iter().map(backfill_candidate_clause_json).collect::<Vec<_>>(),
    });
    let baseline_w210_payload = json!({
        "residual_falsified_clause_count": w210_residual.len(),
        "residual_falsified_one_based_clause_ids": w210_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
    });
    let best_payload = json!({
        "residual_falsified_clause_count": current_residual.len(),
        "residual_falsified_one_based_clause_ids": current_residual.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
        "original_dimacs_valid_model": valid_model,
        "changed_from_w210_var_count": best_delta.len(),
        "one_based_set_values": best_delta.iter().map(|(var, value)| json!({"var": var + 1, "value": value})).collect::<Vec<_>>(),
        "set_file": display_path_for_report(&best_set_path, &root),
        "set_file_sha256": sha256_file(&best_set_path)?,
    });
    let verdict_payload = json!({
        "diagnostic_only": true,
        "original_dimacs_valid_model": valid_model,
        "complete_original_dimacs_valid_model_found": valid_model,
        "route_admitted": false,
        "sat_output_authority": false,
        "model_output_authority": false,
        "proof_output_authority": false,
        "solver_verdict_authority": false,
        "sat_comp_progress_claim": false,
        "blocker": if valid_model {
            "Backfill search found an assignment that validates against the original DIMACS, but this diagnostic does not admit a solver route or grant SAT/model authority."
        } else {
            "Backfill search did not find an original-DIMACS-valid model; residual clauses remain."
        },
    });
    let payload = json!({
        "schema": "ay.satcomp-circuit-introduced-clause-backfill-search/v1",
        "issue": 9424,
        "scoreboard_row": "Circuit_multiplier22",
        "source": diagnostic_source_json(
            git_head(&root),
            "Diagnostic-only Rust SAT-COMP submission/preflight CLI introduced-clause backfill search. No route, SAT stdout, model-output, proof, solved-count, PAR-2, or SAT-COMP authority is granted.",
        ),
        "input": input_payload,
        "introduced_clause_backfill_candidates_report": candidates_report_payload,
        "w210_ledgers": w210_ledgers_payload,
        "materialized_candidates": materialized_candidates_payload,
        "baseline_w210": baseline_w210_payload,
        "seed": seed_payload,
        "search": search_payload,
        "best": best_payload,
        "authority": diagnostic_authority_json(),
        "verdict": verdict_payload,
    });
    write_json(&output, &payload)?;
    println!("{}", serde_json::to_string(&payload["verdict"])?);
    Ok(())
}

fn run_residual_side_effect_backbone(opts: ResidualSideEffectBackboneOptions) -> Result<()> {
    let root = repo_root()?;
    let target_cnf = resolve_path(&root, &opts.target_cnf);
    let report_path = resolve_path(&root, &opts.side_effect_report);
    let output = opts
        .output
        .as_ref()
        .map(|path| resolve_path(&root, path))
        .unwrap_or_else(|| {
            root.join(DEFAULT_OUTPUT_DIR)
                .join("residual-side-effect-backbone.json")
        });
    let formula = parse_dimacs_path(&target_cnf)?;
    let target_sha256 = sha256_file(&target_cnf)?;
    let current_repo_head = git_head(&root)
        .context("residual-side-effect-backbone could not determine current git HEAD")?;
    let report_json = read_bounded_json_report(
        &report_path,
        "assignment-local-search side-effect report",
        MAX_BACKFILL_FRONTIER_REPORT_BYTES,
    )?;
    validate_assignment_local_search_report_for_backfill(
        &report_json,
        &formula,
        &target_sha256,
        &current_repo_head,
    )?;
    let backbone = collect_residual_side_effect_backbone(&formula, &report_json)?;
    let side_effect_report_sha256 = sha256_file(&report_path)?;
    let side_effect_report_repo_head = report_json
        .pointer("/source/repo_head")
        .and_then(JsonValue::as_str)
        .map(str::to_string);
    let frontier = opts
        .frontier_report
        .as_ref()
        .map(|path| -> Result<ResidualSideEffectFrontierSummary> {
            let path = resolve_path(&root, path);
            let frontier_json = read_bounded_json_report(
                &path,
                "introduced-clause-backfill-frontier report",
                MAX_BACKFILL_FRONTIER_REPORT_BYTES,
            )?;
            validate_residual_side_effect_frontier_report(
                &path,
                &frontier_json,
                &formula,
                &target_sha256,
                &current_repo_head,
                &side_effect_report_sha256,
            )
        })
        .transpose()?;
    let frontier_ids = frontier
        .as_ref()
        .map(|summary| &summary.unique_introduced_one_based_clause_ids);
    let anchored_residuals: BTreeSet<_> = backbone.residual_to_anchor_ids.keys().copied().collect();
    let uncovered_residuals: Vec<_> = backbone
        .baseline_residual_one_based_clause_ids
        .difference(&anchored_residuals)
        .copied()
        .collect();
    let frontier_covered_side_effects: BTreeSet<_> = frontier_ids
        .map(|ids| {
            backbone
                .unique_introduced_residual_one_based_clause_ids
                .intersection(ids)
                .copied()
                .collect()
        })
        .unwrap_or_default();
    let frontier_uncovered_side_effects: BTreeSet<_> = frontier_ids
        .map(|ids| {
            backbone
                .unique_introduced_residual_one_based_clause_ids
                .difference(ids)
                .copied()
                .collect()
        })
        .unwrap_or_default();
    let anchors = backbone
        .anchors
        .iter()
        .map(|anchor| residual_side_effect_anchor_json(anchor, frontier_ids))
        .collect::<Vec<_>>();
    let residual_backbone = backbone
        .baseline_residual_one_based_clause_ids
        .iter()
        .map(|clause_id| {
            let anchor_ids = backbone
                .residual_to_anchor_ids
                .get(clause_id)
                .cloned()
                .unwrap_or_default();
            json!({
                "one_based_residual_clause_id": clause_id,
                "covered_by_anchor": !anchor_ids.is_empty(),
                "anchor_count": anchor_ids.len(),
                "anchor_ids": anchor_ids,
            })
        })
        .collect::<Vec<_>>();
    let frontier_payload = frontier.as_ref().map(|summary| {
        json!({
            "present": true,
            "path": display_path_for_report(&summary.path, &root),
            "sha256": summary.sha256,
            "schema": "ay.satcomp-circuit-introduced-clause-backfill-frontier/v1",
            "source_repo_head": summary.source_repo_head,
            "source_repo_head_matches_current": summary.source_repo_head == current_repo_head,
            "assignment_local_search_report_sha256": summary.assignment_local_search_report_sha256,
            "unique_introduced_clause_count": summary.unique_introduced_one_based_clause_ids.len(),
            "unique_introduced_one_based_clause_ids": summary.unique_introduced_one_based_clause_ids.iter().copied().collect::<Vec<_>>(),
            "side_effect_introduced_covered_count": frontier_covered_side_effects.len(),
            "side_effect_introduced_covered_one_based_clause_ids": frontier_covered_side_effects.iter().copied().collect::<Vec<_>>(),
            "side_effect_introduced_uncovered_count": frontier_uncovered_side_effects.len(),
            "side_effect_introduced_uncovered_one_based_clause_ids": frontier_uncovered_side_effects.iter().copied().collect::<Vec<_>>(),
        })
    });
    let frontier_covers_all_anchor_introductions = frontier_ids.map(|_| {
        frontier_uncovered_side_effects.is_empty()
            && !backbone
                .unique_introduced_residual_one_based_clause_ids
                .is_empty()
    });
    let payload = json!({
        "schema": "ay.satcomp-circuit-residual-side-effect-backbone/v1",
        "issue": 9424,
        "scoreboard_row": "Circuit_multiplier22",
        "source": diagnostic_source_json(
            Some(current_repo_head.clone()),
            "Diagnostic-only Rust SAT-COMP submission/preflight CLI residual side-effect backbone. No route, SAT stdout, model-output, proof, solved-count, PAR-2, or SAT-COMP authority is granted.",
        ),
        "input": {
            "path": display_path_for_report(&target_cnf, &root),
            "sha256": target_sha256,
            "num_vars": formula.num_vars,
            "num_clauses": formula.clauses.len(),
        },
        "side_effect_report": {
            "path": display_path_for_report(&report_path, &root),
            "sha256": side_effect_report_sha256,
            "schema": report_json.get("schema").cloned().unwrap_or(JsonValue::Null),
            "repo_head": side_effect_report_repo_head,
            "ay_build": report_json.pointer("/source/ay_build").cloned().unwrap_or(JsonValue::Null),
            "repo_head_matches_current": side_effect_report_repo_head.as_deref() == Some(&current_repo_head),
            "source_repo_head_required_current": true,
            "source_ay_build_required_current": true,
            "input_sha256_verified_against_target_cnf": true,
            "authority": "diagnostic_only",
        },
        "introduced_clause_backfill_frontier": frontier_payload.unwrap_or_else(|| {
            json!({
                "present": false,
                "note": "No frontier report supplied; anchor side effects are emitted but frontier coverage is unknown.",
            })
        }),
        "baseline_residual": {
            "count": backbone.baseline_residual_one_based_clause_ids.len(),
            "one_based_clause_ids": backbone.baseline_residual_one_based_clause_ids.iter().copied().collect::<Vec<_>>(),
        },
        "anchors": anchors,
        "residual_backbone": residual_backbone,
        "uncovered_residuals": {
            "count": uncovered_residuals.len(),
            "one_based_clause_ids": uncovered_residuals,
        },
        "side_effects": {
            "unique_introduced_residual_count": backbone.unique_introduced_residual_one_based_clause_ids.len(),
            "unique_introduced_residual_one_based_clause_ids": backbone.unique_introduced_residual_one_based_clause_ids.iter().copied().collect::<Vec<_>>(),
            "unique_affected_clause_count": backbone.unique_affected_one_based_clause_ids.len(),
            "unique_affected_one_based_clause_ids": backbone.unique_affected_one_based_clause_ids.iter().copied().collect::<Vec<_>>(),
        },
        "counts": {
            "top_candidates_seen": backbone.top_candidates_seen,
            "top_candidates_with_side_effect_summary": backbone.top_candidates_with_side_effect_summary,
            "anchor_candidate_count": backbone.anchors.len(),
            "baseline_residual_count": backbone.baseline_residual_one_based_clause_ids.len(),
            "anchored_residual_count": anchored_residuals.len(),
            "uncovered_residual_count": uncovered_residuals.len(),
            "introduced_side_effect_unique_count": backbone.unique_introduced_residual_one_based_clause_ids.len(),
            "frontier_present": frontier_ids.is_some(),
            "frontier_unique_introduced_clause_count": frontier_ids.map(BTreeSet::len),
            "frontier_covered_introduced_side_effect_count": frontier_ids.map(|_| frontier_covered_side_effects.len()),
            "frontier_uncovered_introduced_side_effect_count": frontier_ids.map(|_| frontier_uncovered_side_effects.len()),
        },
        "authority": diagnostic_authority_json(),
        "verdict": {
            "diagnostic_only": true,
            "anchors_emitted": !backbone.anchors.is_empty(),
            "all_baseline_residuals_have_anchor": uncovered_residuals.is_empty(),
            "uncovered_residual_count": uncovered_residuals.len(),
            "frontier_present": frontier_ids.is_some(),
            "frontier_covers_all_anchor_introductions": frontier_covers_all_anchor_introductions,
            "route_admitted": false,
            "sat_output_authority": false,
            "model_output_authority": false,
            "proof_output_authority": false,
            "solver_verdict_authority": false,
            "sat_comp_progress_claim": false,
            "blocker": if uncovered_residuals.is_empty() {
                "Every baseline residual has at least one diagnostic side-effect anchor, but this backbone does not solve, emit a model/proof, or authorize a SAT-COMP route."
            } else {
                "At least one baseline residual still lacks a diagnostic side-effect anchor; no solver route, model/proof output, or SAT-COMP claim is authorized."
            },
        },
    });
    write_json(&output, &payload)?;
    println!("{}", serde_json::to_string(&payload["verdict"])?);
    Ok(())
}

fn run_frontier_assisted_model_materializer(
    opts: FrontierAssistedModelMaterializerOptions,
) -> Result<()> {
    let FrontierAssistedModelMaterializerOptions {
        common,
        side_effect_report,
        frontier_report,
        seed_set_files,
        target_residual_clause,
        radius,
        frontier_candidate_limit,
        window_size,
        window_limit,
    } = opts;
    let root = repo_root()?;
    ensure_timeout(&common)?;
    if target_residual_clause == 0 {
        bail!("--target-residual-clause must be one-based and positive");
    }
    if frontier_candidate_limit == 0 {
        bail!("--frontier-candidate-limit must be positive");
    }
    if window_size == 0 {
        bail!("--window-size must be positive");
    }
    if window_limit == 0 {
        bail!("--window-limit must be positive");
    }

    let ay_bin = ay_bin(&common)?;
    let mut input = load_inputs(&root, &common)?;
    if target_residual_clause > input.formula.clauses.len() {
        bail!(
            "--target-residual-clause {} is out of range 1..={}",
            target_residual_clause,
            input.formula.clauses.len()
        );
    }
    let target_zero_based_clause = target_residual_clause - 1;
    let target_sha256 = sha256_file(&input.target_cnf)?;
    let current_repo_head = git_head(&root)
        .context("frontier-assisted-model-materializer could not determine current git HEAD")?;

    let side_effect_report_path = resolve_path(&root, &side_effect_report);
    let side_effect_json = read_bounded_json_report(
        &side_effect_report_path,
        "assignment-local-search side-effect report",
        MAX_BACKFILL_FRONTIER_REPORT_BYTES,
    )?;
    validate_assignment_local_search_report_for_backfill(
        &side_effect_json,
        &input.formula,
        &target_sha256,
        &current_repo_head,
    )?;
    let backbone = collect_residual_side_effect_backbone(&input.formula, &side_effect_json)?;
    let side_effect_report_sha256 = sha256_file(&side_effect_report_path)?;

    let w210_assignment = input.assignment.clone();
    let w210_residual_ids = input.residual_ids.clone();
    let w210_residual_one_based: BTreeSet<_> =
        w210_residual_ids.iter().map(|idx| idx + 1).collect();
    if backbone.baseline_residual_one_based_clause_ids != w210_residual_one_based {
        bail!(
            "side-effect baseline residuals {:?} do not match W210 ledgers {:?}",
            backbone.baseline_residual_one_based_clause_ids,
            w210_residual_one_based
        );
    }
    if !w210_residual_one_based.contains(&target_residual_clause) {
        bail!(
            "target residual clause {target_residual_clause} is not falsified by the W210 ledgers"
        );
    }
    let target_anchor_ids = backbone
        .residual_to_anchor_ids
        .get(&target_residual_clause)
        .cloned()
        .unwrap_or_default();
    if !target_anchor_ids.is_empty() {
        bail!(
            "target residual clause {target_residual_clause} already has diagnostic anchors: {target_anchor_ids:?}"
        );
    }

    let frontier_report_path = resolve_path(&root, &frontier_report);
    let frontier_json = read_bounded_json_report(
        &frontier_report_path,
        "introduced-clause-backfill-frontier report",
        MAX_BACKFILL_FRONTIER_REPORT_BYTES,
    )?;
    let frontier = validate_residual_side_effect_frontier_report(
        &frontier_report_path,
        &frontier_json,
        &input.formula,
        &target_sha256,
        &current_repo_head,
        &side_effect_report_sha256,
    )?;
    let frontier_uncovered_side_effects: BTreeSet<_> = backbone
        .unique_introduced_residual_one_based_clause_ids
        .difference(&frontier.unique_introduced_one_based_clause_ids)
        .copied()
        .collect();
    if !frontier_uncovered_side_effects.is_empty() {
        bail!(
            "frontier report does not cover all anchor-introduced side effects: {frontier_uncovered_side_effects:?}"
        );
    }
    let frontier_candidates = collect_introduced_clause_backfill_candidates(
        &frontier_json,
        input.formula.num_vars,
        input.formula.clauses.len(),
    )?;

    let seed_set_values = apply_assignment_sets(
        &root,
        input.formula.num_vars,
        &mut input.assignment,
        &seed_set_files,
    )?;
    input.residual_ids = residual_clause_ids(&input.formula.clauses, &input.assignment);
    let seed_delta = assignment_delta_from_base(&w210_assignment, &input.assignment);
    let seed_residual_one_based: BTreeSet<_> =
        input.residual_ids.iter().map(|idx| idx + 1).collect();
    let radius_free_vars = grow_free_vars(
        input.formula.num_vars,
        &input.formula.clauses,
        &input.residual_ids,
        radius,
    );
    let outside_vars: Vec<usize> = (0..input.formula.num_vars)
        .filter(|var| !radius_free_vars.contains(var))
        .collect();
    let outside_set: BTreeSet<usize> = outside_vars.iter().copied().collect();
    let frontier_ledger = collect_frontier_materializer_ledger(
        &input.formula,
        &input.assignment,
        target_residual_clause,
        &radius_free_vars,
        &backbone,
        &frontier_candidates,
    )?;
    let selected_frontier_rows: Vec<_> = frontier_ledger
        .iter()
        .filter(|row| row.outside_radius)
        .take(frontier_candidate_limit)
        .cloned()
        .collect();
    if selected_frontier_rows.is_empty() {
        bail!(
            "frontier-assisted model materializer found no outside-radius frontier candidates for target residual clause {target_residual_clause}"
        );
    }
    let selected_one_based_vars: Vec<_> = selected_frontier_rows
        .iter()
        .map(|row| row.one_based_var)
        .collect();
    let selected_window_size = window_size.min(selected_one_based_vars.len());
    let windows = frontier_materializer_windows(
        target_residual_clause,
        &selected_one_based_vars,
        selected_window_size,
        window_limit,
    );
    if windows.is_empty() {
        bail!("frontier-assisted model materializer selected no windows");
    }

    let output = output_path(&root, &common, "frontier-assisted-model-materializer")?;
    if let Some(parent) = output.parent() {
        fs::create_dir_all(parent)?;
    }
    let (work_dir, cleanup) =
        prepare_work_dir(&root, &common, "frontier-assisted-model-materializer")?;
    let version = run_version(&ay_bin)?;

    let mut rows = Vec::new();
    for (idx, window) in windows.iter().enumerate() {
        let window_vars: BTreeSet<usize> =
            window.one_based_vars.iter().map(|var| var - 1).collect();
        let out_of_range: Vec<usize> = window_vars
            .iter()
            .filter(|&&var| var >= input.formula.num_vars)
            .map(|var| var + 1)
            .collect();
        if !out_of_range.is_empty() {
            bail!(
                "frontier window {} contains variables outside the formula variable range: {:?}",
                window.name,
                out_of_range
            );
        }
        let extra_outside_window_vars = window_vars
            .iter()
            .filter(|var| outside_set.contains(var))
            .count();
        if extra_outside_window_vars == 0 {
            bail!(
                "frontier window {} does not contain an outside-radius variable",
                window.name
            );
        }
        let already_radius_free = window_vars
            .iter()
            .filter(|var| radius_free_vars.contains(var))
            .count();
        let free_total_vars = radius_free_vars.union(&window_vars).count();
        let reduced_cnf = work_dir.join(format!(
            "frontier-window-{:02}-{}.cnf",
            idx + 1,
            window.name
        ));
        let proof = reduced_cnf.with_extension("cnf.drat");
        let (frozen_count, frozen_vars) = write_reduced_cnf(
            &reduced_cnf,
            &input.formula,
            &input.assignment,
            &radius_free_vars,
            &window_vars,
        )?;
        let solve = run_solver(&ay_bin, &reduced_cnf, &proof, common.timeout_sec)?;
        let is_sat = solve.exit_code == Some(10) && solve.stdout.contains("s SATISFIABLE");
        let is_unsat = solve.exit_code == Some(20) && solve.stdout.contains("s UNSATISFIABLE");
        let proof_check = if is_unsat {
            Some(verify_drat(&reduced_cnf, &proof))
        } else {
            None
        };
        let unsat_verified = proof_check.as_ref().is_some_and(|result| {
            result.exit_code == Some(0) && result.stdout.contains("s VERIFIED")
        });
        let mut model_stats = None;
        let mut original_model_valid = false;
        let mut falsified_original: Option<Vec<usize>> = None;
        let mut frozen_preserved = None;
        let mut changed_window_values = None;
        let mut model_path = None;
        let mut model_sha = None;
        if is_sat {
            let (model, stats) = parse_solver_model(&solve.stdout, input.formula.num_vars);
            model_stats = Some(stats);
            if let Some(model) = model {
                let falsified = falsified_clause_ids(&input.formula.clauses, &model);
                original_model_valid = falsified.is_empty();
                falsified_original = Some(falsified);
                let preserved = frozen_vars
                    .iter()
                    .all(|&var| model[var] == input.assignment[var]);
                frozen_preserved = Some(preserved);
                let changed: Vec<usize> = window_vars
                    .iter()
                    .copied()
                    .filter(|&var| model[var] != input.assignment[var])
                    .map(|var| var + 1)
                    .collect();
                changed_window_values = Some(changed);
                if original_model_valid && preserved {
                    let path = output.with_file_name(format!(
                        "frontier-window-{:02}-{}-model.txt",
                        idx + 1,
                        window.name
                    ));
                    write_dimacs_model(&path, &model)?;
                    model_sha = Some(sha256_file(&path)?);
                    model_path = Some(path);
                }
            }
        }
        let status = if original_model_valid && frozen_preserved == Some(true) {
            "sat_valid_original_model"
        } else if is_sat {
            "sat_invalid_or_incomplete_model"
        } else if is_unsat && unsat_verified {
            "unsat_verified"
        } else if is_unsat {
            "unsat_unverified"
        } else if solve.timed_out {
            "timeout"
        } else {
            "unknown_or_error"
        };
        println!(
            "frontier window {}/{} {} status={} solve_ms={}",
            idx + 1,
            windows.len(),
            window.name,
            status,
            solve.wall_time_ms
        );
        rows.push(json!({
            "window_index": idx + 1,
            "window_name": window.name,
            "one_based_window_vars": window.one_based_vars,
            "window_var_count": window_vars.len(),
            "window_vars_already_radius_free": already_radius_free,
            "extra_outside_window_vars": extra_outside_window_vars,
            "free_radius_vars": radius_free_vars.len(),
            "free_total_vars": free_total_vars,
            "outside_radius_vars": outside_vars.len(),
            "frozen_outside_vars": frozen_count,
            "frozen_outside_one_based_vars": frozen_vars.iter().map(|var| var + 1).collect::<Vec<_>>(),
            "unit_clauses": frozen_count,
            "reduced_num_clauses": input.formula.clauses.len() + frozen_count,
            "cnf_sha256": sha256_file(&reduced_cnf)?,
            "cnf_path": display_path_for_report(&reduced_cnf, &root),
            "cnf_retained": common.retain_work,
            "proof_path": display_path_for_report(&proof, &root),
            "proof_retained": common.retain_work && proof.exists(),
            "solve": solve.json(),
            "is_sat": is_sat,
            "is_unsat": is_unsat,
            "proof_check": proof_check.as_ref().map(CommandResult::json),
            "unsat_verified": unsat_verified,
            "model_stats": model_stats,
            "original_model_valid": original_model_valid,
            "frozen_outside_values_preserved": frozen_preserved,
            "window_values_changed_from_seed_assignment": changed_window_values,
            "falsified_original_clause_count": falsified_original.as_ref().map(Vec::len),
            "first_falsified_original_zero_based": falsified_original.as_ref().map(|items| items.iter().take(16).copied().collect::<Vec<_>>()),
            "valid_model_path": model_path.as_ref().map(|path| display_path_for_report(path, &root)),
            "valid_model_sha256": model_sha,
            "status": status,
        }));
        if !common.retain_work {
            let _ = fs::remove_file(&reduced_cnf);
            let _ = fs::remove_file(&proof);
        }
    }
    if cleanup {
        let _ = fs::remove_dir_all(&work_dir);
    }

    let counts = counts_for_rows(&rows, "frontier_window");
    let all_windows_checked = rows.len() == windows.len();
    let all_unsat_verified = all_windows_checked && counts.unsat_verified == windows.len();
    let any_valid_model = counts.sat_valid > 0;
    let mut payload = base_payload(
        "ay.satcomp-circuit-frontier-assisted-model-materializer/v1",
        &root,
        &common,
        &input,
    )?;
    payload["solver"]["ay_bin_sha256"] = json!(sha256_file(&ay_bin)?);
    payload["solver"]["version"] = version.json();
    payload["side_effect_report"] = json!({
        "path": display_path_for_report(&side_effect_report_path, &root),
        "sha256": side_effect_report_sha256,
        "schema": side_effect_json.get("schema").cloned().unwrap_or(JsonValue::Null),
        "repo_head": side_effect_json.pointer("/source/repo_head").cloned().unwrap_or(JsonValue::Null),
        "ay_build": side_effect_json.pointer("/source/ay_build").cloned().unwrap_or(JsonValue::Null),
        "source_repo_head_required_current": true,
        "source_ay_build_required_current": true,
        "input_sha256_verified_against_target_cnf": true,
        "authority": "diagnostic_only",
    });
    payload["introduced_clause_backfill_frontier"] = json!({
        "path": display_path_for_report(&frontier.path, &root),
        "sha256": frontier.sha256,
        "schema": "ay.satcomp-circuit-introduced-clause-backfill-frontier/v1",
        "source_repo_head": frontier.source_repo_head,
        "source_repo_head_matches_current": frontier.source_repo_head == current_repo_head,
        "assignment_local_search_report_sha256": frontier.assignment_local_search_report_sha256,
        "unique_introduced_clause_count": frontier.unique_introduced_one_based_clause_ids.len(),
        "unique_introduced_one_based_clause_ids": frontier.unique_introduced_one_based_clause_ids.iter().copied().collect::<Vec<_>>(),
        "anchor_introduced_uncovered_count": frontier_uncovered_side_effects.len(),
        "anchor_introduced_uncovered_one_based_clause_ids": frontier_uncovered_side_effects.iter().copied().collect::<Vec<_>>(),
        "authority": diagnostic_authority_json(),
    });
    payload["assignment_overlay"] = json!({
        "enabled": !seed_set_files.is_empty(),
        "seed_set_files": seed_set_files.iter().map(|path| display_path_for_report(&resolve_path(&root, path), &root)).collect::<Vec<_>>(),
        "one_based_set_values": seed_set_values.iter().map(|(var, value)| json!({"var": var + 1, "value": value})).collect::<Vec<_>>(),
        "set_var_count": seed_set_values.len(),
        "changed_from_w210_var_count": seed_delta.len(),
        "one_based_changed_from_w210_vars": seed_delta.iter().map(|(var, value)| json!({"var": var + 1, "value": value})).collect::<Vec<_>>(),
        "w210_residual_falsified_clause_count": w210_residual_ids.len(),
        "w210_residual_falsified_one_based_clause_ids": w210_residual_ids.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
        "seed_residual_falsified_clause_count": input.residual_ids.len(),
        "seed_residual_falsified_one_based_clause_ids": input.residual_ids.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
        "authority": "diagnostic_only",
    });
    payload["target_residual"] = json!({
        "one_based_clause_id": target_residual_clause,
        "zero_based_clause_id": target_zero_based_clause,
        "original_clause_lits": input.formula.clauses[target_zero_based_clause],
        "original_clause_one_based_vars": input.formula.clauses[target_zero_based_clause].iter().map(|lit| lit.unsigned_abs() as usize).collect::<BTreeSet<_>>().into_iter().collect::<Vec<_>>(),
        "in_w210_residual": w210_residual_one_based.contains(&target_residual_clause),
        "in_seed_residual": seed_residual_one_based.contains(&target_residual_clause),
        "covered_by_side_effect_anchor": false,
        "anchor_ids": target_anchor_ids,
    });
    payload["materializer_definition"] = json!({
        "target_residual_clause": target_residual_clause,
        "radius": radius,
        "radius_free_vars": radius_free_vars.len(),
        "outside_radius_var_count": outside_vars.len(),
        "one_based_outside_radius_vars": outside_vars.iter().map(|var| var + 1).collect::<Vec<_>>(),
        "frontier_candidate_limit": frontier_candidate_limit,
        "frontier_ledger_row_count": frontier_ledger.len(),
        "frontier_ledger_outside_radius_row_count": frontier_ledger.iter().filter(|row| row.outside_radius).count(),
        "selected_frontier_candidate_count": selected_frontier_rows.len(),
        "selected_frontier_one_based_vars": selected_one_based_vars,
        "requested_window_size": window_size,
        "selected_window_size": selected_window_size,
        "window_limit": window_limit,
        "selected_window_count": windows.len(),
        "windows": windows.iter().map(|window| json!({"name": window.name, "one_based_vars": window.one_based_vars})).collect::<Vec<_>>(),
        "method": "Validate current-build side-effect and frontier reports, require the target residual to be an uncovered W210 residual, rank frontier-related outside-radius variables, free each selected frontier window in addition to the active residual-radius surface, solve original DIMACS plus frozen units, and validate any SAT model against the original DIMACS clauses. Diagnostic only.",
    });
    payload["frontier_ledger"] = json!({
        "source": "target residual clause plus introduced-clause frontier candidates plus target-related side-effect anchors",
        "rows": frontier_ledger.iter().map(frontier_materializer_ledger_row_json).collect::<Vec<_>>(),
    });
    payload["windows"] = json!(&rows);
    payload["counts"] = json!({
        "checked_windows": rows.len(),
        "selected_windows": windows.len(),
        "unsat_verified": counts.unsat_verified,
        "unsat_unverified": counts.unsat_unverified,
        "sat_valid_original_model": counts.sat_valid,
        "sat_invalid_or_incomplete_model": counts.sat_invalid,
        "timeout": counts.timeout,
        "unknown_or_error": counts.unknown_or_error,
    });
    payload["authority"] = diagnostic_authority_json();
    payload["verdict"] = json!({
        "diagnostic_only": true,
        "target_residual_clause": target_residual_clause,
        "target_residual_uncovered_by_anchor": true,
        "frontier_candidates_selected": !selected_frontier_rows.is_empty(),
        "all_selected_windows_checked": all_windows_checked,
        "all_selected_windows_unsat_verified": all_unsat_verified,
        "complete_original_dimacs_valid_model_found": any_valid_model,
        "valid_model_windows": rows.iter().filter(|row| row["status"] == "sat_valid_original_model").map(|row| row["window_name"].clone()).collect::<Vec<_>>(),
        "route_admitted": false,
        "sat_output_authority": false,
        "model_output_authority": false,
        "proof_output_authority": false,
        "solver_verdict_authority": false,
        "sat_comp_progress_claim": false,
        "blocker": if any_valid_model {
            "At least one frontier-assisted window produced a complete original-DIMACS-valid model, but this diagnostic does not admit a solver route or grant SAT/model/SAT-COMP authority."
        } else if all_unsat_verified {
            "All selected frontier-assisted windows were UNSAT with verified DRAT, so this bounded materialization surface is exhausted without authorizing a solver route."
        } else {
            "No selected frontier-assisted window produced a complete original-DIMACS-valid model, and at least one window was not UNSAT-verified."
        },
    });
    write_json(&output, &payload)?;
    println!("{}", serde_json::to_string(&payload["verdict"])?);
    if any_valid_model || all_unsat_verified {
        Ok(())
    } else {
        bail!(
            "frontier-assisted model materializer did not find a valid model or verify every selected UNSAT proof"
        )
    }
}

fn run_radius_surface(opts: RadiusSurfaceOptions) -> Result<()> {
    let root = repo_root()?;
    let common = opts.common;
    ensure_timeout(&common)?;
    let ay_bin = ay_bin(&common)?;
    let input = load_inputs(&root, &common)?;
    let neighborhoods = grow_neighborhoods(
        input.formula.num_vars,
        &input.formula.clauses,
        &input.residual_ids,
        opts.max_radius,
    );
    let (work_dir, cleanup) = prepare_work_dir(&root, &common, "radius-surface")?;

    let mut rows = Vec::new();
    let mut all_verified = true;
    for row in neighborhoods {
        let radius = row.radius;
        let free_vars = row.free_vars;
        let reduced_cnf = work_dir.join(format!("w210-radius{radius}-free.cnf"));
        let proof = reduced_cnf.with_extension("cnf.drat");
        let (frozen_units, frozen_vars) = write_reduced_cnf(
            &reduced_cnf,
            &input.formula,
            &input.assignment,
            &free_vars,
            &BTreeSet::new(),
        )?;
        let solve = run_solver(&ay_bin, &reduced_cnf, &proof, common.timeout_sec)?;
        let is_unsat = solve.exit_code == Some(20) && solve.stdout.contains("s UNSATISFIABLE");
        let proof_check = if is_unsat {
            Some(verify_drat(&reduced_cnf, &proof))
        } else {
            None
        };
        let drat_verified = proof_check.as_ref().is_some_and(|result| {
            result.exit_code == Some(0) && result.stdout.contains("s VERIFIED")
        });
        all_verified &= is_unsat && drat_verified;
        let mut row_json = json!({
            "radius": radius,
            "free_vars": free_vars.len(),
            "frozen_w210_unit_clauses": frozen_units,
            "touched_clauses": row.touched_clauses,
            "delta_vars": row.delta_vars,
            "reduced_num_clauses": input.formula.clauses.len() + frozen_units,
            "cnf_sha256": sha256_file(&reduced_cnf)?,
            "cnf_path": display_path_for_report(&reduced_cnf, &root),
            "proof_path": display_path_for_report(&proof, &root),
            "solve": solve.json(),
            "proof_check": proof_check.as_ref().map(CommandResult::json),
            "unsat_verified": is_unsat && drat_verified,
        });
        if radius == opts.max_radius {
            row_json["one_based_frozen_vars"] =
                json!(frozen_vars.iter().map(|var| var + 1).collect::<Vec<_>>());
        }
        println!(
            "radius {radius}/{} status={} solve_ms={}",
            opts.max_radius,
            if is_unsat && drat_verified {
                "unsat_verified"
            } else {
                "unverified_or_unknown"
            },
            solve.wall_time_ms
        );
        rows.push(row_json);
        if !common.retain_work {
            let _ = fs::remove_file(&reduced_cnf);
            let _ = fs::remove_file(&proof);
        }
    }
    if cleanup {
        let _ = fs::remove_dir_all(&work_dir);
    }

    let last = rows.last().cloned().unwrap_or_else(|| json!({}));
    let mut payload = base_payload(
        "ay.satcomp-circuit-repair-probe-radius-surface/v1",
        &root,
        &common,
        &input,
    )?;
    payload["neighborhood_definition"] = json!({
        "radius_0": "variables appearing in W210 residual clauses",
        "radius_step": "add every variable from each original DIMACS clause that contains at least one variable already in the prior radius",
        "max_radius": opts.max_radius,
    });
    payload["neighborhoods"] = json!(&rows);
    payload["verdict"] = json!({
        "all_reported_neighborhoods_unsat_verified": all_verified,
        "route_admitted": false,
        "sat_output_authority": false,
        "model_output_authority": false,
        "proof_output_authority": false,
        "sat_comp_progress_claim": false,
        "blocker": "W210 repair is not local to the residual clauses or their reported original-clause incidence neighborhoods.",
        "next_broader_repair_surface": {
            "must_change_at_least_one_w210_value_outside_radius": all_verified,
            "outside_radius_var_count": last.get("frozen_w210_unit_clauses").cloned().unwrap_or_else(|| json!(0)),
            "one_based_outside_radius_vars": last.get("one_based_frozen_vars").cloned().unwrap_or_else(|| json!([])),
        }
    });
    write_payload(&root, &common, "radius-surface", &payload)?;
    if all_verified {
        Ok(())
    } else {
        bail!("not all reported radius surfaces were UNSAT-verified")
    }
}

fn run_outside_single_flip(opts: OutsideSingleFlipOptions) -> Result<()> {
    let root = repo_root()?;
    let common = opts.common;
    ensure_timeout(&common)?;
    let ay_bin = ay_bin(&common)?;
    let input = load_inputs(&root, &common)?;
    let free_vars = grow_free_vars(
        input.formula.num_vars,
        &input.formula.clauses,
        &input.residual_ids,
        opts.radius,
    );
    let outside_vars: Vec<usize> = (0..input.formula.num_vars)
        .filter(|var| !free_vars.contains(var))
        .collect();
    let candidates = selected_candidates(
        &outside_vars,
        opts.candidate_vars.as_deref(),
        opts.candidate_limit,
        opts.radius,
    )?;
    let output = output_path(&root, &common, "outside-single-flip")?;
    if let Some(parent) = output.parent() {
        fs::create_dir_all(parent)?;
    }
    let (work_dir, cleanup) = prepare_work_dir(&root, &common, "outside-single-flip")?;

    let mut rows = Vec::new();
    let mut valid_model_candidate = None;
    let mut valid_model_path = None;
    for (idx, &candidate) in candidates.iter().enumerate() {
        let reduced_cnf = work_dir.join(format!(
            "outside-r{}-flip-var{}.cnf",
            opts.radius,
            candidate + 1
        ));
        let proof = reduced_cnf.with_extension("cnf.drat");
        let unit_count = write_flip_cnf(
            &reduced_cnf,
            &input.formula,
            &input.assignment,
            &free_vars,
            candidate,
        )?;
        let solve = run_solver(&ay_bin, &reduced_cnf, &proof, common.timeout_sec)?;
        let is_sat = solve.exit_code == Some(10) && solve.stdout.contains("s SATISFIABLE");
        let is_unsat = solve.exit_code == Some(20) && solve.stdout.contains("s UNSATISFIABLE");
        let proof_check = if is_unsat {
            Some(verify_drat(&reduced_cnf, &proof))
        } else {
            None
        };
        let unsat_verified = proof_check.as_ref().is_some_and(|result| {
            result.exit_code == Some(0) && result.stdout.contains("s VERIFIED")
        });
        let mut model_stats = None;
        let mut original_model_valid = false;
        let mut falsified_original: Option<Vec<usize>> = None;
        let mut preserved_other_outside = None;
        let mut candidate_flipped = None;
        if is_sat {
            let (model, stats) = parse_solver_model(&solve.stdout, input.formula.num_vars);
            model_stats = Some(stats);
            if let Some(model) = model {
                let falsified = falsified_clause_ids(&input.formula.clauses, &model);
                original_model_valid = falsified.is_empty();
                falsified_original = Some(falsified);
                let flipped = model[candidate] != input.assignment[candidate];
                let preserved = outside_vars
                    .iter()
                    .filter(|&&var| var != candidate)
                    .all(|&var| model[var] == input.assignment[var]);
                candidate_flipped = Some(flipped);
                preserved_other_outside = Some(preserved);
                if original_model_valid && flipped && preserved {
                    let model_path = output.with_file_name(format!(
                        "outside-radius{}-flip-var{}-model.txt",
                        opts.radius,
                        candidate + 1
                    ));
                    write_dimacs_model(&model_path, &model)?;
                    valid_model_candidate = Some(candidate);
                    valid_model_path = Some(model_path);
                }
            }
        }
        let status = if original_model_valid
            && candidate_flipped == Some(true)
            && preserved_other_outside == Some(true)
        {
            "sat_valid_model"
        } else if is_sat {
            "sat_invalid_or_incomplete_model"
        } else if is_unsat && unsat_verified {
            "unsat_verified"
        } else if is_unsat {
            "unsat_unverified"
        } else if solve.timed_out {
            "timeout"
        } else {
            "unknown_or_error"
        };
        println!(
            "candidate {}/{} var={} status={} solve_ms={}",
            idx + 1,
            candidates.len(),
            candidate + 1,
            status,
            solve.wall_time_ms
        );
        rows.push(json!({
            "candidate_index": idx + 1,
            "one_based_flipped_var": candidate + 1,
            "w210_value": input.assignment[candidate],
            "forced_value": !input.assignment[candidate],
            "free_radius_vars": free_vars.len(),
            "outside_radius_vars": outside_vars.len(),
            "unit_clauses": unit_count,
            "reduced_num_clauses": input.formula.clauses.len() + unit_count,
            "cnf_sha256": sha256_file(&reduced_cnf)?,
            "cnf_path": display_path_for_report(&reduced_cnf, &root),
            "proof_path": display_path_for_report(&proof, &root),
            "solve": solve.json(),
            "is_sat": is_sat,
            "is_unsat": is_unsat,
            "proof_check": proof_check.as_ref().map(CommandResult::json),
            "unsat_verified": unsat_verified,
            "model_stats": model_stats,
            "original_model_valid": original_model_valid,
            "candidate_flipped_in_model": candidate_flipped,
            "other_outside_w210_values_preserved": preserved_other_outside,
            "falsified_original_clause_count": falsified_original.as_ref().map(Vec::len),
            "first_falsified_original_zero_based": falsified_original.as_ref().map(|items| items.iter().take(16).copied().collect::<Vec<_>>()),
            "status": status,
        }));
        if !common.retain_work {
            let _ = fs::remove_file(&reduced_cnf);
            let _ = fs::remove_file(&proof);
        }
        if valid_model_candidate.is_some() {
            break;
        }
    }
    if cleanup {
        let _ = fs::remove_dir_all(&work_dir);
    }

    let counts = counts_for_rows(&rows, "candidate");
    let all_selected_checked = rows.len() == candidates.len();
    let all_selected_unsat_verified =
        all_selected_checked && counts.unsat_verified == candidates.len();
    let mut payload = base_payload(
        "ay.satcomp-circuit-repair-probe-outside-single-flip/v1",
        &root,
        &common,
        &input,
    )?;
    payload["probe_definition"] = json!({
        "radius": opts.radius,
        "radius_free_vars": free_vars.len(),
        "outside_radius_var_count": outside_vars.len(),
        "one_based_outside_radius_vars": outside_vars.iter().map(|var| var + 1).collect::<Vec<_>>(),
        "candidate_limit": opts.candidate_limit,
        "candidate_vars": opts.candidate_vars.as_ref().map(|_| candidates.iter().map(|var| var + 1).collect::<Vec<_>>()),
        "method": "For each selected outside-radius variable, force that one W210 value to flip, freeze every other outside-radius variable to its W210 value, leave the radius neighborhood free, solve original DIMACS plus those units, and validate any emitted complete model against the original DIMACS clauses.",
    });
    payload["candidates"] = json!(&rows);
    payload["counts"] = json!({
        "checked_candidates": rows.len(),
        "total_outside_radius_candidates": outside_vars.len(),
        "unsat_verified": counts.unsat_verified,
        "unsat_unverified": counts.unsat_unverified,
        "sat_valid_model": counts.sat_valid,
        "sat_invalid_or_incomplete_model": counts.sat_invalid,
        "timeout": counts.timeout,
        "unknown_or_error": counts.unknown_or_error,
    });
    payload["verdict"] = json!({
        "complete_original_dimacs_valid_model_found": valid_model_candidate.is_some(),
        "valid_model_one_based_flipped_var": valid_model_candidate.map(|var| var + 1),
        "valid_model_path": valid_model_path.as_ref().map(|path| display_path_for_report(path, &root)),
        "all_selected_single_flips_unsat_verified": all_selected_unsat_verified,
        "all_outside_radius_single_flips_checked": candidates.len() == outside_vars.len() && all_selected_checked,
        "route_admitted": false,
        "sat_output_authority": false,
        "model_output_authority": false,
        "proof_output_authority": false,
        "sat_comp_progress_claim": false,
        "blocker": if valid_model_candidate.is_none() {
            "No selected single outside-radius W210 flip produced a complete original-DIMACS-valid model."
        } else {
            "A selected single outside-radius W210 flip produced a complete assignment that validates against the original DIMACS, but this probe does not admit a solver route or make a SAT-COMP claim."
        },
    });
    write_json(&output, &payload)?;
    println!("{}", serde_json::to_string(&payload["verdict"])?);
    if valid_model_candidate.is_some() || all_selected_unsat_verified {
        Ok(())
    } else {
        bail!("outside-single-flip probe did not find a valid model or verify every selected UNSAT proof")
    }
}

fn run_component_window(opts: ComponentWindowOptions) -> Result<()> {
    let root = repo_root()?;
    let common = opts.common;
    ensure_timeout(&common)?;
    let ay_bin = ay_bin(&common)?;
    let mut input = load_inputs(&root, &common)?;
    let w210_assignment = input.assignment.clone();
    let w210_residual_ids = input.residual_ids.clone();
    let seed_set_values = apply_assignment_sets(
        &root,
        input.formula.num_vars,
        &mut input.assignment,
        &opts.seed_set_files,
    )?;
    input.residual_ids = residual_clause_ids(&input.formula.clauses, &input.assignment);
    let seed_delta = assignment_delta_from_base(&w210_assignment, &input.assignment);
    let radius_free_vars = grow_free_vars(
        input.formula.num_vars,
        &input.formula.clauses,
        &input.residual_ids,
        opts.radius,
    );
    let outside_vars: Vec<usize> = (0..input.formula.num_vars)
        .filter(|var| !radius_free_vars.contains(var))
        .collect();
    let outside_set: BTreeSet<usize> = outside_vars.iter().copied().collect();
    let window_selection = selected_windows(
        &opts.windows,
        opts.window_limit,
        opts.auto_low_free_windows,
        opts.auto_window_max_size,
        opts.auto_component_hitting_windows,
        opts.auto_component_family_windows,
        &resolve_path(&root, &opts.component_hook_targets),
        &outside_vars,
    )?;
    let window_source = window_selection.source;
    let auto_low_free_candidate_windows = window_selection.auto_low_free_candidate_windows;
    let auto_component_hitting_candidate_windows =
        window_selection.auto_component_hitting_candidate_windows;
    let component_hook_targets = window_selection.component_hook_targets.clone();
    let component_hitting_windows = window_selection.component_hitting_windows.clone();
    let auto_component_family_candidate_windows =
        window_selection.auto_component_family_candidate_windows;
    let component_family_windows = window_selection.component_family_windows.clone();
    let windows = window_selection.windows;
    let output = output_path(&root, &common, "component-window")?;
    if let Some(parent) = output.parent() {
        fs::create_dir_all(parent)?;
    }
    let (work_dir, cleanup) = prepare_work_dir(&root, &common, "component-window")?;
    let version = run_version(&ay_bin)?;

    let mut rows = Vec::new();
    for (idx, window) in windows.iter().enumerate() {
        let window_vars: BTreeSet<usize> =
            window.one_based_vars.iter().map(|var| var - 1).collect();
        let out_of_range: Vec<usize> = window_vars
            .iter()
            .filter(|&&var| var >= input.formula.num_vars)
            .map(|var| var + 1)
            .collect();
        if !out_of_range.is_empty() {
            bail!(
                "window {} contains variables outside the formula variable range: {:?}",
                window.name,
                out_of_range
            );
        }
        let already_radius_free = window_vars
            .iter()
            .filter(|var| radius_free_vars.contains(var))
            .count();
        let extra_outside_window_vars = window_vars
            .iter()
            .filter(|var| outside_set.contains(var))
            .count();
        let free_total_vars = radius_free_vars.union(&window_vars).count();
        let reduced_cnf = work_dir.join(format!("window-{:02}-{}.cnf", idx + 1, window.name));
        let proof = reduced_cnf.with_extension("cnf.drat");
        let (frozen_count, frozen_vars) = write_reduced_cnf(
            &reduced_cnf,
            &input.formula,
            &input.assignment,
            &radius_free_vars,
            &window_vars,
        )?;
        let solve = run_solver(&ay_bin, &reduced_cnf, &proof, common.timeout_sec)?;
        let is_sat = solve.exit_code == Some(10) && solve.stdout.contains("s SATISFIABLE");
        let is_unsat = solve.exit_code == Some(20) && solve.stdout.contains("s UNSATISFIABLE");
        let proof_check = if is_unsat {
            Some(verify_drat(&reduced_cnf, &proof))
        } else {
            None
        };
        let unsat_verified = proof_check.as_ref().is_some_and(|result| {
            result.exit_code == Some(0) && result.stdout.contains("s VERIFIED")
        });
        let mut model_stats = None;
        let mut original_model_valid = false;
        let mut falsified_original: Option<Vec<usize>> = None;
        let mut frozen_preserved = None;
        let mut changed_window_values = None;
        let mut model_path = None;
        let mut model_sha = None;
        if is_sat {
            let (model, stats) = parse_solver_model(&solve.stdout, input.formula.num_vars);
            model_stats = Some(stats);
            if let Some(model) = model {
                let falsified = falsified_clause_ids(&input.formula.clauses, &model);
                original_model_valid = falsified.is_empty();
                falsified_original = Some(falsified);
                let preserved = frozen_vars
                    .iter()
                    .all(|&var| model[var] == input.assignment[var]);
                frozen_preserved = Some(preserved);
                let changed: Vec<usize> = window_vars
                    .iter()
                    .copied()
                    .filter(|&var| model[var] != input.assignment[var])
                    .map(|var| var + 1)
                    .collect();
                changed_window_values = Some(changed);
                if original_model_valid && preserved {
                    let path = output.with_file_name(format!(
                        "window-{:02}-{}-model.txt",
                        idx + 1,
                        window.name
                    ));
                    write_dimacs_model(&path, &model)?;
                    model_sha = Some(sha256_file(&path)?);
                    model_path = Some(path);
                }
            }
        }
        let status = if original_model_valid && frozen_preserved == Some(true) {
            "sat_valid_original_model"
        } else if is_sat {
            "sat_invalid_or_incomplete_model"
        } else if is_unsat && unsat_verified {
            "unsat_verified"
        } else if is_unsat {
            "unsat_unverified"
        } else if solve.timed_out {
            "timeout"
        } else {
            "unknown_or_error"
        };
        println!(
            "window {}/{} {} status={} solve_ms={}",
            idx + 1,
            windows.len(),
            window.name,
            status,
            solve.wall_time_ms
        );
        rows.push(json!({
            "window_index": idx + 1,
            "window_name": window.name,
            "one_based_window_vars": window.one_based_vars,
            "window_var_count": window_vars.len(),
            "window_vars_already_radius_free": already_radius_free,
            "extra_outside_window_vars": extra_outside_window_vars,
            "free_radius_vars": radius_free_vars.len(),
            "free_total_vars": free_total_vars,
            "outside_radius_vars": outside_vars.len(),
            "frozen_outside_vars": frozen_count,
            "frozen_outside_one_based_vars": frozen_vars.iter().map(|var| var + 1).collect::<Vec<_>>(),
            "unit_clauses": frozen_count,
            "reduced_num_clauses": input.formula.clauses.len() + frozen_count,
            "cnf_sha256": sha256_file(&reduced_cnf)?,
            "cnf_path": display_path_for_report(&reduced_cnf, &root),
            "cnf_retained": common.retain_work,
            "proof_path": display_path_for_report(&proof, &root),
            "proof_retained": common.retain_work && proof.exists(),
            "solve": solve.json(),
            "is_sat": is_sat,
            "is_unsat": is_unsat,
            "proof_check": proof_check.as_ref().map(CommandResult::json),
            "unsat_verified": unsat_verified,
            "model_stats": model_stats,
            "original_model_valid": original_model_valid,
            "frozen_outside_values_preserved": frozen_preserved,
            "window_values_changed_from_seed_assignment": changed_window_values,
            "falsified_original_clause_count": falsified_original.as_ref().map(Vec::len),
            "first_falsified_original_zero_based": falsified_original.as_ref().map(|items| items.iter().take(16).copied().collect::<Vec<_>>()),
            "valid_model_path": model_path.as_ref().map(|path| display_path_for_report(path, &root)),
            "valid_model_sha256": model_sha,
            "status": status,
        }));
        if !common.retain_work {
            let _ = fs::remove_file(&reduced_cnf);
            let _ = fs::remove_file(&proof);
        }
    }
    if cleanup {
        let _ = fs::remove_dir_all(&work_dir);
    }

    let counts = counts_for_rows(&rows, "window");
    let all_windows_checked = rows.len() == windows.len();
    let all_unsat_verified = all_windows_checked && counts.unsat_verified == windows.len();
    let any_valid_model = counts.sat_valid > 0;
    let mut payload = base_payload(
        "ay.satcomp-circuit-repair-probe-component-window/v1",
        &root,
        &common,
        &input,
    )?;
    payload["solver"]["ay_bin_sha256"] = json!(sha256_file(&ay_bin)?);
    payload["solver"]["version"] = version.json();
    payload["assignment_overlay"] = json!({
        "enabled": !opts.seed_set_files.is_empty(),
        "seed_set_files": opts.seed_set_files.iter().map(|path| display_path_for_report(&resolve_path(&root, path), &root)).collect::<Vec<_>>(),
        "one_based_set_values": seed_set_values.iter().map(|(var, value)| json!({"var": var + 1, "value": value})).collect::<Vec<_>>(),
        "set_var_count": seed_set_values.len(),
        "changed_from_w210_var_count": seed_delta.len(),
        "one_based_changed_from_w210_vars": seed_delta.iter().map(|(var, value)| json!({"var": var + 1, "value": value})).collect::<Vec<_>>(),
        "w210_residual_falsified_clause_count": w210_residual_ids.len(),
        "w210_residual_falsified_one_based_clause_ids": w210_residual_ids.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
        "seed_residual_falsified_clause_count": input.residual_ids.len(),
        "seed_residual_falsified_one_based_clause_ids": input.residual_ids.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
        "authority": "diagnostic_only",
    });
    payload["probe_definition"] = json!({
        "radius": opts.radius,
        "radius_free_vars": radius_free_vars.len(),
        "outside_radius_var_count": outside_vars.len(),
        "one_based_outside_radius_vars": outside_vars.iter().map(|var| var + 1).collect::<Vec<_>>(),
        "window_source": window_source,
        "auto_low_free_windows": opts.auto_low_free_windows,
        "auto_window_max_size": opts.auto_window_max_size,
        "auto_component_hitting_windows": opts.auto_component_hitting_windows,
        "auto_component_family_windows": opts.auto_component_family_windows,
        "component_hook_targets": component_hook_targets.as_ref().map(|path| artifact_json(path, &root)).transpose()?,
        "component_hitting_windows": component_hitting_windows.iter().map(component_hitting_window_json).collect::<Vec<_>>(),
        "component_family_windows": component_family_windows.iter().map(component_family_window_json).collect::<Vec<_>>(),
        "window_limit": opts.window_limit,
        "windows": windows.iter().map(|window| json!({"name": window.name, "one_based_vars": window.one_based_vars})).collect::<Vec<_>>(),
        "method": "Apply optional seed set-files to W210, recompute residual radius variables from the seed assignment, keep every radius variable free. For each selected window, also keep the window variables free when they are not already radius-free and freeze every other outside-radius variable to its seed assignment value. Solve original DIMACS plus those units; validate any SAT model against the original DIMACS clauses.",
    });
    payload["windows"] = json!(&rows);
    payload["counts"] = json!({
        "checked_windows": rows.len(),
        "selected_windows": windows.len(),
        "auto_low_free_candidate_windows": auto_low_free_candidate_windows,
        "auto_low_free_selected_windows": auto_low_free_candidate_windows.map(|_| windows.len()),
        "auto_low_free_pruned_by_window_limit": auto_low_free_candidate_windows.map(|count| count.saturating_sub(windows.len())),
        "auto_component_hitting_candidate_windows": auto_component_hitting_candidate_windows,
        "auto_component_hitting_selected_windows": auto_component_hitting_candidate_windows.map(|_| windows.len()),
        "auto_component_hitting_pruned_by_window_limit": auto_component_hitting_candidate_windows.map(|count| count.saturating_sub(windows.len())),
        "auto_component_family_candidate_windows": auto_component_family_candidate_windows,
        "auto_component_family_selected_windows": auto_component_family_candidate_windows.map(|_| windows.len()),
        "auto_component_family_pruned_by_window_limit": auto_component_family_candidate_windows.map(|count| count.saturating_sub(windows.len())),
        "unsat_verified": counts.unsat_verified,
        "unsat_unverified": counts.unsat_unverified,
        "sat_valid_original_model": counts.sat_valid,
        "sat_invalid_or_incomplete_model": counts.sat_invalid,
        "timeout": counts.timeout,
        "unknown_or_error": counts.unknown_or_error,
    });
    payload["verdict"] = json!({
        "all_selected_windows_checked": all_windows_checked,
        "all_selected_windows_unsat_verified": all_unsat_verified,
        "complete_original_dimacs_valid_model_found": any_valid_model,
        "valid_model_windows": rows.iter().filter(|row| row["status"] == "sat_valid_original_model").map(|row| row["window_name"].clone()).collect::<Vec<_>>(),
        "route_admitted": false,
        "sat_output_authority": false,
        "model_output_authority": false,
        "proof_output_authority": false,
        "solver_verdict_authority": false,
        "sat_comp_progress_claim": false,
        "blocker": if any_valid_model {
            "At least one selected component window produced a complete original-DIMACS-valid model, but this probe does not admit a solver route or make a SAT-COMP claim."
        } else {
            "No selected component window produced a complete original-DIMACS-valid model."
        },
    });
    write_json(&output, &payload)?;
    println!("{}", serde_json::to_string(&payload["verdict"])?);
    if any_valid_model || all_unsat_verified {
        Ok(())
    } else {
        bail!("component-window probe did not find a valid model or verify every selected UNSAT proof")
    }
}

struct LoadedInputs {
    target_cnf: PathBuf,
    ledgers: Vec<PathBuf>,
    formula: RawFormula,
    assignment: Vec<bool>,
    ledger_stats: JsonValue,
    residual_ids: Vec<usize>,
}

#[derive(Clone, Debug)]
struct NeighborhoodRow {
    radius: usize,
    free_vars: BTreeSet<usize>,
    touched_clauses: usize,
    delta_vars: usize,
}

#[derive(Clone, Debug, Default)]
struct RowCounts {
    unsat_verified: usize,
    unsat_unverified: usize,
    sat_valid: usize,
    sat_invalid: usize,
    timeout: usize,
    unknown_or_error: usize,
}

fn load_inputs(root: &Path, common: &CommonOptions) -> Result<LoadedInputs> {
    let target_cnf = resolve_path(root, &common.target_cnf);
    let ledgers = ledger_paths(root, common);
    let formula = parse_dimacs_path(&target_cnf)?;
    let (assignment, ledger_stats) = parse_w210_assignment(formula.num_vars, &ledgers)?;
    let residual_ids = residual_clause_ids(&formula.clauses, &assignment);
    Ok(LoadedInputs {
        target_cnf,
        ledgers,
        formula,
        assignment,
        ledger_stats,
        residual_ids,
    })
}

fn base_payload(
    schema: &str,
    root: &Path,
    common: &CommonOptions,
    input: &LoadedInputs,
) -> Result<JsonValue> {
    Ok(json!({
        "schema": schema,
        "issue": 9424,
        "scoreboard_row": "Circuit_multiplier22",
        "source": diagnostic_source_json(
            git_head(root),
            "Diagnostic-only Rust SAT-COMP submission/preflight CLI probe. No route, SAT stdout, model, proof, solved-count, PAR-2, or SAT-COMP authority is granted.",
        ),
        "input": {
            "path": display_path_for_report(&input.target_cnf, root),
            "sha256": sha256_file(&input.target_cnf)?,
            "num_vars": input.formula.num_vars,
            "num_clauses": input.formula.clauses.len(),
        },
        "w210_ledgers": {
            "paths": input.ledgers.iter().map(|path| display_path_for_report(path, root)).collect::<Vec<_>>(),
            "rows_seen": input.ledger_stats["rows_seen"],
            "rows_accepted": input.ledger_stats["rows_accepted"],
            "duplicate_same_value_rows": input.ledger_stats["duplicate_same_value_rows"],
            "conflicting_rows": input.ledger_stats["conflicting_rows"],
            "covered_vars": input.formula.num_vars,
        },
        "baseline_residual": {
            "zero_based_clause_ids": input.residual_ids,
            "one_based_clause_ids": input.residual_ids.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
            "count": input.residual_ids.len(),
        },
        "solver": {
            "ay_bin": ay_bin(common).map(|path| display_path_for_report(&path, root)).unwrap_or_else(|_| String::new()),
            "timeout_seconds": common.timeout_sec,
        },
    }))
}

fn parse_dimacs_path(path: &Path) -> Result<RawFormula> {
    let bytes = read_maybe_compressed(path)?;
    let mut header = None;
    let mut clauses = Vec::new();
    let parsed_header = parse_dimacs_events(Cursor::new(bytes), |event| {
        match event {
            DimacsEvent::Header(value) => header = Some(value),
            DimacsEvent::Record(DimacsRecordRef::Clause(lits)) => clauses.push(lits.to_vec()),
            DimacsEvent::Record(DimacsRecordRef::Tagged { tag, .. }) => {
                return Err(ay_sat::dimacs_core::DimacsCoreError::InvalidLiteral {
                    token: format!("unexpected tagged line '{tag}' in CNF input"),
                    line_number: 0,
                });
            }
            _ => {}
        }
        Ok(())
    })?;
    let header = header.unwrap_or(parsed_header);
    if clauses.len() != header.num_clauses {
        bail!(
            "clause count drift in {}: parsed={} expected={}",
            path.display(),
            clauses.len(),
            header.num_clauses
        );
    }
    Ok(RawFormula {
        num_vars: header.num_vars,
        clauses,
    })
}

fn read_tsv_table(path: &Path) -> Result<TsvTable> {
    let text = fs::read_to_string(path)
        .with_context(|| format!("failed to read TSV '{}'", path.display()))?;
    let mut lines = text.lines();
    let header_line = lines
        .next()
        .with_context(|| format!("empty TSV '{}'", path.display()))?;
    let header: Vec<String> = header_line.split('\t').map(str::to_string).collect();
    let mut rows = Vec::new();
    for line in lines.filter(|line| !line.trim().is_empty()) {
        let cells: Vec<&str> = line.split('\t').collect();
        let mut row = BTreeMap::new();
        for (idx, name) in header.iter().enumerate() {
            row.insert(
                name.clone(),
                cells.get(idx).copied().unwrap_or_default().to_string(),
            );
        }
        rows.push(row);
    }
    Ok(TsvTable {
        path: path.to_path_buf(),
        header,
        rows,
    })
}

fn parse_source_frame_rows(
    table: &TsvTable,
    allow_missing_source_value: bool,
) -> Result<SourceFrameParsedRows> {
    for column in [
        "source_frame_row_id",
        "clause_id",
        "literal_index",
        "lit",
        "var",
        "source_family",
        "source_value",
        "required_value_to_satisfy_literal",
    ] {
        if !table.header.iter().any(|name| name == column) {
            bail!("{} missing required column {column}", table.path.display());
        }
    }
    let mut parsed = SourceFrameParsedRows::default();
    for (idx, row) in table.rows.iter().enumerate() {
        match parse_source_frame_row(table, idx + 2, row, allow_missing_source_value) {
            Ok(row) => parsed.rows.push(row),
            Err(error) => {
                parsed.parse_errors += 1;
                if parsed.parse_error_samples.len() < 8 {
                    parsed.parse_error_samples.push(format!("{error:#}"));
                }
            }
        }
    }
    Ok(parsed)
}

fn parse_source_frame_row(
    table: &TsvTable,
    line_number: usize,
    row: &BTreeMap<String, String>,
    allow_missing_source_value: bool,
) -> Result<SourceFrameRow> {
    let source_value =
        optional_bool_cell(source_frame_cell(table, line_number, row, "source_value")?)?;
    if source_value.is_none() && !allow_missing_source_value {
        bail!(
            "{}:{line_number} source_value must be Boolean for materialized source rows",
            table.path.display()
        );
    }
    Ok(SourceFrameRow {
        source_frame_row_id: source_frame_cell(table, line_number, row, "source_frame_row_id")?
            .to_string(),
        clause_id_one_based: parse_source_frame_usize(table, line_number, row, "clause_id")?,
        literal_index_one_based: parse_source_frame_usize(
            table,
            line_number,
            row,
            "literal_index",
        )?,
        lit: parse_source_frame_i32(table, line_number, row, "lit")?,
        var_one_based: parse_source_frame_usize(table, line_number, row, "var")?,
        source_family: source_frame_cell(table, line_number, row, "source_family")?.to_string(),
        source_value,
        required_value_to_satisfy_literal: parse_bool_cell(source_frame_cell(
            table,
            line_number,
            row,
            "required_value_to_satisfy_literal",
        )?)?,
    })
}

fn source_frame_cell<'a>(
    table: &TsvTable,
    line_number: usize,
    row: &'a BTreeMap<String, String>,
    column: &str,
) -> Result<&'a str> {
    row.get(column)
        .map(String::as_str)
        .with_context(|| format!("{}:{line_number} missing {column}", table.path.display()))
}

fn parse_source_frame_usize(
    table: &TsvTable,
    line_number: usize,
    row: &BTreeMap<String, String>,
    column: &str,
) -> Result<usize> {
    let value = source_frame_cell(table, line_number, row, column)?;
    value.parse::<usize>().with_context(|| {
        format!(
            "{}:{line_number} invalid {column} value '{}'",
            table.path.display(),
            value
        )
    })
}

fn parse_source_frame_i32(
    table: &TsvTable,
    line_number: usize,
    row: &BTreeMap<String, String>,
    column: &str,
) -> Result<i32> {
    let value = source_frame_cell(table, line_number, row, column)?;
    value.parse::<i32>().with_context(|| {
        format!(
            "{}:{line_number} invalid {column} value '{}'",
            table.path.display(),
            value
        )
    })
}

fn optional_bool_cell(raw: &str) -> Result<Option<bool>> {
    let value = raw.trim();
    if value.is_empty() || value == "." {
        Ok(None)
    } else {
        parse_bool_cell(value).map(Some)
    }
}

fn source_frame_row_has_valid_binding(formula: &RawFormula, row: &SourceFrameRow) -> bool {
    if !ALLOWED_SOURCE_FRAME_FAMILIES.contains(&row.source_family.as_str()) {
        return false;
    }
    if row.var_one_based == 0 || row.var_one_based > formula.num_vars {
        return false;
    }
    if lit_var(row.lit) != row.var_one_based {
        return false;
    }
    if row.clause_id_one_based == 0 || row.clause_id_one_based > formula.clauses.len() {
        return false;
    }
    let clause = &formula.clauses[row.clause_id_one_based - 1];
    if row.literal_index_one_based == 0 || row.literal_index_one_based > clause.len() {
        return false;
    }
    if clause[row.literal_index_one_based - 1] != row.lit || !clause.contains(&row.lit) {
        return false;
    }
    row.required_value_to_satisfy_literal == (row.lit > 0)
}

fn artifact_json(path: &Path, root: &Path) -> Result<JsonValue> {
    Ok(json!({
        "path": display_path_for_report(path, root),
        "sha256": sha256_file(path)?,
    }))
}

fn read_maybe_compressed(path: &Path) -> Result<Vec<u8>> {
    let tool = match path.extension().and_then(|ext| ext.to_str()) {
        Some("xz") => Some("xz"),
        Some("gz") => Some("gzip"),
        Some("bz2") => Some("bzip2"),
        _ => None,
    };
    if let Some(tool) = tool {
        let output = Command::new(tool)
            .arg("-dc")
            .arg(path)
            .output()
            .with_context(|| format!("failed to run {tool} for '{}'", path.display()))?;
        if !output.status.success() {
            bail!(
                "{tool} -dc failed for '{}': {}",
                path.display(),
                String::from_utf8_lossy(&output.stderr)
            );
        }
        Ok(output.stdout)
    } else {
        fs::read(path).with_context(|| format!("failed to read '{}'", path.display()))
    }
}

fn parse_w210_assignment(num_vars: usize, ledgers: &[PathBuf]) -> Result<(Vec<bool>, JsonValue)> {
    let mut assignment = vec![None; num_vars];
    let mut rows_seen = 0usize;
    let mut rows_accepted = 0usize;
    let mut duplicate_same = 0usize;
    let mut conflicts = 0usize;
    for path in ledgers {
        let text = fs::read_to_string(path)
            .with_context(|| format!("failed to read W210 ledger '{}'", path.display()))?;
        let mut lines = text.lines();
        let header = lines
            .next()
            .with_context(|| format!("empty W210 ledger '{}'", path.display()))?;
        let columns: Vec<&str> = header.split('\t').collect();
        let var_col = columns
            .iter()
            .position(|name| *name == "original_var")
            .with_context(|| format!("{} missing original_var column", path.display()))?;
        let value_col = columns
            .iter()
            .position(|name| *name == "value")
            .with_context(|| format!("{} missing value column", path.display()))?;
        for (line_idx, line) in lines.enumerate() {
            if line.trim().is_empty() {
                continue;
            }
            rows_seen += 1;
            let cells: Vec<&str> = line.split('\t').collect();
            let var_cell = cells.get(var_col).with_context(|| {
                format!("{}:{} missing original_var", path.display(), line_idx + 2)
            })?;
            let value_cell = cells
                .get(value_col)
                .with_context(|| format!("{}:{} missing value", path.display(), line_idx + 2))?;
            let var = var_cell.parse::<usize>().with_context(|| {
                format!("{}:{} invalid original_var", path.display(), line_idx + 2)
            })?;
            if var == 0 || var > num_vars {
                bail!(
                    "{}:{} original_var out of range: {}",
                    path.display(),
                    line_idx + 2,
                    var
                );
            }
            let value = parse_bool_cell(value_cell)?;
            let slot = &mut assignment[var - 1];
            match slot {
                None => {
                    *slot = Some(value);
                    rows_accepted += 1;
                }
                Some(existing) if *existing == value => duplicate_same += 1,
                Some(_) => conflicts += 1,
            }
        }
    }
    let missing = assignment.iter().position(Option::is_none);
    if let Some(idx) = missing {
        bail!("W210 assignment missing variable {}", idx + 1);
    }
    Ok((
        assignment.into_iter().map(Option::unwrap).collect(),
        json!({
            "rows_seen": rows_seen,
            "rows_accepted": rows_accepted,
            "duplicate_same_value_rows": duplicate_same,
            "conflicting_rows": conflicts,
        }),
    ))
}

fn parse_dimacs_model_path(path: &Path, num_vars: usize) -> Result<(Vec<bool>, JsonValue)> {
    let text = fs::read_to_string(path)
        .with_context(|| format!("failed to read DIMACS model '{}'", path.display()))?;
    let (assignment, stats) = parse_solver_model(&text, num_vars);
    let Some(assignment) = assignment else {
        bail!(
            "DIMACS model '{}' is incomplete or invalid: {stats}",
            path.display()
        );
    };
    Ok((assignment, stats))
}

fn apply_assignment_flips(
    root: &Path,
    num_vars: usize,
    assignment: &mut [bool],
    raw_flips: &[String],
    flip_files: &[PathBuf],
) -> Result<Vec<usize>> {
    let mut flips = BTreeSet::new();
    for raw in raw_flips {
        for one_based in parse_var_selector(raw)? {
            insert_one_based_flip(num_vars, &mut flips, one_based)?;
        }
    }
    for path in flip_files {
        let path = resolve_path(root, path);
        for one_based in parse_flip_file(&path)? {
            insert_one_based_flip(num_vars, &mut flips, one_based)?;
        }
    }
    for &var in &flips {
        assignment[var] = !assignment[var];
    }
    Ok(flips.into_iter().collect())
}

fn apply_assignment_sets(
    root: &Path,
    num_vars: usize,
    assignment: &mut [bool],
    set_files: &[PathBuf],
) -> Result<Vec<(usize, bool)>> {
    let mut values = BTreeMap::new();
    for path in set_files {
        let path = resolve_path(root, path);
        for (one_based, value) in parse_set_file(&path)? {
            if one_based == 0 || one_based > num_vars {
                bail!("set variable out of range: {one_based}");
            }
            let var = one_based - 1;
            match values.get(&var).copied() {
                None => {
                    values.insert(var, value);
                }
                Some(existing) if existing == value => {}
                Some(existing) => {
                    bail!("conflicting set values for variable {one_based}: {existing} vs {value}");
                }
            }
        }
    }
    for (&var, &value) in &values {
        assignment[var] = value;
    }
    Ok(values.into_iter().collect())
}

fn local_search_candidates(
    root: &Path,
    num_vars: usize,
    clauses: &[Vec<i32>],
    residual_ids: &[usize],
    opts: &AssignmentLocalSearchOptions,
) -> Result<Vec<usize>> {
    let mut candidates = BTreeSet::new();
    if let Some(raw) = &opts.candidate_vars {
        for one_based in parse_var_selector(raw)? {
            insert_one_based_candidate(num_vars, &mut candidates, one_based)?;
        }
    }
    for path in &opts.candidate_files {
        let path = resolve_path(root, path);
        for one_based in parse_flip_file(&path)? {
            insert_one_based_candidate(num_vars, &mut candidates, one_based)?;
        }
    }
    if candidates.is_empty() && opts.residual_candidates {
        for &clause_idx in residual_ids {
            if let Some(clause) = clauses.get(clause_idx) {
                for &lit in clause {
                    candidates.insert(lit_var(lit) - 1);
                }
            }
        }
    }
    if candidates.is_empty() {
        candidates.extend(0..num_vars);
    }
    let mut candidates: Vec<_> = candidates.into_iter().collect();
    if let Some(limit) = opts.candidate_limit {
        candidates.truncate(limit);
    }
    if candidates.is_empty() {
        bail!("assignment-local-search candidate set is empty");
    }
    Ok(candidates)
}

fn pair_search_candidates(
    candidates: &[usize],
    limit: Option<usize>,
    enabled: bool,
) -> Result<Vec<usize>> {
    let mut pair_candidates = candidates.to_vec();
    if let Some(limit) = limit {
        pair_candidates.truncate(limit);
    }
    if enabled && limit.is_none() && pair_candidates.len() > 256 {
        bail!(
            "pair search over {} candidates is too broad; use --residual-candidates or --pair-candidate-limit",
            pair_candidates.len()
        );
    }
    Ok(pair_candidates)
}

#[derive(Default)]
struct GroupTemplates {
    groups: Vec<Vec<usize>>,
    truncated: bool,
}

struct GroupTrialScore {
    residual_count: usize,
    affected_clause_count: usize,
}

struct AssignmentResidualScorer<'a> {
    clauses: &'a [Vec<i32>],
    occurrences: Vec<Vec<usize>>,
    marks: Vec<u32>,
    epoch: u32,
}

impl<'a> AssignmentResidualScorer<'a> {
    fn new(num_vars: usize, clauses: &'a [Vec<i32>]) -> Self {
        let mut occurrences = vec![Vec::new(); num_vars];
        for (clause_idx, clause) in clauses.iter().enumerate() {
            for &lit in clause {
                let var = lit_var(lit) - 1;
                if let Some(var_occurrences) = occurrences.get_mut(var) {
                    var_occurrences.push(clause_idx);
                }
            }
        }
        Self {
            clauses,
            occurrences,
            marks: vec![0; clauses.len()],
            epoch: 0,
        }
    }

    fn flip_group_residual_count(
        &mut self,
        assignment: &[bool],
        group: &[usize],
        current_residual_flags: &[bool],
        current_residual_count: usize,
    ) -> GroupTrialScore {
        self.next_epoch();
        let mut affected = Vec::new();
        for &var in group {
            if let Some(clause_ids) = self.occurrences.get(var) {
                for &clause_idx in clause_ids {
                    if self.marks[clause_idx] != self.epoch {
                        self.marks[clause_idx] = self.epoch;
                        affected.push(clause_idx);
                    }
                }
            }
        }

        let mut residual_count = current_residual_count;
        for &clause_idx in &affected {
            let was_residual = current_residual_flags[clause_idx];
            let now_residual =
                clause_residual_after_group_flip(&self.clauses[clause_idx], assignment, group);
            match (was_residual, now_residual) {
                (true, false) => residual_count -= 1,
                (false, true) => residual_count += 1,
                _ => {}
            }
        }

        GroupTrialScore {
            residual_count,
            affected_clause_count: affected.len(),
        }
    }

    fn next_epoch(&mut self) {
        if self.epoch == u32::MAX {
            self.marks.fill(0);
            self.epoch = 0;
        }
        self.epoch += 1;
    }
}

fn group_search_candidates(
    candidates: &[usize],
    limit: Option<usize>,
    enabled: bool,
) -> Result<Vec<usize>> {
    let mut group_candidates = candidates.to_vec();
    if let Some(limit) = limit {
        group_candidates.truncate(limit);
    }
    if enabled && limit.is_none() && group_candidates.len() > 256 {
        bail!(
            "group search over {} candidates is too broad; use --residual-candidates or --group-candidate-limit",
            group_candidates.len()
        );
    }
    Ok(group_candidates)
}

fn component_family_group_selection(
    root: &Path,
    num_vars: usize,
    opts: &AssignmentLocalSearchOptions,
) -> Result<ComponentFamilyGroupSelection> {
    if opts.component_family_rounds == 0 {
        return Ok(ComponentFamilyGroupSelection::default());
    }
    let Some(limit) = opts.component_family_group_limit else {
        bail!("assignment-local-search --component-family-rounds requires --component-family-group-limit");
    };
    let component_hook_targets = resolve_path(root, &opts.component_hook_targets);
    let table = read_tsv_table(&component_hook_targets)?;
    let components = parse_component_hitting_windows(&table)?;
    let mut candidates = component_family_windows(&components)?;
    candidates.sort_by(component_family_order);
    let candidate_count = candidates.len();
    let windows: Vec<ComponentFamilyWindow> = candidates.into_iter().take(limit).collect();
    let mut groups = Vec::new();
    for window in &windows {
        let mut group = Vec::new();
        for &one_based in &window.one_based_vars {
            if one_based == 0 || one_based > num_vars {
                bail!("component-family group variable out of range: {one_based}");
            }
            group.push(one_based - 1);
        }
        groups.push(group);
    }
    Ok(ComponentFamilyGroupSelection {
        groups,
        windows,
        candidate_count: Some(candidate_count),
        component_hook_targets: Some(component_hook_targets),
    })
}

fn source_frame_value_selection(
    root: &Path,
    formula: &RawFormula,
    opts: &AssignmentLocalSearchOptions,
) -> Result<SourceFrameValueSelection> {
    if opts.source_frame_value_rounds == 0 {
        return Ok(SourceFrameValueSelection::default());
    }
    let Some(limit) = opts.source_frame_value_limit else {
        bail!("assignment-local-search --source-frame-value-rounds requires --source-frame-value-limit");
    };
    let component_hook_targets = resolve_path(root, &opts.component_hook_targets);
    let source_frame_rows = resolve_path(root, &opts.source_frame_rows);
    let component_table = read_tsv_table(&component_hook_targets)?;
    let source_frame_table = read_tsv_table(&source_frame_rows)?;
    let components = parse_component_hitting_windows(&component_table)?;
    let mut candidates = component_family_windows(&components)?;
    candidates.sort_by(component_family_order);
    let candidate_count = candidates.len();
    let selected_windows: Vec<ComponentFamilyWindow> = candidates.into_iter().take(limit).collect();
    let source_rows = parse_source_frame_rows(&source_frame_table, false)?;
    let overlays = selected_windows
        .into_iter()
        .map(|window| source_frame_value_overlay_from_window(formula, window, &source_rows.rows))
        .collect();
    Ok(SourceFrameValueSelection {
        overlays,
        candidate_count: Some(candidate_count),
        component_hook_targets: Some(component_hook_targets),
        source_frame_rows: Some(source_frame_rows),
        source_frame_parse_errors: source_rows.parse_errors,
        source_frame_parse_error_samples: source_rows.parse_error_samples,
    })
}

fn source_frame_value_overlay_from_window(
    formula: &RawFormula,
    window: ComponentFamilyWindow,
    source_rows: &[SourceFrameRow],
) -> SourceFrameValueOverlay {
    let clause_ids: BTreeSet<usize> = window.one_based_clause_ids.iter().copied().collect();
    let mut required_values = BTreeMap::new();
    let mut conflicting_vars = BTreeSet::new();
    let mut source_rows_seen = 0usize;
    let mut valid_binding_rows = 0usize;
    let mut invalid_binding_rows = 0usize;
    let mut duplicate_same_required_values = 0usize;
    let mut conflicting_required_values = 0usize;
    let mut source_frame_row_id_samples = Vec::new();
    for row in source_rows {
        if !clause_ids.contains(&row.clause_id_one_based) {
            continue;
        }
        source_rows_seen += 1;
        if source_frame_row_id_samples.len() < 16 {
            source_frame_row_id_samples.push(row.source_frame_row_id.clone());
        }
        if !source_frame_row_has_valid_binding(formula, row) {
            invalid_binding_rows += 1;
            continue;
        }
        valid_binding_rows += 1;
        let var = row.var_one_based - 1;
        let required_value = row.required_value_to_satisfy_literal;
        match required_values.get(&var) {
            None => {
                required_values.insert(var, required_value);
            }
            Some(existing) if *existing == required_value => {
                duplicate_same_required_values += 1;
            }
            Some(_) => {
                conflicting_required_values += 1;
                conflicting_vars.insert(var);
            }
        }
    }
    let assignments = required_values
        .into_iter()
        .filter(|(var, _)| !conflicting_vars.contains(var))
        .collect();
    SourceFrameValueOverlay {
        window,
        assignments,
        source_rows_seen,
        valid_binding_rows,
        invalid_binding_rows,
        duplicate_same_required_values,
        conflicting_required_values,
        conflicting_one_based_vars: conflicting_vars.into_iter().map(|var| var + 1).collect(),
        source_frame_row_id_samples,
    }
}

fn assignment_after_required_value_overlay(
    assignment: &[bool],
    overlay: &SourceFrameValueOverlay,
) -> Vec<bool> {
    let mut trial = assignment.to_vec();
    apply_required_value_overlay(&mut trial, overlay);
    trial
}

fn apply_required_value_overlay(assignment: &mut [bool], overlay: &SourceFrameValueOverlay) {
    for &(var, value) in &overlay.assignments {
        assignment[var] = value;
    }
}

fn source_frame_choice_selection(
    root: &Path,
    formula: &RawFormula,
    assignment: &[bool],
    current_residual: &[usize],
    opts: &AssignmentLocalSearchOptions,
) -> Result<SourceFrameChoiceSelection> {
    if opts.source_frame_choice_rounds == 0 {
        return Ok(SourceFrameChoiceSelection::default());
    }
    let Some(limit) = opts.source_frame_choice_limit else {
        bail!("assignment-local-search --source-frame-choice-rounds requires --source-frame-choice-limit");
    };
    let source_frame_rows = resolve_path(root, &opts.source_frame_rows);
    let source_frame_table = read_tsv_table(&source_frame_rows)?;
    let source_rows = parse_source_frame_rows(&source_frame_table, false)?;
    let residual_clause_ids: BTreeSet<usize> = current_residual.iter().map(|idx| idx + 1).collect();
    let mut candidates = Vec::new();
    for row in &source_rows.rows {
        if !residual_clause_ids.contains(&row.clause_id_one_based) {
            continue;
        }
        if !source_frame_row_has_valid_binding(formula, row) {
            continue;
        }
        candidates.push(SourceFrameChoiceRow {
            source_frame_row_id: row.source_frame_row_id.clone(),
            clause_id_one_based: row.clause_id_one_based,
            literal_index_one_based: row.literal_index_one_based,
            var: row.var_one_based - 1,
            required_value: row.required_value_to_satisfy_literal,
        });
    }
    let (remaining_clause_ledger, remaining_choices) =
        if let Some(ledger) = &opts.source_frame_choice_current_remaining_clause_value_ledger {
            let remaining_clause_ledger = resolve_path(root, ledger);
            let remaining_clause_table = read_tsv_table(&remaining_clause_ledger)?;
            (
                Some(remaining_clause_ledger),
                parse_remaining_clause_choice_rows(
                    &remaining_clause_table,
                    formula,
                    &residual_clause_ids,
                ),
            )
        } else {
            (None, RemainingClauseChoiceRows::default())
        };
    let remaining_clause_choice_rows = remaining_choices.rows.len();
    candidates.extend(remaining_choices.rows);
    let existing_choice_keys = candidates
        .iter()
        .map(source_frame_choice_row_key)
        .collect::<BTreeSet<_>>();
    let dynamic_residual_choices = if opts.source_frame_choice_dynamic_residual_choices {
        dynamic_current_residual_choice_rows(
            formula,
            assignment,
            current_residual,
            &existing_choice_keys,
        )
    } else {
        Vec::new()
    };
    let dynamic_residual_choice_rows = dynamic_residual_choices.len();
    let dynamic_residual_choice_clause_count = dynamic_residual_choices
        .iter()
        .map(|row| row.clause_id_one_based)
        .collect::<BTreeSet<_>>()
        .len();
    candidates.extend(dynamic_residual_choices);
    candidates.sort_by(|left, right| {
        (
            left.clause_id_one_based,
            source_frame_choice_row_source_rank(left),
            left.literal_index_one_based,
            left.var,
            &left.source_frame_row_id,
        )
            .cmp(&(
                right.clause_id_one_based,
                source_frame_choice_row_source_rank(right),
                right.literal_index_one_based,
                right.var,
                &right.source_frame_row_id,
            ))
    });
    let candidate_row_count = candidates.len();
    let mut side_effect_prune_input_rows = None;
    let mut side_effect_prune_kept_rows = None;
    let mut side_effect_prune_non_worsening_rows = 0usize;
    let mut side_effect_prune_top_per_clause_rows = 0usize;
    let mut side_effect_prune_pruned_rows = None;
    if let Some(top_per_clause) = opts.source_frame_choice_side_effect_top_per_clause {
        let prune = prune_source_frame_choice_rows_by_side_effect(
            formula,
            assignment,
            &candidates,
            top_per_clause,
        );
        side_effect_prune_input_rows = Some(prune.input_rows);
        side_effect_prune_kept_rows = Some(prune.rows.len());
        side_effect_prune_non_worsening_rows = prune.non_worsening_rows;
        side_effect_prune_top_per_clause_rows = prune.top_per_clause_rows;
        side_effect_prune_pruned_rows = Some(prune.input_rows.saturating_sub(prune.rows.len()));
        candidates = prune.rows;
    }
    candidates.truncate(limit);
    let selected_row_count = candidates.len();
    let mut rows_by_clause: BTreeMap<usize, Vec<SourceFrameChoiceRow>> = BTreeMap::new();
    for row in candidates {
        rows_by_clause
            .entry(row.clause_id_one_based)
            .or_default()
            .push(row);
    }
    Ok(SourceFrameChoiceSelection {
        rows_by_clause,
        candidate_row_count: Some(candidate_row_count),
        selected_row_count,
        side_effect_prune_input_rows,
        side_effect_prune_kept_rows,
        side_effect_prune_non_worsening_rows,
        side_effect_prune_top_per_clause_rows,
        side_effect_prune_pruned_rows,
        source_frame_rows: Some(source_frame_rows),
        remaining_clause_ledger,
        remaining_clause_rows_seen: remaining_choices.rows_seen,
        remaining_clause_choice_rows,
        dynamic_residual_choice_clause_count,
        dynamic_residual_choice_rows,
        source_frame_parse_errors: source_rows.parse_errors,
        source_frame_parse_error_samples: source_rows.parse_error_samples,
        remaining_clause_parse_errors: remaining_choices.parse_errors,
        remaining_clause_parse_error_samples: remaining_choices.parse_error_samples,
    })
}

#[derive(Clone, Debug, Default)]
struct RemainingClauseChoiceRows {
    rows: Vec<SourceFrameChoiceRow>,
    rows_seen: usize,
    parse_errors: usize,
    parse_error_samples: Vec<String>,
}

struct SourceFrameChoiceSideEffectPrune {
    rows: Vec<SourceFrameChoiceRow>,
    input_rows: usize,
    non_worsening_rows: usize,
    top_per_clause_rows: usize,
}

fn prune_source_frame_choice_rows_by_side_effect(
    formula: &RawFormula,
    assignment: &[bool],
    rows: &[SourceFrameChoiceRow],
    top_per_clause: usize,
) -> SourceFrameChoiceSideEffectPrune {
    let input_rows = rows.len();
    let mut scored = rows
        .iter()
        .enumerate()
        .map(|(idx, row)| {
            let mut introduced_count = 0usize;
            let mut cleared_count = 0usize;
            let mut affected_count = 0usize;
            for clause in &formula.clauses {
                if !clause.iter().any(|&lit| lit_var(lit) - 1 == row.var) {
                    continue;
                }
                affected_count += 1;
                let was_residual = !clause.iter().any(|&lit| literal_satisfied(lit, assignment));
                let now_residual = !clause.iter().any(|&lit| {
                    let var = lit_var(lit) - 1;
                    let value = if var == row.var {
                        row.required_value
                    } else {
                        assignment[var]
                    };
                    if lit > 0 {
                        value
                    } else {
                        !value
                    }
                });
                match (was_residual, now_residual) {
                    (true, false) => cleared_count += 1,
                    (false, true) => introduced_count += 1,
                    _ => {}
                }
            }
            let candidate_residual_delta = introduced_count as isize - cleared_count as isize;
            (
                idx,
                row.clone(),
                candidate_residual_delta,
                introduced_count,
                cleared_count,
                affected_count,
            )
        })
        .collect::<Vec<_>>();
    let non_worsening_rows = scored
        .iter()
        .filter(|(_, _, delta, _, _, _)| *delta <= 0)
        .count();
    let mut keep = BTreeSet::new();
    let mut non_worsening_keep = BTreeSet::new();
    for (idx, _, delta, _, _, _) in &scored {
        if *delta <= 0 {
            keep.insert(*idx);
            non_worsening_keep.insert(*idx);
        }
    }
    let mut by_clause: BTreeMap<usize, Vec<_>> = BTreeMap::new();
    for score in scored.drain(..) {
        by_clause
            .entry(score.1.clause_id_one_based)
            .or_default()
            .push(score);
    }
    for clause_scores in by_clause.values_mut() {
        clause_scores.sort_by(|left, right| {
            (
                left.2,
                left.3,
                std::cmp::Reverse(left.4),
                left.5,
                left.1.literal_index_one_based,
                left.1.var,
                &left.1.source_frame_row_id,
            )
                .cmp(&(
                    right.2,
                    right.3,
                    std::cmp::Reverse(right.4),
                    right.5,
                    right.1.literal_index_one_based,
                    right.1.var,
                    &right.1.source_frame_row_id,
                ))
        });
        for (idx, _, _, _, _, _) in clause_scores
            .iter()
            .filter(|(_, _, delta, _, _, _)| *delta > 0)
            .take(top_per_clause)
        {
            keep.insert(*idx);
        }
    }
    let top_per_clause_rows = keep.difference(&non_worsening_keep).count();
    let rows = rows
        .iter()
        .enumerate()
        .filter(|&(idx, _row)| keep.contains(&idx))
        .map(|(_idx, row)| row.clone())
        .collect::<Vec<_>>();
    SourceFrameChoiceSideEffectPrune {
        rows,
        input_rows,
        non_worsening_rows,
        top_per_clause_rows,
    }
}

fn dynamic_current_residual_choice_rows(
    formula: &RawFormula,
    assignment: &[bool],
    current_residual: &[usize],
    existing_choice_keys: &BTreeSet<(usize, usize, usize, bool)>,
) -> Vec<SourceFrameChoiceRow> {
    let mut rows = Vec::new();
    for &clause_idx in current_residual {
        let Some(clause) = formula.clauses.get(clause_idx) else {
            continue;
        };
        for (literal_idx, &lit) in clause.iter().enumerate() {
            let var = lit_var(lit) - 1;
            let required_value = lit > 0;
            if assignment[var] == required_value {
                continue;
            }
            let key = (clause_idx + 1, literal_idx + 1, var, required_value);
            if existing_choice_keys.contains(&key) {
                continue;
            }
            rows.push(SourceFrameChoiceRow {
                source_frame_row_id: format!(
                    "dynamic_current_residual:clause_{}:lit_{}:var_{}",
                    clause_idx + 1,
                    literal_idx + 1,
                    var + 1
                ),
                clause_id_one_based: clause_idx + 1,
                literal_index_one_based: literal_idx + 1,
                var,
                required_value,
            });
        }
    }
    rows
}

fn source_frame_choice_row_key(row: &SourceFrameChoiceRow) -> (usize, usize, usize, bool) {
    (
        row.clause_id_one_based,
        row.literal_index_one_based,
        row.var,
        row.required_value,
    )
}

fn source_frame_choice_row_source_rank(row: &SourceFrameChoiceRow) -> usize {
    if row
        .source_frame_row_id
        .starts_with("dynamic_current_residual:")
    {
        1
    } else {
        0
    }
}

fn parse_remaining_clause_choice_rows(
    table: &TsvTable,
    formula: &RawFormula,
    residual_clause_ids: &BTreeSet<usize>,
) -> RemainingClauseChoiceRows {
    let mut parsed = RemainingClauseChoiceRows::default();
    for (idx, row) in table.rows.iter().enumerate() {
        let line_number = idx + 2;
        let clause_id =
            match remaining_clause_usize_cell(table, line_number, row, "clause_index_1_based") {
                Ok(clause_id) => clause_id,
                Err(error) => {
                    parsed.parse_errors += 1;
                    if parsed.parse_error_samples.len() < 8 {
                        parsed.parse_error_samples.push(format!("{error:#}"));
                    }
                    continue;
                }
            };
        if !residual_clause_ids.contains(&clause_id) {
            continue;
        }
        parsed.rows_seen += 1;
        match parse_remaining_clause_choice_row(table, line_number, row, formula, clause_id) {
            Ok(mut rows) => {
                parsed.rows.append(&mut rows);
            }
            Err(error) => {
                parsed.parse_errors += 1;
                if parsed.parse_error_samples.len() < 8 {
                    parsed.parse_error_samples.push(format!("{error:#}"));
                }
            }
        }
    }
    parsed
}

fn parse_remaining_clause_choice_row(
    table: &TsvTable,
    line_number: usize,
    row: &BTreeMap<String, String>,
    formula: &RawFormula,
    clause_id: usize,
) -> Result<Vec<SourceFrameChoiceRow>> {
    if clause_id == 0 || clause_id > formula.clauses.len() {
        bail!(
            "{}:{line_number} clause_index_1_based {clause_id} is out of range",
            table.path.display()
        );
    }
    let clause = &formula.clauses[clause_id - 1];
    let ledger_clause = parse_remaining_clause_i32s(table, line_number, row, "clause")?;
    if ledger_clause != *clause {
        bail!(
            "{}:{line_number} clause does not match original DIMACS clause {clause_id}",
            table.path.display()
        );
    }
    let literal_values = remaining_clause_cell(table, line_number, row, "literal_values")?;
    let literal_values = unquote_tsv_json_cell(literal_values);
    let values: JsonValue = serde_json::from_str(&literal_values).with_context(|| {
        format!(
            "{}:{line_number} invalid literal_values JSON",
            table.path.display()
        )
    })?;
    let entries = values.as_array().with_context(|| {
        format!(
            "{}:{line_number} literal_values must be a JSON array",
            table.path.display()
        )
    })?;
    if entries.len() != clause.len() {
        bail!(
            "{}:{line_number} literal_values has {} entries but clause {clause_id} has {} literals",
            table.path.display(),
            entries.len(),
            clause.len()
        );
    }
    let mut choices = Vec::new();
    for (entry_idx, entry) in entries.iter().enumerate() {
        let lit = json_i32_field(table, line_number, entry_idx, entry, "lit")?;
        let var_one_based = json_usize_field(table, line_number, entry_idx, entry, "var")?;
        if var_one_based == 0 || var_one_based > formula.num_vars {
            bail!(
                "{}:{line_number} literal_values[{entry_idx}] var {var_one_based} is out of range",
                table.path.display()
            );
        }
        if lit_var(lit) != var_one_based {
            bail!(
                "{}:{line_number} literal_values[{entry_idx}] lit/var mismatch: {lit} vs {var_one_based}",
                table.path.display()
            );
        }
        let var_value = json_bool_field(table, line_number, entry_idx, entry, "var_value")?;
        let literal_value = json_bool_field(table, line_number, entry_idx, entry, "literal_value")?;
        let expected_literal_value = if lit > 0 { var_value } else { !var_value };
        if literal_value != expected_literal_value {
            bail!(
                "{}:{line_number} literal_values[{entry_idx}] literal_value disagrees with lit/var_value",
                table.path.display()
            );
        }
        let Some(literal_index) = clause.iter().position(|&clause_lit| clause_lit == lit) else {
            bail!(
                "{}:{line_number} literal_values[{entry_idx}] lit {lit} is not in clause {clause_id}",
                table.path.display()
            );
        };
        let source = json_string_field(table, line_number, entry_idx, entry, "source")?;
        if !matches!(
            source,
            "frontier_choice_cegar" | "cyclic_scc_tie_cegar" | "forced_gate_output_cegar_checked"
        ) {
            bail!(
                "{}:{line_number} literal_values[{entry_idx}] unsupported source {source}",
                table.path.display()
            );
        }
        choices.push(SourceFrameChoiceRow {
            source_frame_row_id: format!(
                "remaining_clause_value:clause_{clause_id}:lit_{}:var_{var_one_based}",
                literal_index + 1
            ),
            clause_id_one_based: clause_id,
            literal_index_one_based: literal_index + 1,
            var: var_one_based - 1,
            required_value: lit > 0,
        });
    }
    Ok(choices)
}

fn remaining_clause_cell<'a>(
    table: &TsvTable,
    line_number: usize,
    row: &'a BTreeMap<String, String>,
    column: &str,
) -> Result<&'a str> {
    let value = row.get(column).map(String::as_str).with_context(|| {
        format!(
            "{}:{line_number} missing required column {column}",
            table.path.display()
        )
    })?;
    if value.trim().is_empty() || value == "." {
        bail!(
            "{}:{line_number} has empty required column {column}",
            table.path.display()
        );
    }
    Ok(value)
}

fn remaining_clause_usize_cell(
    table: &TsvTable,
    line_number: usize,
    row: &BTreeMap<String, String>,
    column: &str,
) -> Result<usize> {
    let value = remaining_clause_cell(table, line_number, row, column)?;
    value.parse::<usize>().with_context(|| {
        format!(
            "{}:{line_number} invalid {column} value '{}'",
            table.path.display(),
            value
        )
    })
}

fn parse_remaining_clause_i32s(
    table: &TsvTable,
    line_number: usize,
    row: &BTreeMap<String, String>,
    column: &str,
) -> Result<Vec<i32>> {
    let value = remaining_clause_cell(table, line_number, row, column)?;
    let mut values = Vec::new();
    for cell in value.split_whitespace() {
        values.push(cell.parse::<i32>().with_context(|| {
            format!(
                "{}:{line_number} invalid {column} literal '{}'",
                table.path.display(),
                cell
            )
        })?);
    }
    if values.is_empty() {
        bail!(
            "{}:{line_number} has empty literal list in {column}",
            table.path.display()
        );
    }
    Ok(values)
}

fn unquote_tsv_json_cell(raw: &str) -> String {
    let trimmed = raw.trim();
    if trimmed.len() >= 2 && trimmed.starts_with('"') && trimmed.ends_with('"') {
        trimmed[1..trimmed.len() - 1].replace("\"\"", "\"")
    } else {
        trimmed.to_string()
    }
}

fn json_i32_field(
    table: &TsvTable,
    line_number: usize,
    entry_idx: usize,
    entry: &JsonValue,
    field: &str,
) -> Result<i32> {
    let value = entry
        .get(field)
        .and_then(JsonValue::as_i64)
        .with_context(|| {
            format!(
                "{}:{line_number} literal_values[{entry_idx}] missing integer field {field}",
                table.path.display()
            )
        })?;
    i32::try_from(value).with_context(|| {
        format!(
            "{}:{line_number} literal_values[{entry_idx}] {field} out of i32 range",
            table.path.display()
        )
    })
}

fn json_usize_field(
    table: &TsvTable,
    line_number: usize,
    entry_idx: usize,
    entry: &JsonValue,
    field: &str,
) -> Result<usize> {
    let value = entry
        .get(field)
        .and_then(JsonValue::as_u64)
        .with_context(|| {
            format!(
            "{}:{line_number} literal_values[{entry_idx}] missing unsigned integer field {field}",
            table.path.display()
        )
        })?;
    usize::try_from(value).with_context(|| {
        format!(
            "{}:{line_number} literal_values[{entry_idx}] {field} out of usize range",
            table.path.display()
        )
    })
}

fn json_bool_field(
    table: &TsvTable,
    line_number: usize,
    entry_idx: usize,
    entry: &JsonValue,
    field: &str,
) -> Result<bool> {
    entry
        .get(field)
        .and_then(JsonValue::as_bool)
        .with_context(|| {
            format!(
                "{}:{line_number} literal_values[{entry_idx}] missing Boolean field {field}",
                table.path.display()
            )
        })
}

fn json_string_field<'a>(
    table: &TsvTable,
    line_number: usize,
    entry_idx: usize,
    entry: &'a JsonValue,
    field: &str,
) -> Result<&'a str> {
    entry
        .get(field)
        .and_then(JsonValue::as_str)
        .with_context(|| {
            format!(
                "{}:{line_number} literal_values[{entry_idx}] missing string field {field}",
                table.path.display()
            )
        })
}

struct SourceFrameChoiceSearch {
    best_state: SourceFrameChoiceState,
    best_residual: Vec<usize>,
    final_width: usize,
    evaluated_states: usize,
    top_candidates: Vec<JsonValue>,
}

fn source_frame_choice_beam_search(
    formula: &RawFormula,
    assignment: &[bool],
    selection: &SourceFrameChoiceSelection,
    beam_width: usize,
    prefer_nonempty_neutral: bool,
    seen_residuals: Option<&BTreeSet<Vec<usize>>>,
) -> SourceFrameChoiceSearch {
    let base_residual = residual_clause_ids(&formula.clauses, assignment);
    let mut base_residual_flags = vec![false; formula.clauses.len()];
    for &clause_idx in &base_residual {
        base_residual_flags[clause_idx] = true;
    }
    let occurrences = source_frame_choice_occurrences(formula);
    let mut beam = vec![SourceFrameChoiceState::default()];
    let mut evaluated_states = 0usize;
    for rows in selection.rows_by_clause.values() {
        let mut next = Vec::new();
        for state in &beam {
            next.push(state.clone());
            for row in rows {
                evaluated_states += 1;
                if let Some(candidate) = source_frame_choice_extend_state(state, row) {
                    next.push(candidate);
                }
            }
        }
        let mut scored_next = next
            .into_iter()
            .map(|state| {
                let residual_count = source_frame_choice_residual_count(
                    formula,
                    assignment,
                    &state,
                    &occurrences,
                    &base_residual_flags,
                    base_residual.len(),
                );
                (residual_count, state)
            })
            .collect::<Vec<_>>();
        scored_next.sort_by(|left, right| {
            (
                left.0,
                left.1.assignments.len(),
                &left.1.clause_ids,
                &left.1.row_ids,
            )
                .cmp(&(
                    right.0,
                    right.1.assignments.len(),
                    &right.1.clause_ids,
                    &right.1.row_ids,
                ))
        });
        scored_next.truncate(beam_width);
        beam = scored_next
            .into_iter()
            .map(|(_, state)| state)
            .collect::<Vec<_>>();
        if beam.is_empty() {
            break;
        }
    }

    let mut scored = beam
        .into_iter()
        .map(|state| {
            let trial = assignment_after_source_frame_choice_state(assignment, &state);
            let residual = residual_clause_ids(&formula.clauses, &trial);
            (residual.len(), state.assignments.len(), state, residual)
        })
        .collect::<Vec<_>>();
    scored.sort_by(|left, right| {
        (left.0, left.1, &left.2.clause_ids, &left.2.row_ids).cmp(&(
            right.0,
            right.1,
            &right.2.clause_ids,
            &right.2.row_ids,
        ))
    });
    let top_candidates = scored
        .iter()
        .take(16)
        .map(|(count, _, state, residual)| {
            let affected = source_frame_choice_affected_clause_ids(state, &occurrences);
            json!({
                "source_frame_row_ids": &state.row_ids,
                "one_based_clause_ids": &state.clause_ids,
                "one_based_set_values": source_frame_choice_state_set_values(state),
                "residual_falsified_clause_count": count,
                "residual_falsified_one_based_clause_ids": residual.iter().take(32).map(|idx| idx + 1).collect::<Vec<_>>(),
                "side_effect_summary": source_frame_choice_side_effect_summary(&base_residual, residual, &affected),
            })
        })
        .collect();
    let final_width = scored.len();
    let selected_idx = if prefer_nonempty_neutral {
        scored
            .iter()
            .position(|(count, _, state, residual)| {
                !state.assignments.is_empty()
                    && !seen_residuals
                        .is_some_and(|seen_residuals| seen_residuals.contains(residual))
                    && (*count < base_residual.len() || *count == base_residual.len())
            })
            .unwrap_or(0)
    } else {
        0
    };
    let (best_state, best_residual) = scored
        .get(selected_idx)
        .map(|(_, _, state, residual)| (state.clone(), residual.clone()))
        .unwrap_or_else(|| (SourceFrameChoiceState::default(), base_residual));
    SourceFrameChoiceSearch {
        best_state,
        best_residual,
        final_width,
        evaluated_states,
        top_candidates,
    }
}

fn source_frame_choice_extend_state(
    state: &SourceFrameChoiceState,
    row: &SourceFrameChoiceRow,
) -> Option<SourceFrameChoiceState> {
    if let Some(existing) = state.assignments.get(&row.var) {
        if *existing != row.required_value {
            return None;
        }
    }
    let mut next = state.clone();
    next.assignments.insert(row.var, row.required_value);
    next.row_ids.push(row.source_frame_row_id.clone());
    next.clause_ids.push(row.clause_id_one_based);
    Some(next)
}

fn assignment_after_source_frame_choice_state(
    assignment: &[bool],
    state: &SourceFrameChoiceState,
) -> Vec<bool> {
    let mut trial = assignment.to_vec();
    apply_source_frame_choice_state(&mut trial, state);
    trial
}

fn source_frame_choice_occurrences(formula: &RawFormula) -> Vec<Vec<usize>> {
    let mut occurrences = vec![Vec::new(); formula.num_vars];
    for (clause_idx, clause) in formula.clauses.iter().enumerate() {
        for &lit in clause {
            let var = lit_var(lit) - 1;
            if let Some(var_occurrences) = occurrences.get_mut(var) {
                var_occurrences.push(clause_idx);
            }
        }
    }
    occurrences
}

fn source_frame_choice_residual_count(
    formula: &RawFormula,
    assignment: &[bool],
    state: &SourceFrameChoiceState,
    occurrences: &[Vec<usize>],
    base_residual_flags: &[bool],
    base_residual_count: usize,
) -> usize {
    let mut affected = BTreeSet::new();
    for &var in state.assignments.keys() {
        if let Some(clause_ids) = occurrences.get(var) {
            affected.extend(clause_ids.iter().copied());
        }
    }
    let mut residual_count = base_residual_count;
    for clause_idx in affected {
        let was_residual = base_residual_flags[clause_idx];
        let now_residual = !formula.clauses[clause_idx].iter().any(|&lit| {
            let var = lit_var(lit) - 1;
            let value = state
                .assignments
                .get(&var)
                .copied()
                .unwrap_or(assignment[var]);
            if lit > 0 {
                value
            } else {
                !value
            }
        });
        match (was_residual, now_residual) {
            (true, false) => residual_count -= 1,
            (false, true) => residual_count += 1,
            _ => {}
        }
    }
    residual_count
}

fn source_frame_choice_affected_clause_ids(
    state: &SourceFrameChoiceState,
    occurrences: &[Vec<usize>],
) -> Vec<usize> {
    let mut affected = BTreeSet::new();
    for &var in state.assignments.keys() {
        if let Some(clause_ids) = occurrences.get(var) {
            affected.extend(clause_ids.iter().copied());
        }
    }
    affected.into_iter().collect()
}

fn apply_source_frame_choice_state(assignment: &mut [bool], state: &SourceFrameChoiceState) {
    for (&var, &value) in &state.assignments {
        assignment[var] = value;
    }
}

fn source_frame_choice_state_set_values(state: &SourceFrameChoiceState) -> Vec<JsonValue> {
    state
        .assignments
        .iter()
        .map(|(var, value)| json!({"var": var + 1, "value": value}))
        .collect()
}

fn source_frame_choice_side_effect_summary(
    base_residual: &[usize],
    candidate_residual: &[usize],
    affected_clause_ids: &[usize],
) -> JsonValue {
    let base: BTreeSet<usize> = base_residual.iter().copied().collect();
    let candidate: BTreeSet<usize> = candidate_residual.iter().copied().collect();
    let cleared = base
        .difference(&candidate)
        .map(|idx| idx + 1)
        .collect::<Vec<_>>();
    let retained = base
        .intersection(&candidate)
        .map(|idx| idx + 1)
        .collect::<Vec<_>>();
    let introduced = candidate
        .difference(&base)
        .map(|idx| idx + 1)
        .collect::<Vec<_>>();
    json!({
        "baseline_residual_falsified_clause_count": base.len(),
        "candidate_residual_falsified_clause_count": candidate.len(),
        "net_residual_delta": candidate.len() as isize - base.len() as isize,
        "relative_to": "round_start_assignment",
        "authority": "diagnostic_only",
        "affected_clause_count": affected_clause_ids.len(),
        "affected_one_based_clause_ids": affected_clause_ids.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
        "cleared_round_start_residual_count": cleared.len(),
        "cleared_round_start_residual_one_based_clause_ids": cleared,
        "retained_baseline_residual_count": retained.len(),
        "retained_baseline_residual_one_based_clause_ids": retained,
        "introduced_residual_count": introduced.len(),
        "introduced_residual_one_based_clause_ids": introduced,
    })
}

fn read_bounded_json_report(path: &Path, label: &str, max_bytes: u64) -> Result<JsonValue> {
    let report_size = fs::metadata(path)
        .with_context(|| format!("failed to stat {label} '{}'", path.display()))?
        .len();
    if report_size > max_bytes {
        bail!(
            "{label} '{}' is too large: {} bytes exceeds {}",
            path.display(),
            report_size,
            max_bytes
        );
    }
    let report_bytes =
        fs::read(path).with_context(|| format!("failed to read {label} '{}'", path.display()))?;
    serde_json::from_slice(&report_bytes)
        .with_context(|| format!("failed to parse {label} JSON '{}'", path.display()))
}

fn collect_residual_side_effect_backbone(
    formula: &RawFormula,
    report: &JsonValue,
) -> Result<ResidualSideEffectBackbone> {
    let baseline = report
        .get("baseline_w210")
        .context("assignment-local-search report missing baseline_w210 object")?;
    baseline
        .as_object()
        .context("assignment-local-search report baseline_w210 must be an object")?;
    let baseline_ids =
        json_usize_array_required(baseline, "residual_falsified_one_based_clause_ids")
            .context("baseline_w210.residual_falsified_one_based_clause_ids")?;
    validate_one_based_clause_ids(
        &baseline_ids,
        formula.clauses.len(),
        "baseline_w210.residual_falsified_one_based_clause_ids",
    )?;
    ensure_unique_usizes(
        &baseline_ids,
        "baseline_w210.residual_falsified_one_based_clause_ids",
    )?;
    validate_optional_usize_count(
        baseline,
        "residual_falsified_clause_count",
        baseline_ids.len(),
        "baseline_w210.residual_falsified_clause_count",
    )?;
    let baseline_set: BTreeSet<usize> = baseline_ids.into_iter().collect();
    let rounds = report
        .pointer("/search/source_frame_choice_rounds")
        .and_then(JsonValue::as_array)
        .context(
            "assignment-local-search report missing /search/source_frame_choice_rounds array",
        )?;
    let mut backbone = ResidualSideEffectBackbone {
        baseline_residual_one_based_clause_ids: baseline_set.clone(),
        ..ResidualSideEffectBackbone::default()
    };
    for (round_idx, round) in rounds.iter().enumerate() {
        round.as_object().with_context(|| {
            format!("source_frame_choice_rounds[{round_idx}] must be an object")
        })?;
        let round_number = if round.get("round").is_some() {
            report_usize_field(round, "round", "source_frame_choice_rounds[].round")?
        } else {
            round_idx + 1
        };
        let top_candidates = round
            .get("top_candidates")
            .and_then(JsonValue::as_array)
            .with_context(|| {
                format!("source_frame_choice_rounds[{round_idx}] missing top_candidates array")
            })?;
        backbone.top_candidates_seen += top_candidates.len();
        for (candidate_idx, candidate) in top_candidates.iter().enumerate() {
            candidate.as_object().with_context(|| {
                format!(
                    "source_frame_choice_rounds[{round_idx}].top_candidates[{candidate_idx}] must be an object"
                )
            })?;
            let summary = candidate.get("side_effect_summary").with_context(|| {
                format!(
                    "source_frame_choice_rounds[{round_idx}].top_candidates[{candidate_idx}] missing side_effect_summary"
                )
            })?;
            summary.as_object().with_context(|| {
                format!(
                    "source_frame_choice_rounds[{round_idx}].top_candidates[{candidate_idx}] side_effect_summary must be an object"
                )
            })?;
            let summary_authority = summary
                .get("authority")
                .and_then(JsonValue::as_str)
                .with_context(|| {
                    format!(
                        "source_frame_choice_rounds[{round_idx}].top_candidates[{candidate_idx}] side_effect_summary.authority must be diagnostic_only"
                    )
                })?;
            if summary_authority != "diagnostic_only" {
                bail!(
                    "source_frame_choice_rounds[{round_idx}].top_candidates[{candidate_idx}] side_effect_summary.authority must be diagnostic_only"
                );
            }
            backbone.top_candidates_with_side_effect_summary += 1;

            validate_optional_usize_count(
                summary,
                "baseline_residual_falsified_clause_count",
                baseline_set.len(),
                "side_effect_summary.baseline_residual_falsified_clause_count",
            )?;
            let affected_ids =
                json_usize_array_field(candidate, summary, "affected_one_based_clause_ids")?;
            validate_one_based_clause_ids(
                &affected_ids,
                formula.clauses.len(),
                "side_effect_summary.affected_one_based_clause_ids",
            )?;
            ensure_unique_usizes(
                &affected_ids,
                "side_effect_summary.affected_one_based_clause_ids",
            )?;
            validate_optional_usize_count(
                summary,
                "affected_clause_count",
                affected_ids.len(),
                "side_effect_summary.affected_clause_count",
            )?;
            let cleared_ids = json_usize_array_field(
                candidate,
                summary,
                "cleared_round_start_residual_one_based_clause_ids",
            )?;
            validate_one_based_clause_ids(
                &cleared_ids,
                formula.clauses.len(),
                "side_effect_summary.cleared_round_start_residual_one_based_clause_ids",
            )?;
            ensure_unique_usizes(
                &cleared_ids,
                "side_effect_summary.cleared_round_start_residual_one_based_clause_ids",
            )?;
            validate_optional_usize_count(
                summary,
                "cleared_round_start_residual_count",
                cleared_ids.len(),
                "side_effect_summary.cleared_round_start_residual_count",
            )?;
            let retained_ids =
                json_usize_array(summary, "retained_baseline_residual_one_based_clause_ids")?;
            validate_one_based_clause_ids(
                &retained_ids,
                formula.clauses.len(),
                "side_effect_summary.retained_baseline_residual_one_based_clause_ids",
            )?;
            ensure_unique_usizes(
                &retained_ids,
                "side_effect_summary.retained_baseline_residual_one_based_clause_ids",
            )?;
            validate_optional_usize_count(
                summary,
                "retained_baseline_residual_count",
                retained_ids.len(),
                "side_effect_summary.retained_baseline_residual_count",
            )?;
            let introduced_ids = json_usize_array_field(
                candidate,
                summary,
                "introduced_residual_one_based_clause_ids",
            )?;
            validate_one_based_clause_ids(
                &introduced_ids,
                formula.clauses.len(),
                "side_effect_summary.introduced_residual_one_based_clause_ids",
            )?;
            ensure_unique_usizes(
                &introduced_ids,
                "side_effect_summary.introduced_residual_one_based_clause_ids",
            )?;
            validate_optional_usize_count(
                summary,
                "introduced_residual_count",
                introduced_ids.len(),
                "side_effect_summary.introduced_residual_count",
            )?;
            let candidate_residual_ids =
                json_usize_array(candidate, "residual_falsified_one_based_clause_ids")?;
            validate_one_based_clause_ids(
                &candidate_residual_ids,
                formula.clauses.len(),
                "top_candidates[].residual_falsified_one_based_clause_ids",
            )?;
            ensure_unique_usizes(
                &candidate_residual_ids,
                "top_candidates[].residual_falsified_one_based_clause_ids",
            )?;
            let candidate_residual_count = optional_report_usize_field(
                candidate,
                "residual_falsified_clause_count",
                "top_candidates[].residual_falsified_clause_count",
            )?;
            if let Some(count) = candidate_residual_count {
                if !candidate_residual_ids.is_empty() && count != candidate_residual_ids.len() {
                    bail!(
                        "top_candidates[].residual_falsified_clause_count expected {}, got {}",
                        candidate_residual_ids.len(),
                        count
                    );
                }
            }
            if let Some(summary_count) = optional_report_usize_field(
                summary,
                "candidate_residual_falsified_clause_count",
                "side_effect_summary.candidate_residual_falsified_clause_count",
            )? {
                if let Some(candidate_count) = candidate_residual_count {
                    if summary_count != candidate_count {
                        bail!(
                            "side_effect_summary.candidate_residual_falsified_clause_count {summary_count} does not match top candidate residual count {candidate_count}"
                        );
                    }
                }
            }
            let net_residual_delta = optional_report_isize_field(
                summary,
                "net_residual_delta",
                "side_effect_summary.net_residual_delta",
            )?;
            let candidate_set_values = parse_candidate_set_values(candidate)?;
            for (var, _) in &candidate_set_values {
                if *var > formula.num_vars {
                    bail!(
                        "source_frame_choice_rounds[{round_idx}].top_candidates[{candidate_idx}] one_based_set_values var {} is out of range 1..={}",
                        var,
                        formula.num_vars
                    );
                }
            }
            let candidate_clause_ids = json_usize_array(candidate, "one_based_clause_ids")?;
            validate_one_based_clause_ids(
                &candidate_clause_ids,
                formula.clauses.len(),
                "top_candidates[].one_based_clause_ids",
            )?;
            let source_frame_row_ids = json_string_array(candidate, "source_frame_row_ids")?;
            let cleared_baseline_ids: Vec<_> = cleared_ids
                .iter()
                .copied()
                .filter(|clause_id| baseline_set.contains(clause_id))
                .collect();
            backbone
                .unique_affected_one_based_clause_ids
                .extend(affected_ids.iter().copied());
            backbone
                .unique_introduced_residual_one_based_clause_ids
                .extend(introduced_ids.iter().copied());
            if cleared_baseline_ids.is_empty() {
                continue;
            }
            let anchor_id = format!("round{round_number}-candidate{}", candidate_idx + 1);
            for clause_id in &cleared_baseline_ids {
                backbone
                    .residual_to_anchor_ids
                    .entry(*clause_id)
                    .or_default()
                    .push(anchor_id.clone());
            }
            backbone.anchors.push(ResidualSideEffectAnchor {
                anchor_id,
                round: round_number,
                top_candidate_rank: candidate_idx + 1,
                source_frame_row_ids,
                candidate_one_based_clause_ids: candidate_clause_ids,
                one_based_set_values: candidate_set_values,
                candidate_residual_falsified_clause_count: candidate_residual_count,
                candidate_residual_one_based_clause_ids: candidate_residual_ids,
                net_residual_delta,
                affected_one_based_clause_ids: affected_ids,
                cleared_round_start_residual_one_based_clause_ids: cleared_ids,
                cleared_baseline_residual_one_based_clause_ids: cleared_baseline_ids,
                retained_baseline_residual_one_based_clause_ids: retained_ids,
                introduced_residual_one_based_clause_ids: introduced_ids,
            });
        }
    }
    Ok(backbone)
}

fn residual_side_effect_anchor_json(
    anchor: &ResidualSideEffectAnchor,
    frontier_ids: Option<&BTreeSet<usize>>,
) -> JsonValue {
    let frontier_covered: Option<Vec<_>> = frontier_ids.map(|ids| {
        anchor
            .introduced_residual_one_based_clause_ids
            .iter()
            .copied()
            .filter(|clause_id| ids.contains(clause_id))
            .collect()
    });
    let frontier_uncovered: Option<Vec<_>> = frontier_ids.map(|ids| {
        anchor
            .introduced_residual_one_based_clause_ids
            .iter()
            .copied()
            .filter(|clause_id| !ids.contains(clause_id))
            .collect()
    });
    json!({
        "anchor_id": anchor.anchor_id,
        "round": anchor.round,
        "top_candidate_rank": anchor.top_candidate_rank,
        "source_frame_row_ids": &anchor.source_frame_row_ids,
        "candidate_one_based_clause_ids": &anchor.candidate_one_based_clause_ids,
        "one_based_set_values": anchor.one_based_set_values.iter().map(|(var, value)| json!({"var": var, "value": value})).collect::<Vec<_>>(),
        "candidate_residual_falsified_clause_count": anchor.candidate_residual_falsified_clause_count,
        "candidate_residual_falsified_one_based_clause_ids": &anchor.candidate_residual_one_based_clause_ids,
        "net_residual_delta": anchor.net_residual_delta,
        "affected_clause_count": anchor.affected_one_based_clause_ids.len(),
        "affected_one_based_clause_ids": &anchor.affected_one_based_clause_ids,
        "cleared_round_start_residual_count": anchor.cleared_round_start_residual_one_based_clause_ids.len(),
        "cleared_round_start_residual_one_based_clause_ids": &anchor.cleared_round_start_residual_one_based_clause_ids,
        "cleared_baseline_residual_count": anchor.cleared_baseline_residual_one_based_clause_ids.len(),
        "cleared_baseline_residual_one_based_clause_ids": &anchor.cleared_baseline_residual_one_based_clause_ids,
        "retained_baseline_residual_count": anchor.retained_baseline_residual_one_based_clause_ids.len(),
        "retained_baseline_residual_one_based_clause_ids": &anchor.retained_baseline_residual_one_based_clause_ids,
        "introduced_residual_count": anchor.introduced_residual_one_based_clause_ids.len(),
        "introduced_residual_one_based_clause_ids": &anchor.introduced_residual_one_based_clause_ids,
        "frontier_covered_introduced_residual_count": frontier_covered.as_ref().map(Vec::len),
        "frontier_covered_introduced_one_based_clause_ids": frontier_covered,
        "frontier_uncovered_introduced_residual_count": frontier_uncovered.as_ref().map(Vec::len),
        "frontier_uncovered_introduced_one_based_clause_ids": frontier_uncovered,
        "authority": diagnostic_authority_json(),
    })
}

fn collect_frontier_materializer_ledger(
    formula: &RawFormula,
    assignment: &[bool],
    target_residual_clause: usize,
    radius_free_vars: &BTreeSet<usize>,
    backbone: &ResidualSideEffectBackbone,
    candidates: &BackfillCandidateReport,
) -> Result<Vec<FrontierMaterializerLedgerRow>> {
    let mut rows: BTreeMap<usize, FrontierMaterializerLedgerRow> = BTreeMap::new();
    let target_clause = formula
        .clauses
        .get(target_residual_clause - 1)
        .with_context(|| format!("target residual clause {target_residual_clause} out of range"))?;
    for &lit in target_clause {
        let one_based_var = lit.unsigned_abs() as usize;
        record_frontier_materializer_var(
            &mut rows,
            formula.num_vars,
            assignment,
            radius_free_vars,
            one_based_var,
            0,
            "target_residual_clause",
            None,
            Some(target_residual_clause),
        )?;
    }

    for clause in &candidates.clauses {
        for &one_based_var in &clause.original_clause_vars {
            record_frontier_materializer_var(
                &mut rows,
                formula.num_vars,
                assignment,
                radius_free_vars,
                one_based_var,
                clause.occurrence_count,
                "frontier_clause_var",
                None,
                Some(clause.one_based_clause_id),
            )?;
        }
        for &one_based_var in &clause.introducing_candidate_vars {
            record_frontier_materializer_var(
                &mut rows,
                formula.num_vars,
                assignment,
                radius_free_vars,
                one_based_var,
                clause.occurrence_count,
                "frontier_introducing_candidate",
                None,
                Some(clause.one_based_clause_id),
            )?;
        }
        for &one_based_var in &clause.already_introducing_candidate_vars {
            record_frontier_materializer_var(
                &mut rows,
                formula.num_vars,
                assignment,
                radius_free_vars,
                one_based_var,
                clause.occurrence_count,
                "frontier_already_introducing_candidate",
                None,
                Some(clause.one_based_clause_id),
            )?;
        }
        for &one_based_var in &clause.new_backfill_vars {
            record_frontier_materializer_var(
                &mut rows,
                formula.num_vars,
                assignment,
                radius_free_vars,
                one_based_var,
                clause.occurrence_count,
                "frontier_new_backfill_candidate",
                None,
                Some(clause.one_based_clause_id),
            )?;
        }
    }
    for (&one_based_var, &occurrences) in &candidates.candidate_var_occurrence_counts {
        record_frontier_materializer_var(
            &mut rows,
            formula.num_vars,
            assignment,
            radius_free_vars,
            one_based_var,
            occurrences,
            "frontier_candidate_occurrence",
            None,
            None,
        )?;
    }

    for anchor in &backbone.anchors {
        let target_related = anchor
            .candidate_one_based_clause_ids
            .contains(&target_residual_clause)
            || anchor
                .candidate_residual_one_based_clause_ids
                .contains(&target_residual_clause)
            || anchor
                .affected_one_based_clause_ids
                .contains(&target_residual_clause)
            || anchor
                .retained_baseline_residual_one_based_clause_ids
                .contains(&target_residual_clause);
        if !target_related {
            continue;
        }
        for &(one_based_var, _) in &anchor.one_based_set_values {
            record_frontier_materializer_var(
                &mut rows,
                formula.num_vars,
                assignment,
                radius_free_vars,
                one_based_var,
                0,
                "target_related_anchor_set_value",
                Some(&anchor.anchor_id),
                Some(target_residual_clause),
            )?;
        }
    }

    let mut rows: Vec<_> = rows
        .into_values()
        .map(|mut row| {
            row.score = frontier_materializer_score(&row);
            row
        })
        .collect();
    rows.sort_by(|left, right| {
        right
            .score
            .cmp(&left.score)
            .then_with(|| left.one_based_var.cmp(&right.one_based_var))
    });
    Ok(rows)
}

fn record_frontier_materializer_var(
    rows: &mut BTreeMap<usize, FrontierMaterializerLedgerRow>,
    num_vars: usize,
    assignment: &[bool],
    radius_free_vars: &BTreeSet<usize>,
    one_based_var: usize,
    frontier_occurrences: usize,
    source_tag: &str,
    anchor_id: Option<&str>,
    related_clause_id: Option<usize>,
) -> Result<()> {
    if one_based_var == 0 || one_based_var > num_vars {
        bail!("frontier materializer variable {one_based_var} is out of range 1..={num_vars}");
    }
    let var = one_based_var - 1;
    let row = rows
        .entry(one_based_var)
        .or_insert_with(|| FrontierMaterializerLedgerRow {
            one_based_var,
            current_value: assignment[var],
            outside_radius: !radius_free_vars.contains(&var),
            frontier_occurrences: 0,
            source_tags: BTreeSet::new(),
            anchor_ids: BTreeSet::new(),
            related_clause_ids: BTreeSet::new(),
            score: 0,
        });
    row.frontier_occurrences = row
        .frontier_occurrences
        .saturating_add(frontier_occurrences);
    row.source_tags.insert(source_tag.to_string());
    if let Some(anchor_id) = anchor_id {
        row.anchor_ids.insert(anchor_id.to_string());
    }
    if let Some(clause_id) = related_clause_id {
        row.related_clause_ids.insert(clause_id);
    }
    Ok(())
}

fn frontier_materializer_score(row: &FrontierMaterializerLedgerRow) -> usize {
    let outside = if row.outside_radius { 1_000_000 } else { 0 };
    outside
        + row.frontier_occurrences.saturating_mul(1_000)
        + row.source_tags.len().saturating_mul(100)
        + row.anchor_ids.len().saturating_mul(10)
        + row.related_clause_ids.len()
}

fn frontier_materializer_ledger_row_json(row: &FrontierMaterializerLedgerRow) -> JsonValue {
    json!({
        "one_based_var": row.one_based_var,
        "current_value": row.current_value,
        "outside_radius": row.outside_radius,
        "frontier_occurrences": row.frontier_occurrences,
        "source_tags": row.source_tags.iter().cloned().collect::<Vec<_>>(),
        "anchor_ids": row.anchor_ids.iter().cloned().collect::<Vec<_>>(),
        "related_one_based_clause_ids": row.related_clause_ids.iter().copied().collect::<Vec<_>>(),
        "score": row.score,
        "authority": diagnostic_authority_json(),
    })
}

fn frontier_materializer_windows(
    target_residual_clause: usize,
    selected_one_based_vars: &[usize],
    window_size: usize,
    window_limit: usize,
) -> Vec<Window> {
    let mut windows = Vec::new();
    let mut current = Vec::with_capacity(window_size);
    collect_frontier_materializer_windows(
        target_residual_clause,
        selected_one_based_vars,
        window_size,
        0,
        &mut current,
        window_limit,
        &mut windows,
    );
    windows
}

fn collect_frontier_materializer_windows(
    target_residual_clause: usize,
    selected_one_based_vars: &[usize],
    size: usize,
    start: usize,
    current: &mut Vec<usize>,
    limit: usize,
    windows: &mut Vec<Window>,
) {
    if windows.len() >= limit {
        return;
    }
    if current.len() == size {
        let one_based_vars = current.clone();
        let name = format!(
            "frontier-c{}-s{}-{}",
            target_residual_clause,
            size,
            one_based_vars
                .iter()
                .map(|var| format!("v{var}"))
                .collect::<Vec<_>>()
                .join("-")
        );
        windows.push(Window {
            name,
            one_based_vars,
        });
        return;
    }
    for idx in start..selected_one_based_vars.len() {
        current.push(selected_one_based_vars[idx]);
        collect_frontier_materializer_windows(
            target_residual_clause,
            selected_one_based_vars,
            size,
            idx + 1,
            current,
            limit,
            windows,
        );
        current.pop();
        if windows.len() >= limit {
            return;
        }
    }
}

fn validate_residual_side_effect_frontier_report(
    path: &Path,
    report: &JsonValue,
    formula: &RawFormula,
    target_sha256: &str,
    current_repo_head: &str,
    side_effect_report_sha256: &str,
) -> Result<ResidualSideEffectFrontierSummary> {
    let schema = report
        .get("schema")
        .and_then(JsonValue::as_str)
        .context("introduced-clause-backfill-frontier report missing string schema")?;
    if schema != "ay.satcomp-circuit-introduced-clause-backfill-frontier/v1" {
        bail!(
            "introduced-clause-backfill-frontier report schema must be ay.satcomp-circuit-introduced-clause-backfill-frontier/v1; got {schema}"
        );
    }
    let source_repo_head = report
        .pointer("/source/repo_head")
        .and_then(JsonValue::as_str)
        .context("introduced-clause-backfill-frontier report source.repo_head must be a string")?;
    if source_repo_head != current_repo_head {
        bail!(
            "introduced-clause-backfill-frontier report source.repo_head {source_repo_head} is stale; current git HEAD is {current_repo_head}"
        );
    }
    let source = report
        .get("source")
        .context("introduced-clause-backfill-frontier report missing source object")?;
    validate_source_ay_build_current(source, "introduced-clause-backfill-frontier report source")?;
    let input = report
        .get("input")
        .context("introduced-clause-backfill-frontier report missing input object")?;
    input
        .as_object()
        .context("introduced-clause-backfill-frontier report input must be an object")?;
    let input_num_vars = report_usize_field(input, "num_vars", "input.num_vars")?;
    if input_num_vars != formula.num_vars {
        bail!(
            "introduced-clause-backfill-frontier report input.num_vars {} does not match target CNF {}",
            input_num_vars,
            formula.num_vars
        );
    }
    let input_num_clauses = report_usize_field(input, "num_clauses", "input.num_clauses")?;
    if input_num_clauses != formula.clauses.len() {
        bail!(
            "introduced-clause-backfill-frontier report input.num_clauses {} does not match target CNF {}",
            input_num_clauses,
            formula.clauses.len()
        );
    }
    let input_sha256 = input
        .get("sha256")
        .and_then(JsonValue::as_str)
        .context("introduced-clause-backfill-frontier report input.sha256 must be a string")?;
    if input_sha256 != target_sha256 {
        bail!(
            "introduced-clause-backfill-frontier report input.sha256 {input_sha256} does not match target CNF {target_sha256}"
        );
    }
    let authority = report
        .get("authority")
        .context("introduced-clause-backfill-frontier report missing authority object")?;
    validate_diagnostic_authority_object(
        authority,
        "introduced-clause-backfill-frontier report authority",
    )?;
    let verdict = report
        .get("verdict")
        .context("introduced-clause-backfill-frontier report missing verdict object")?;
    validate_diagnostic_verdict_authority(
        verdict,
        "introduced-clause-backfill-frontier report verdict",
    )?;
    let assignment_report = report.get("assignment_local_search_report").context(
        "introduced-clause-backfill-frontier report missing assignment_local_search_report object",
    )?;
    assignment_report.as_object().context(
        "introduced-clause-backfill-frontier report assignment_local_search_report must be an object",
    )?;
    let assignment_report_sha = assignment_report
        .get("sha256")
        .and_then(JsonValue::as_str)
        .context(
            "introduced-clause-backfill-frontier report assignment_local_search_report.sha256 must be a string",
        )?;
    if assignment_report_sha != side_effect_report_sha256 {
        bail!(
            "introduced-clause-backfill-frontier report assignment_local_search_report.sha256 {assignment_report_sha} does not match side-effect report {side_effect_report_sha256}"
        );
    }
    validate_assignment_local_search_report_provenance_object(
        assignment_report,
        current_repo_head,
        "introduced-clause-backfill-frontier report assignment_local_search_report",
    )?;
    let introduced = report
        .get("introduced_clauses")
        .context("introduced-clause-backfill-frontier report missing introduced_clauses object")?;
    introduced.as_object().context(
        "introduced-clause-backfill-frontier report introduced_clauses must be an object",
    )?;
    let mut introduced_ids = if introduced
        .get("unique_introduced_one_based_clause_ids")
        .is_some()
    {
        json_usize_array(introduced, "unique_introduced_one_based_clause_ids")?
    } else if introduced.get("one_based_clause_ids").is_some() {
        json_usize_array(introduced, "one_based_clause_ids")?
    } else {
        introduced
            .get("clauses")
            .and_then(JsonValue::as_array)
            .context(
                "introduced-clause-backfill-frontier report introduced_clauses must contain unique_introduced_one_based_clause_ids, one_based_clause_ids, or clauses",
            )?
            .iter()
            .enumerate()
            .map(|(idx, clause)| {
                report_usize_field(
                    clause,
                    "one_based_clause_id",
                    &format!("introduced_clauses.clauses[{idx}].one_based_clause_id"),
                )
            })
            .collect::<Result<Vec<_>>>()?
    };
    introduced_ids.sort_unstable();
    ensure_unique_usizes(
        &introduced_ids,
        "introduced_clauses.unique_introduced_one_based_clause_ids",
    )?;
    validate_one_based_clause_ids(
        &introduced_ids,
        formula.clauses.len(),
        "introduced_clauses.unique_introduced_one_based_clause_ids",
    )?;
    validate_optional_usize_count(
        introduced,
        "unique_introduced_clause_count",
        introduced_ids.len(),
        "introduced_clauses.unique_introduced_clause_count",
    )?;
    if let Some(clauses) = introduced.get("clauses").and_then(JsonValue::as_array) {
        for (idx, clause) in clauses.iter().enumerate() {
            clause
                .as_object()
                .with_context(|| format!("introduced_clauses.clauses[{idx}] must be an object"))?;
            if let Some(authority) = clause.get("authority") {
                validate_diagnostic_authority_object(
                    authority,
                    &format!("introduced_clauses.clauses[{idx}].authority"),
                )?;
            }
            let clause_id = report_usize_field(
                clause,
                "one_based_clause_id",
                &format!("introduced_clauses.clauses[{idx}].one_based_clause_id"),
            )?;
            validate_one_based_clause_ids(
                &[clause_id],
                formula.clauses.len(),
                "introduced_clauses.clauses[].one_based_clause_id",
            )?;
            if let Some(lits_value) = clause.get("original_clause_lits") {
                let lits = json_i32_array_required(
                    &json!({ "original_clause_lits": lits_value }),
                    "original_clause_lits",
                )?;
                if lits != formula.clauses[clause_id - 1] {
                    bail!(
                        "introduced_clauses.clauses[{idx}] original_clause_lits do not match target CNF clause {clause_id}"
                    );
                }
            }
        }
    }
    Ok(ResidualSideEffectFrontierSummary {
        path: path.to_path_buf(),
        sha256: sha256_file(path)?,
        source_repo_head: source_repo_head.to_string(),
        assignment_local_search_report_sha256: assignment_report_sha.to_string(),
        unique_introduced_one_based_clause_ids: introduced_ids.into_iter().collect(),
    })
}

fn validate_assignment_local_search_report_for_backfill(
    report: &JsonValue,
    formula: &RawFormula,
    target_sha256: &str,
    current_repo_head: &str,
) -> Result<()> {
    let schema = report
        .get("schema")
        .and_then(JsonValue::as_str)
        .context("assignment-local-search report missing string schema")?;
    if schema != "ay.satcomp-circuit-assignment-local-search/v1" {
        bail!("assignment-local-search report has unsupported schema: {schema}");
    }
    let report_repo_head = report
        .pointer("/source/repo_head")
        .and_then(JsonValue::as_str)
        .context("assignment-local-search report source.repo_head must be a string")?;
    if report_repo_head != current_repo_head {
        bail!(
            "assignment-local-search report source.repo_head {report_repo_head} is stale; current git HEAD is {current_repo_head}"
        );
    }
    let source = report
        .get("source")
        .context("assignment-local-search report missing source object")?;
    validate_source_ay_build_current(source, "assignment-local-search report source")?;
    let authority = report
        .get("authority")
        .context("assignment-local-search report missing authority object")?;
    validate_diagnostic_authority_object(authority, "assignment-local-search report authority")?;

    let input = report
        .get("input")
        .context("assignment-local-search report missing input object")?;
    let input_num_vars = report_usize_field(input, "num_vars", "input.num_vars")?;
    if input_num_vars != formula.num_vars {
        bail!(
            "assignment-local-search report input.num_vars {} does not match target CNF {}",
            input_num_vars,
            formula.num_vars
        );
    }
    let input_num_clauses = report_usize_field(input, "num_clauses", "input.num_clauses")?;
    if input_num_clauses != formula.clauses.len() {
        bail!(
            "assignment-local-search report input.num_clauses {} does not match target CNF {}",
            input_num_clauses,
            formula.clauses.len()
        );
    }
    let input_sha256 = input
        .get("sha256")
        .and_then(JsonValue::as_str)
        .context("assignment-local-search report missing input.sha256")?;
    if input_sha256 != target_sha256 {
        bail!(
            "assignment-local-search report input.sha256 {input_sha256} does not match target CNF {target_sha256}"
        );
    }

    let verdict = report
        .get("verdict")
        .context("assignment-local-search report missing verdict object")?;
    validate_false_authority_flags(verdict, "assignment-local-search report verdict")?;
    Ok(())
}

fn validate_assignment_local_search_report_provenance_object(
    object: &JsonValue,
    current_repo_head: &str,
    label: &str,
) -> Result<()> {
    object
        .as_object()
        .with_context(|| format!("{label} must be an object"))?;
    let schema = object
        .get("schema")
        .and_then(JsonValue::as_str)
        .with_context(|| format!("{label}.schema must be a string"))?;
    if schema != "ay.satcomp-circuit-assignment-local-search/v1" {
        bail!("{label}.schema must be ay.satcomp-circuit-assignment-local-search/v1; got {schema}");
    }
    let sha256 = object
        .get("sha256")
        .and_then(JsonValue::as_str)
        .with_context(|| format!("{label}.sha256 must be a string"))?;
    if sha256.trim().is_empty() {
        bail!("{label}.sha256 must not be empty");
    }
    let repo_head = object
        .get("repo_head")
        .and_then(JsonValue::as_str)
        .with_context(|| format!("{label}.repo_head must be a string"))?;
    if repo_head != current_repo_head {
        bail!("{label}.repo_head {repo_head} is stale; current git HEAD is {current_repo_head}");
    }
    let ay_build = object
        .get("ay_build")
        .with_context(|| format!("{label}.ay_build must be an object"))?;
    validate_ay_build_current(ay_build, &format!("{label}.ay_build"))?;
    Ok(())
}

fn validate_source_ay_build_current(source: &JsonValue, label: &str) -> Result<()> {
    source
        .as_object()
        .with_context(|| format!("{label} must be an object"))?;
    let ay_build = source
        .get("ay_build")
        .with_context(|| format!("{label}.ay_build must be an object"))?;
    validate_ay_build_current(ay_build, &format!("{label}.ay_build"))
}

fn validate_ay_build_current(object: &JsonValue, label: &str) -> Result<()> {
    object
        .as_object()
        .with_context(|| format!("{label} must be an object"))?;
    let commit = object
        .get("commit")
        .and_then(JsonValue::as_str)
        .with_context(|| format!("{label}.commit must be a string"))?;
    if commit != BUILD_INFO.commit {
        bail!(
            "{label}.commit {commit} is stale; current ay build commit is {}",
            BUILD_INFO.commit
        );
    }
    let stamp = object
        .get("stamp")
        .and_then(JsonValue::as_str)
        .with_context(|| format!("{label}.stamp must be a string"))?;
    if stamp != BUILD_INFO.stamp {
        bail!(
            "{label}.stamp {stamp} is stale; current ay build stamp is {}",
            BUILD_INFO.stamp
        );
    }
    Ok(())
}

fn report_usize_field(object: &JsonValue, field: &str, label: &str) -> Result<usize> {
    let raw = object
        .get(field)
        .and_then(JsonValue::as_u64)
        .with_context(|| format!("{label} must be an unsigned integer"))?;
    usize::try_from(raw).with_context(|| format!("{label} out of usize range"))
}

fn optional_report_usize_field(
    object: &JsonValue,
    field: &str,
    label: &str,
) -> Result<Option<usize>> {
    let Some(value) = object.get(field) else {
        return Ok(None);
    };
    let raw = value
        .as_u64()
        .with_context(|| format!("{label} must be an unsigned integer"))?;
    Ok(Some(
        usize::try_from(raw).with_context(|| format!("{label} out of usize range"))?,
    ))
}

fn optional_report_isize_field(
    object: &JsonValue,
    field: &str,
    label: &str,
) -> Result<Option<isize>> {
    let Some(value) = object.get(field) else {
        return Ok(None);
    };
    let raw = value
        .as_i64()
        .with_context(|| format!("{label} must be an integer"))?;
    Ok(Some(
        isize::try_from(raw).with_context(|| format!("{label} out of isize range"))?,
    ))
}

fn collect_introduced_clause_backfill_frontier(
    formula: &RawFormula,
    report: &JsonValue,
) -> Result<BackfillFrontierReport> {
    let rounds = report
        .pointer("/search/source_frame_choice_rounds")
        .and_then(JsonValue::as_array)
        .context(
            "assignment-local-search report missing /search/source_frame_choice_rounds array",
        )?;
    let mut frontier = BackfillFrontierReport {
        source_frame_choice_rounds_seen: rounds.len(),
        ..BackfillFrontierReport::default()
    };
    for (round_idx, round) in rounds.iter().enumerate() {
        let round_number = if round.get("round").is_some() {
            report_usize_field(round, "round", "source_frame_choice_rounds[].round")?
        } else {
            round_idx + 1
        };
        let top_candidates = round
            .get("top_candidates")
            .and_then(JsonValue::as_array)
            .with_context(|| {
                format!("source_frame_choice_rounds[{round_idx}] missing top_candidates array")
            })?;
        frontier.top_candidates_seen += top_candidates.len();
        for (candidate_idx, candidate) in top_candidates.iter().enumerate() {
            let summary_value = candidate.get("side_effect_summary").with_context(|| {
                format!(
                    "source_frame_choice_rounds[{round_idx}].top_candidates[{candidate_idx}] missing side_effect_summary"
                )
            })?;
            summary_value.as_object().with_context(|| {
                    format!(
                        "source_frame_choice_rounds[{round_idx}].top_candidates[{candidate_idx}] side_effect_summary must be an object"
                    )
                })?;
            let summary_authority = summary_value
                .get("authority")
                .and_then(JsonValue::as_str)
                .with_context(|| {
                    format!(
                        "source_frame_choice_rounds[{round_idx}].top_candidates[{candidate_idx}] side_effect_summary.authority must be diagnostic_only"
                    )
                })?;
            if summary_authority != "diagnostic_only" {
                bail!(
                    "source_frame_choice_rounds[{round_idx}].top_candidates[{candidate_idx}] side_effect_summary.authority must be diagnostic_only"
                );
            }
            frontier.top_candidates_with_side_effect_summary += 1;
            let introduced_ids = json_usize_array_field(
                candidate,
                summary_value,
                "introduced_residual_one_based_clause_ids",
            )
            .with_context(|| {
                format!(
                    "source_frame_choice_rounds[{round_idx}].top_candidates[{candidate_idx}] introduced IDs"
                )
            })?;
            if introduced_ids.is_empty() {
                continue;
            }
            validate_one_based_clause_ids(
                &introduced_ids,
                formula.clauses.len(),
                "introduced_residual_one_based_clause_ids",
            )?;
            frontier.top_candidates_with_introductions += 1;
            let candidate_set_values = parse_candidate_set_values(candidate).with_context(|| {
                format!(
                    "source_frame_choice_rounds[{round_idx}].top_candidates[{candidate_idx}] set values"
                )
            })?;
            for (var, _) in &candidate_set_values {
                if *var > formula.num_vars {
                    bail!(
                        "source_frame_choice_rounds[{round_idx}].top_candidates[{candidate_idx}] one_based_set_values var {} is out of range 1..={}",
                        var,
                        formula.num_vars
                    );
                }
            }
            let candidate_vars = candidate_set_values
                .iter()
                .map(|(var, _)| *var)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            let source_frame_row_ids = json_string_array(candidate, "source_frame_row_ids")?;
            let candidate_clause_ids = json_usize_array(candidate, "one_based_clause_ids")?;
            validate_one_based_clause_ids(
                &candidate_clause_ids,
                formula.clauses.len(),
                "one_based_clause_ids",
            )?;
            let candidate_residual_count = optional_report_usize_field(
                candidate,
                "residual_falsified_clause_count",
                "residual_falsified_clause_count",
            )?;
            let net_residual_delta = optional_report_isize_field(
                summary_value,
                "net_residual_delta",
                "side_effect_summary.net_residual_delta",
            )?;
            let introduced_residual_count = optional_report_usize_field(
                summary_value,
                "introduced_residual_count",
                "side_effect_summary.introduced_residual_count",
            )?;
            let affected_ids =
                json_usize_array_field(candidate, summary_value, "affected_one_based_clause_ids")?;
            validate_one_based_clause_ids(
                &affected_ids,
                formula.clauses.len(),
                "affected_one_based_clause_ids",
            )?;
            let cleared_ids = json_usize_array_field(
                candidate,
                summary_value,
                "cleared_round_start_residual_one_based_clause_ids",
            )?;
            validate_one_based_clause_ids(
                &cleared_ids,
                formula.clauses.len(),
                "cleared_round_start_residual_one_based_clause_ids",
            )?;
            for introduced_clause_id in introduced_ids {
                let original_clause_lits = formula.clauses[introduced_clause_id - 1].clone();
                let original_clause_vars = original_clause_lits
                    .iter()
                    .map(|lit| lit_var(*lit))
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect::<Vec<_>>();
                frontier.rows.push(BackfillFrontierRow {
                    round: round_number,
                    top_candidate_rank: candidate_idx + 1,
                    introduced_clause_id_one_based: introduced_clause_id,
                    original_clause_lits,
                    original_clause_vars,
                    candidate_one_based_set_values: candidate_set_values.clone(),
                    candidate_one_based_vars: candidate_vars.clone(),
                    source_frame_row_ids: source_frame_row_ids.clone(),
                    candidate_one_based_clause_ids: candidate_clause_ids.clone(),
                    candidate_residual_falsified_clause_count: candidate_residual_count,
                    net_residual_delta,
                    introduced_residual_count,
                    affected_one_based_clause_ids: affected_ids.clone(),
                    cleared_one_based_clause_ids: cleared_ids.clone(),
                });
            }
        }
    }
    Ok(frontier)
}

fn json_usize_array_field(
    candidate: &JsonValue,
    object: &JsonValue,
    field: &str,
) -> Result<Vec<usize>> {
    object
        .get(field)
        .map(|_| json_usize_array(object, field))
        .unwrap_or_else(|| json_usize_array(candidate, field))
}

fn json_usize_array(object: &JsonValue, field: &str) -> Result<Vec<usize>> {
    let Some(value) = object.get(field) else {
        return Ok(Vec::new());
    };
    let entries = value
        .as_array()
        .with_context(|| format!("{field} must be an array"))?;
    entries
        .iter()
        .enumerate()
        .map(|(idx, value)| {
            let raw = value
                .as_u64()
                .with_context(|| format!("{field}[{idx}] must be an unsigned integer"))?;
            usize::try_from(raw).with_context(|| format!("{field}[{idx}] out of usize range"))
        })
        .collect()
}

fn validate_one_based_clause_ids(ids: &[usize], num_clauses: usize, label: &str) -> Result<()> {
    for (idx, clause_id) in ids.iter().enumerate() {
        if *clause_id == 0 || *clause_id > num_clauses {
            bail!("{label}[{idx}] clause ID {clause_id} is out of range 1..={num_clauses}");
        }
    }
    Ok(())
}

fn json_string_array(object: &JsonValue, field: &str) -> Result<Vec<String>> {
    let Some(value) = object.get(field) else {
        return Ok(Vec::new());
    };
    let entries = value
        .as_array()
        .with_context(|| format!("{field} must be an array"))?;
    entries
        .iter()
        .enumerate()
        .map(|(idx, value)| {
            value
                .as_str()
                .map(str::to_string)
                .with_context(|| format!("{field}[{idx}] must be a string"))
        })
        .collect()
}

fn parse_candidate_set_values(candidate: &JsonValue) -> Result<Vec<(usize, bool)>> {
    let Some(values) = candidate.get("one_based_set_values") else {
        return Ok(Vec::new());
    };
    let entries = values
        .as_array()
        .context("one_based_set_values must be an array")?;
    let mut parsed = Vec::new();
    for (idx, entry) in entries.iter().enumerate() {
        let var = entry
            .get("var")
            .and_then(JsonValue::as_u64)
            .with_context(|| format!("one_based_set_values[{idx}] missing var"))?;
        let var = usize::try_from(var)
            .with_context(|| format!("one_based_set_values[{idx}].var out of usize range"))?;
        if var == 0 {
            bail!("one_based_set_values[{idx}].var must be one-based");
        }
        let value = entry
            .get("value")
            .and_then(JsonValue::as_bool)
            .with_context(|| format!("one_based_set_values[{idx}] missing Boolean value"))?;
        parsed.push((var, value));
    }
    Ok(parsed)
}

fn backfill_frontier_row_json(row: &BackfillFrontierRow) -> JsonValue {
    json!({
        "round": row.round,
        "top_candidate_rank": row.top_candidate_rank,
        "introduced_one_based_clause_id": row.introduced_clause_id_one_based,
        "original_clause_lits": &row.original_clause_lits,
        "original_clause_one_based_vars": &row.original_clause_vars,
        "candidate_one_based_set_values": row.candidate_one_based_set_values.iter().map(|(var, value)| json!({"var": var, "value": value})).collect::<Vec<_>>(),
        "candidate_one_based_vars": &row.candidate_one_based_vars,
        "source_frame_row_ids": &row.source_frame_row_ids,
        "candidate_one_based_clause_ids": &row.candidate_one_based_clause_ids,
        "candidate_residual_falsified_clause_count": row.candidate_residual_falsified_clause_count,
        "net_residual_delta": row.net_residual_delta,
        "introduced_residual_count": row.introduced_residual_count,
        "affected_one_based_clause_ids": &row.affected_one_based_clause_ids,
        "cleared_round_start_residual_one_based_clause_ids": &row.cleared_one_based_clause_ids,
        "authority": {
            "classification": "diagnostic_only",
            "route_admitted": false,
            "sat_output_authority": false,
            "model_output_authority": false,
            "proof_output_authority": false,
            "solver_verdict_authority": false,
            "sat_comp_progress_claim": false,
        },
    })
}

fn backfill_frontier_clause_groups(rows: &[BackfillFrontierRow]) -> Vec<JsonValue> {
    let mut groups: BTreeMap<
        usize,
        (
            Vec<i32>,
            BTreeSet<usize>,
            BTreeSet<usize>,
            BTreeSet<String>,
            usize,
        ),
    > = BTreeMap::new();
    for row in rows {
        let entry = groups
            .entry(row.introduced_clause_id_one_based)
            .or_insert_with(|| {
                (
                    row.original_clause_lits.clone(),
                    row.original_clause_vars.iter().copied().collect(),
                    BTreeSet::new(),
                    BTreeSet::new(),
                    0,
                )
            });
        entry.2.extend(row.candidate_one_based_vars.iter().copied());
        entry.3.extend(row.source_frame_row_ids.iter().cloned());
        entry.4 += 1;
    }
    groups
        .into_iter()
        .map(
            |(
                clause_id,
                (
                    original_clause_lits,
                    original_clause_vars,
                    candidate_vars,
                    source_frame_row_ids,
                    occurrence_count,
                ),
            )| {
                json!({
                    "one_based_clause_id": clause_id,
                    "original_clause_lits": original_clause_lits,
                    "original_clause_one_based_vars": original_clause_vars.into_iter().collect::<Vec<_>>(),
                    "candidate_one_based_vars": candidate_vars.into_iter().collect::<Vec<_>>(),
                    "source_frame_row_id_samples": source_frame_row_ids.into_iter().take(16).collect::<Vec<_>>(),
                    "occurrence_count": occurrence_count,
                    "authority": {
                        "classification": "diagnostic_only",
                        "route_admitted": false,
                        "sat_output_authority": false,
                        "model_output_authority": false,
                        "proof_output_authority": false,
                        "solver_verdict_authority": false,
                        "sat_comp_progress_claim": false,
                    },
                })
            },
        )
        .collect()
}

fn write_backfill_frontier_tsv(path: &Path, rows: &[BackfillFrontierRow]) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let mut file =
        File::create(path).with_context(|| format!("failed to create '{}'", path.display()))?;
    writeln!(
        file,
        "one_based_clause_id\toriginal_clause_lits\toriginal_clause_vars\tcandidate_one_based_vars"
    )?;
    let mut groups: BTreeMap<usize, (Vec<i32>, BTreeSet<usize>, BTreeSet<usize>)> = BTreeMap::new();
    for row in rows {
        let entry = groups
            .entry(row.introduced_clause_id_one_based)
            .or_insert_with(|| {
                (
                    row.original_clause_lits.clone(),
                    row.original_clause_vars.iter().copied().collect(),
                    BTreeSet::new(),
                )
            });
        entry.2.extend(row.candidate_one_based_vars.iter().copied());
    }
    for (clause_id, (original_clause_lits, original_clause_vars, candidate_vars)) in groups {
        writeln!(
            file,
            "{}\t{}\t{}\t{}",
            clause_id,
            join_i32s(&original_clause_lits),
            join_usizes(&original_clause_vars.into_iter().collect::<Vec<_>>()),
            join_usizes(&candidate_vars.into_iter().collect::<Vec<_>>()),
        )?;
    }
    Ok(())
}

fn validate_introduced_clause_backfill_frontier_report_for_candidates(
    report: &JsonValue,
    current_repo_head: &str,
) -> Result<(usize, usize)> {
    let schema = report
        .get("schema")
        .and_then(JsonValue::as_str)
        .context("introduced-clause-backfill-frontier report missing string schema")?;
    if schema != "ay.satcomp-circuit-introduced-clause-backfill-frontier/v1" {
        bail!(
            "introduced-clause-backfill-frontier report schema must be ay.satcomp-circuit-introduced-clause-backfill-frontier/v1; got {schema}"
        );
    }
    let report_repo_head = report
        .pointer("/source/repo_head")
        .and_then(JsonValue::as_str)
        .context("introduced-clause-backfill-frontier report source.repo_head must be a string")?;
    if report_repo_head != current_repo_head {
        bail!(
            "introduced-clause-backfill-frontier report source.repo_head {report_repo_head} is stale; current git HEAD is {current_repo_head}"
        );
    }
    let source = report
        .get("source")
        .context("introduced-clause-backfill-frontier report missing source object")?;
    validate_source_ay_build_current(source, "introduced-clause-backfill-frontier report source")?;

    let input = report
        .get("input")
        .context("introduced-clause-backfill-frontier report missing input object")?;
    input
        .as_object()
        .context("introduced-clause-backfill-frontier report input must be an object")?;
    let input_path = input
        .get("path")
        .and_then(JsonValue::as_str)
        .context("introduced-clause-backfill-frontier report input.path must be a string")?;
    if input_path.trim().is_empty() {
        bail!("introduced-clause-backfill-frontier report input.path must not be empty");
    }
    let input_sha256 = input
        .get("sha256")
        .and_then(JsonValue::as_str)
        .context("introduced-clause-backfill-frontier report input.sha256 must be a string")?;
    if input_sha256.trim().is_empty() {
        bail!("introduced-clause-backfill-frontier report input.sha256 must not be empty");
    }
    let num_vars = report_usize_field(input, "num_vars", "input.num_vars")?;
    let num_clauses = report_usize_field(input, "num_clauses", "input.num_clauses")?;

    let authority = report
        .get("authority")
        .context("introduced-clause-backfill-frontier report missing authority object")?;
    validate_diagnostic_authority_object(
        authority,
        "introduced-clause-backfill-frontier report authority",
    )?;
    let verdict = report
        .get("verdict")
        .context("introduced-clause-backfill-frontier report missing verdict object")?;
    validate_diagnostic_verdict_authority(
        verdict,
        "introduced-clause-backfill-frontier report verdict",
    )?;
    let assignment_report = report.get("assignment_local_search_report").context(
        "introduced-clause-backfill-frontier report missing assignment_local_search_report object",
    )?;
    validate_assignment_local_search_report_provenance_object(
        assignment_report,
        current_repo_head,
        "introduced-clause-backfill-frontier report assignment_local_search_report",
    )?;

    let introduced = report
        .get("introduced_clauses")
        .context("introduced-clause-backfill-frontier report missing introduced_clauses object")?;
    introduced.as_object().context(
        "introduced-clause-backfill-frontier report introduced_clauses must be an object",
    )?;
    introduced
        .get("clauses")
        .and_then(JsonValue::as_array)
        .context(
        "introduced-clause-backfill-frontier report introduced_clauses.clauses must be an array",
    )?;

    Ok((num_vars, num_clauses))
}

fn collect_introduced_clause_backfill_candidates(
    report: &JsonValue,
    num_vars: usize,
    num_clauses: usize,
) -> Result<BackfillCandidateReport> {
    let clause_values = report
        .pointer("/introduced_clauses/clauses")
        .and_then(JsonValue::as_array)
        .context("introduced-clause-backfill-frontier report introduced_clauses.clauses must be an array")?;
    let mut candidates = BackfillCandidateReport::default();
    let mut seen_clause_ids = BTreeSet::new();
    for (idx, clause) in clause_values.iter().enumerate() {
        clause
            .as_object()
            .with_context(|| format!("introduced_clauses.clauses[{idx}] must be an object"))?;
        let authority = clause.get("authority").with_context(|| {
            format!("introduced_clauses.clauses[{idx}] missing authority object")
        })?;
        validate_diagnostic_authority_object(
            authority,
            &format!("introduced_clauses.clauses[{idx}].authority"),
        )?;
        let one_based_clause_id = report_usize_field(
            clause,
            "one_based_clause_id",
            &format!("introduced_clauses.clauses[{idx}].one_based_clause_id"),
        )?;
        validate_one_based_clause_ids(
            &[one_based_clause_id],
            num_clauses,
            "introduced_clauses.clauses[].one_based_clause_id",
        )?;
        if !seen_clause_ids.insert(one_based_clause_id) {
            bail!("introduced_clauses.clauses[{idx}] duplicates clause ID {one_based_clause_id}");
        }

        let original_clause_lits = json_i32_array_required(clause, "original_clause_lits")
            .with_context(|| format!("introduced_clauses.clauses[{idx}].original_clause_lits"))?;
        let mut vars_from_lits = BTreeSet::new();
        for (lit_idx, lit) in original_clause_lits.iter().enumerate() {
            if *lit == 0 {
                bail!(
                    "introduced_clauses.clauses[{idx}].original_clause_lits[{lit_idx}] must be nonzero"
                );
            }
            let var = lit_var(*lit);
            if var == 0 || var > num_vars {
                bail!(
                    "introduced_clauses.clauses[{idx}].original_clause_lits[{lit_idx}] var {var} is out of range 1..={num_vars}"
                );
            }
            vars_from_lits.insert(var);
        }

        let original_clause_vars =
            json_usize_array_required(clause, "original_clause_one_based_vars").with_context(
                || format!("introduced_clauses.clauses[{idx}].original_clause_one_based_vars"),
            )?;
        validate_one_based_vars(
            &original_clause_vars,
            num_vars,
            "introduced_clauses.clauses[].original_clause_one_based_vars",
        )?;
        ensure_unique_usizes(
            &original_clause_vars,
            "introduced_clauses.clauses[].original_clause_one_based_vars",
        )?;
        let original_clause_var_set: BTreeSet<usize> =
            original_clause_vars.iter().copied().collect();
        if original_clause_var_set != vars_from_lits {
            bail!(
                "introduced_clauses.clauses[{idx}] original_clause_one_based_vars do not match original_clause_lits vars"
            );
        }

        let introducing_candidate_vars =
            json_usize_array_required(clause, "candidate_one_based_vars").with_context(|| {
                format!("introduced_clauses.clauses[{idx}].candidate_one_based_vars")
            })?;
        validate_one_based_vars(
            &introducing_candidate_vars,
            num_vars,
            "introduced_clauses.clauses[].candidate_one_based_vars",
        )?;
        ensure_unique_usizes(
            &introducing_candidate_vars,
            "introduced_clauses.clauses[].candidate_one_based_vars",
        )?;
        let source_frame_row_id_samples = json_string_array(clause, "source_frame_row_id_samples")
            .with_context(|| {
                format!("introduced_clauses.clauses[{idx}].source_frame_row_id_samples")
            })?;
        let occurrence_count = report_usize_field(
            clause,
            "occurrence_count",
            &format!("introduced_clauses.clauses[{idx}].occurrence_count"),
        )?;

        candidates.clauses.push(BackfillCandidateClause {
            one_based_clause_id,
            original_clause_lits,
            original_clause_vars,
            introducing_candidate_vars,
            already_introducing_candidate_vars: Vec::new(),
            new_backfill_vars: Vec::new(),
            source_frame_row_id_samples,
            occurrence_count,
        });
    }

    let rows = report
        .pointer("/introduced_clauses/occurrences")
        .or_else(|| report.pointer("/introduced_clauses/rows"))
        .and_then(JsonValue::as_array);
    let mut row_candidate_vars_by_clause: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    let mut row_count_by_clause: BTreeMap<usize, usize> = BTreeMap::new();
    let mut row_sources_by_clause: BTreeMap<usize, BTreeSet<String>> = BTreeMap::new();
    if let Some(rows) = rows {
        let known_clause_ids: BTreeSet<_> = candidates
            .clauses
            .iter()
            .map(|clause| clause.one_based_clause_id)
            .collect();
        for (idx, row) in rows.iter().enumerate() {
            let authority = row
                .get("authority")
                .with_context(|| format!("introduced_clauses.rows[{idx}] missing authority"))?;
            validate_diagnostic_authority_object(
                authority,
                &format!("introduced_clauses.rows[{idx}].authority"),
            )?;
            let clause_id = row
                .get("introduced_one_based_clause_id")
                .or_else(|| row.get("one_based_clause_id"))
                .and_then(JsonValue::as_u64)
                .and_then(|value| usize::try_from(value).ok())
                .with_context(|| format!("introduced_clauses.rows[{idx}] missing clause id"))?;
            validate_one_based_clause_ids(
                &[clause_id],
                num_clauses,
                "introduced_clauses.rows[].introduced_one_based_clause_id",
            )?;
            if !known_clause_ids.contains(&clause_id) {
                bail!("introduced_clauses.rows[{idx}] references unknown clause {clause_id}");
            }
            let row_candidate_vars = json_usize_array(row, "candidate_one_based_vars")?;
            validate_one_based_vars(
                &row_candidate_vars,
                num_vars,
                "introduced_clauses.rows[].candidate_one_based_vars",
            )?;
            *row_count_by_clause.entry(clause_id).or_insert(0) += 1;
            for var in row_candidate_vars {
                row_candidate_vars_by_clause
                    .entry(clause_id)
                    .or_default()
                    .insert(var);
                candidates.candidate_vars.insert(var);
                candidates.introducing_candidate_vars.insert(var);
                candidates.candidate_clause_pairs.insert((var, clause_id));
                candidates.candidate_var_occurrences += 1;
                *candidates
                    .candidate_var_occurrence_counts
                    .entry(var)
                    .or_insert(0) += 1;
            }
            for row_id in json_string_array(row, "source_frame_row_ids")? {
                row_sources_by_clause
                    .entry(clause_id)
                    .or_default()
                    .insert(row_id);
            }
        }
    } else {
        for clause in &candidates.clauses {
            for &var in &clause.introducing_candidate_vars {
                candidates.candidate_vars.insert(var);
                candidates.introducing_candidate_vars.insert(var);
                candidates
                    .candidate_clause_pairs
                    .insert((var, clause.one_based_clause_id));
                candidates.candidate_var_occurrences += clause.occurrence_count;
                *candidates
                    .candidate_var_occurrence_counts
                    .entry(var)
                    .or_insert(0) += clause.occurrence_count;
            }
        }
    }

    for clause in &mut candidates.clauses {
        if let Some(row_vars) = row_candidate_vars_by_clause.remove(&clause.one_based_clause_id) {
            clause.introducing_candidate_vars = row_vars.into_iter().collect();
        }
        if let Some(row_count) = row_count_by_clause.remove(&clause.one_based_clause_id) {
            clause.occurrence_count = row_count;
        }
        if let Some(row_sources) = row_sources_by_clause.remove(&clause.one_based_clause_id) {
            clause.source_frame_row_id_samples = row_sources.into_iter().take(16).collect();
        }
        let original_clause_var_set: BTreeSet<_> =
            clause.original_clause_vars.iter().copied().collect();
        let introducing_candidate_var_set: BTreeSet<_> =
            clause.introducing_candidate_vars.iter().copied().collect();
        clause.already_introducing_candidate_vars = original_clause_var_set
            .intersection(&introducing_candidate_var_set)
            .copied()
            .collect();
        clause.new_backfill_vars = original_clause_var_set
            .difference(&introducing_candidate_var_set)
            .copied()
            .collect();
        candidates
            .already_introducing_candidate_vars
            .extend(clause.already_introducing_candidate_vars.iter().copied());
        candidates
            .new_backfill_vars
            .extend(clause.new_backfill_vars.iter().copied());
        candidates.window_vars.extend(
            original_clause_var_set
                .union(&introducing_candidate_var_set)
                .copied(),
        );
        candidates
            .introducing_candidate_vars_outside_clause_vars
            .extend(
                introducing_candidate_var_set
                    .difference(&original_clause_var_set)
                    .copied(),
            );
    }
    validate_backfill_candidate_aggregate_fields(report, &candidates)?;
    Ok(candidates)
}

fn validate_backfill_candidate_aggregate_fields(
    report: &JsonValue,
    candidates: &BackfillCandidateReport,
) -> Result<()> {
    let introduced = report
        .get("introduced_clauses")
        .context("introduced-clause-backfill-frontier report missing introduced_clauses object")?;
    let frontier_clause_vars: BTreeSet<usize> = candidates
        .clauses
        .iter()
        .flat_map(|clause| clause.original_clause_vars.iter().copied())
        .collect();
    validate_optional_usize_array_set(
        introduced,
        "frontier_clause_one_based_vars",
        &frontier_clause_vars,
        "introduced_clauses.frontier_clause_one_based_vars",
    )?;
    validate_optional_usize_count(
        introduced,
        "frontier_clause_var_count",
        frontier_clause_vars.len(),
        "introduced_clauses.frontier_clause_var_count",
    )?;
    validate_optional_usize_array_set(
        introduced,
        "candidate_one_based_vars",
        &candidates.introducing_candidate_vars,
        "introduced_clauses.candidate_one_based_vars",
    )?;
    validate_optional_usize_count(
        introduced,
        "candidate_var_count",
        candidates.introducing_candidate_vars.len(),
        "introduced_clauses.candidate_var_count",
    )?;
    let clause_ids: BTreeSet<usize> = candidates
        .clauses
        .iter()
        .map(|clause| clause.one_based_clause_id)
        .collect();
    validate_optional_usize_array_set(
        introduced,
        "one_based_clause_ids",
        &clause_ids,
        "introduced_clauses.one_based_clause_ids",
    )?;
    validate_optional_usize_array_set(
        introduced,
        "unique_introduced_one_based_clause_ids",
        &clause_ids,
        "introduced_clauses.unique_introduced_one_based_clause_ids",
    )?;
    validate_optional_usize_count(
        introduced,
        "unique_clause_count",
        candidates.clauses.len(),
        "introduced_clauses.unique_clause_count",
    )?;
    validate_optional_usize_count(
        introduced,
        "unique_introduced_clause_count",
        candidates.clauses.len(),
        "introduced_clauses.unique_introduced_clause_count",
    )?;
    Ok(())
}

fn validate_introduced_clause_backfill_candidates_report_for_search(
    report: &JsonValue,
    formula: &RawFormula,
    target_sha256: &str,
    current_repo_head: &str,
) -> Result<BackfillCandidateReport> {
    let schema = report
        .get("schema")
        .and_then(JsonValue::as_str)
        .context("introduced-clause-backfill-candidates report missing string schema")?;
    if schema != "ay.satcomp-circuit-introduced-clause-backfill-candidates/v1" {
        bail!(
            "introduced-clause-backfill-candidates report schema must be ay.satcomp-circuit-introduced-clause-backfill-candidates/v1; got {schema}"
        );
    }
    let report_repo_head = report
        .pointer("/source/repo_head")
        .and_then(JsonValue::as_str)
        .context(
            "introduced-clause-backfill-candidates report source.repo_head must be a string",
        )?;
    if report_repo_head != current_repo_head {
        bail!(
            "introduced-clause-backfill-candidates report source.repo_head {report_repo_head} is stale; current git HEAD is {current_repo_head}"
        );
    }
    let source = report
        .get("source")
        .context("introduced-clause-backfill-candidates report missing source object")?;
    validate_source_ay_build_current(
        source,
        "introduced-clause-backfill-candidates report source",
    )?;

    let input = report
        .get("input")
        .context("introduced-clause-backfill-candidates report missing input object")?;
    input
        .as_object()
        .context("introduced-clause-backfill-candidates report input must be an object")?;
    let input_num_vars = report_usize_field(input, "num_vars", "input.num_vars")?;
    if input_num_vars != formula.num_vars {
        bail!(
            "introduced-clause-backfill-candidates report input.num_vars {} does not match target CNF {}",
            input_num_vars,
            formula.num_vars
        );
    }
    let input_num_clauses = report_usize_field(input, "num_clauses", "input.num_clauses")?;
    if input_num_clauses != formula.clauses.len() {
        bail!(
            "introduced-clause-backfill-candidates report input.num_clauses {} does not match target CNF {}",
            input_num_clauses,
            formula.clauses.len()
        );
    }
    let input_sha256 = input
        .get("sha256")
        .and_then(JsonValue::as_str)
        .context("introduced-clause-backfill-candidates report missing input.sha256")?;
    if input_sha256 != target_sha256 {
        bail!(
            "introduced-clause-backfill-candidates report input.sha256 {input_sha256} does not match target CNF {target_sha256}"
        );
    }

    let authority = report
        .get("authority")
        .context("introduced-clause-backfill-candidates report missing authority object")?;
    validate_diagnostic_authority_object(
        authority,
        "introduced-clause-backfill-candidates report authority",
    )?;
    let verdict = report
        .get("verdict")
        .context("introduced-clause-backfill-candidates report missing verdict object")?;
    validate_diagnostic_verdict_authority(
        verdict,
        "introduced-clause-backfill-candidates report verdict",
    )?;
    let candidate_source = report
        .pointer("/candidates/source")
        .and_then(JsonValue::as_str)
        .context(
            "introduced-clause-backfill-candidates report candidates.source must be a string",
        )?;
    if candidate_source != "introduced_clauses occurrence candidate_one_based_vars" {
        bail!(
            "introduced-clause-backfill-candidates report candidates.source must be introduced_clauses occurrence candidate_one_based_vars; got {candidate_source}"
        );
    }
    let verdict_candidate_source = verdict
        .get("candidate_vars_source")
        .and_then(JsonValue::as_str)
        .context(
            "introduced-clause-backfill-candidates report verdict.candidate_vars_source must be a string",
        )?;
    if verdict_candidate_source != "introduced_clauses occurrence candidate_one_based_vars" {
        bail!(
            "introduced-clause-backfill-candidates report verdict.candidate_vars_source must be introduced_clauses occurrence candidate_one_based_vars; got {verdict_candidate_source}"
        );
    }

    let frontier = report
        .get("introduced_clause_backfill_frontier")
        .context(
            "introduced-clause-backfill-candidates report missing introduced_clause_backfill_frontier object",
        )?;
    frontier.as_object().context(
        "introduced-clause-backfill-candidates report introduced_clause_backfill_frontier must be an object",
    )?;
    let frontier_schema = frontier
        .get("schema")
        .and_then(JsonValue::as_str)
        .context(
            "introduced-clause-backfill-candidates report introduced_clause_backfill_frontier.schema must be a string",
        )?;
    if frontier_schema != "ay.satcomp-circuit-introduced-clause-backfill-frontier/v1" {
        bail!(
            "introduced-clause-backfill-candidates report frontier schema must be ay.satcomp-circuit-introduced-clause-backfill-frontier/v1; got {frontier_schema}"
        );
    }
    let frontier_repo_head = frontier
        .get("repo_head")
        .and_then(JsonValue::as_str)
        .context(
            "introduced-clause-backfill-candidates report introduced_clause_backfill_frontier.repo_head must be a string",
        )?;
    if frontier_repo_head != current_repo_head {
        bail!(
            "introduced-clause-backfill-candidates report introduced_clause_backfill_frontier.repo_head {frontier_repo_head} is stale; current git HEAD is {current_repo_head}"
        );
    }
    let frontier_ay_build = frontier.get("ay_build").context(
        "introduced-clause-backfill-candidates report introduced_clause_backfill_frontier.ay_build must be an object",
    )?;
    validate_ay_build_current(
        frontier_ay_build,
        "introduced-clause-backfill-candidates report introduced_clause_backfill_frontier.ay_build",
    )?;
    let frontier_assignment_report = frontier.get("assignment_local_search_report").context(
        "introduced-clause-backfill-candidates report introduced_clause_backfill_frontier missing assignment_local_search_report object",
    )?;
    validate_assignment_local_search_report_provenance_object(
        frontier_assignment_report,
        current_repo_head,
        "introduced-clause-backfill-candidates report introduced_clause_backfill_frontier.assignment_local_search_report",
    )?;

    let candidates =
        collect_introduced_clause_backfill_candidates_from_candidates_report(report, formula)?;
    validate_backfill_search_candidate_aggregate_fields(report, &candidates)?;
    Ok(candidates)
}

fn collect_introduced_clause_backfill_candidates_from_candidates_report(
    report: &JsonValue,
    formula: &RawFormula,
) -> Result<BackfillCandidateReport> {
    let clause_values = report
        .pointer("/candidates/clause_windows")
        .and_then(JsonValue::as_array)
        .context(
            "introduced-clause-backfill-candidates report candidates.clause_windows must be an array",
        )?;
    let mut candidates = BackfillCandidateReport::default();
    let mut seen_clause_ids = BTreeSet::new();
    for (idx, clause) in clause_values.iter().enumerate() {
        clause.as_object().with_context(|| {
            format!("introduced-clause-backfill-candidates report candidates.clause_windows[{idx}] must be an object")
        })?;
        let authority = clause.get("authority").with_context(|| {
            format!("candidates.clause_windows[{idx}] missing authority object")
        })?;
        validate_diagnostic_authority_object(
            authority,
            &format!("candidates.clause_windows[{idx}].authority"),
        )?;
        let one_based_clause_id = report_usize_field(
            clause,
            "one_based_clause_id",
            &format!("candidates.clause_windows[{idx}].one_based_clause_id"),
        )?;
        validate_one_based_clause_ids(
            &[one_based_clause_id],
            formula.clauses.len(),
            "candidates.clause_windows[].one_based_clause_id",
        )?;
        if !seen_clause_ids.insert(one_based_clause_id) {
            bail!("candidates.clause_windows[{idx}] duplicates clause ID {one_based_clause_id}");
        }

        let original_clause_lits = json_i32_array_required(clause, "original_clause_lits")
            .with_context(|| format!("candidates.clause_windows[{idx}].original_clause_lits"))?;
        if original_clause_lits != formula.clauses[one_based_clause_id - 1] {
            bail!(
                "candidates.clause_windows[{idx}] original_clause_lits do not match target CNF clause {one_based_clause_id}"
            );
        }
        let original_clause_vars =
            json_usize_array_required(clause, "original_clause_one_based_vars").with_context(
                || format!("candidates.clause_windows[{idx}].original_clause_one_based_vars"),
            )?;
        validate_one_based_vars(
            &original_clause_vars,
            formula.num_vars,
            "candidates.clause_windows[].original_clause_one_based_vars",
        )?;
        ensure_unique_usizes(
            &original_clause_vars,
            "candidates.clause_windows[].original_clause_one_based_vars",
        )?;
        let vars_from_lits: BTreeSet<usize> = original_clause_lits
            .iter()
            .map(|lit| lit_var(*lit))
            .collect();
        let original_clause_var_set: BTreeSet<usize> =
            original_clause_vars.iter().copied().collect();
        if original_clause_var_set != vars_from_lits {
            bail!(
                "candidates.clause_windows[{idx}] original_clause_one_based_vars do not match original_clause_lits vars"
            );
        }

        let introducing_candidate_vars =
            json_usize_array_required(clause, "introducing_candidate_one_based_vars")
                .with_context(|| {
                    format!("candidates.clause_windows[{idx}].introducing_candidate_one_based_vars")
                })?;
        validate_one_based_vars(
            &introducing_candidate_vars,
            formula.num_vars,
            "candidates.clause_windows[].introducing_candidate_one_based_vars",
        )?;
        ensure_unique_usizes(
            &introducing_candidate_vars,
            "candidates.clause_windows[].introducing_candidate_one_based_vars",
        )?;
        let introducing_candidate_var_set: BTreeSet<usize> =
            introducing_candidate_vars.iter().copied().collect();

        let already_introducing_candidate_vars =
            json_usize_array_required(clause, "already_introducing_candidate_one_based_vars")
                .with_context(|| {
                    format!(
                "candidates.clause_windows[{idx}].already_introducing_candidate_one_based_vars"
            )
                })?;
        validate_one_based_vars(
            &already_introducing_candidate_vars,
            formula.num_vars,
            "candidates.clause_windows[].already_introducing_candidate_one_based_vars",
        )?;
        ensure_unique_usizes(
            &already_introducing_candidate_vars,
            "candidates.clause_windows[].already_introducing_candidate_one_based_vars",
        )?;
        let expected_already: Vec<_> = original_clause_var_set
            .intersection(&introducing_candidate_var_set)
            .copied()
            .collect();
        if already_introducing_candidate_vars != expected_already {
            bail!(
                "candidates.clause_windows[{idx}] already_introducing_candidate_one_based_vars do not match clause/source-candidate intersection"
            );
        }

        let new_backfill_vars = json_usize_array_required(clause, "new_backfill_one_based_vars")
            .with_context(|| {
                format!("candidates.clause_windows[{idx}].new_backfill_one_based_vars")
            })?;
        validate_one_based_vars(
            &new_backfill_vars,
            formula.num_vars,
            "candidates.clause_windows[].new_backfill_one_based_vars",
        )?;
        ensure_unique_usizes(
            &new_backfill_vars,
            "candidates.clause_windows[].new_backfill_one_based_vars",
        )?;
        let expected_new: Vec<_> = original_clause_var_set
            .difference(&introducing_candidate_var_set)
            .copied()
            .collect();
        if new_backfill_vars != expected_new {
            bail!(
                "candidates.clause_windows[{idx}] new_backfill_one_based_vars do not match clause vars minus source candidates"
            );
        }

        let source_frame_row_id_samples = json_string_array(clause, "source_frame_row_id_samples")
            .with_context(|| {
                format!("candidates.clause_windows[{idx}].source_frame_row_id_samples")
            })?;
        let occurrence_count = report_usize_field(
            clause,
            "occurrence_count",
            &format!("candidates.clause_windows[{idx}].occurrence_count"),
        )?;
        if occurrence_count == 0 {
            bail!("candidates.clause_windows[{idx}].occurrence_count must be positive");
        }

        candidates.candidate_var_occurrences += occurrence_count * introducing_candidate_vars.len();
        for &var in &introducing_candidate_vars {
            candidates.candidate_vars.insert(var);
            candidates.introducing_candidate_vars.insert(var);
            candidates
                .candidate_clause_pairs
                .insert((var, one_based_clause_id));
            *candidates
                .candidate_var_occurrence_counts
                .entry(var)
                .or_insert(0) += occurrence_count;
        }
        candidates
            .already_introducing_candidate_vars
            .extend(already_introducing_candidate_vars.iter().copied());
        candidates
            .new_backfill_vars
            .extend(new_backfill_vars.iter().copied());
        candidates.window_vars.extend(
            original_clause_var_set
                .union(&introducing_candidate_var_set)
                .copied(),
        );
        candidates
            .introducing_candidate_vars_outside_clause_vars
            .extend(
                introducing_candidate_var_set
                    .difference(&original_clause_var_set)
                    .copied(),
            );
        candidates.clauses.push(BackfillCandidateClause {
            one_based_clause_id,
            original_clause_lits,
            original_clause_vars,
            introducing_candidate_vars,
            already_introducing_candidate_vars,
            new_backfill_vars,
            source_frame_row_id_samples,
            occurrence_count,
        });
    }
    if candidates.clauses.is_empty() {
        bail!("introduced-clause-backfill-candidates report has no clause windows");
    }
    Ok(candidates)
}

fn validate_backfill_search_candidate_aggregate_fields(
    report: &JsonValue,
    candidates: &BackfillCandidateReport,
) -> Result<()> {
    let candidate_object = report
        .get("candidates")
        .context("introduced-clause-backfill-candidates report missing candidates object")?;
    let counts = report
        .get("counts")
        .context("introduced-clause-backfill-candidates report missing counts object")?;
    let clause_windows = report
        .get("clause_windows")
        .context("introduced-clause-backfill-candidates report missing clause_windows object")?;
    let clause_ids: BTreeSet<_> = candidates
        .clauses
        .iter()
        .map(|clause| clause.one_based_clause_id)
        .collect();

    validate_optional_usize_count(
        candidate_object,
        "introduced_clause_count",
        candidates.clauses.len(),
        "candidates.introduced_clause_count",
    )?;
    validate_optional_usize_array_set(
        candidate_object,
        "introduced_one_based_clause_ids",
        &clause_ids,
        "candidates.introduced_one_based_clause_ids",
    )?;
    validate_optional_usize_count(
        candidate_object,
        "candidate_var_count",
        candidates.candidate_vars.len(),
        "candidates.candidate_var_count",
    )?;
    validate_optional_usize_array_set(
        candidate_object,
        "candidate_one_based_vars",
        &candidates.candidate_vars,
        "candidates.candidate_one_based_vars",
    )?;
    validate_optional_usize_count(
        candidate_object,
        "candidate_clause_pair_count",
        candidates.candidate_clause_pairs.len(),
        "candidates.candidate_clause_pair_count",
    )?;
    validate_optional_usize_count(
        candidate_object,
        "introducing_candidate_var_count",
        candidates.introducing_candidate_vars.len(),
        "candidates.introducing_candidate_var_count",
    )?;
    validate_optional_usize_array_set(
        candidate_object,
        "introducing_candidate_one_based_vars",
        &candidates.introducing_candidate_vars,
        "candidates.introducing_candidate_one_based_vars",
    )?;
    validate_optional_usize_count(
        candidate_object,
        "already_introducing_candidate_var_count",
        candidates.already_introducing_candidate_vars.len(),
        "candidates.already_introducing_candidate_var_count",
    )?;
    validate_optional_usize_array_set(
        candidate_object,
        "already_introducing_candidate_one_based_vars",
        &candidates.already_introducing_candidate_vars,
        "candidates.already_introducing_candidate_one_based_vars",
    )?;
    validate_optional_usize_count(
        candidate_object,
        "new_backfill_var_count",
        candidates.new_backfill_vars.len(),
        "candidates.new_backfill_var_count",
    )?;
    validate_optional_usize_array_set(
        candidate_object,
        "new_backfill_one_based_vars",
        &candidates.new_backfill_vars,
        "candidates.new_backfill_one_based_vars",
    )?;
    validate_optional_usize_count(
        counts,
        "unique_introduced_clause_count",
        candidates.clauses.len(),
        "counts.unique_introduced_clause_count",
    )?;
    validate_optional_usize_count(
        counts,
        "candidate_var_count",
        candidates.candidate_vars.len(),
        "counts.candidate_var_count",
    )?;
    validate_optional_usize_count(
        counts,
        "candidate_clause_pair_count",
        candidates.candidate_clause_pairs.len(),
        "counts.candidate_clause_pair_count",
    )?;
    validate_optional_usize_count(
        counts,
        "clause_window_count",
        candidates.clauses.len(),
        "counts.clause_window_count",
    )?;
    validate_optional_usize_count(
        counts,
        "clause_window_var_count",
        candidates.window_vars.len(),
        "counts.clause_window_var_count",
    )?;
    validate_optional_usize_count(
        counts,
        "window_var_count",
        candidates.window_vars.len(),
        "counts.window_var_count",
    )?;
    validate_optional_usize_count(
        counts,
        "new_backfill_var_count",
        candidates.new_backfill_vars.len(),
        "counts.new_backfill_var_count",
    )?;
    validate_optional_usize_array_set(
        clause_windows,
        "one_based_clause_ids",
        &clause_ids,
        "clause_windows.one_based_clause_ids",
    )?;
    validate_optional_usize_count(
        clause_windows,
        "window_var_count",
        candidates.window_vars.len(),
        "clause_windows.window_var_count",
    )?;
    validate_optional_usize_array_set(
        clause_windows,
        "window_one_based_vars",
        &candidates.window_vars,
        "clause_windows.window_one_based_vars",
    )?;
    let mirrored_clauses = clause_windows
        .get("clauses")
        .and_then(JsonValue::as_array)
        .context("clause_windows.clauses must be an array")?;
    if mirrored_clauses.len() != candidates.clauses.len() {
        bail!(
            "clause_windows.clauses length {} does not match candidates.clause_windows length {}",
            mirrored_clauses.len(),
            candidates.clauses.len()
        );
    }
    Ok(())
}

fn backfill_search_candidate_source_kind(
    one_based_var: usize,
    source_var_set: &BTreeSet<usize>,
    window_only_var_set: &BTreeSet<usize>,
    outside_radius_only_var_set: &BTreeSet<usize>,
) -> &'static str {
    if source_var_set.contains(&one_based_var) {
        "source_candidate"
    } else if window_only_var_set.contains(&one_based_var) {
        "window_only"
    } else if outside_radius_only_var_set.contains(&one_based_var) {
        "outside_radius_only"
    } else {
        "unknown"
    }
}

fn validate_diagnostic_authority_object(object: &JsonValue, label: &str) -> Result<()> {
    object
        .as_object()
        .with_context(|| format!("{label} must be an object"))?;
    let classification = object
        .get("classification")
        .and_then(JsonValue::as_str)
        .with_context(|| format!("{label}.classification must be diagnostic_only"))?;
    if classification != "diagnostic_only" {
        bail!("{label}.classification must be diagnostic_only");
    }
    validate_false_authority_flags(object, label)
}

fn validate_diagnostic_verdict_authority(object: &JsonValue, label: &str) -> Result<()> {
    object
        .as_object()
        .with_context(|| format!("{label} must be an object"))?;
    let diagnostic_only = object
        .get("diagnostic_only")
        .and_then(JsonValue::as_bool)
        .with_context(|| format!("{label}.diagnostic_only must be Boolean true"))?;
    if !diagnostic_only {
        bail!("{label}.diagnostic_only must be true");
    }
    validate_false_authority_flags(object, label)
}

fn validate_false_authority_flags(object: &JsonValue, label: &str) -> Result<()> {
    for field in [
        "route_admitted",
        "sat_output_authority",
        "model_output_authority",
        "proof_output_authority",
        "solver_verdict_authority",
        "sat_comp_progress_claim",
    ] {
        let value = object
            .get(field)
            .and_then(JsonValue::as_bool)
            .with_context(|| format!("{label}.{field} must be Boolean false"))?;
        if value {
            bail!("{label}.{field} must be false");
        }
    }
    Ok(())
}

fn diagnostic_source_json(repo_head: Option<String>, note: &str) -> JsonValue {
    json!({
        "repo_head": repo_head,
        "ay_build": ay_build_json(),
        "note": note,
    })
}

fn ay_build_json() -> JsonValue {
    json!({
        "version": BUILD_INFO.version,
        "increment": BUILD_INFO.increment,
        "commit": BUILD_INFO.commit,
        "datetime_utc": BUILD_INFO.datetime_utc,
        "stamp": BUILD_INFO.stamp,
    })
}

fn validate_optional_usize_array_set(
    object: &JsonValue,
    field: &str,
    expected: &BTreeSet<usize>,
    label: &str,
) -> Result<()> {
    if object.get(field).is_none() {
        return Ok(());
    }
    let values = json_usize_array(object, field)?;
    ensure_unique_usizes(&values, label)?;
    let actual: BTreeSet<usize> = values.into_iter().collect();
    if &actual != expected {
        bail!(
            "{label} does not match introduced_clauses.clauses-derived values: expected {expected:?}, got {actual:?}"
        );
    }
    Ok(())
}

fn validate_optional_usize_count(
    object: &JsonValue,
    field: &str,
    expected: usize,
    label: &str,
) -> Result<()> {
    if object.get(field).is_none() {
        return Ok(());
    }
    let actual = report_usize_field(object, field, label)?;
    if actual != expected {
        bail!("{label} expected {expected}, got {actual}");
    }
    Ok(())
}

fn json_usize_array_required(object: &JsonValue, field: &str) -> Result<Vec<usize>> {
    object
        .get(field)
        .with_context(|| format!("{field} must be an array"))?;
    json_usize_array(object, field)
}

fn json_i32_array_required(object: &JsonValue, field: &str) -> Result<Vec<i32>> {
    let value = object
        .get(field)
        .with_context(|| format!("{field} must be an array"))?;
    let entries = value
        .as_array()
        .with_context(|| format!("{field} must be an array"))?;
    entries
        .iter()
        .enumerate()
        .map(|(idx, value)| {
            let raw = value
                .as_i64()
                .with_context(|| format!("{field}[{idx}] must be an integer"))?;
            i32::try_from(raw).with_context(|| format!("{field}[{idx}] out of i32 range"))
        })
        .collect()
}

fn validate_one_based_vars(vars: &[usize], num_vars: usize, label: &str) -> Result<()> {
    for (idx, var) in vars.iter().enumerate() {
        if *var == 0 || *var > num_vars {
            bail!("{label}[{idx}] variable {var} is out of range 1..={num_vars}");
        }
    }
    Ok(())
}

fn ensure_unique_usizes(values: &[usize], label: &str) -> Result<()> {
    let unique: BTreeSet<usize> = values.iter().copied().collect();
    if unique.len() != values.len() {
        bail!("{label} contains duplicate values");
    }
    Ok(())
}

fn backfill_candidate_clause_json(clause: &BackfillCandidateClause) -> JsonValue {
    json!({
        "one_based_clause_id": clause.one_based_clause_id,
        "window": backfill_candidate_window_spec(clause),
        "original_clause_lits": &clause.original_clause_lits,
        "original_clause_one_based_vars": &clause.original_clause_vars,
        "introducing_candidate_one_based_vars": &clause.introducing_candidate_vars,
        "already_introducing_candidate_one_based_vars": &clause.already_introducing_candidate_vars,
        "new_backfill_one_based_vars": &clause.new_backfill_vars,
        "source_frame_row_id_samples": &clause.source_frame_row_id_samples,
        "occurrence_count": clause.occurrence_count,
        "authority": diagnostic_authority_json(),
    })
}

fn diagnostic_authority_json() -> JsonValue {
    json!({
        "classification": "diagnostic_only",
        "route_admitted": false,
        "sat_output_authority": false,
        "model_output_authority": false,
        "proof_output_authority": false,
        "solver_verdict_authority": false,
        "sat_comp_progress_claim": false,
    })
}

fn backfill_candidate_window_spec(clause: &BackfillCandidateClause) -> String {
    format!(
        "introduced-clause-{}={}",
        clause.one_based_clause_id,
        join_usizes_csv(&clause.original_clause_vars)
    )
}

fn write_backfill_candidate_var_tsv(path: &Path, report: &BackfillCandidateReport) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let mut file =
        File::create(path).with_context(|| format!("failed to create '{}'", path.display()))?;
    writeln!(
        file,
        "original_var\tsource_kind\tintroduced_unique_clause_count\tintroduced_clause_occurrences\tintroduced_one_based_clause_ids\tfrontier_clause_one_based_vars"
    )?;
    let stats_by_var = backfill_candidate_stats_by_var(&report.clauses);
    for var in &report.candidate_vars {
        let Some(stats) = stats_by_var.get(var) else {
            bail!("candidate variable {var} was not present in any introduced clause window");
        };
        let clause_ids = stats.clause_ids.iter().copied().collect::<Vec<_>>();
        let frontier_clause_vars = stats
            .frontier_clause_vars
            .iter()
            .copied()
            .collect::<Vec<_>>();
        let occurrence_count = report
            .candidate_var_occurrence_counts
            .get(var)
            .copied()
            .unwrap_or(stats.occurrence_count);
        writeln!(
            file,
            "{}\tintroduced_clause_backfill_candidate\t{}\t{}\t{}\t{}",
            var,
            clause_ids.len(),
            occurrence_count,
            join_usizes(&clause_ids),
            join_usizes(&frontier_clause_vars),
        )?;
    }
    Ok(())
}

fn write_backfill_clause_window_tsv(
    path: &Path,
    clauses: &[BackfillCandidateClause],
) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let mut file =
        File::create(path).with_context(|| format!("failed to create '{}'", path.display()))?;
    writeln!(
        file,
        "one_based_clause_id\toriginal_clause_lits\tclause_one_based_vars\tcandidate_one_based_vars\twindow_one_based_vars\toccurrence_count"
    )?;
    for clause in clauses {
        let window_vars: Vec<_> = clause
            .original_clause_vars
            .iter()
            .copied()
            .chain(clause.introducing_candidate_vars.iter().copied())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        writeln!(
            file,
            "{}\t{}\t{}\t{}\t{}\t{}",
            clause.one_based_clause_id,
            join_i32s(&clause.original_clause_lits),
            join_usizes(&clause.original_clause_vars),
            join_usizes(&clause.introducing_candidate_vars),
            join_usizes(&window_vars),
            clause.occurrence_count
        )?;
    }
    Ok(())
}

#[derive(Clone, Debug, Default)]
struct BackfillCandidateVarStats {
    clause_ids: BTreeSet<usize>,
    frontier_clause_vars: BTreeSet<usize>,
    occurrence_count: usize,
}

fn backfill_candidate_stats_by_var(
    clauses: &[BackfillCandidateClause],
) -> BTreeMap<usize, BackfillCandidateVarStats> {
    let mut stats_by_var: BTreeMap<usize, BackfillCandidateVarStats> = BTreeMap::new();
    for clause in clauses {
        for var in &clause.introducing_candidate_vars {
            let stats = stats_by_var.entry(*var).or_default();
            stats.clause_ids.insert(clause.one_based_clause_id);
            stats
                .frontier_clause_vars
                .extend(clause.original_clause_vars.iter().copied());
            stats.occurrence_count += clause.occurrence_count;
        }
    }
    stats_by_var
}

fn join_usizes(values: &[usize]) -> String {
    values
        .iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(" ")
}

fn join_usizes_csv(values: &[usize]) -> String {
    values
        .iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(",")
}

fn join_i32s(values: &[i32]) -> String {
    values
        .iter()
        .map(i32::to_string)
        .collect::<Vec<_>>()
        .join(" ")
}

fn group_required_vars(
    root: &Path,
    num_vars: usize,
    opts: &AssignmentLocalSearchOptions,
) -> Result<BTreeSet<usize>> {
    let mut required = BTreeSet::new();
    if let Some(raw) = &opts.group_require_vars {
        for one_based in parse_var_selector(raw)? {
            insert_one_based_candidate(num_vars, &mut required, one_based)?;
        }
    }
    for path in &opts.group_require_files {
        let path = resolve_path(root, path);
        for one_based in parse_flip_file(&path)? {
            insert_one_based_candidate(num_vars, &mut required, one_based)?;
        }
    }
    if required.is_empty() && opts.group_require_count > 1 {
        bail!("assignment-local-search group-require-count is greater than one but no required variables were supplied");
    }
    Ok(required)
}

fn windowed_group_templates(
    candidates: &[usize],
    group_size: usize,
    window_size: usize,
    required_vars: &BTreeSet<usize>,
    required_count: usize,
    evaluation_limit: usize,
) -> Result<GroupTemplates> {
    if group_size < 3 {
        bail!("assignment-local-search group-size must be at least 3; use single/pair phases for smaller moves");
    }
    if window_size < group_size {
        bail!("assignment-local-search group-window-size must be at least group-size");
    }
    if evaluation_limit == 0 {
        bail!("assignment-local-search group-evaluation-limit must be positive");
    }
    if !required_vars.is_empty() && required_count > group_size {
        bail!("assignment-local-search group-require-count must be at most group-size");
    }
    if candidates.len() < group_size {
        bail!(
            "assignment-local-search group candidate set must contain at least {group_size} variables"
        );
    }

    let mut groups = BTreeSet::new();
    let mut truncated = false;
    for start in 0..candidates.len() {
        let end = (start + window_size).min(candidates.len());
        if end - start < group_size {
            break;
        }
        let mut current = Vec::with_capacity(group_size);
        if collect_window_group_templates(
            &candidates[start..end],
            group_size,
            0,
            &mut current,
            &mut groups,
            required_vars,
            required_count,
            evaluation_limit,
        ) {
            truncated = true;
            break;
        }
    }
    Ok(GroupTemplates {
        groups: groups.into_iter().collect(),
        truncated,
    })
}

fn collect_window_group_templates(
    window: &[usize],
    group_size: usize,
    start: usize,
    current: &mut Vec<usize>,
    groups: &mut BTreeSet<Vec<usize>>,
    required_vars: &BTreeSet<usize>,
    required_count: usize,
    evaluation_limit: usize,
) -> bool {
    if current.len() == group_size {
        if group_satisfies_required(current, required_vars, required_count) {
            groups.insert(current.clone());
            return groups.len() >= evaluation_limit;
        }
        return false;
    }
    let needed = group_size - current.len();
    if window.len() < needed || start > window.len() - needed {
        return false;
    }
    for idx in start..=window.len() - needed {
        current.push(window[idx]);
        if collect_window_group_templates(
            window,
            group_size,
            idx + 1,
            current,
            groups,
            required_vars,
            required_count,
            evaluation_limit,
        ) {
            current.pop();
            return true;
        }
        current.pop();
    }
    false
}

fn group_satisfies_required(
    group: &[usize],
    required_vars: &BTreeSet<usize>,
    required_count: usize,
) -> bool {
    if required_vars.is_empty() || required_count == 0 {
        return true;
    }
    group
        .iter()
        .filter(|var| required_vars.contains(var))
        .take(required_count)
        .count()
        == required_count
}

fn insert_one_based_candidate(
    num_vars: usize,
    candidates: &mut BTreeSet<usize>,
    one_based: usize,
) -> Result<()> {
    if one_based == 0 || one_based > num_vars {
        bail!("candidate variable out of range: {one_based}");
    }
    candidates.insert(one_based - 1);
    Ok(())
}

fn assignment_delta_from_base(base: &[bool], assignment: &[bool]) -> Vec<(usize, bool)> {
    base.iter()
        .zip(assignment.iter())
        .enumerate()
        .filter_map(|(var, (base_value, value))| (base_value != value).then_some((var, *value)))
        .collect()
}

fn write_set_tsv(path: &Path, base: &[bool], set_values: &[(usize, bool)]) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let mut file =
        File::create(path).with_context(|| format!("failed to create '{}'", path.display()))?;
    writeln!(
        file,
        "original_var\tbaseline_value\tcandidate_value\tchanged"
    )?;
    for &(var, value) in set_values {
        writeln!(file, "{}\t{}\t{}\ttrue", var + 1, base[var], value)?;
    }
    Ok(())
}

fn residual_flags(num_clauses: usize, residual_ids: &[usize]) -> Vec<bool> {
    let mut flags = vec![false; num_clauses];
    for &clause_idx in residual_ids {
        if let Some(flag) = flags.get_mut(clause_idx) {
            *flag = true;
        }
    }
    flags
}

fn residual_clause_ids_after_group_flip(
    clauses: &[Vec<i32>],
    assignment: &[bool],
    group: &[usize],
) -> Vec<usize> {
    clauses
        .iter()
        .enumerate()
        .filter_map(|(idx, clause)| {
            clause_residual_after_group_flip(clause, assignment, group).then_some(idx)
        })
        .collect()
}

fn clause_residual_after_group_flip(clause: &[i32], assignment: &[bool], group: &[usize]) -> bool {
    !clause.iter().any(|&lit| {
        let var = lit_var(lit) - 1;
        let mut value = assignment[var];
        if group.binary_search(&var).is_ok() {
            value = !value;
        }
        if lit > 0 {
            value
        } else {
            !value
        }
    })
}

fn insert_one_based_flip(
    num_vars: usize,
    flips: &mut BTreeSet<usize>,
    one_based: usize,
) -> Result<()> {
    if one_based == 0 || one_based > num_vars {
        bail!("flip variable out of range: {one_based}");
    }
    flips.insert(one_based - 1);
    Ok(())
}

fn parse_flip_file(path: &Path) -> Result<Vec<usize>> {
    let text = fs::read_to_string(path)
        .with_context(|| format!("failed to read flip file '{}'", path.display()))?;
    let Some(header) = text.lines().find(|line| !line.trim().is_empty()) else {
        return Ok(Vec::new());
    };
    if header.contains('\t') {
        let columns: Vec<&str> = header.split('\t').collect();
        if let Some(var_col) = columns
            .iter()
            .position(|name| matches!(*name, "original_var" | "var" | "variable"))
        {
            let mut vars = Vec::new();
            for (line_idx, line) in text.lines().enumerate().skip(1) {
                if line.trim().is_empty() {
                    continue;
                }
                let cells: Vec<&str> = line.split('\t').collect();
                let var_cell = cells.get(var_col).with_context(|| {
                    format!("{}:{} missing flip variable", path.display(), line_idx + 1)
                })?;
                vars.push(var_cell.parse::<usize>().with_context(|| {
                    format!("{}:{} invalid flip variable", path.display(), line_idx + 1)
                })?);
            }
            return Ok(vars);
        }
    }
    parse_var_selector(&text.replace(['\n', '\r'], " "))
        .with_context(|| format!("failed to parse flip selectors in '{}'", path.display()))
}

fn parse_set_file(path: &Path) -> Result<Vec<(usize, bool)>> {
    let table = read_tsv_table(path)?;
    let var_col = table
        .header
        .iter()
        .position(|name| matches!(name.as_str(), "original_var" | "var" | "variable"))
        .with_context(|| {
            format!(
                "{} missing original_var/var/variable column",
                path.display()
            )
        })?;
    let value_col = table
        .header
        .iter()
        .position(|name| matches!(name.as_str(), "candidate_value" | "set_value" | "value"))
        .with_context(|| {
            format!(
                "{} missing candidate_value/set_value/value column",
                path.display()
            )
        })?;
    let mut values = Vec::new();
    for (line_idx, row) in table.rows.iter().enumerate() {
        let var_cell = row
            .get(&table.header[var_col])
            .map(String::as_str)
            .unwrap_or_default();
        let value_cell = row
            .get(&table.header[value_col])
            .map(String::as_str)
            .unwrap_or_default();
        let var = var_cell.parse::<usize>().with_context(|| {
            format!(
                "{}:{} invalid set variable '{}'",
                path.display(),
                line_idx + 2,
                var_cell
            )
        })?;
        let value = parse_bool_cell(value_cell).with_context(|| {
            format!(
                "{}:{} invalid set value '{}'",
                path.display(),
                line_idx + 2,
                value_cell
            )
        })?;
        values.push((var, value));
    }
    Ok(values)
}

fn parse_bool_cell(raw: &str) -> Result<bool> {
    match raw.trim().to_ascii_lowercase().as_str() {
        "true" | "t" | "1" => Ok(true),
        "false" | "f" | "0" => Ok(false),
        other => bail!("unrecognized Boolean value: {other}"),
    }
}

fn literal_satisfied(lit: i32, assignment: &[bool]) -> bool {
    let value = assignment[lit.unsigned_abs() as usize - 1];
    if lit > 0 {
        value
    } else {
        !value
    }
}

fn residual_clause_ids(clauses: &[Vec<i32>], assignment: &[bool]) -> Vec<usize> {
    clauses
        .iter()
        .enumerate()
        .filter_map(|(idx, clause)| {
            if clause.iter().any(|&lit| literal_satisfied(lit, assignment)) {
                None
            } else {
                Some(idx)
            }
        })
        .collect()
}

fn residual_clause_samples(
    clauses: &[Vec<i32>],
    assignment: &[bool],
    residual_ids: &[usize],
    limit: usize,
) -> Vec<JsonValue> {
    residual_ids
        .iter()
        .take(limit)
        .map(|&idx| {
            let clause = &clauses[idx];
            json!({
                "zero_based_clause_id": idx,
                "one_based_clause_id": idx + 1,
                "literals": clause,
                "literal_values": clause.iter().map(|&lit| {
                    let var = lit.unsigned_abs() as usize - 1;
                    json!({
                        "literal": lit,
                        "one_based_var": var + 1,
                        "assignment_value": assignment[var],
                        "literal_satisfied": literal_satisfied(lit, assignment),
                    })
                }).collect::<Vec<_>>(),
            })
        })
        .collect()
}

fn lit_var(lit: i32) -> usize {
    lit.unsigned_abs() as usize
}

fn selected_candidates(
    outside_vars: &[usize],
    raw: Option<&str>,
    limit: Option<usize>,
    radius: usize,
) -> Result<Vec<usize>> {
    let mut candidates: Vec<usize> = if let Some(raw) = raw {
        let requested: BTreeSet<usize> = parse_var_selector(raw)?
            .into_iter()
            .map(|var| var - 1)
            .collect();
        let outside: BTreeSet<usize> = outside_vars.iter().copied().collect();
        let unknown: Vec<usize> = requested.difference(&outside).map(|var| var + 1).collect();
        if !unknown.is_empty() {
            bail!("candidate vars are not outside radius {radius}: {unknown:?}");
        }
        outside_vars
            .iter()
            .copied()
            .filter(|var| requested.contains(var))
            .collect()
    } else {
        outside_vars.to_vec()
    };
    if let Some(limit) = limit {
        candidates.truncate(limit);
    }
    Ok(candidates)
}

fn selected_windows(
    raw_windows: &[String],
    limit: Option<usize>,
    auto_low_free_windows: bool,
    auto_window_max_size: usize,
    auto_component_hitting_windows: bool,
    auto_component_family_windows: bool,
    component_hook_targets: &Path,
    outside_vars: &[usize],
) -> Result<WindowSelection> {
    if auto_low_free_windows && auto_component_hitting_windows {
        bail!("--auto-low-free-windows cannot be combined with --auto-component-hitting-windows");
    }
    if auto_low_free_windows && auto_component_family_windows {
        bail!("--auto-low-free-windows cannot be combined with --auto-component-family-windows");
    }
    if auto_component_hitting_windows && auto_component_family_windows {
        bail!("--auto-component-hitting-windows cannot be combined with --auto-component-family-windows");
    }
    if auto_low_free_windows {
        if !raw_windows.is_empty() {
            bail!("--auto-low-free-windows cannot be combined with explicit --window entries");
        }
        return auto_low_free_windows_for_outside(outside_vars, auto_window_max_size, limit);
    }
    if auto_component_hitting_windows {
        if !raw_windows.is_empty() {
            bail!(
                "--auto-component-hitting-windows cannot be combined with explicit --window entries"
            );
        }
        return component_hitting_windows_for_targets(component_hook_targets, limit);
    }
    if auto_component_family_windows {
        if !raw_windows.is_empty() {
            bail!(
                "--auto-component-family-windows cannot be combined with explicit --window entries"
            );
        }
        return component_family_windows_for_targets(component_hook_targets, limit);
    }
    let source = if raw_windows.is_empty() {
        "default"
    } else {
        "explicit"
    };
    let mut windows = if raw_windows.is_empty() {
        default_windows()
    } else {
        raw_windows
            .iter()
            .map(|raw| parse_window(raw))
            .collect::<Result<Vec<_>>>()?
    };
    if let Some(limit) = limit {
        windows.truncate(limit);
    }
    Ok(WindowSelection {
        windows,
        source,
        auto_low_free_candidate_windows: None,
        auto_component_hitting_candidate_windows: None,
        component_hitting_windows: Vec::new(),
        auto_component_family_candidate_windows: None,
        component_family_windows: Vec::new(),
        component_hook_targets: None,
    })
}

fn auto_low_free_windows_for_outside(
    outside_vars: &[usize],
    max_size: usize,
    limit: Option<usize>,
) -> Result<WindowSelection> {
    if max_size == 0 {
        bail!("--auto-window-max-size must be positive");
    }
    let Some(limit) = limit else {
        bail!("--auto-low-free-windows requires --window-limit to keep reduced-CNF probes bounded");
    };
    let candidate_windows = auto_low_free_candidate_count(outside_vars.len(), max_size);
    if limit == 0 {
        return Ok(WindowSelection {
            windows: Vec::new(),
            source: "auto_low_free",
            auto_low_free_candidate_windows: Some(candidate_windows),
            auto_component_hitting_candidate_windows: None,
            component_hitting_windows: Vec::new(),
            auto_component_family_candidate_windows: None,
            component_family_windows: Vec::new(),
            component_hook_targets: None,
        });
    }
    let mut windows = Vec::new();
    let capped_max = max_size.min(outside_vars.len());
    for size in 1..=capped_max {
        let mut current = Vec::with_capacity(size);
        collect_auto_windows(outside_vars, size, 0, &mut current, limit, &mut windows);
        if windows.len() >= limit {
            break;
        }
    }
    Ok(WindowSelection {
        windows,
        source: "auto_low_free",
        auto_low_free_candidate_windows: Some(candidate_windows),
        auto_component_hitting_candidate_windows: None,
        component_hitting_windows: Vec::new(),
        auto_component_family_candidate_windows: None,
        component_family_windows: Vec::new(),
        component_hook_targets: None,
    })
}

fn component_hitting_windows_for_targets(
    component_hook_targets: &Path,
    limit: Option<usize>,
) -> Result<WindowSelection> {
    let Some(limit) = limit else {
        bail!("--auto-component-hitting-windows requires --window-limit to keep reduced-CNF probes bounded");
    };
    let table = read_tsv_table(component_hook_targets)?;
    let mut candidates = parse_component_hitting_windows(&table)?;
    candidates.sort_by(component_hitting_order);
    let candidate_count = candidates.len();
    let selected: Vec<ComponentHittingWindow> = candidates.into_iter().take(limit).collect();
    let windows = selected
        .iter()
        .map(|candidate| Window {
            name: candidate.name.clone(),
            one_based_vars: candidate.one_based_vars.clone(),
        })
        .collect();
    Ok(WindowSelection {
        windows,
        source: "component_hitting",
        auto_low_free_candidate_windows: None,
        auto_component_hitting_candidate_windows: Some(candidate_count),
        component_hitting_windows: selected,
        auto_component_family_candidate_windows: None,
        component_family_windows: Vec::new(),
        component_hook_targets: Some(component_hook_targets.to_path_buf()),
    })
}

fn component_family_windows_for_targets(
    component_hook_targets: &Path,
    limit: Option<usize>,
) -> Result<WindowSelection> {
    let Some(limit) = limit else {
        bail!("--auto-component-family-windows requires --window-limit to keep reduced-CNF probes bounded");
    };
    let table = read_tsv_table(component_hook_targets)?;
    let components = parse_component_hitting_windows(&table)?;
    let mut candidates = component_family_windows(&components)?;
    candidates.sort_by(component_family_order);
    let candidate_count = candidates.len();
    let selected: Vec<ComponentFamilyWindow> = candidates.into_iter().take(limit).collect();
    let windows = selected
        .iter()
        .map(|candidate| Window {
            name: candidate.name.clone(),
            one_based_vars: candidate.one_based_vars.clone(),
        })
        .collect();
    Ok(WindowSelection {
        windows,
        source: "component_family",
        auto_low_free_candidate_windows: None,
        auto_component_hitting_candidate_windows: None,
        component_hitting_windows: Vec::new(),
        auto_component_family_candidate_windows: Some(candidate_count),
        component_family_windows: selected,
        component_hook_targets: Some(component_hook_targets.to_path_buf()),
    })
}

fn component_hitting_order(
    left: &ComponentHittingWindow,
    right: &ComponentHittingWindow,
) -> std::cmp::Ordering {
    (
        left.one_based_vars.len(),
        source_frame_class_priority(&left.source_frame_class),
        left.diagnostic_missing_literal_rows,
        left.clause_count,
        left.component_id,
    )
        .cmp(&(
            right.one_based_vars.len(),
            source_frame_class_priority(&right.source_frame_class),
            right.diagnostic_missing_literal_rows,
            right.clause_count,
            right.component_id,
        ))
}

fn component_family_order(
    left: &ComponentFamilyWindow,
    right: &ComponentFamilyWindow,
) -> std::cmp::Ordering {
    (
        left.one_based_vars.len(),
        left.diagnostic_missing_literal_rows,
        left.component_count,
        std::cmp::Reverse(left.covered_clause_count),
        &left.component_ids,
        &left.one_based_vars,
    )
        .cmp(&(
            right.one_based_vars.len(),
            right.diagnostic_missing_literal_rows,
            right.component_count,
            std::cmp::Reverse(right.covered_clause_count),
            &right.component_ids,
            &right.one_based_vars,
        ))
}

fn component_family_windows(
    components: &[ComponentHittingWindow],
) -> Result<Vec<ComponentFamilyWindow>> {
    if components.len() >= usize::BITS as usize {
        bail!(
            "component family window generation supports fewer than {} components, saw {}",
            usize::BITS,
            components.len()
        );
    }
    let required_families: BTreeSet<String> = ALLOWED_SOURCE_FRAME_FAMILIES
        .iter()
        .map(|family| (*family).to_string())
        .collect();
    let mut windows = Vec::new();
    for mask in 1usize..(1usize << components.len()) {
        let selected: Vec<&ComponentHittingWindow> = components
            .iter()
            .enumerate()
            .filter_map(|(idx, component)| {
                if mask & (1usize << idx) != 0 {
                    Some(component)
                } else {
                    None
                }
            })
            .collect();
        let covered_families = covered_component_families(&selected);
        if !required_families.is_subset(&covered_families) {
            continue;
        }
        windows.push(component_family_window_from_components(
            &selected,
            covered_families,
        ));
    }
    Ok(windows)
}

fn covered_component_families(components: &[&ComponentHittingWindow]) -> BTreeSet<String> {
    let mut families = BTreeSet::new();
    for component in components {
        for family in component
            .covered_real_source_families
            .split_whitespace()
            .filter(|family| *family != ".")
        {
            families.insert(family.to_string());
        }
    }
    families
}

fn component_family_window_from_components(
    components: &[&ComponentHittingWindow],
    covered_families: BTreeSet<String>,
) -> ComponentFamilyWindow {
    let component_ids: Vec<usize> = components
        .iter()
        .map(|component| component.component_id)
        .collect();
    let one_based_vars: Vec<usize> = components
        .iter()
        .flat_map(|component| component.one_based_vars.iter().copied())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let one_based_clause_ids: Vec<usize> = components
        .iter()
        .flat_map(|component| component.one_based_clause_ids.iter().copied())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let source_frame_classes: Vec<String> = components
        .iter()
        .map(|component| component.source_frame_class.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let diagnostic_missing_literal_rows = components
        .iter()
        .map(|component| component.diagnostic_missing_literal_rows)
        .sum();
    let component_part = component_ids
        .iter()
        .map(|component_id| format!("c{component_id}"))
        .collect::<Vec<_>>()
        .join("-");
    let var_part = one_based_vars
        .iter()
        .map(|var| format!("v{var}"))
        .collect::<Vec<_>>()
        .join("-");
    ComponentFamilyWindow {
        component_ids,
        name: format!("component-family-{component_part}-{var_part}"),
        one_based_vars,
        covered_real_source_families: covered_families.into_iter().collect(),
        source_frame_classes,
        diagnostic_missing_literal_rows,
        covered_clause_count: one_based_clause_ids.len(),
        one_based_clause_ids,
        component_count: components.len(),
    }
}

fn source_frame_class_priority(class: &str) -> usize {
    match class {
        "pure_frontier_frame" => 0,
        "mixed_frontier_scc_frame" => 1,
        "bridge_source_frame" => 2,
        _ => 3,
    }
}

fn parse_component_hitting_windows(table: &TsvTable) -> Result<Vec<ComponentHittingWindow>> {
    table
        .rows
        .iter()
        .enumerate()
        .map(|(idx, row)| parse_component_hitting_window_row(row, idx + 2))
        .collect()
}

fn parse_component_hitting_window_row(
    row: &BTreeMap<String, String>,
    line_number: usize,
) -> Result<ComponentHittingWindow> {
    let component_id = required_usize_cell(row, "component_id", line_number)?;
    let clause_count = required_usize_cell(row, "clause_count", line_number)?;
    let min_size = required_usize_cell(row, "min_variable_hitting_set_size", line_number)?;
    let diagnostic_missing_literal_rows =
        required_usize_cell(row, "diagnostic_missing_literal_rows", line_number)?;
    let representative = required_cell(row, "representative_minimal_vars", line_number)?;
    let one_based_vars = parse_var_selector(representative)
        .with_context(|| format!("component hook row {line_number} representative vars"))?;
    if one_based_vars.len() != min_size {
        bail!(
            "component hook row {line_number} representative_minimal_vars has {} vars but min_variable_hitting_set_size is {min_size}",
            one_based_vars.len()
        );
    }
    let clause_ids = required_cell(row, "clause_ids", line_number)?;
    let one_based_clause_ids = parse_space_usizes(clause_ids)
        .with_context(|| format!("component hook row {line_number} clause_ids"))?;
    let source_frame_class = required_cell(row, "source_frame_class", line_number)?.to_string();
    let covered_real_source_families =
        required_cell(row, "covered_real_source_families", line_number)?.to_string();
    let construction_action = required_cell(row, "construction_action", line_number)?.to_string();
    let name = format!(
        "component-{}-hit-{}",
        component_id,
        one_based_vars
            .iter()
            .map(|var| format!("v{var}"))
            .collect::<Vec<_>>()
            .join("-")
    );
    Ok(ComponentHittingWindow {
        component_id,
        name,
        one_based_vars,
        min_variable_hitting_set_size: min_size,
        diagnostic_missing_literal_rows,
        clause_count,
        one_based_clause_ids,
        source_frame_class,
        covered_real_source_families,
        construction_action,
    })
}

fn required_cell<'a>(
    row: &'a BTreeMap<String, String>,
    column: &str,
    line_number: usize,
) -> Result<&'a str> {
    let value = row
        .get(column)
        .with_context(|| format!("component hook row {line_number} missing column {column}"))?;
    if value.trim().is_empty() || value == "." {
        bail!("component hook row {line_number} has empty {column}");
    }
    Ok(value)
}

fn required_usize_cell(
    row: &BTreeMap<String, String>,
    column: &str,
    line_number: usize,
) -> Result<usize> {
    required_cell(row, column, line_number)?
        .parse::<usize>()
        .with_context(|| format!("component hook row {line_number} invalid {column}"))
}

fn parse_space_usizes(raw: &str) -> Result<Vec<usize>> {
    let mut values = Vec::new();
    for cell in raw.split_whitespace() {
        values.push(cell.parse::<usize>()?);
    }
    if values.is_empty() {
        bail!("empty usize list");
    }
    Ok(values)
}

fn component_hitting_window_json(candidate: &ComponentHittingWindow) -> JsonValue {
    json!({
        "component_id": candidate.component_id,
        "name": &candidate.name,
        "one_based_vars": &candidate.one_based_vars,
        "min_variable_hitting_set_size": candidate.min_variable_hitting_set_size,
        "diagnostic_missing_literal_rows": candidate.diagnostic_missing_literal_rows,
        "clause_count": candidate.clause_count,
        "one_based_clause_ids": &candidate.one_based_clause_ids,
        "source_frame_class": &candidate.source_frame_class,
        "covered_real_source_families": &candidate.covered_real_source_families,
        "construction_action": &candidate.construction_action,
    })
}

fn component_family_window_json(candidate: &ComponentFamilyWindow) -> JsonValue {
    json!({
        "component_ids": &candidate.component_ids,
        "name": &candidate.name,
        "one_based_vars": &candidate.one_based_vars,
        "covered_real_source_families": &candidate.covered_real_source_families,
        "source_frame_classes": &candidate.source_frame_classes,
        "diagnostic_missing_literal_rows": candidate.diagnostic_missing_literal_rows,
        "covered_clause_count": candidate.covered_clause_count,
        "one_based_clause_ids": &candidate.one_based_clause_ids,
        "component_count": candidate.component_count,
    })
}

fn source_frame_value_overlay_json(overlay: &SourceFrameValueOverlay) -> JsonValue {
    json!({
        "name": &overlay.window.name,
        "component_ids": &overlay.window.component_ids,
        "one_based_window_vars": &overlay.window.one_based_vars,
        "one_based_clause_ids": &overlay.window.one_based_clause_ids,
        "covered_real_source_families": &overlay.window.covered_real_source_families,
        "source_rows_seen": overlay.source_rows_seen,
        "valid_binding_rows": overlay.valid_binding_rows,
        "invalid_binding_rows": overlay.invalid_binding_rows,
        "duplicate_same_required_values": overlay.duplicate_same_required_values,
        "conflicting_required_values": overlay.conflicting_required_values,
        "conflicting_one_based_vars": &overlay.conflicting_one_based_vars,
        "source_frame_row_id_samples": &overlay.source_frame_row_id_samples,
        "set_value_count": overlay.assignments.len(),
        "one_based_set_values": overlay.assignments.iter().map(|(var, value)| json!({"var": var + 1, "value": value})).collect::<Vec<_>>(),
    })
}

fn auto_low_free_candidate_count(outside_var_count: usize, max_size: usize) -> usize {
    (1..=max_size.min(outside_var_count))
        .map(|size| saturating_binomial(outside_var_count, size))
        .fold(0usize, usize::saturating_add)
}

fn saturating_binomial(n: usize, k: usize) -> usize {
    if k > n {
        return 0;
    }
    let k = k.min(n - k);
    let mut result = 1u128;
    for step in 1..=k {
        let numerator = (n - k + step) as u128;
        result = result.saturating_mul(numerator) / step as u128;
        if result >= usize::MAX as u128 {
            return usize::MAX;
        }
    }
    result as usize
}

fn collect_auto_windows(
    outside_vars: &[usize],
    size: usize,
    start: usize,
    current: &mut Vec<usize>,
    limit: usize,
    windows: &mut Vec<Window>,
) {
    if windows.len() >= limit {
        return;
    }
    if current.len() == size {
        let one_based_vars: Vec<usize> = current.iter().map(|var| var + 1).collect();
        let name = format!(
            "auto-s{}-{}",
            size,
            one_based_vars
                .iter()
                .map(|var| format!("v{var}"))
                .collect::<Vec<_>>()
                .join("-")
        );
        windows.push(Window {
            name,
            one_based_vars,
        });
        return;
    }
    let needed = size - current.len();
    if outside_vars.len() < needed || start > outside_vars.len() - needed {
        return;
    }
    for idx in start..=outside_vars.len() - needed {
        current.push(outside_vars[idx]);
        collect_auto_windows(outside_vars, size, idx + 1, current, limit, windows);
        current.pop();
        if windows.len() >= limit {
            return;
        }
    }
}

fn default_windows() -> Vec<Window> {
    vec![
        Window {
            name: "450-468".to_string(),
            one_based_vars: (450..=468).collect(),
        },
        Window {
            name: "450-459-470-471".to_string(),
            one_based_vars: (450..=459).chain([470, 471]).collect(),
        },
        Window {
            name: "458-459-468-470-471".to_string(),
            one_based_vars: vec![458, 459, 468, 470, 471],
        },
        Window {
            name: "469-471-480-482-483".to_string(),
            one_based_vars: vec![469, 471, 480, 482, 483],
        },
        Window {
            name: "496-498-500-519".to_string(),
            one_based_vars: vec![496, 498, 500, 519],
        },
        Window {
            name: "97-98-99-110".to_string(),
            one_based_vars: vec![97, 98, 99, 110],
        },
        Window {
            name: "350-351-352-363".to_string(),
            one_based_vars: vec![350, 351, 352, 363],
        },
        Window {
            name: "966-968-970".to_string(),
            one_based_vars: vec![966, 968, 970],
        },
    ]
}

fn parse_window(raw: &str) -> Result<Window> {
    let (name, selector) = raw.split_once('=').unwrap_or((raw, raw));
    let name = name.trim();
    if name.is_empty() {
        bail!("window name is empty: {raw}");
    }
    if !name
        .chars()
        .all(|ch| ch.is_ascii_alphanumeric() || matches!(ch, '.' | '_' | '-'))
    {
        bail!("window name must be path-safe: {name}");
    }
    Ok(Window {
        name: name.to_string(),
        one_based_vars: parse_var_selector(selector)?,
    })
}

fn parse_var_selector(raw: &str) -> Result<Vec<usize>> {
    let mut values = Vec::new();
    for cell in raw.replace(',', " ").split_whitespace() {
        if let Some((start, end)) = cell.split_once('-') {
            let start = start.parse::<usize>()?;
            let end = end.parse::<usize>()?;
            if start == 0 || start > end {
                bail!("invalid one-based variable range: {cell}");
            }
            values.extend(start..=end);
        } else {
            let value = cell.parse::<usize>()?;
            if value == 0 {
                bail!("invalid one-based variable: {cell}");
            }
            values.push(value);
        }
    }
    if values.is_empty() {
        bail!("empty variable selector");
    }
    let unique: BTreeSet<usize> = values.iter().copied().collect();
    if unique.len() != values.len() {
        bail!("duplicate variables in selector: {raw}");
    }
    Ok(values)
}

fn counts_for_rows(rows: &[JsonValue], _kind: &str) -> RowCounts {
    let mut counts = RowCounts::default();
    for row in rows {
        match row["status"].as_str().unwrap_or("") {
            "unsat_verified" => counts.unsat_verified += 1,
            "unsat_unverified" => counts.unsat_unverified += 1,
            "sat_valid_model" | "sat_valid_original_model" => counts.sat_valid += 1,
            "sat_invalid_or_incomplete_model" => counts.sat_invalid += 1,
            "timeout" => counts.timeout += 1,
            _ => counts.unknown_or_error += 1,
        }
    }
    counts
}

fn write_payload(
    root: &Path,
    common: &CommonOptions,
    stem: &str,
    payload: &JsonValue,
) -> Result<()> {
    let output = output_path(root, common, stem)?;
    write_json(&output, payload)?;
    println!("{}", serde_json::to_string(&payload["verdict"])?);
    Ok(())
}

fn write_json(path: &Path, payload: &JsonValue) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(path, serde_json::to_string_pretty(payload)? + "\n")?;
    Ok(())
}

fn ledger_paths(root: &Path, common: &CommonOptions) -> Vec<PathBuf> {
    if common.w210_ledgers.is_empty() {
        DEFAULT_W210_LEDGERS
            .iter()
            .map(|path| resolve_path(root, Path::new(path)))
            .collect()
    } else {
        common
            .w210_ledgers
            .iter()
            .map(|path| resolve_path(root, path))
            .collect()
    }
}

fn output_path(root: &Path, common: &CommonOptions, stem: &str) -> Result<PathBuf> {
    Ok(match &common.output {
        Some(path) => resolve_path(root, path),
        None => root.join(DEFAULT_OUTPUT_DIR).join(format!("{stem}.json")),
    })
}

fn prepare_work_dir(root: &Path, common: &CommonOptions, stem: &str) -> Result<(PathBuf, bool)> {
    if let Some(path) = &common.work_dir {
        let path = resolve_path(root, path);
        fs::create_dir_all(&path)?;
        Ok((path, false))
    } else {
        Ok((
            make_temp_dir(&format!("ay-9424-{stem}"))?,
            !common.retain_work,
        ))
    }
}

fn resolve_path(root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        root.join(path)
    }
}

fn repo_root() -> Result<PathBuf> {
    std::env::current_dir().context("failed to get current directory")
}

fn ay_bin(common: &CommonOptions) -> Result<PathBuf> {
    match &common.ay_bin {
        Some(path) => Ok(path.clone()),
        None => std::env::current_exe().context("failed to resolve current executable"),
    }
}

fn ensure_timeout(common: &CommonOptions) -> Result<()> {
    if common.timeout_sec == 0 {
        bail!("--timeout-sec must be positive");
    }
    Ok(())
}

fn git_head(root: &Path) -> Option<String> {
    let output = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(root)
        .output()
        .ok()?;
    if output.status.success() {
        Some(String::from_utf8_lossy(&output.stdout).trim().to_string())
    } else {
        None
    }
}

#[cfg(test)]
mod full_cnf_objective_producer_tests {
    use std::collections::BTreeSet;
    use std::path::Path;

    use super::*;

    #[test]
    fn full_cnf_retains_only_nonempty_strict_improvements() {
        assert!(full_cnf_retains_strict_update(8, 7, false));
        assert!(!full_cnf_retains_strict_update(8, 8, false));
        assert!(!full_cnf_retains_strict_update(8, 9, false));
        assert!(!full_cnf_retains_strict_update(8, 7, true));
    }

    #[test]
    fn full_cnf_neutral_bridge_requires_opt_in_and_unseen_residual() {
        let current = vec![1014, 5649, 6506, 10594];
        let neutral_new = vec![5649, 6506, 6845, 10594];
        let mut seen = BTreeSet::new();
        seen.insert(current.clone());

        let strict = full_cnf_update_decision(&current, &[5649, 6506], false, false, &seen);
        assert!(strict.accepted);
        assert!(strict.strict_improvement);
        assert!(!strict.neutral_bridge);

        let disabled = full_cnf_update_decision(&current, &neutral_new, false, false, &seen);
        assert!(!disabled.accepted);
        assert!(!disabled.neutral_bridge);

        let enabled = full_cnf_update_decision(&current, &neutral_new, false, true, &seen);
        assert!(enabled.accepted);
        assert!(!enabled.strict_improvement);
        assert!(enabled.neutral_bridge);

        seen.insert(neutral_new.clone());
        let repeated = full_cnf_update_decision(&current, &neutral_new, false, true, &seen);
        assert!(!repeated.accepted);
        assert!(!repeated.neutral_bridge);

        let empty = full_cnf_update_decision(&current, &[5649, 6506], true, true, &seen);
        assert!(!empty.accepted);
    }

    #[test]
    fn full_cnf_verdict_requires_checker_before_authority() {
        let residual = full_cnf_objective_verdict_json(false, true);
        assert_eq!(residual["sat_output_authority"], false);
        assert_eq!(residual["model_output_authority"], false);
        assert_eq!(residual["solver_verdict_authority"], false);

        let unchecked = full_cnf_objective_verdict_json(true, false);
        assert_eq!(unchecked["sat_output_authority"], false);
        assert_eq!(unchecked["model_output_authority"], false);
        assert_eq!(unchecked["solver_verdict_authority"], false);

        let checked = full_cnf_objective_verdict_json(true, true);
        assert_eq!(checked["sat_output_authority"], true);
        assert_eq!(checked["model_output_authority"], true);
        assert_eq!(checked["solver_verdict_authority"], true);
        assert_eq!(checked["route_admitted"], false);
        assert_eq!(checked["sat_comp_progress_claim"], false);
    }

    #[test]
    fn full_cnf_model_stdout_round_trips_through_model_parser() {
        let stdout = render_satcomp_model_stdout(&[true, false, true]);
        let (assignment, stats) = parse_solver_model(&stdout, 3);
        assert_eq!(assignment, Some(vec![true, false, true]));
        assert_eq!(stats["missing_model_var_count"], 0);
        assert_eq!(stats["duplicate_conflicting_lits"], 0);
    }

    #[test]
    fn full_cnf_reported_path_matches_relative_or_absolute_artifacts() {
        let root = Path::new("/tmp/ay-full-cnf-test-root");
        let expected = root.join("target/model.out");
        assert!(full_cnf_reported_path_matches(
            root,
            "target/model.out",
            &expected
        ));
        assert!(full_cnf_reported_path_matches(
            root,
            "/tmp/ay-full-cnf-test-root/target/model.out",
            &expected
        ));
        assert!(!full_cnf_reported_path_matches(
            root,
            "target/other.out",
            &expected
        ));
    }
}
