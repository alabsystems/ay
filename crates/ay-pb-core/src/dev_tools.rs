// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Typed implementation surface for the non-default `ay-pb-dev` binary.
//!
//! This module is compiled only with `dev-tools`. It deliberately wraps
//! crate-internal solver lanes rather than making those lanes part of ay-pb's
//! production API.

use std::fs::{File, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::optimize::two_club::{
    self, LpNodeBound, TwoClubCampaignPartition as InternalPartition,
    TwoClubCampaignResult as InternalResult, TwoClubRuntime,
};
use crate::{PbInstance, PbObjective};

#[derive(Debug, thiserror::Error)]
pub enum DevToolError {
    #[error("invalid developer-tool configuration: {0}")]
    InvalidConfig(String),
    #[error("developer campaign declined: {0}")]
    Declined(&'static str),
    #[error("{action} {path}: {source}")]
    Io {
        action: &'static str,
        path: String,
        #[source]
        source: io::Error,
    },
    #[error("Farkas anchor generation failed: {0}")]
    Farkas(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TwoClubBranchRule {
    First,
    ViolatingDegree,
    Marked,
    /// Marked branching with MIN-violating-degree vertex selection.
    MarkedMinDegree,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TwoClubPartition {
    Whole,
    Worker {
        worker: usize,
        workers: usize,
    },
    DepthTwo {
        base_mod: usize,
        classes: Vec<usize>,
        worker: usize,
        workers: usize,
    },
    Pivot {
        pivot_count: usize,
        worker: usize,
        workers: usize,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TwoClubLpConfig {
    pub enabled: bool,
    pub warmup: u64,
    pub cadence: u64,
    pub window: usize,
    pub max_rows: usize,
    pub low_margin: usize,
    pub ceiling: bool,
    pub exact_margin: i128,
    /// Strengthened neighborhood rows (Carvalho–Almeida lifting) in every
    /// float LP solve (`ay-pb-dev two-club --nbhd-rows`). Default OFF.
    ///
    /// MEASURED NEGATIVE on 2club200v15p5scn: the family is adversarially
    /// verified VALID (exhaustive per-graph validity gates in
    /// `optimize::two_club`), and its rows were used in ~75% of prunes when
    /// armed — yet the ceiling failure ubs at c=149/151 were IDENTICAL to off
    /// (72.2/73.7) with a 4.3x node-throughput tax; see
    /// the development design notes Do not arm it
    /// there expecting gains; it is kept as a documented capability for other
    /// instances and for the validity gates.
    pub nbhd_rows: bool,
}

impl Default for TwoClubLpConfig {
    fn default() -> Self {
        let config = LpNodeBound::standard();
        Self {
            enabled: config.enabled,
            warmup: config.warmup,
            cadence: config.cadence,
            window: config.window,
            max_rows: config.max_rows,
            low_margin: config.low_margin,
            ceiling: config.ceiling,
            exact_margin: config.exact_margin,
            nbhd_rows: config.nbhd_rows,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwoClubSdpConfig {
    pub worker: PathBuf,
    pub instance: PathBuf,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwoClubConfig {
    pub max_nodes_per_cell: u64,
    pub branch_rule: TwoClubBranchRule,
    pub trace: bool,
    pub dump_frontier: bool,
    pub sdp: Option<TwoClubSdpConfig>,
    pub lp: TwoClubLpConfig,
    pub partition: TwoClubPartition,
}

impl Default for TwoClubConfig {
    fn default() -> Self {
        Self {
            max_nodes_per_cell: 20_000_000,
            branch_rule: TwoClubBranchRule::First,
            trace: false,
            dump_frontier: false,
            sdp: None,
            lp: TwoClubLpConfig::default(),
            partition: TwoClubPartition::Whole,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TwoClubOutcome {
    Proved { objective: i128, selected: usize },
    Cutoff,
    Worker { best: usize, all_done: bool },
}

pub fn run_two_club(
    instance: &PbInstance,
    objective: &PbObjective,
    seed: Option<&[bool]>,
    config: &TwoClubConfig,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Result<TwoClubOutcome, DevToolError> {
    fn validate_worker(worker: usize, workers: usize) -> Result<(), DevToolError> {
        if workers == 0 {
            return Err(DevToolError::InvalidConfig(
                "workers must be positive".to_owned(),
            ));
        }
        if worker >= workers {
            return Err(DevToolError::InvalidConfig(format!(
                "worker {worker} is outside 0..{workers}"
            )));
        }
        Ok(())
    }

    let partition = match &config.partition {
        TwoClubPartition::Whole => InternalPartition::Whole,
        TwoClubPartition::Worker { worker, workers } => {
            validate_worker(*worker, *workers)?;
            InternalPartition::Worker {
                worker: *worker,
                workers: *workers,
            }
        }
        TwoClubPartition::DepthTwo {
            base_mod,
            classes,
            worker,
            workers,
        } => {
            validate_worker(*worker, *workers)?;
            if *base_mod == 0 {
                return Err(DevToolError::InvalidConfig(
                    "depth-two base-mod must be positive".to_owned(),
                ));
            }
            if classes.is_empty() || classes.iter().any(|class| *class >= *base_mod) {
                return Err(DevToolError::InvalidConfig(format!(
                    "depth-two classes must be nonempty and below base-mod {base_mod}"
                )));
            }
            InternalPartition::DepthTwo {
                base_mod: *base_mod,
                classes: classes.as_slice(),
                worker: *worker,
                workers: *workers,
            }
        }
        TwoClubPartition::Pivot {
            pivot_count,
            worker,
            workers,
        } => {
            validate_worker(*worker, *workers)?;
            if *pivot_count > 20 {
                return Err(DevToolError::InvalidConfig(
                    "pivot-count must be at most 20".to_owned(),
                ));
            }
            InternalPartition::Pivot {
                pivot_count: *pivot_count,
                worker: *worker,
                workers: *workers,
            }
        }
    };
    let lp = if config.lp.enabled {
        LpNodeBound {
            enabled: true,
            warmup: config.lp.warmup,
            cadence: config.lp.cadence,
            window: config.lp.window,
            max_rows: config.lp.max_rows,
            low_margin: config.lp.low_margin,
            ceiling: config.lp.ceiling,
            exact_margin: config.lp.exact_margin,
            nbhd_rows: config.lp.nbhd_rows,
        }
    } else {
        LpNodeBound::disabled()
    };
    let mut runtime = match config.branch_rule {
        TwoClubBranchRule::First => TwoClubRuntime::explicit(
            config.max_nodes_per_cell,
            false,
            config.trace,
            config.dump_frontier,
        ),
        TwoClubBranchRule::ViolatingDegree => TwoClubRuntime::explicit(
            config.max_nodes_per_cell,
            true,
            config.trace,
            config.dump_frontier,
        ),
        TwoClubBranchRule::Marked => TwoClubRuntime::explicit_marked(
            config.max_nodes_per_cell,
            config.trace,
            config.dump_frontier,
        ),
        TwoClubBranchRule::MarkedMinDegree => TwoClubRuntime::explicit_marked_min_degree(
            config.max_nodes_per_cell,
            config.trace,
            config.dump_frontier,
        ),
    };
    if let Some(sdp) = &config.sdp {
        if !config.lp.enabled || !config.lp.ceiling {
            return Err(DevToolError::InvalidConfig(
                "the SDP worker requires the LP ceiling tier".to_owned(),
            ));
        }
        if !sdp.worker.is_file() {
            return Err(DevToolError::InvalidConfig(format!(
                "SDP worker is not a file: {}",
                sdp.worker.display()
            )));
        }
        if !sdp.instance.is_file() {
            return Err(DevToolError::InvalidConfig(format!(
                "SDP instance is not a file: {}",
                sdp.instance.display()
            )));
        }
        runtime = runtime.with_sdp_worker(&sdp.worker, &sdp.instance);
    }
    let result = two_club::run_configured_campaign(
        instance,
        objective,
        seed,
        partition,
        &lp,
        runtime,
        should_stop,
        on_improve,
    )
    .ok_or(DevToolError::Declined("2-club recognizer or required seed"))?;
    Ok(match result {
        InternalResult::Whole(Some(solution)) => TwoClubOutcome::Proved {
            objective: solution.objective.ok_or(DevToolError::Declined(
                "proved 2-club result has no objective",
            ))?,
            selected: solution.assignment.iter().filter(|&&value| value).count(),
        },
        InternalResult::Whole(None) => TwoClubOutcome::Cutoff,
        InternalResult::Worker((best, all_done)) => TwoClubOutcome::Worker { best, all_done },
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProbeEngine {
    Bnn,
    BranchAndBound,
    Sls,
    /// Fixed-cardinality violation descent
    /// ([`crate::optimize::card_descent`]) — unicost covering only.
    CardDescent,
    Lp,
    SafeLp,
    Milp,
    Floor,
    /// Paired A/B of the Lagrangian subgradient floor with and without the
    /// single-row-closure separator, over the SAME preprocessed constraints
    /// the production consumer (`native_oll::lp_relaxation_floor`) hands it.
    SubgradientFloor,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProbeConfig {
    pub node_budget: u64,
    pub milp_budget: Duration,
}

impl Default for ProbeConfig {
    fn default() -> Self {
        Self {
            node_budget: 10_000_000,
            milp_budget: Duration::from_mins(1),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProbeOutcome {
    Bnn {
        recognized: bool,
        seeded: bool,
        best: Option<i128>,
    },
    BranchAndBound {
        value: Option<i128>,
        proven_optimal: bool,
    },
    Sls {
        best: Option<i128>,
    },
    CardDescent {
        best: Option<i128>,
    },
    Lp {
        base: Option<i128>,
        with_cuts: Option<i128>,
        /// Ablation twin of `with_cuts` with the single-row-closure separator
        /// disabled, computed back-to-back in the same process so the pair is
        /// load-immune. `with_cuts - with_cuts_no_src` is SRC's contribution
        /// to the simplex cut loop on this instance.
        with_cuts_no_src: Option<i128>,
        /// Structured-family / SRC cuts separated during the `with_cuts` run
        /// (pre-dedup totals over rounds).
        family_cuts: u32,
        src_cuts: u32,
    },
    SafeLp {
        bound: Option<i128>,
        finite_point: bool,
    },
    Milp {
        optimum: Option<i128>,
    },
    Floor {
        certified: Option<i128>,
    },
    SubgradientFloor {
        /// Whether preprocessing simplified the instance (mirroring the
        /// production consumer) or the original constraints were used.
        preprocessed: bool,
        with_src: Option<i128>,
        without_src: Option<i128>,
        /// Cuts separated during the `with_src` arm (pre-dedup totals).
        family_cuts: u32,
        src_cuts: u32,
        /// Family cuts separated during the `without_src` arm — the paired
        /// control for how much of the loop SRC displaces.
        family_cuts_without_src: u32,
    },
}

pub fn run_probe(
    instance: &PbInstance,
    engine: ProbeEngine,
    config: ProbeConfig,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Result<ProbeOutcome, DevToolError> {
    run_probe_impl(instance, engine, config, should_stop, on_improve, None)
}

/// Probe entry used by the leaf package that owns the external MILP engine.
#[doc(hidden)]
pub fn run_probe_with_upgrade(
    instance: &PbInstance,
    engine: ProbeEngine,
    config: ProbeConfig,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
    optimum_upgrade: &'static dyn crate::portfolio::LinearOptimumUpgrade,
) -> Result<ProbeOutcome, DevToolError> {
    run_probe_impl(
        instance,
        engine,
        config,
        should_stop,
        on_improve,
        Some(optimum_upgrade),
    )
}

fn run_probe_impl(
    instance: &PbInstance,
    engine: ProbeEngine,
    config: ProbeConfig,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
    optimum_upgrade: Option<&'static dyn crate::portfolio::LinearOptimumUpgrade>,
) -> Result<ProbeOutcome, DevToolError> {
    let objective = instance.objective.as_ref().ok_or_else(|| {
        DevToolError::InvalidConfig("probe requires an optimization objective".to_owned())
    })?;
    Ok(match engine {
        ProbeEngine::Bnn => {
            let recognized = crate::optimize::bnn_feas::is_recognized(instance, objective);
            let seed = crate::optimize::bnn_feas::seed(instance, objective);
            let seed_value = seed
                .as_deref()
                .map(|assignment| crate::solver::eval_objective(objective, assignment));
            if let (Some(value), Some(assignment)) = (seed_value, seed.as_deref()) {
                on_improve(value, assignment);
            }
            let best = crate::optimize::bnn_feas::enumerate_adversarial_incumbents(
                instance,
                objective,
                seed_value,
                should_stop,
                on_improve,
            )
            .filter(|value| *value != i128::MAX);
            ProbeOutcome::Bnn {
                recognized,
                seeded: seed.is_some(),
                best,
            }
        }
        ProbeEngine::BranchAndBound => {
            let result = crate::optimize::branch_and_bound::solve_branch_and_bound(
                instance,
                objective,
                None,
                config.node_budget,
                should_stop,
            );
            ProbeOutcome::BranchAndBound {
                value: result.as_ref().map(|result| result.value),
                proven_optimal: result.is_some_and(|result| result.proven_optimal),
            }
        }
        ProbeEngine::Sls => {
            let best = crate::optimize::sls::search_with_options(
                instance,
                objective,
                None,
                should_stop,
                on_improve,
                false,
            )
            .map(|result| result.objective);
            ProbeOutcome::Sls { best }
        }
        ProbeEngine::CardDescent => {
            let best = crate::optimize::card_descent::search(
                instance,
                objective,
                None,
                should_stop,
                on_improve,
            );
            ProbeOutcome::CardDescent { best }
        }
        ProbeEngine::Lp => {
            let base = crate::optimize::lp_bound::lp_lower_bound_no_cuts(
                objective,
                &instance.constraints,
                instance.num_vars,
                should_stop,
            );
            crate::optimize::lp_bound::reset_cut_loop_observation();
            let with_cuts = crate::optimize::lp_bound::lp_lower_bound(
                objective,
                &instance.constraints,
                instance.num_vars,
                should_stop,
            );
            let observation = crate::optimize::lp_bound::cut_loop_observation();
            let with_cuts_no_src = crate::optimize::lp_bound::lp_lower_bound_without_src(
                objective,
                &instance.constraints,
                instance.num_vars,
                should_stop,
            );
            ProbeOutcome::Lp {
                base,
                with_cuts,
                with_cuts_no_src,
                family_cuts: observation.simplex_family_cuts,
                src_cuts: observation.simplex_src_cuts,
            }
        }
        ProbeEngine::SafeLp => {
            let (bound, point) = crate::optimize::safe_lp_bound::safe_lp_bound_and_point(
                objective,
                &instance.constraints,
                instance.num_vars,
                should_stop,
            );
            ProbeOutcome::SafeLp {
                bound,
                finite_point: point
                    .is_some_and(|point| point.iter().all(|value| value.is_finite())),
            }
        }
        ProbeEngine::Milp => {
            let optimum = optimum_upgrade
                .filter(|upgrade| upgrade.eligible(instance, objective))
                .and_then(|upgrade| {
                    crate::portfolio::run_linear_optimum_upgrade(
                        upgrade,
                        instance,
                        objective,
                        None,
                        config.milp_budget,
                        on_improve,
                    )
                })
                .map(|result| result.value);
            ProbeOutcome::Milp { optimum }
        }
        ProbeEngine::Floor => ProbeOutcome::Floor {
            certified: crate::proof::certified_objective_floor_interruptible(
                &instance.constraints,
                objective,
                should_stop,
            ),
        },
        ProbeEngine::SubgradientFloor => {
            // Mirror the production consumer (`native_oll::lp_relaxation_floor`):
            // the subgradient tier runs over the PREPROCESSED (strengthened)
            // constraints. On UNSAT/Interrupted fall back to the originals so
            // the probe still reports something comparable.
            let strengthened = match crate::preprocess::preprocess_interruptible(instance, || {
                should_stop()
            }) {
                crate::preprocess::PreprocessResult::Simplified { instance, .. } => Some(instance),
                _ => None,
            };
            let preprocessed = strengthened.is_some();
            let (constraints, num_vars) = strengthened
                .as_ref()
                .map_or((&instance.constraints, instance.num_vars), |simplified| {
                    (&simplified.constraints, simplified.num_vars)
                });
            crate::optimize::lp_bound::reset_cut_loop_observation();
            let with_src = crate::optimize::lp_bound::lagrangian_dual_floor(
                objective,
                constraints,
                num_vars,
                should_stop,
            );
            let with_observation = crate::optimize::lp_bound::cut_loop_observation();
            crate::optimize::lp_bound::reset_cut_loop_observation();
            let without_src = crate::optimize::lp_bound::lagrangian_dual_floor_without_src(
                objective,
                constraints,
                num_vars,
                should_stop,
            );
            let without_observation = crate::optimize::lp_bound::cut_loop_observation();
            ProbeOutcome::SubgradientFloor {
                preprocessed,
                with_src,
                without_src,
                family_cuts: with_observation.subgradient_family_cuts,
                src_cuts: with_observation.subgradient_src_cuts,
                family_cuts_without_src: without_observation.subgradient_family_cuts,
            }
        }
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FarkasAnchorPaths {
    pub valid: PathBuf,
    pub tampered: PathBuf,
}

fn stage_atomic(path: &Path, contents: &[u8]) -> io::Result<(PathBuf, File)> {
    let parent = path
        .parent()
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "output has no parent"))?;
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "non-UTF-8 output name"))?;
    for attempt in 0..100u32 {
        let temporary = parent.join(format!(".{name}.tmp-{}-{attempt}", std::process::id()));
        match OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary)
        {
            Ok(mut file) => {
                if let Err(error) = file.write_all(contents).and_then(|()| file.sync_all()) {
                    drop(file);
                    let _ = std::fs::remove_file(&temporary);
                    return Err(error);
                }
                return Ok((temporary, file));
            }
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        }
    }
    Err(io::Error::new(
        io::ErrorKind::AlreadyExists,
        "could not reserve an atomic temporary file",
    ))
}

/// Regenerates both Lean anchor fixtures. Both complete payloads are validated
/// and staged before either destination is replaced; each replacement is an
/// atomic same-directory rename.
pub fn write_farkas_anchor(output_dir: &Path) -> Result<FarkasAnchorPaths, DevToolError> {
    std::fs::create_dir_all(output_dir).map_err(|source| DevToolError::Io {
        action: "create",
        path: output_dir.display().to_string(),
        source,
    })?;
    let (valid_json, tampered_json) =
        crate::optimize::lp_bound::generate_farkas_anchor_json().map_err(DevToolError::Farkas)?;
    let valid = output_dir.join("valid_cert.json");
    let tampered = output_dir.join("tampered_cert.json");
    let (valid_temp, valid_file) =
        stage_atomic(&valid, valid_json.as_bytes()).map_err(|source| DevToolError::Io {
            action: "stage",
            path: valid.display().to_string(),
            source,
        })?;
    let (tampered_temp, tampered_file) = match stage_atomic(&tampered, tampered_json.as_bytes()) {
        Ok(staged) => staged,
        Err(error) => {
            drop(valid_file);
            let _ = std::fs::remove_file(&valid_temp);
            return Err(DevToolError::Io {
                action: "stage",
                path: tampered.display().to_string(),
                source: error,
            });
        }
    };
    drop(valid_file);
    drop(tampered_file);

    if let Err(error) = std::fs::rename(&valid_temp, &valid) {
        let _ = std::fs::remove_file(&valid_temp);
        let _ = std::fs::remove_file(&tampered_temp);
        return Err(DevToolError::Io {
            action: "commit",
            path: valid.display().to_string(),
            source: error,
        });
    }
    if let Err(error) = std::fs::rename(&tampered_temp, &tampered) {
        let _ = std::fs::remove_file(&tampered_temp);
        return Err(DevToolError::Io {
            action: "commit",
            path: tampered.display().to_string(),
            source: error,
        });
    }
    Ok(FarkasAnchorPaths { valid, tampered })
}
