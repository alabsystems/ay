// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Root formulation preparation before the branch-and-bound state is built.
//!
//! Phase order is part of the solver contract. Exact bound propagation and
//! probing produce a tightened model; symmetry is detected in that frame;
//! structural branching advice is read from the caller model; symmetry rows
//! and integer-hull-preserving cuts then produce the model searched by B&B.
//! Exported evidence still belongs to the caller frame, so any transformation
//! that preserves the optimum without preserving literal-tree exhaustiveness
//! must poison whole-tree capture before search starts.

use std::num::NonZeroUsize;
use std::time::{Duration, Instant};

use num_rational::BigRational;

use crate::model::{Col, Model};
use crate::opts::SolveOpts;
use crate::outcome::{Outcome, UnknownReason};

use super::{
    add_root_cuts_rounds, bottleneck_granularity, child_order, market_split_shape,
    pure_general_integer_shape, root_probe_wanted, ChildOrder, SearchMode, PRESOLVE_SHARE,
    ROOT_PROBE_CAP, ROOT_PROBE_SHARE, SYM_ROWS_TOTAL,
};

mod structural;
#[cfg(test)]
mod tests;

/// Inputs whose order defines the root formulation seen by the search.
pub(super) struct RootFormulationRequest<'a> {
    pub(super) model: &'a Model,
    pub(super) opts: &'a SolveOpts,
    pub(super) mode: SearchMode,
    pub(super) shared_binary_prefix: &'a [Col],
    pub(super) capture: &'a mut crate::tree_cert::TreeCapture,
    pub(super) attribution_started: Instant,
}

/// Formulation and structural advice derived before constructing the LP state.
pub(super) struct RootFormulation {
    pub(super) model: Model,
    pub(super) mode: SearchMode,
    pub(super) market: MarketProfile,
    /// Nonzero worker count is also the proof-first route's authority token.
    pub(super) proof_first_workers: Option<NonZeroUsize>,
    pub(super) child_order: ChildOrder,
    pub(super) symmetry: Option<crate::symmetry::Symmetry>,
    pub(super) symmetry_pins: usize,
    pub(super) symmetry_rows_added: bool,
    pub(super) gub_supports: Option<Vec<Vec<usize>>>,
    pub(super) gub_enabled: bool,
    pub(super) amo_rows: Vec<crate::cardinality_branch::UnitAmoRow>,
    pub(super) amo_requested: bool,
    pub(super) amo_enabled: bool,
    pub(super) bottleneck_granularity: Option<BigRational>,
    pub(super) work_started: Instant,
}

#[derive(Clone, Copy)]
pub(super) enum MarketProfile {
    General,
    Split,
}

impl MarketProfile {
    pub(super) fn is_split(self) -> bool {
        matches!(self, Self::Split)
    }
}

struct SearchProfile {
    mode: SearchMode,
    market: MarketProfile,
    proof_first_workers: Option<NonZeroUsize>,
    child_order: ChildOrder,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SymmetryMode {
    Orbital,
    Rows,
    Off,
}

/// Terminal reason why root preparation could not produce a search frame.
pub(super) enum RootPreparationError {
    /// Exact propagation proved the caller model infeasible without an
    /// exportable certificate.
    Infeasible,
    /// Verified symmetry advice named a column absent from the tightened
    /// model, so the optional symmetry lane must fail closed.
    MissingSymmetryColumn,
}

impl RootPreparationError {
    /// Convert the bounded preparation failure into the solver's public
    /// terminal outcome at the orchestration boundary.
    pub(super) fn into_outcome(self) -> Outcome {
        match self {
            Self::Infeasible => Outcome::Infeasible {
                cert: None,
                tree_cert: None,
            },
            Self::MissingSymmetryColumn => Outcome::Unknown {
                reason: UnknownReason::SolverIncomplete {
                    detail: "verified symmetry referenced a missing model column".to_owned(),
                },
            },
        }
    }
}

impl SymmetryMode {
    fn current() -> Self {
        match crate::tune::count_opt(crate::tune::Knob::SymMode) {
            Some(1) => Self::Rows,
            Some(2) => Self::Off,
            _ => Self::Orbital,
        }
    }

    const fn label(self) -> &'static str {
        match self {
            Self::Orbital => "orbital",
            Self::Rows => "rows",
            Self::Off => "off",
        }
    }
}

/// Apply every root-only formulation transformation in its historical order.
///
/// `request.model` remains the caller/source frame. The returned `model` is the
/// cut frame consumed by the LP and tree; column identity is preserved between
/// those frames, while certificate authority remains with the caller frame.
pub(super) fn prepare_root_formulation(
    request: RootFormulationRequest<'_>,
) -> Result<RootFormulation, RootPreparationError> {
    let RootFormulationRequest {
        model,
        opts,
        mode,
        shared_binary_prefix,
        capture,
        attribution_started,
    } = request;
    let work_started = Instant::now();
    charge_cheap_presolve_decline(model, mode);
    let allocation_region = crate::attrib::AllocRegion::new(0);
    let tightened = presolve_model(model, opts, mode)?;
    let tightened = probe_root(tightened, opts, mode)?;
    let profile = search_profile(&tightened, mode, shared_binary_prefix);
    let SearchProfile {
        mode,
        market,
        proof_first_workers,
        child_order,
    } = profile;
    drop(allocation_region);

    let cuts_started = Instant::now();
    let symmetry_mode = SymmetryMode::current();
    let (tightened, mut symmetry, symmetry_pins) =
        prepare_symmetry(tightened, mode, symmetry_mode, capture);
    let structural =
        structural::prepare_structural_branching(model, mode, symmetry_mode, symmetry.as_ref());
    let (tightened, symmetry_rows_added) =
        apply_symmetry_rows(tightened, &mut symmetry, symmetry_mode, capture)?;
    // Inspect the clean, tightened formulation. Root cuts are valid for integer
    // points, but their auxiliary rows can hide the original VUB/lattice shape.
    let bottleneck_granularity = bottleneck_granularity(&tightened);
    trace_bottleneck_granularity(bottleneck_granularity.as_ref());
    let root_cut_policy =
        if mode.cheap || mode.projected || market.is_split() || proof_first_workers.is_some() {
            RootCutPolicy::Skip
        } else {
            RootCutPolicy::Separate
        };
    let model = apply_root_cuts(tightened, opts, mode, root_cut_policy);
    record_root_preparation(attribution_started, work_started, cuts_started, mode);

    Ok(RootFormulation {
        model,
        mode,
        market,
        proof_first_workers,
        child_order,
        symmetry,
        symmetry_pins,
        symmetry_rows_added,
        gub_supports: structural.gub_supports,
        gub_enabled: structural.gub_enabled,
        amo_rows: structural.amo_rows,
        amo_requested: structural.amo_requested,
        amo_enabled: structural.amo_enabled,
        bottleneck_granularity,
        work_started,
    })
}

fn charge_cheap_presolve_decline(model: &Model, mode: SearchMode) {
    if !mode.cheap {
        return;
    }
    let open_sides = (0..model.num_cols())
        .map(|column| {
            let (lower, upper) = model.col_bounds(Col(column as u32));
            u64::from(!lower.is_finite()) + u64::from(!upper.is_finite())
        })
        .sum();
    crate::sepstat::gate_charge(crate::sepstat::GATE_CHEAP_PRESOLVE, open_sides);
}

/// Apply only bounds implied by exact row propagation.
///
/// The deadline may weaken the tightening but cannot invalidate it. This pass
/// has no exportable propagation witness, so an infeasibility verdict carries
/// neither a root certificate nor a literal tree.
fn presolve_model(
    model: &Model,
    opts: &SolveOpts,
    mode: SearchMode,
) -> Result<Model, RootPreparationError> {
    if mode.cheap || crate::tune::caller_flag(crate::tune::Knob::NoPresolve) == Some(true) {
        return Ok(model.clone());
    }
    let presolve_deadline = opts.effective_deadline(Instant::now()).map(|deadline| {
        let now = Instant::now();
        let share = crate::tune::real(crate::tune::Knob::PresolveShare, PRESOLVE_SHARE);
        now + deadline.saturating_duration_since(now).mul_f64(share)
    });
    match crate::presolve::tighten_bounds(model, presolve_deadline) {
        crate::presolve::Presolved::Infeasible => Err(RootPreparationError::Infeasible),
        crate::presolve::Presolved::Tightened(tightened) => Ok(*tightened),
    }
}

/// Probe binary fixings through the same exact propagation used by presolve.
///
/// Forced bounds and clique rows therefore preserve every feasible integer
/// point. As with presolve, an infeasible propagation result has no exportable
/// certificate and is reported without inventing one.
fn probe_root(
    model: Model,
    opts: &SolveOpts,
    mode: SearchMode,
) -> Result<Model, RootPreparationError> {
    if !root_probe_wanted(&model, &mode) {
        return Ok(model);
    }
    let cfg = crate::probe::ProbeCfg {
        cap: crate::tune::count_opt(crate::tune::Knob::RootProbeCap).unwrap_or(ROOT_PROBE_CAP),
        clique_cap: crate::tune::count_opt(crate::tune::Knob::RootProbeCliqueCap).unwrap_or(0),
        use_lp_rank: crate::tune::caller_flag(crate::tune::Knob::RootProbeNoLpRank) != Some(true),
    };
    let deadline = opts.effective_deadline(Instant::now()).map(|deadline| {
        bounded_share_deadline(
            Instant::now(),
            deadline,
            crate::tune::real_opt(crate::tune::Knob::RootProbeShare),
            ROOT_PROBE_SHARE,
        )
    });
    match crate::probe::root_probe(&model, deadline, cfg) {
        crate::probe::RootProbe::Infeasible => Err(RootPreparationError::Infeasible),
        crate::probe::RootProbe::Probed {
            model,
            forced,
            cliques,
            probes,
        } => {
            if crate::debug_flags::milp_debug_flags().trace {
                eprintln!(
                    "--trace root probe: {probes} binaries probed, {forced} forced, {cliques} cliques"
                );
            }
            Ok(*model)
        }
    }
}

/// Allocate a fractional child budget without permitting an invalid internal
/// policy value to extend the governing deadline.
fn bounded_share_deadline(
    started: Instant,
    limit: Instant,
    configured: Option<f64>,
    fallback: f64,
) -> Instant {
    let share = configured
        .filter(|share| (0.0..=1.0).contains(share))
        .unwrap_or(fallback);
    started
        .checked_add(limit.saturating_duration_since(started).mul_f64(share))
        .unwrap_or(limit)
        .min(limit)
}

fn search_profile(model: &Model, mode: SearchMode, shared_binary_prefix: &[Col]) -> SearchProfile {
    let market_split = !mode.cheap && market_split_shape(model);
    let general_integer = !mode.cheap
        && crate::tune::caller_flag(crate::tune::Knob::NoGiDfs).map_or(true, |no| !no)
        && pure_general_integer_shape(model);
    let mode = SearchMode {
        dfs: mode.dfs || market_split || general_integer,
        ..mode
    };
    let proof_first_workers = if shared_binary_prefix.is_empty() {
        None
    } else {
        NonZeroUsize::new(mode.prefix_workers)
    };
    let child_order = child_order(general_integer, market_split);
    SearchProfile {
        mode,
        market: if market_split {
            MarketProfile::Split
        } else {
            MarketProfile::General
        },
        proof_first_workers,
        child_order,
    }
}

/// Detect symmetry after optional dominated-column pins.
///
/// A dual-dominated pin preserves feasibility and the optimum value, but it
/// removes literal assignments. Poison capture immediately so a later tree can
/// never claim caller-frame exhaustiveness from the reduced search.
fn prepare_symmetry(
    model: Model,
    mode: SearchMode,
    symmetry_mode: SymmetryMode,
    capture: &mut crate::tree_cert::TreeCapture,
) -> (Model, Option<crate::symmetry::Symmetry>, usize) {
    let enabled = mode.depth == 0
        && !mode.cheap
        && !mode.no_sym
        && symmetry_mode != SymmetryMode::Off
        && !crate::tune::on(crate::tune::Knob::NoSym);
    if !enabled {
        return (model, None, 0);
    }
    let mut model = model;
    let symmetry_pins = crate::symmetry::dual_pin_dominated(&mut model);
    if symmetry_pins > 0 {
        capture.poison();
        if crate::debug_flags::milp_debug_flags().trace {
            eprintln!("--trace symmetry: dual-pinned {symmetry_pins} dominated columns");
        }
    }
    let started = Instant::now();
    let symmetry = crate::symmetry::detect(&model);
    trace_symmetry_detection(symmetry.as_ref(), started.elapsed());
    (model, symmetry, symmetry_pins)
}

fn trace_symmetry_detection(symmetry: Option<&crate::symmetry::Symmetry>, elapsed: Duration) {
    if !crate::debug_flags::milp_debug_flags().trace {
        return;
    }
    match symmetry {
        Some(symmetry) => eprintln!(
            "--trace symmetry: {} verified generators (moved cols per gen: {:?}) in {:.3}s; orbitopes {:?} (k x m); stab_group={}",
            symmetry.gens.len(),
            symmetry
                .gens
                .iter()
                .take(8)
                .map(|generator| 2 * generator.pairs.len())
                .collect::<Vec<_>>(),
            elapsed.as_secs_f64(),
            symmetry
                .orbitopes
                .iter()
                .map(|orbitope| (orbitope.blocks.len(), orbitope.blocks.first().map_or(0, Vec::len)))
                .collect::<Vec<_>>(),
            symmetry.stab_group_size(),
        ),
        None => eprintln!(
            "--trace symmetry: none detected in {:.3}s",
            elapsed.as_secs_f64()
        ),
    }
}

#[derive(Clone, Copy)]
enum RootCutPolicy {
    Separate,
    Skip,
}

/// Add verified lex leaders to select one optimum-preserving representative.
///
/// These rows change literal-tree coverage, so capture is poisoned even though
/// they preserve an optimum. A stale symmetry column fails closed as Unknown.
fn apply_symmetry_rows(
    model: Model,
    symmetry: &mut Option<crate::symmetry::Symmetry>,
    mode: SymmetryMode,
    capture: &mut crate::tree_cert::TreeCapture,
) -> Result<(Model, bool), RootPreparationError> {
    if mode != SymmetryMode::Rows || symmetry.is_none() {
        return Ok((model, false));
    }
    let Some(value) = symmetry.take() else {
        return Ok((model, false));
    };
    let rows = value.breaking_rows();
    let mut model = model;
    for &(column, generator_column) in &rows {
        let Some(column) = model.col_at(column as usize) else {
            return Err(RootPreparationError::MissingSymmetryColumn);
        };
        let Some(generator_column) = model.col_at(generator_column as usize) else {
            return Err(RootPreparationError::MissingSymmetryColumn);
        };
        model.add_row(
            0.0,
            f64::INFINITY,
            &[(column, 1.0), (generator_column, -1.0)],
        );
    }
    if crate::debug_flags::milp_debug_flags().trace {
        eprintln!(
            "--trace symmetry: added {} lex-leader rows (rows mode)",
            rows.len()
        );
    }
    crate::local_census::add_usize(&SYM_ROWS_TOTAL, rows.len());
    capture.poison();
    Ok((model, true))
}

fn trace_bottleneck_granularity(granularity: Option<&BigRational>) {
    if granularity.is_some() && crate::debug_flags::milp_debug_flags().trace {
        eprintln!("--trace lattice-bottleneck objective granule = {granularity:?}");
    }
}

/// Add only cuts valid for every integer point of the tightened formulation.
///
/// Skipping separation changes relaxation strength, never the feasible integer
/// set or the authority of a later exact certificate.
fn apply_root_cuts(
    model: Model,
    opts: &SolveOpts,
    mode: SearchMode,
    policy: RootCutPolicy,
) -> Model {
    let allocation_region = crate::attrib::AllocRegion::new(1);
    let result = match policy {
        RootCutPolicy::Separate => add_root_cuts_rounds(model, opts, mode.cut_rounds),
        RootCutPolicy::Skip => model,
    };
    drop(allocation_region);
    result
}

fn record_root_preparation(
    attribution_started: Instant,
    work_started: Instant,
    cuts_started: Instant,
    mode: SearchMode,
) {
    if crate::debug_flags::milp_debug_flags().trace {
        eprintln!(
            "--trace presolve took {:.2}s; root cuts took {:.2}s",
            cuts_started.duration_since(work_started).as_secs_f64(),
            cuts_started.elapsed().as_secs_f64()
        );
    }
    if !crate::attrib::on() {
        return;
    }
    use std::sync::atomic::Ordering::Relaxed;
    let setup = attribution_started.elapsed().as_nanos() as u64;
    let root_cuts = cuts_started.elapsed().as_nanos() as u64;
    if mode.depth == 0 {
        crate::attrib::SETUP_NANOS_ROOT.fetch_add(setup, Relaxed);
        crate::attrib::ROOTCUT_NANOS_ROOT.fetch_add(root_cuts, Relaxed);
    } else {
        crate::attrib::SETUP_NANOS_SUB.fetch_add(setup, Relaxed);
        crate::attrib::ROOTCUT_NANOS_SUB.fetch_add(root_cuts, Relaxed);
    }
}
