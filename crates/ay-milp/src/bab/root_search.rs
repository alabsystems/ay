// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Root relaxation, primal seeding, and root-box tightening.
//!
//! This phase runs before any frontier node exists. Float solutions are advice:
//! a heuristic seed enters the incumbent only after `Model::check_point`, and a
//! reduced-cost fixing is accepted only through the exact safe-bound machinery.
//!
//! Phase order is stable: solve the root LP, run the bounded pump and structural
//! seed fallbacks, apply structure-specific neighbourhood improvement, polish
//! once, arm the early-RINS cadence from the rigorous gap, then tighten the root
//! box. Reduced-cost pins are transferred through symmetry before row closure;
//! neither step may observe a partially updated box.

mod lns;
mod polish;
mod pump;
mod seeds;

use super::*;
use crate::simplex::Candidate;

/// Immutable formulation and objective frame observed by all root phases.
pub(super) struct RootSolveFrame<'a> {
    pub(super) caller_model: &'a Model,
    pub(super) model: &'a Model,
    pub(super) lp: &'a FloatLp,
    pub(super) integer_columns: &'a [usize],
    pub(super) minimize_objective: &'a [(u32, Rational)],
    pub(super) sense: Sense,
    pub(super) deadline: Option<Instant>,
    pub(super) work_started: Instant,
}

/// Mutable primal/search state committed by the root phase.
pub(super) struct RootPrimalState<'a> {
    pub(super) root_lower: &'a mut Vec<f64>,
    pub(super) root_upper: &'a mut Vec<f64>,
    pub(super) open_continuous: &'a [usize],
    pub(super) open_continuous_sides: &'a mut usize,
    pub(super) symmetry: &'a mut Option<crate::symmetry::Symmetry>,
    pub(super) incumbent: &'a mut Option<(Vec<BigRational>, BigRational)>,
    pub(super) next_rins: &'a mut usize,
}

pub(super) struct RootSearchRequest<'a> {
    pub(super) frame: RootSolveFrame<'a>,
    pub(super) state: RootPrimalState<'a>,
    pub(super) policy: RootSearchPolicy,
}

#[derive(Clone, Copy)]
pub(super) struct RootSearchPolicy {
    pub(super) execution: RootExecutionPolicy,
    pub(super) primal: RootPrimalPolicy,
    pub(super) trace: RootTrace,
}

#[derive(Clone, Copy)]
pub(super) struct RootExecutionPolicy {
    pub(super) scope: RootScope,
    pub(super) cost: RootCostProfile,
    pub(super) projection: RootProjection,
}

#[derive(Clone, Copy)]
pub(super) enum RootScope {
    TopLevel,
    Nested,
}

#[derive(Clone, Copy)]
pub(super) enum RootCostProfile {
    Full,
    Cheap,
}

#[derive(Clone, Copy)]
pub(super) enum RootProjection {
    Original,
    Projected,
}

impl RootExecutionPolicy {
    fn is_top_level(self) -> bool {
        matches!(self.scope, RootScope::TopLevel)
    }

    fn is_cheap(self) -> bool {
        matches!(self.cost, RootCostProfile::Cheap)
    }

    fn is_projected(self) -> bool {
        matches!(self.projection, RootProjection::Projected)
    }
}

#[derive(Clone, Copy)]
pub(super) struct RootPrimalPolicy {
    pub(super) market: RootMarketPolicy,
    pub(super) suite: RootSuitePolicy,
}

#[derive(Clone, Copy)]
pub(super) enum RootMarketPolicy {
    General,
    Split,
}

#[derive(Clone, Copy)]
pub(super) enum RootSuitePolicy {
    Enabled,
    ProofFirstPrefix,
}

#[derive(Clone, Copy)]
enum RootSuiteDisposition {
    Run,
    Skip,
}

impl RootSuiteDisposition {
    fn runs(self) -> bool {
        matches!(self, Self::Run)
    }
}

#[derive(Clone, Copy)]
enum PumpLandingState {
    Virgin,
    Landed,
}

impl PumpLandingState {
    fn from_last_gain(last_gain: Option<Instant>) -> Self {
        if last_gain.is_some() {
            Self::Landed
        } else {
            Self::Virgin
        }
    }
}

#[derive(Clone, Copy)]
pub(super) enum RootTrace {
    Disabled,
    Enabled,
}

impl RootTrace {
    pub(super) fn enabled(self) -> bool {
        matches!(self, Self::Enabled)
    }
}

struct RootLpMeasurement {
    candidate: Candidate,
    iterations: u64,
    root_work: Duration,
    solve_time: Duration,
}

struct RootHeuristicFrame<'a> {
    caller_model: &'a Model,
    model: &'a Model,
    lp: &'a FloatLp,
    integer_columns: &'a [usize],
    minimize_objective: &'a [(u32, Rational)],
    sense: Sense,
    deadline: Option<Instant>,
    root: &'a Candidate,
}

struct RootHeuristicState<'a> {
    root_lower: &'a mut Vec<f64>,
    root_upper: &'a mut Vec<f64>,
    open_continuous: &'a [usize],
    open_continuous_sides: &'a mut usize,
    symmetry: &'a mut Option<crate::symmetry::Symmetry>,
    incumbent: &'a mut Option<(Vec<BigRational>, BigRational)>,
    next_rins: &'a mut usize,
}

struct RootHeuristicContext<'a> {
    frame: RootHeuristicFrame<'a>,
    state: RootHeuristicState<'a>,
    policy: RootSearchPolicy,
    phase_started: Instant,
    suite: RootSuiteDisposition,
}

#[derive(Clone, Copy)]
struct RootHeuristicBudget {
    phase: Option<Instant>,
    pump_after_landing: Option<Instant>,
    pump_before_landing: Option<Instant>,
    stall: Duration,
}

impl RootHeuristicBudget {
    fn new(deadline: Option<Instant>, market: RootMarketPolicy, root_lp_time: Duration) -> Self {
        let default_share = if matches!(market, RootMarketPolicy::Split) {
            0.0
        } else {
            ROOT_HEURISTIC_SHARE
        };
        let share = crate::tune::real_opt(crate::tune::Knob::HeurShare)
            .filter(|share| (0.0..=1.0).contains(share))
            .unwrap_or(default_share);
        let phase = deadline.map(|limit| {
            let now = Instant::now();
            now.checked_add(limit.saturating_duration_since(now).mul_f64(share))
                .unwrap_or(limit)
                .min(limit)
        });
        let anchor = Instant::now();
        let pump_deadline = |floor_seconds: f64| {
            phase.map(|limit| {
                anchor
                    .checked_add(pump_window(
                        root_lp_time,
                        limit.saturating_duration_since(anchor),
                        floor_seconds,
                    ))
                    .unwrap_or(limit)
                    .min(limit)
            })
        };
        Self {
            phase,
            pump_after_landing: pump_deadline(PUMP_FLOOR_SECS),
            pump_before_landing: pump_deadline(PUMP_BARREN_MULT * HEUR_STALL_SECS),
            stall: Duration::from_secs_f64(HEUR_STALL_SECS),
        }
    }

    fn pump_expired(self, landing: PumpLandingState) -> bool {
        let deadline = match landing {
            PumpLandingState::Landed => self.pump_after_landing,
            PumpLandingState::Virgin => self.pump_before_landing,
        };
        deadline.is_some_and(|limit| Instant::now() >= limit)
    }
}

/// The only terminal root-LP route: out-of-memory maps to the public outcome
/// at the orchestration boundary without making `Outcome` a large `Err` arm.
pub(super) struct RootSearchMemoryLimit;

impl RootSearchMemoryLimit {
    pub(super) fn into_outcome(self) -> Outcome {
        Outcome::Unknown {
            reason: UnknownReason::MemoryLimit,
        }
    }
}

pub(super) fn prepare_root_search(
    request: RootSearchRequest<'_>,
) -> Result<Candidate, RootSearchMemoryLimit> {
    let measured = solve_root_lp(&request);
    if measured.candidate.status == SimplexStatus::OutOfMemory {
        return Err(RootSearchMemoryLimit);
    }
    if measured.candidate.status != SimplexStatus::Optimal {
        return Ok(measured.candidate);
    }

    let budget = RootHeuristicBudget::new(
        request.frame.deadline,
        request.policy.primal.market,
        measured.solve_time,
    );
    let phase_started = Instant::now();
    let suite = if matches!(
        request.policy.primal.suite,
        RootSuitePolicy::ProofFirstPrefix
    ) || (request.policy.execution.is_projected()
        && request.state.incumbent.is_some())
    {
        RootSuiteDisposition::Skip
    } else {
        RootSuiteDisposition::Run
    };
    let mut context = RootHeuristicContext {
        frame: RootHeuristicFrame {
            caller_model: request.frame.caller_model,
            model: request.frame.model,
            lp: request.frame.lp,
            integer_columns: request.frame.integer_columns,
            minimize_objective: request.frame.minimize_objective,
            sense: request.frame.sense,
            deadline: request.frame.deadline,
            root: &measured.candidate,
        },
        state: RootHeuristicState {
            root_lower: request.state.root_lower,
            root_upper: request.state.root_upper,
            open_continuous: request.state.open_continuous,
            open_continuous_sides: request.state.open_continuous_sides,
            symmetry: request.state.symmetry,
            incumbent: request.state.incumbent,
            next_rins: request.state.next_rins,
        },
        policy: request.policy,
        phase_started,
        suite,
    };
    let pump = pump::run(&context, budget, measured.iterations);
    let progress = seeds::run(&mut context, budget, measured.root_work, pump);
    polish::run(&mut context, budget, &progress);
    arm_early_rins(&mut context);
    tighten_root_box(&mut context);
    Ok(measured.candidate)
}

fn solve_root_lp(request: &RootSearchRequest<'_>) -> RootLpMeasurement {
    let started = Instant::now();
    let work_before = crate::simplex::stats::solve_work();
    let candidate = {
        let _ledger = crate::simplex::PhaseScope::new(crate::simplex::PH_ROOT_LP);
        request.frame.lp.solve_bounded(
            &request.frame.lp.lower.clone(),
            &request.frame.lp.upper.clone(),
            None,
            request.frame.deadline,
        )
    };
    let iterations = crate::simplex::stats::solve_work().saturating_sub(work_before);
    let root_work = request.frame.work_started.elapsed();
    let solve_time = started.elapsed();
    if request.policy.trace.enabled() {
        let bound = (0..request.frame.lp.n)
            .map(|column| request.frame.lp.cost[column] * candidate.values[column])
            .sum::<f64>();
        eprintln!(
            "--trace root LP: {:?} in {:.2}s bound={bound:.6} (mat/rhs/cost scale = {:?})",
            candidate.status,
            started.elapsed().as_secs_f64(),
            request.frame.lp.scale_for_trace()
        );
        eprintln!(
            "--trace root work (presolve+cuts+root LP) = {:.2}s",
            root_work.as_secs_f64()
        );
    }
    RootLpMeasurement {
        candidate,
        iterations,
        root_work,
        solve_time,
    }
}

fn arm_early_rins(context: &mut RootHeuristicContext<'_>) {
    let gap_is_wide = context
        .state
        .incumbent
        .as_ref()
        .is_none_or(|(_, incumbent)| {
            let mut scratch = vec![(0.0, 0.0); context.frame.lp.n];
            safe_bound(
                context.frame.lp,
                &context.frame.root.duals,
                context.state.root_lower,
                context.state.root_upper,
                &mut scratch,
            )
            .is_none_or(|bound| {
                let incumbent = to_f64(incumbent);
                incumbent - bound > 0.05 * (1.0 + incumbent.abs())
            })
        });
    trace_root_gap(context);
    if gap_is_wide && !crate::cuts::is_bigm_indicator(context.frame.caller_model) {
        *context.state.next_rins = 1;
    }
}

fn trace_root_gap(context: &RootHeuristicContext<'_>) {
    if !context.policy.trace.enabled() {
        return;
    }
    let Some((_, incumbent)) = context.state.incumbent.as_ref() else {
        return;
    };
    let mut scratch = vec![(0.0, 0.0); context.frame.lp.n];
    let Some(bound) = safe_bound(
        context.frame.lp,
        &context.frame.root.duals,
        context.state.root_lower,
        context.state.root_upper,
        &mut scratch,
    ) else {
        return;
    };
    let incumbent = to_f64(incumbent);
    eprintln!(
        "--trace root gap = {:.1}% (inc {incumbent}, bound {bound:.1})",
        100.0 * (incumbent - bound) / (1.0 + incumbent.abs())
    );
}

fn tighten_root_box(context: &mut RootHeuristicContext<'_>) {
    let symmetry_snapshot = context.state.symmetry.as_ref().map(|_| {
        (
            context.state.root_lower.clone(),
            context.state.root_upper.clone(),
        )
    });
    let fixed = reduced_cost_fix(
        context.frame.lp,
        context.frame.root,
        context.state.root_lower,
        context.state.root_upper,
        context.frame.integer_columns,
        context.state.open_continuous,
        context.state.incumbent.as_ref().map(|(_, value)| value),
    );
    if context.policy.trace.enabled() && fixed > 0 {
        eprintln!("--trace reduced-cost fixing pinned {fixed} columns");
    }
    if fixed > 0 {
        if let (Some(symmetry), Some((lower, upper))) =
            (context.state.symmetry.as_ref(), &symmetry_snapshot)
        {
            let moved = symmetry.propagate_pins(
                lower,
                upper,
                context.state.root_lower,
                context.state.root_upper,
            );
            if context.policy.trace.enabled() && moved > 0 {
                eprintln!("--trace orbital pin propagation moved {moved} root bounds");
            }
        }
    }
    trace_forgone_closure(context, fixed);
    if fixed == 0 || context.state.open_continuous.is_empty() {
        return;
    }
    let now_open = search_bootstrap::open_sides(
        context.state.open_continuous,
        context.state.root_lower,
        context.state.root_upper,
    );
    if now_open >= *context.state.open_continuous_sides {
        return;
    }
    let closed = close_bounds_via_rows(
        context.frame.model,
        context.state.root_lower,
        context.state.root_upper,
        context.frame.deadline,
    );
    *context.state.open_continuous_sides = search_bootstrap::open_sides(
        context.state.open_continuous,
        context.state.root_lower,
        context.state.root_upper,
    );
    if context.policy.trace.enabled() {
        eprintln!(
            "--trace cutoff closure: {closed} more bound sides closed ({} still open)",
            context.state.open_continuous_sides
        );
    }
}

fn trace_forgone_closure(context: &RootHeuristicContext<'_>, fixed: usize) {
    if fixed > 0
        && (context.state.open_continuous.is_empty()
            || search_bootstrap::open_sides(
                context.state.open_continuous,
                context.state.root_lower,
                context.state.root_upper,
            ) >= *context.state.open_continuous_sides)
    {
        crate::sepstat::gate_charge(crate::sepstat::GATE_CUTOFF_CLOSURE, fixed as u64);
    }
}

fn minimize_value(lp: &FloatLp, point: &[BigRational]) -> BigRational {
    let mut value = BigRational::zero();
    for column in 0..lp.n {
        if lp.cost[column] != 0.0 {
            if let Some(cost) = exact(lp.cost[column]) {
                value += cost * &point[column];
            }
        }
    }
    value
}
