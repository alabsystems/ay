// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded feasibility-pump restart schedule.

use super::*;

pub(super) struct PumpProgress {
    pub(super) seed: Option<Vec<BigRational>>,
    pub(super) seed_value: Option<BigRational>,
    pub(super) last_gain: Option<Instant>,
}

struct PumpState {
    progress: PumpProgress,
    stale_landings: usize,
    previous_attempt: Duration,
    expensive_failures: usize,
    failed_spend: Duration,
    stale_fractionality: usize,
    best_fractionality: f64,
}

enum AttemptResult {
    Landed(Vec<BigRational>),
    Continue,
    Stop,
}

enum AttemptSchedule {
    Run(Option<Instant>),
    Stop,
}

/// Final restart policy after the proof-first suite gate and explicit override.
#[derive(Debug, PartialEq, Eq)]
enum PumpRestartResolution {
    Fixed(usize),
    StructuralDefault,
}

#[derive(Clone, Copy)]
struct PumpWorkEnvelope {
    root_lp_iterations: u64,
    iteration_budget: Option<u64>,
    work_start: u64,
}

impl PumpWorkEnvelope {
    fn spent(self) -> u64 {
        crate::simplex::stats::solve_work() - self.work_start
    }
}

pub(super) fn run(
    context: &RootHeuristicContext<'_>,
    budget: RootHeuristicBudget,
    root_lp_iterations: u64,
) -> PumpProgress {
    let restarts = restart_count(context);
    let work = PumpWorkEnvelope {
        root_lp_iterations,
        iteration_budget: pump_iter_cap(root_lp_iterations),
        work_start: crate::simplex::stats::solve_work(),
    };
    let mut state = PumpState {
        progress: PumpProgress {
            seed: None,
            seed_value: None,
            last_gain: None,
        },
        stale_landings: 0,
        previous_attempt: Duration::ZERO,
        expensive_failures: 0,
        failed_spend: Duration::ZERO,
        stale_fractionality: 0,
        best_fractionality: f64::INFINITY,
    };
    for attempt in 0..restarts {
        if should_stop(context, budget, &state, work, attempt) {
            break;
        }
        let deadline = match attempt_deadline(budget, &state) {
            AttemptSchedule::Run(deadline) => deadline,
            AttemptSchedule::Stop => break,
        };
        match run_attempt(context, &mut state, attempt, deadline) {
            AttemptResult::Landed(point) => admit_landing(context, &mut state, point, attempt),
            AttemptResult::Continue => {}
            AttemptResult::Stop => break,
        }
    }
    state.progress
}

fn restart_count(context: &RootHeuristicContext<'_>) -> usize {
    match resolve_restart_count(
        context.suite,
        crate::tune::count_opt(crate::tune::Knob::PumpRestarts),
    ) {
        PumpRestartResolution::Fixed(restarts) => return restarts,
        PumpRestartResolution::StructuralDefault => {}
    }
    if in_rens() {
        return 0;
    }
    if context.policy.execution.is_cheap() {
        return 4;
    }
    let wide_tall_partition = context.frame.model.num_cols() >= 10 * context.frame.model.num_rows()
        && context.frame.model.num_rows() >= 200
        && set_partition_incidence(context.frame.model).is_some_and(|shape| shape.sp_rows >= 200);
    if wide_tall_partition {
        0
    } else {
        PUMP_RESTARTS
    }
}

fn resolve_restart_count(
    suite: RootSuiteDisposition,
    requested: Option<usize>,
) -> PumpRestartResolution {
    match (suite, requested) {
        (RootSuiteDisposition::Skip, _) => PumpRestartResolution::Fixed(0),
        (RootSuiteDisposition::Run, Some(restarts)) => PumpRestartResolution::Fixed(restarts),
        (RootSuiteDisposition::Run, None) => PumpRestartResolution::StructuralDefault,
    }
}

fn should_stop(
    context: &RootHeuristicContext<'_>,
    budget: RootHeuristicBudget,
    state: &PumpState,
    work: PumpWorkEnvelope,
    attempt: usize,
) -> bool {
    let stalled = state
        .progress
        .last_gain
        .is_some_and(|gain| gain.elapsed() >= budget.stall);
    let barren = state.progress.last_gain.is_none()
        && state.progress.seed_value.is_none()
        && state.failed_spend.as_secs_f64() >= PUMP_BARREN_MULT * HEUR_STALL_SECS;
    let fractionality_stuck =
        state.progress.seed_value.is_none() && state.stale_fractionality >= PUMP_FRAC_STALE;
    let out_of_work = work.iteration_budget.is_some_and(|cap| work.spent() >= cap);
    if out_of_work && context.policy.trace.enabled() {
        eprintln!(
            "--trace   pump work cap: {} iters spent >= {} ({:.1}x root LP {}) at attempt {attempt}",
            work.spent(),
            work.iteration_budget.unwrap_or(0),
            work.iteration_budget.unwrap_or(0) as f64 / work.root_lp_iterations.max(1) as f64,
            work.root_lp_iterations,
        );
    }
    budget.pump_expired(PumpLandingState::from_last_gain(state.progress.last_gain))
        || state.stale_landings >= 3
        || stalled
        || barren
        || fractionality_stuck
        || out_of_work
}

fn attempt_deadline(budget: RootHeuristicBudget, state: &PumpState) -> AttemptSchedule {
    if let Some(gain) = state.progress.last_gain {
        if state.previous_attempt > (gain + budget.stall).saturating_duration_since(Instant::now())
        {
            return AttemptSchedule::Stop;
        }
        return AttemptSchedule::Run(Some(
            budget
                .pump_after_landing
                .map_or(gain + budget.stall, |limit| limit.min(gain + budget.stall)),
        ));
    }
    AttemptSchedule::Run(budget.pump_before_landing)
}

fn run_attempt(
    context: &RootHeuristicContext<'_>,
    state: &mut PumpState,
    attempt: usize,
    deadline: Option<Instant>,
) -> AttemptResult {
    let started = Instant::now();
    let mut fractionality = f64::INFINITY;
    let landed = feasibility_pump(
        context.frame.model,
        context.frame.lp,
        context.frame.integer_columns,
        attempt,
        deadline,
        &mut fractionality,
    )
    .and_then(|point| {
        improve(
            context.frame.model,
            context.frame.integer_columns,
            &point,
            deadline,
        )
    });
    state.previous_attempt = started.elapsed();
    update_fractionality(state, fractionality);
    let Some(point) = landed else {
        return failed_attempt(context, state, attempt);
    };
    state.expensive_failures = 0;
    AttemptResult::Landed(point)
}

fn update_fractionality(state: &mut PumpState, fractionality: f64) {
    if fractionality.is_finite()
        && fractionality < state.best_fractionality - state.best_fractionality.abs() * 0.01 - 1e-9
    {
        state.best_fractionality = fractionality;
        state.stale_fractionality = 0;
    } else {
        state.best_fractionality = state.best_fractionality.min(fractionality);
        state.stale_fractionality += 1;
    }
}

fn failed_attempt(
    context: &RootHeuristicContext<'_>,
    state: &mut PumpState,
    attempt: usize,
) -> AttemptResult {
    state.failed_spend += state.previous_attempt;
    if context.policy.trace.enabled() {
        eprintln!(
            "--trace   pump attempt {attempt}: FAILED (at {:.2}s)",
            context.phase_started.elapsed().as_secs_f64()
        );
    }
    if state.previous_attempt.as_secs_f64() < 4.0 * HEUR_STALL_SECS {
        state.expensive_failures = 0;
        return AttemptResult::Continue;
    }
    state.expensive_failures += 1;
    if state.expensive_failures >= 2
        || state.previous_attempt.as_secs_f64() >= 20.0 * HEUR_STALL_SECS
    {
        AttemptResult::Stop
    } else {
        AttemptResult::Continue
    }
}

fn admit_landing(
    context: &RootHeuristicContext<'_>,
    state: &mut PumpState,
    point: Vec<BigRational>,
    attempt: usize,
) {
    let value = minimize_value(context.frame.lp, &point);
    if context.policy.trace.enabled() {
        eprintln!(
            "--trace   pump attempt {attempt}: landed {value} (at {:.2}s)",
            context.phase_started.elapsed().as_secs_f64()
        );
    }
    if state
        .progress
        .seed_value
        .as_ref()
        .is_none_or(|best| value < *best)
    {
        state.progress.seed_value = Some(value);
        state.progress.seed = Some(point);
        state.stale_landings = 0;
        state.progress.last_gain = Some(Instant::now());
    } else {
        state.stale_landings += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn root_heuristic_child_deadlines_never_extend_the_outer_limit() {
        let limit = Instant::now() + Duration::from_secs(20);
        let _active = crate::tune::activate_caller(crate::tune::Profile::EMPTY.with(
            crate::tune::Knob::HeurShare,
            crate::tune::Setting::Real(2.0),
        ));
        let budget = RootHeuristicBudget::new(
            Some(limit),
            RootMarketPolicy::General,
            Duration::from_secs(1),
        );
        for deadline in [
            budget.phase,
            budget.pump_after_landing,
            budget.pump_before_landing,
        ] {
            assert!(deadline.is_some_and(|deadline| deadline <= limit));
        }
        assert!(budget.phase.is_some_and(|deadline| deadline < limit));
    }

    #[test]
    fn skipped_suite_vetoes_an_explicit_pump_override() {
        assert_eq!(
            resolve_restart_count(RootSuiteDisposition::Skip, Some(7)),
            PumpRestartResolution::Fixed(0)
        );
        assert_eq!(
            resolve_restart_count(RootSuiteDisposition::Run, Some(7)),
            PumpRestartResolution::Fixed(7)
        );
        assert_eq!(
            resolve_restart_count(RootSuiteDisposition::Run, None),
            PumpRestartResolution::StructuralDefault
        );
    }
}
