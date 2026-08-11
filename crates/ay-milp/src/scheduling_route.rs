// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact bounded route for disjunctive single-machine scheduling models.
//!
//! The recognized formulation has one integer start and one nonnegative
//! tardiness variable per job, paired binary order variables for every job
//! pair, and the usual big-M disjunctions.  Recognition is deliberately
//! structural: names, row order, column order, and the number of jobs are not
//! part of the contract.  Every row and column must belong to the formulation,
//! so a near miss declines to the ordinary MILP engine.
//!
//! Once recognized, a subset/Pareto dynamic program enumerates schedules in
//! exact integer arithmetic.  A returned point is reconstructed in the source
//! column frame and checked by [`Model::check_point`].  This final check is
//! load-bearing: the DP intentionally ignores the inactive side of each big-M
//! pair while deriving a lower bound, so an undersized M can only make the
//! route decline; it can never produce a wrong optimum.

use std::cmp::max;
use std::time::{Duration, Instant};

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive, Zero};

use crate::{Col, ColKind, Model, Row, Sense};

/// The exact DP is intentionally a bounded specialist.  Twenty jobs already
/// means 1,048,576 subset buckets and is ample for the production family this
/// route owns; larger models fall through without allocating the table.
const MAX_JOBS: usize = 20;
const MAX_DP_TRIAL: Duration = Duration::from_secs(2);
const MAX_CERT_REPLAY: Duration = Duration::from_secs(5);
const MAX_ACCEPTED_STATES: u64 = 8_000_000;
const MAX_TRANSITIONS: u64 = 100_000_000;
/// Counts both the cheap incidence pass and the exact structural pass. A
/// matching model visits each nonzero twice; an enormous near miss declines
/// before exact-rational allocation can consume the fallback budget.
const MAX_RECOGNITION_TERM_VISITS: u64 = 1_000_000;
const MAX_RECOGNITION_ROWS: usize = 100_000;
const MAX_RECOGNITION_COLS: usize = 2 + 2 * MAX_JOBS + MAX_JOBS * (MAX_JOBS - 1);
const DEADLINE_POLL_MASK: u64 = (1 << 12) - 1;

/// Model-bound optimality artifact for the scheduling route.
///
/// The job sequence uses source-model column indices, not recognizer-local job
/// numbers.  Verification re-recognizes the source formulation, reconstructs
/// and exactly checks the source witness, and independently replays the
/// bounded subset/Pareto DP.  A certificate copied to a different model, or a
/// sequence/value edited in transit, therefore fails closed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SingleMachineSchedulingOptimalityCertificate {
    value: BigRational,
    sequence: Vec<u32>,
}

pub(crate) enum SingleMachineSchedulingDecision {
    Optimal {
        value: BigRational,
        model_values: Vec<BigRational>,
        certificate: SingleMachineSchedulingOptimalityCertificate,
    },
}

#[derive(Debug, Clone)]
struct Job {
    start_col: usize,
    slack_col: usize,
    release: i64,
    due: i64,
    duration: i64,
    start_upper: Option<i64>,
}

#[derive(Debug, Clone, Copy)]
struct BinaryRelation {
    col: usize,
    /// Setting this binary to zero activates `before -> after`.
    before: usize,
    after: usize,
}

#[derive(Debug)]
struct RecognizedScheduling {
    jobs: Vec<Job>,
    binaries: Vec<BinaryRelation>,
    tardiness_aggregate_col: usize,
    start_aggregate_col: usize,
    tardiness_aggregate_rhs: i64,
    start_aggregate_rhs: i64,
    objective_scale: BigRational,
    objective_constant: BigRational,
}

#[derive(Debug, Clone, Copy)]
struct FrontierEntry {
    finish: i64,
    cost: i128,
    /// Five bits per scheduled job; job zero is stored in the low bits.
    order: u128,
}

#[derive(Debug)]
struct DpOptimum {
    cost: i128,
    candidate_orders: Vec<u128>,
}

#[derive(Debug)]
struct ExactRow {
    terms: Vec<(usize, BigRational)>,
    lower: Option<BigRational>,
    upper: Option<BigRational>,
}

#[derive(Debug)]
struct RecognitionBudget {
    deadline: Option<Instant>,
    term_visits: u64,
}

impl RecognitionBudget {
    fn new(deadline: Option<Instant>) -> Self {
        Self {
            deadline,
            term_visits: 0,
        }
    }

    fn poll_row(&self, row: usize) -> Result<(), String> {
        if row & 255 == 0 {
            check_deadline(self.deadline)?;
        }
        Ok(())
    }

    fn visit_term(&mut self) -> Result<(), String> {
        self.term_visits = self
            .term_visits
            .checked_add(1)
            .ok_or_else(|| "scheduling recognition term count overflow".to_owned())?;
        if self.term_visits > MAX_RECOGNITION_TERM_VISITS {
            return Err("scheduling recognition term cap reached".into());
        }
        if self.term_visits & DEADLINE_POLL_MASK == 0 {
            check_deadline(self.deadline)?;
        }
        Ok(())
    }
}

/// Try the bounded scheduling route. A miss is not an error: it leaves the
/// native MILP path authoritative.
pub(crate) fn try_solve(
    model: &Model,
    outer_deadline: Option<Instant>,
) -> Option<SingleMachineSchedulingDecision> {
    let deadline = trial_deadline(outer_deadline, Instant::now())?;
    solve_once(model, deadline)
}

/// Certificate posture: solve once, then independently replay the typed
/// artifact before allowing it to satisfy `require_certificates`.
pub(crate) fn try_solve_certified(
    model: &Model,
    outer_deadline: Option<Instant>,
) -> Option<SingleMachineSchedulingDecision> {
    let deadline = trial_deadline(outer_deadline, Instant::now())?;
    let decision = solve_once(model, deadline)?;
    let SingleMachineSchedulingDecision::Optimal {
        value,
        model_values,
        certificate,
    } = decision;
    let replay_deadline = certificate_deadline(outer_deadline, Instant::now())?;
    verify_optimality_certificate_with_deadline(model, &value, &certificate, Some(replay_deadline))
        .ok()?;
    Some(SingleMachineSchedulingDecision::Optimal {
        value,
        model_values,
        certificate,
    })
}

/// Independently verify a scheduling optimality artifact against `model`.
pub fn verify_optimality_certificate(
    model: &Model,
    claimed_value: &BigRational,
    certificate: &SingleMachineSchedulingOptimalityCertificate,
) -> Result<(), String> {
    let deadline = Instant::now()
        .checked_add(MAX_CERT_REPLAY)
        .ok_or_else(|| "scheduling certificate deadline overflow".to_owned())?;
    verify_optimality_certificate_with_deadline(model, claimed_value, certificate, Some(deadline))
}

fn solve_once(model: &Model, deadline: Instant) -> Option<SingleMachineSchedulingDecision> {
    let scheduling = recognize(model, Some(deadline)).ok()?;
    let optimum = solve_dp(&scheduling, Some(deadline)).ok()?;
    for encoded in optimum.candidate_orders {
        let Ok(sequence) = decode_order(encoded, scheduling.jobs.len()) else {
            continue;
        };
        let Ok((model_values, value, cost)) = reconstruct(model, &scheduling, &sequence) else {
            continue;
        };
        if cost != optimum.cost {
            continue;
        }
        let certificate = SingleMachineSchedulingOptimalityCertificate {
            value: value.clone(),
            sequence: sequence
                .iter()
                .map(|&job| scheduling.jobs[job].start_col as u32)
                .collect(),
        };
        return Some(SingleMachineSchedulingDecision::Optimal {
            value,
            model_values,
            certificate,
        });
    }
    None
}

fn verify_optimality_certificate_with_deadline(
    model: &Model,
    claimed_value: &BigRational,
    certificate: &SingleMachineSchedulingOptimalityCertificate,
    deadline: Option<Instant>,
) -> Result<(), String> {
    if certificate.value != *claimed_value {
        return Err(format!(
            "scheduling artifact value {} does not match claimed optimum {claimed_value}",
            certificate.value
        ));
    }
    check_deadline(deadline)?;
    let scheduling = recognize(model, deadline)?;
    if certificate.sequence.len() != scheduling.jobs.len() {
        return Err(format!(
            "scheduling artifact contains {} jobs, recognized model contains {}",
            certificate.sequence.len(),
            scheduling.jobs.len()
        ));
    }
    let mut job_at_col = vec![None; model.num_cols()];
    for (job, spec) in scheduling.jobs.iter().enumerate() {
        job_at_col[spec.start_col] = Some(job);
    }
    let mut seen = vec![false; scheduling.jobs.len()];
    let mut sequence = Vec::with_capacity(scheduling.jobs.len());
    for &column in &certificate.sequence {
        let Some(job) = job_at_col.get(column as usize).and_then(|entry| *entry) else {
            return Err(format!(
                "scheduling artifact column {column} is not a recognized start variable"
            ));
        };
        if std::mem::replace(&mut seen[job], true) {
            return Err(format!("scheduling artifact repeats start column {column}"));
        }
        sequence.push(job);
    }
    if seen.iter().any(|present| !present) {
        return Err("scheduling artifact omits a recognized job".into());
    }
    let (_model_values, attained, sequence_cost) = reconstruct(model, &scheduling, &sequence)?;
    if attained != *claimed_value {
        return Err(format!(
            "scheduling artifact sequence attains {attained}, claimed optimum is {claimed_value}"
        ));
    }
    check_deadline(deadline)?;
    let optimum = solve_dp(&scheduling, deadline)?;
    if sequence_cost != optimum.cost {
        return Err(format!(
            "scheduling artifact sequence cost {sequence_cost}, independently replayed optimum is {}",
            optimum.cost
        ));
    }
    Ok(())
}

/// Recognize the complete source formulation. Every row and column is
/// accounted for; any extra side constraint changes the optimization problem
/// and therefore makes this specialist decline.
fn recognize(model: &Model, deadline: Option<Instant>) -> Result<RecognizedScheduling, String> {
    check_deadline(deadline)?;
    if model.num_rows() > MAX_RECOGNITION_ROWS {
        return Err("scheduling recognition row cap reached".into());
    }
    if model.num_cols() > MAX_RECOGNITION_COLS {
        return Err("scheduling recognition column cap reached".into());
    }
    let mut budget = RecognitionBudget::new(deadline);
    if !model.has_objective() || model.sense() != Sense::Minimize {
        return Err("model is not a minimization problem".into());
    }

    let mut objective_cols = Vec::new();
    let mut objective_scale = None;
    let mut slack_cols = Vec::new();
    let mut start_cols = Vec::new();
    let mut binary_cols = Vec::new();
    for index in 0..model.num_cols() {
        let col = Col(index as u32);
        let coefficient = model.obj_coeff_exact_at(index as u32, model.obj_coeff(col));
        let (lower, upper) = model.col_bounds(col);
        match model.col_kind(col) {
            ColKind::Continuous if !coefficient.is_zero() => {
                if coefficient <= BigRational::zero() || !is_free(lower, upper) {
                    return Err(
                        "objective aggregate is not a free continuous column with a positive coefficient"
                            .into(),
                    );
                }
                if let Some(scale) = &objective_scale {
                    if scale != &coefficient {
                        return Err("objective aggregates have different coefficients".into());
                    }
                } else {
                    objective_scale = Some(coefficient.clone());
                }
                objective_cols.push(index);
            }
            ColKind::Continuous => {
                if lower != 0.0 || !is_pos_inf(upper) {
                    return Err(
                        "non-objective continuous column is not a nonnegative tardiness variable"
                            .into(),
                    );
                }
                slack_cols.push(index);
            }
            ColKind::Integer => {
                if !coefficient.is_zero() {
                    return Err("integer start column has a direct objective coefficient".into());
                }
                finite_integer(lower).ok_or_else(|| {
                    "integer start column does not have an integral finite release bound".to_owned()
                })?;
                if upper.is_finite() {
                    finite_integer(upper).ok_or_else(|| {
                        "integer start column has a non-integral upper bound".to_owned()
                    })?;
                } else if !is_pos_inf(upper) {
                    return Err("integer start column has an invalid upper bound".into());
                }
                start_cols.push(index);
            }
            ColKind::Binary => {
                if !coefficient.is_zero() || lower != 0.0 || upper != 1.0 {
                    return Err("order column is not an unfixed objective-free binary".into());
                }
                binary_cols.push(index);
            }
        }
    }
    if objective_cols.len() != 2 {
        return Err("scheduling formulation needs exactly two objective aggregates".into());
    }
    let objective_scale =
        objective_scale.ok_or_else(|| "missing scheduling objective scale".to_owned())?;
    if start_cols.len() < 2 || start_cols.len() > MAX_JOBS {
        return Err(format!(
            "scheduling job count {} is outside the supported 2..={MAX_JOBS} range",
            start_cols.len()
        ));
    }
    if slack_cols.len() != start_cols.len() {
        return Err("start/tardiness column counts differ".into());
    }
    if binary_cols.len()
        != start_cols
            .len()
            .checked_mul(start_cols.len() - 1)
            .ok_or_else(|| "binary count overflow".to_owned())?
    {
        return Err("order-binary count does not equal n(n-1)".into());
    }

    let mut incidence = vec![Vec::<usize>::new(); model.num_cols()];
    for row_index in 0..model.num_rows() {
        budget.poll_row(row_index)?;
        let (terms, _, _) = model.row(Row(row_index as u32));
        for &(column, _) in terms {
            budget.visit_term()?;
            incidence[column as usize].push(row_index);
        }
    }

    let start_membership = membership(model.num_cols(), &start_cols);
    let binary_membership = membership(model.num_cols(), &binary_cols);

    let mut used_rows = vec![false; model.num_rows()];
    let mut tardiness_aggregate = None;
    let mut start_aggregate = None;
    for &aggregate_col in &objective_cols {
        if incidence[aggregate_col].len() != 1 {
            return Err("objective aggregate does not occur in exactly one row".into());
        }
        let row_index = incidence[aggregate_col][0];
        let row = exact_row(model, row_index, &mut budget)?;
        if row.lower.is_some() {
            return Err("objective aggregate row is not upper-bounded".into());
        }
        let aggregate_coefficient = row
            .terms
            .iter()
            .find(|(column, _)| *column == aggregate_col)
            .map(|(_, coefficient)| coefficient)
            .ok_or_else(|| "objective aggregate row omits its objective column".to_owned())?;
        if aggregate_coefficient >= &BigRational::zero() {
            return Err("objective aggregate row coefficient is not negative".into());
        }
        let row_scale = -aggregate_coefficient;
        let rhs = integer_ratio(
            row.upper
                .as_ref()
                .ok_or_else(|| "objective aggregate row has no finite upper bound".to_owned())?,
            &row_scale,
        )?;
        let mut other_cols = Vec::new();
        for (column, coefficient) in &row.terms {
            if *column == aggregate_col {
                if coefficient != aggregate_coefficient {
                    return Err("objective aggregate row repeats its aggregate".into());
                }
            } else {
                if coefficient != &row_scale {
                    return Err("objective aggregate row member scaling is inconsistent".into());
                }
                other_cols.push(*column);
            }
        }
        other_cols.sort_unstable();
        if other_cols == slack_cols {
            if tardiness_aggregate
                .replace((aggregate_col, row_index, rhs))
                .is_some()
            {
                return Err("duplicate tardiness aggregate".into());
            }
        } else if other_cols == start_cols {
            if start_aggregate
                .replace((aggregate_col, row_index, rhs))
                .is_some()
            {
                return Err("duplicate start-time aggregate".into());
            }
        } else {
            return Err("objective aggregate members are not exactly one variable family".into());
        }
        used_rows[row_index] = true;
    }
    let (tardiness_aggregate_col, tardiness_aggregate_row, tardiness_aggregate_rhs) =
        tardiness_aggregate.ok_or_else(|| "missing tardiness aggregate".to_owned())?;
    let (start_aggregate_col, _start_aggregate_row, start_aggregate_rhs) =
        start_aggregate.ok_or_else(|| "missing start-time aggregate".to_owned())?;

    let mut start_to_slack = vec![None; model.num_cols()];
    let mut start_due = vec![None; model.num_cols()];
    for &slack_col in &slack_cols {
        let rows: Vec<usize> = incidence[slack_col]
            .iter()
            .copied()
            .filter(|&row| row != tardiness_aggregate_row)
            .collect();
        if rows.len() != 1 {
            return Err("tardiness column does not occur in exactly one epigraph row".into());
        }
        let row_index = rows[0];
        if used_rows[row_index] {
            return Err("epigraph row overlaps another structural row".into());
        }
        let row = exact_row(model, row_index, &mut budget)?;
        if row.lower.is_some() || row.terms.len() != 2 {
            return Err("tardiness epigraph is not a two-term upper inequality".into());
        }
        let slack_coefficient = row
            .terms
            .iter()
            .find(|(column, _)| *column == slack_col)
            .map(|(_, coefficient)| coefficient)
            .ok_or_else(|| "tardiness epigraph omits its slack".to_owned())?;
        if slack_coefficient >= &BigRational::zero() {
            return Err("tardiness epigraph slack coefficient is not negative".into());
        }
        let row_scale = -slack_coefficient;
        let due = integer_ratio(
            row.upper
                .as_ref()
                .ok_or_else(|| "tardiness epigraph has no finite due date".to_owned())?,
            &row_scale,
        )?;
        let mut paired_start = None;
        for (column, coefficient) in row.terms {
            if column == slack_col {
                if coefficient != -&row_scale {
                    return Err("tardiness epigraph repeats or rescales its slack".into());
                }
            } else if start_membership[column] && coefficient == row_scale {
                paired_start = Some(column);
            } else {
                return Err("tardiness epigraph does not pair one slack with one start".into());
            }
        }
        let start_col = paired_start.ok_or_else(|| "epigraph omits its start".to_owned())?;
        if start_to_slack[start_col].replace(slack_col).is_some()
            || start_due[start_col].replace(due).is_some()
        {
            return Err("multiple tardiness epigraphs use the same start".into());
        }
        used_rows[row_index] = true;
    }
    if start_cols
        .iter()
        .any(|&column| start_to_slack[column].is_none() || start_due[column].is_none())
    {
        return Err("a start column has no tardiness epigraph".into());
    }

    let mut start_job = vec![None; model.num_cols()];
    for (job, &column) in start_cols.iter().enumerate() {
        start_job[column] = Some(job);
    }
    let mut binary_index = vec![None; model.num_cols()];
    for (index, &column) in binary_cols.iter().enumerate() {
        binary_index[column] = Some(index);
    }
    let mut complement = vec![Vec::<usize>::new(); binary_cols.len()];
    let mut relations = vec![None; binary_cols.len()];
    let mut durations = vec![None; start_cols.len()];

    for row_index in 0..model.num_rows() {
        if used_rows[row_index] {
            continue;
        }
        budget.poll_row(row_index)?;
        let row = exact_row(model, row_index, &mut budget)?;
        let binary_terms: Vec<_> = row
            .terms
            .iter()
            .filter(|(column, _)| binary_membership[*column])
            .collect();
        let start_terms: Vec<_> = row
            .terms
            .iter()
            .filter(|(column, _)| start_membership[*column])
            .collect();

        if row.terms.len() == 2 && binary_terms.len() == 2 && start_terms.is_empty() {
            let row_scale = &binary_terms[0].1;
            if row_scale > &BigRational::zero()
                && &binary_terms[1].1 == row_scale
                && row.lower.as_ref() == Some(row_scale)
                && row.upper.as_ref() == Some(row_scale)
            {
                let first = binary_index[binary_terms[0].0]
                    .ok_or_else(|| "complement binary index missing".to_owned())?;
                let second = binary_index[binary_terms[1].0]
                    .ok_or_else(|| "complement binary index missing".to_owned())?;
                if first == second {
                    return Err("binary complement row repeats one column".into());
                }
                push_unique(&mut complement[first], second);
                push_unique(&mut complement[second], first);
                used_rows[row_index] = true;
                continue;
            }
        }

        if row.terms.len() == 3
            && binary_terms.len() == 1
            && start_terms.len() == 2
            && row.upper.is_none()
        {
            let lower = row
                .lower
                .as_ref()
                .ok_or_else(|| "precedence row has no finite lower bound".to_owned())?;
            let binary_coefficient = &binary_terms[0].1;
            if binary_coefficient <= &BigRational::zero() {
                return Err("precedence big-M coefficient is not positive".into());
            }
            let mut before = None;
            let mut after = None;
            let mut positive_scale = None;
            let mut negative_scale = None;
            for (column, coefficient) in start_terms {
                if coefficient > &BigRational::zero() {
                    after = start_job[*column];
                    positive_scale = Some(coefficient.clone());
                } else if coefficient < &BigRational::zero() {
                    before = start_job[*column];
                    negative_scale = Some(-coefficient);
                } else {
                    return Err("precedence start coefficient is zero".into());
                }
            }
            let row_scale = positive_scale
                .ok_or_else(|| "precedence row has no positive start coefficient".to_owned())?;
            if negative_scale.as_ref() != Some(&row_scale) {
                return Err("precedence start coefficients do not have opposite scaling".into());
            }
            let before =
                before.ok_or_else(|| "precedence row omits its before start".to_owned())?;
            let after = after.ok_or_else(|| "precedence row omits its after start".to_owned())?;
            if before == after {
                return Err("precedence row uses the same job twice".into());
            }
            let duration = integer_ratio(lower, &row_scale)?;
            if duration <= 0 {
                return Err("processing duration is not positive".into());
            }
            match durations[before] {
                Some(previous) if previous != duration => {
                    return Err("one job has inconsistent processing durations".into())
                }
                Some(_) => {}
                None => durations[before] = Some(duration),
            }
            let binary_col = binary_terms[0].0;
            let index = binary_index[binary_col]
                .ok_or_else(|| "precedence binary index missing".to_owned())?;
            if relations[index]
                .replace(BinaryRelation {
                    col: binary_col,
                    before,
                    after,
                })
                .is_some()
            {
                return Err("one order binary occurs in multiple precedence rows".into());
            }
            used_rows[row_index] = true;
            continue;
        }

        return Err(format!(
            "row {row_index} is outside the single-machine scheduling formulation"
        ));
    }
    if used_rows.iter().any(|used| !used) {
        return Err("not every source row was consumed".into());
    }
    if complement.iter().any(|partners| partners.len() != 1) {
        return Err("an order binary does not have one unique complement".into());
    }
    if relations.iter().any(Option::is_none) {
        return Err("an order binary has no unique precedence row".into());
    }
    if durations.iter().any(Option::is_none) {
        return Err("a job has no consistent processing duration".into());
    }

    let relations: Vec<BinaryRelation> = relations
        .into_iter()
        .map(|relation| relation.ok_or_else(|| "missing precedence relation".to_owned()))
        .collect::<Result<_, _>>()?;
    let mut pair_seen = vec![false; start_cols.len() * start_cols.len()];
    for binary in 0..binary_cols.len() {
        let partner = complement[binary][0];
        if binary >= partner {
            continue;
        }
        if complement[partner][0] != binary {
            return Err("binary complement relation is not symmetric".into());
        }
        let forward = relations[binary];
        let reverse = relations[partner];
        if forward.before != reverse.after || forward.after != reverse.before {
            return Err("complemented order binaries do not encode opposite precedences".into());
        }
        let low = forward.before.min(forward.after);
        let high = forward.before.max(forward.after);
        let slot = low * start_cols.len() + high;
        if std::mem::replace(&mut pair_seen[slot], true) {
            return Err("a job pair has multiple complemented order pairs".into());
        }
    }
    for low in 0..start_cols.len() {
        for high in (low + 1)..start_cols.len() {
            if !pair_seen[low * start_cols.len() + high] {
                return Err("not every unordered job pair has an order disjunction".into());
            }
        }
    }

    let jobs = start_cols
        .iter()
        .enumerate()
        .map(|(job, &start_col)| {
            let (lower, upper) = model.col_bounds(Col(start_col as u32));
            Ok(Job {
                start_col,
                slack_col: start_to_slack[start_col]
                    .ok_or_else(|| "missing paired slack".to_owned())?,
                release: finite_integer(lower)
                    .ok_or_else(|| "missing integral release".to_owned())?,
                due: start_due[start_col].ok_or_else(|| "missing due date".to_owned())?,
                duration: durations[job].ok_or_else(|| "missing duration".to_owned())?,
                start_upper: if upper.is_finite() {
                    Some(
                        finite_integer(upper)
                            .ok_or_else(|| "nonintegral start upper bound".to_owned())?,
                    )
                } else {
                    None
                },
            })
        })
        .collect::<Result<Vec<_>, String>>()?;

    let objective_constant = model.obj_offset_exact()
        - &objective_scale * (rational(tardiness_aggregate_rhs) + rational(start_aggregate_rhs));
    Ok(RecognizedScheduling {
        jobs,
        binaries: relations,
        tardiness_aggregate_col,
        start_aggregate_col,
        tardiness_aggregate_rhs,
        start_aggregate_rhs,
        objective_scale,
        objective_constant,
    })
}

fn solve_dp(
    scheduling: &RecognizedScheduling,
    deadline: Option<Instant>,
) -> Result<DpOptimum, String> {
    let n = scheduling.jobs.len();
    let subset_count = 1usize
        .checked_shl(n as u32)
        .ok_or_else(|| "subset table size overflow".to_owned())?;
    let mut frontiers: Vec<Vec<FrontierEntry>> = (0..subset_count).map(|_| Vec::new()).collect();
    frontiers[0].push(FrontierEntry {
        finish: i64::MIN,
        cost: 0,
        order: 0,
    });
    let mut transitions = 0u64;
    let mut accepted = 1u64;

    for subset in 0..(subset_count - 1) {
        if frontiers[subset].is_empty() {
            continue;
        }
        let depth = subset.count_ones() as usize;
        // A transition only writes strict supersets, so this immutable borrow
        // cannot alias a destination frontier. Copying the (small) Pareto set
        // also keeps the loop straightforward and deterministic.
        let source = frontiers[subset].clone();
        for state in source {
            for job in 0..n {
                if subset & (1usize << job) != 0 {
                    continue;
                }
                transitions = transitions
                    .checked_add(1)
                    .ok_or_else(|| "scheduling transition count overflow".to_owned())?;
                if transitions > MAX_TRANSITIONS {
                    return Err("scheduling DP transition cap reached".into());
                }
                if transitions & DEADLINE_POLL_MASK == 0 {
                    check_deadline(deadline)?;
                }
                let spec = &scheduling.jobs[job];
                let start = max(state.finish, spec.release);
                if spec.start_upper.is_some_and(|upper| start > upper) {
                    continue;
                }
                let finish = start
                    .checked_add(spec.duration)
                    .ok_or_else(|| "scheduling time overflow".to_owned())?;
                let tardiness = (i128::from(start) - i128::from(spec.due)).max(0);
                let cost = state
                    .cost
                    .checked_add(i128::from(start))
                    .and_then(|value| value.checked_add(tardiness))
                    .ok_or_else(|| "scheduling objective overflow".to_owned())?;
                let shift = depth
                    .checked_mul(5)
                    .ok_or_else(|| "scheduling order encoding overflow".to_owned())?;
                let order = state.order | ((job as u128) << shift);
                let candidate = FrontierEntry {
                    finish,
                    cost,
                    order,
                };
                let destination = subset | (1usize << job);
                if insert_nondominated(&mut frontiers[destination], candidate) {
                    accepted = accepted
                        .checked_add(1)
                        .ok_or_else(|| "scheduling state count overflow".to_owned())?;
                    if accepted > MAX_ACCEPTED_STATES {
                        return Err("scheduling DP state cap reached".into());
                    }
                }
            }
        }
    }
    check_deadline(deadline)?;
    let full = &frontiers[subset_count - 1];
    let best = full
        .iter()
        .map(|entry| entry.cost)
        .min()
        .ok_or_else(|| "scheduling DP found no complete sequence".to_owned())?;
    let candidate_orders = full
        .iter()
        .filter(|entry| entry.cost == best)
        .map(|entry| entry.order)
        .collect();
    Ok(DpOptimum {
        cost: best,
        candidate_orders,
    })
}

/// Maintain a two-dimensional Pareto frontier sorted by increasing finish
/// time. Nondominance then implies strictly decreasing cost, so predecessor
/// and consecutive-successor checks are sufficient.
fn insert_nondominated(frontier: &mut Vec<FrontierEntry>, candidate: FrontierEntry) -> bool {
    let position = frontier.partition_point(|entry| entry.finish < candidate.finish);
    if position < frontier.len() && frontier[position].finish == candidate.finish {
        if frontier[position].cost <= candidate.cost {
            return false;
        }
        frontier.remove(position);
    }
    if position > 0 && frontier[position - 1].cost <= candidate.cost {
        return false;
    }
    while position < frontier.len() && frontier[position].cost >= candidate.cost {
        frontier.remove(position);
    }
    frontier.insert(position, candidate);
    true
}

fn reconstruct(
    model: &Model,
    scheduling: &RecognizedScheduling,
    sequence: &[usize],
) -> Result<(Vec<BigRational>, BigRational, i128), String> {
    if sequence.len() != scheduling.jobs.len() {
        return Err("scheduling sequence has the wrong length".into());
    }
    let mut seen = vec![false; scheduling.jobs.len()];
    let mut starts = vec![0i64; scheduling.jobs.len()];
    let mut clock = i64::MIN;
    let mut cost = 0i128;
    for &job in sequence {
        let spec = scheduling
            .jobs
            .get(job)
            .ok_or_else(|| "scheduling sequence contains an out-of-range job".to_owned())?;
        if std::mem::replace(&mut seen[job], true) {
            return Err("scheduling sequence repeats a job".into());
        }
        let start = max(clock, spec.release);
        if spec.start_upper.is_some_and(|upper| start > upper) {
            return Err("scheduling sequence violates a start upper bound".into());
        }
        clock = start
            .checked_add(spec.duration)
            .ok_or_else(|| "scheduling time overflow".to_owned())?;
        starts[job] = start;
        cost = cost
            .checked_add(i128::from(start))
            .and_then(|value| value.checked_add((i128::from(start) - i128::from(spec.due)).max(0)))
            .ok_or_else(|| "scheduling objective overflow".to_owned())?;
    }
    if seen.iter().any(|present| !present) {
        return Err("scheduling sequence omits a job".into());
    }

    let mut positions = vec![0usize; scheduling.jobs.len()];
    for (position, &job) in sequence.iter().enumerate() {
        positions[job] = position;
    }
    let mut values = vec![BigRational::zero(); model.num_cols()];
    let mut tardiness_sum = 0i128;
    let mut start_sum = 0i128;
    for (job, spec) in scheduling.jobs.iter().enumerate() {
        let start = starts[job];
        let tardiness = (i128::from(start) - i128::from(spec.due)).max(0);
        values[spec.start_col] = rational(start);
        values[spec.slack_col] = rational_i128(tardiness);
        start_sum = start_sum
            .checked_add(i128::from(start))
            .ok_or_else(|| "start aggregate overflow".to_owned())?;
        tardiness_sum = tardiness_sum
            .checked_add(tardiness)
            .ok_or_else(|| "tardiness aggregate overflow".to_owned())?;
    }
    values[scheduling.start_aggregate_col] = rational_i128(
        start_sum
            .checked_sub(i128::from(scheduling.start_aggregate_rhs))
            .ok_or_else(|| "start aggregate overflow".to_owned())?,
    );
    values[scheduling.tardiness_aggregate_col] = rational_i128(
        tardiness_sum
            .checked_sub(i128::from(scheduling.tardiness_aggregate_rhs))
            .ok_or_else(|| "tardiness aggregate overflow".to_owned())?,
    );
    for relation in &scheduling.binaries {
        values[relation.col] = if positions[relation.before] < positions[relation.after] {
            BigRational::zero()
        } else {
            BigRational::one()
        };
    }

    model
        .check_point(&values)
        .map_err(|violation| format!("reconstructed source witness rejected: {violation:?}"))?;
    let value = model.objective_value_at(&values);
    let expected =
        &scheduling.objective_scale * rational_i128(cost) + &scheduling.objective_constant;
    if value != expected {
        return Err(format!(
            "reconstructed source objective {value} differs from scheduling value {expected}"
        ));
    }
    Ok((values, value, cost))
}

fn exact_row(
    model: &Model,
    row_index: usize,
    budget: &mut RecognitionBudget,
) -> Result<ExactRow, String> {
    let (terms, lower, upper) = model.row(Row(row_index as u32));
    let mut exact_terms = Vec::with_capacity(terms.len());
    for &(column, coefficient) in terms {
        budget.visit_term()?;
        exact_terms.push((
            column as usize,
            model.row_coeff_exact(row_index, column, coefficient),
        ));
    }
    Ok(ExactRow {
        terms: exact_terms,
        lower: model.row_lb_exact(row_index, lower),
        upper: model.row_ub_exact(row_index, upper),
    })
}

fn decode_order(encoded: u128, jobs: usize) -> Result<Vec<usize>, String> {
    let mut order = Vec::with_capacity(jobs);
    let mut bits = encoded;
    for _ in 0..jobs {
        let job = (bits & 31) as usize;
        if job >= jobs {
            return Err("scheduling order encoding contains an out-of-range job".into());
        }
        order.push(job);
        bits >>= 5;
    }
    if bits != 0 {
        return Err("scheduling order encoding has trailing data".into());
    }
    Ok(order)
}

fn membership(columns: usize, members: &[usize]) -> Vec<bool> {
    let mut result = vec![false; columns];
    for &member in members {
        result[member] = true;
    }
    result
}

fn push_unique(values: &mut Vec<usize>, value: usize) {
    if !values.contains(&value) {
        values.push(value);
    }
}

fn rational(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn rational_i128(value: i128) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn integer_rational(value: &BigRational) -> Result<i64, String> {
    if !value.is_integer() {
        return Err(format!(
            "structural scheduling value {value} is not integral"
        ));
    }
    value
        .to_integer()
        .to_i64()
        .ok_or_else(|| format!("structural scheduling integer {value} is outside i64"))
}

fn integer_ratio(value: &BigRational, positive_scale: &BigRational) -> Result<i64, String> {
    if positive_scale <= &BigRational::zero() {
        return Err("structural scheduling row scale is not positive".into());
    }
    integer_rational(&(value / positive_scale))
}

fn finite_integer(value: f64) -> Option<i64> {
    if !value.is_finite()
        || value.fract() != 0.0
        || value < i64::MIN as f64
        || value > i64::MAX as f64
    {
        return None;
    }
    let integer = value as i64;
    ((integer as f64) == value).then_some(integer)
}

fn is_free(lower: f64, upper: f64) -> bool {
    lower == f64::NEG_INFINITY && upper == f64::INFINITY
}

fn is_pos_inf(value: f64) -> bool {
    value == f64::INFINITY
}

fn check_deadline(deadline: Option<Instant>) -> Result<(), String> {
    if deadline.is_some_and(|limit| Instant::now() >= limit) {
        Err("scheduling route deadline reached".into())
    } else {
        Ok(())
    }
}

fn trial_deadline(outer: Option<Instant>, now: Instant) -> Option<Instant> {
    let ceiling = now.checked_add(MAX_DP_TRIAL)?;
    match outer {
        Some(deadline) if deadline > now => Some(deadline.min(ceiling)),
        Some(_) => None,
        None => Some(ceiling),
    }
}

fn certificate_deadline(outer: Option<Instant>, now: Instant) -> Option<Instant> {
    let ceiling = now.checked_add(MAX_CERT_REPLAY)?;
    match outer {
        Some(deadline) if deadline > now => Some(deadline.min(ceiling)),
        Some(_) => None,
        None => Some(ceiling),
    }
}

pub(crate) fn optimality_parts(
    certificate: &SingleMachineSchedulingOptimalityCertificate,
) -> (&BigRational, &[u32]) {
    (&certificate.value, &certificate.sequence)
}

pub(crate) fn optimality_from_parts(
    value: BigRational,
    sequence: Vec<u32>,
) -> SingleMachineSchedulingOptimalityCertificate {
    SingleMachineSchedulingOptimalityCertificate { value, sequence }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scheduling_model(big_m: f64) -> Model {
        // Three jobs. The insertion order is intentionally unlike the MPS
        // family (starts first, then aggregates, interleaved rows) so tests
        // exercise structural recognition rather than positional matching.
        let mut model = Model::new();
        let starts = [
            model.add_int_col(0.0, f64::INFINITY),
            model.add_int_col(2.0, f64::INFINITY),
            model.add_int_col(1.0, f64::INFINITY),
        ];
        let slacks = [
            model.add_col(0.0, f64::INFINITY),
            model.add_col(0.0, f64::INFINITY),
            model.add_col(0.0, f64::INFINITY),
        ];
        let tardiness_aggregate = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let start_aggregate = model.add_col(f64::NEG_INFINITY, f64::INFINITY);

        let mut order = [[None; 3]; 3];
        for before in 0..3 {
            for after in 0..3 {
                if before != after {
                    order[before][after] = Some(model.add_binary_col());
                }
            }
        }
        model.set_objective(
            &[(tardiness_aggregate, 2.0), (start_aggregate, 2.0)],
            Sense::Minimize,
        );
        model.set_objective_offset(3.0);

        let dues = [2.0, 5.0, 4.0];
        let epigraph_scale = 0.5;
        for job in [2, 0, 1] {
            model.add_row(
                f64::NEG_INFINITY,
                dues[job] * epigraph_scale,
                &[
                    (starts[job], epigraph_scale),
                    (slacks[job], -epigraph_scale),
                ],
            );
        }
        let tardiness_aggregate_scale = 2.0;
        model.add_row(
            f64::NEG_INFINITY,
            tardiness_aggregate_scale,
            &[
                (slacks[0], tardiness_aggregate_scale),
                (slacks[1], tardiness_aggregate_scale),
                (slacks[2], tardiness_aggregate_scale),
                (tardiness_aggregate, -tardiness_aggregate_scale),
            ],
        );
        let start_aggregate_scale = 0.25;
        model.add_row(
            f64::NEG_INFINITY,
            4.0 * start_aggregate_scale,
            &[
                (starts[0], start_aggregate_scale),
                (starts[1], start_aggregate_scale),
                (starts[2], start_aggregate_scale),
                (start_aggregate, -start_aggregate_scale),
            ],
        );

        let durations = [2.0, 3.0, 1.0];
        let complement_scale = 3.0;
        // This is the exact model-frame scaling produced when the MPS reader
        // normalizes a row whose raw big-M coefficient is 10,000.
        let precedence_scale = 0.0625;
        for low in 0..3 {
            for high in (low + 1)..3 {
                let forward = order[low][high].expect("forward binary");
                let reverse = order[high][low].expect("reverse binary");
                // Duplicate complement equalities match a common generated
                // MPS formulation but are not tied to a particular count.
                model.add_row(
                    complement_scale,
                    complement_scale,
                    &[(forward, complement_scale), (reverse, complement_scale)],
                );
                model.add_row(
                    complement_scale,
                    complement_scale,
                    &[(reverse, complement_scale), (forward, complement_scale)],
                );
                model.add_row(
                    durations[low] * precedence_scale,
                    f64::INFINITY,
                    &[
                        (forward, big_m * precedence_scale),
                        (starts[high], precedence_scale),
                        (starts[low], -precedence_scale),
                    ],
                );
                model.add_row(
                    durations[high] * precedence_scale,
                    f64::INFINITY,
                    &[
                        (reverse, big_m * precedence_scale),
                        (starts[low], precedence_scale),
                        (starts[high], -precedence_scale),
                    ],
                );
            }
        }
        model
    }

    #[test]
    fn solves_structural_single_machine_model_and_replays_certificate() {
        let model = scheduling_model(100.0);
        let decision = try_solve_certified(&model, None).expect("route should own model");
        let SingleMachineSchedulingDecision::Optimal {
            value,
            model_values,
            certificate,
        } = decision;
        model.check_point(&model_values).expect("source witness");
        assert_eq!(model.objective_value_at(&model_values), value);
        verify_optimality_certificate(&model, &value, &certificate).expect("typed replay");
    }

    #[test]
    fn full_session_posture_publishes_typed_optimality_artifact() {
        let model = scheduling_model(100.0);
        let opts = crate::SolveOpts::new().with_require_certificates(true);
        let mut session = crate::BabSession::new(model, &opts).expect("session");
        let outcome = session.check().expect("session solve");
        let crate::Outcome::Optimal { value, .. } = outcome else {
            panic!("scheduling route did not return an optimum");
        };
        let certificate = session
            .single_machine_scheduling_optimality_certificate()
            .expect("typed scheduling certificate");
        verify_optimality_certificate(session.model(), &value, certificate)
            .expect("published certificate replay");
        assert!(session.replay_claims().is_empty());
    }

    #[test]
    fn unrelated_side_row_declines_fail_closed() {
        let mut model = scheduling_model(100.0);
        let start = model.col_at(0).expect("first start");
        model.add_row(f64::NEG_INFINITY, 50.0, &[(start, 1.0)]);
        assert!(try_solve(&model, None).is_none());
    }

    #[test]
    fn undersized_big_m_declines_when_dp_optimum_is_not_source_feasible() {
        let model = scheduling_model(0.5);
        assert!(try_solve(&model, None).is_none());
    }

    #[test]
    fn tampered_sequence_value_and_model_are_rejected() {
        let model = scheduling_model(100.0);
        let decision = try_solve(&model, None).expect("route should own model");
        let SingleMachineSchedulingDecision::Optimal {
            value, certificate, ..
        } = decision;

        let mut sequence_tamper = certificate.clone();
        sequence_tamper.sequence[1] = sequence_tamper.sequence[0];
        assert!(verify_optimality_certificate(&model, &value, &sequence_tamper).is_err());

        let mut value_tamper = certificate.clone();
        value_tamper.value += rational(1);
        assert!(verify_optimality_certificate(&model, &value, &value_tamper).is_err());

        let mut changed_model = model.clone();
        changed_model.set_objective_offset(4.0);
        assert!(verify_optimality_certificate(&changed_model, &value, &certificate).is_err());
    }

    #[test]
    fn expired_deadline_declines_without_search() {
        let model = scheduling_model(100.0);
        assert!(try_solve(&model, Some(Instant::now())).is_none());
    }

    #[test]
    fn recognition_budget_enforces_term_cap_and_deadline() {
        let mut capped = RecognitionBudget {
            deadline: None,
            term_visits: MAX_RECOGNITION_TERM_VISITS,
        };
        assert!(capped.visit_term().is_err());

        let expired = RecognitionBudget::new(Some(Instant::now()));
        assert!(expired.poll_row(0).is_err());
    }

    #[test]
    fn pareto_frontier_keeps_only_nondominated_entries() {
        let mut frontier = Vec::new();
        assert!(insert_nondominated(
            &mut frontier,
            FrontierEntry {
                finish: 5,
                cost: 10,
                order: 1,
            }
        ));
        assert!(insert_nondominated(
            &mut frontier,
            FrontierEntry {
                finish: 7,
                cost: 8,
                order: 2,
            }
        ));
        assert!(!insert_nondominated(
            &mut frontier,
            FrontierEntry {
                finish: 8,
                cost: 9,
                order: 3,
            }
        ));
        assert!(insert_nondominated(
            &mut frontier,
            FrontierEntry {
                finish: 6,
                cost: 7,
                order: 4,
            }
        ));
        assert_eq!(
            frontier
                .iter()
                .map(|entry| (entry.finish, entry.cost))
                .collect::<Vec<_>>(),
            vec![(5, 10), (6, 7)]
        );
    }
}
