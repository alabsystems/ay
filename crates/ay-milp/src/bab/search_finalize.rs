// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Terminal branch-and-bound authority mapping.
//!
//! This module is the only terminal path that turns frontier coverage into a
//! bound, optimality, unboundedness, or infeasibility claim. Missing coverage,
//! failed replay, and frame-mismatched certificates always decline closed.
//!
//! The order is part of the authority contract:
//!
//! 1. An unbounded relaxation is reported only after a feasibility solve.
//! 2. A finite claim aggregates every live region and retained lost/restart
//!    bank in the internal minimize frame, then reframes it exactly once.
//! 3. A marked-margin crossing merely triggers caller-frame replay; only the
//!    replayed certificate can return infeasibility.
//! 4. Exhausted, interrupted, and timed-out trees map to distinct outcomes.

use std::collections::BinaryHeap;
use std::time::{Duration, Instant};

use num_rational::BigRational;
use num_traits::Zero;

use super::*;

pub(super) struct FinalizationFrame<'a> {
    pub(super) caller_model: &'a Model,
    pub(super) search_model: &'a Model,
    pub(super) opts: &'a SolveOpts,
    pub(super) sense: Sense,
    pub(super) model_offset: BigRational,
    pub(super) symmetry_retry: SymmetryRetry<'a>,
}

pub(super) struct RetryAdvice<'a> {
    pub(super) branch_hints: &'a [Col],
    pub(super) root_probe_shortlist: &'a [Col],
    pub(super) shared_binary_prefix: &'a [Col],
}

enum SymmetryRetryKind<'a> {
    Ineligible,
    Eligible {
        base_mode: SearchMode,
        deadline: Option<Instant>,
        advice: RetryAdvice<'a>,
    },
}

pub(super) struct SymmetryRetry<'a>(SymmetryRetryKind<'a>);

impl<'a> SymmetryRetry<'a> {
    pub(super) fn classify(
        mode: SearchMode,
        opts: &SolveOpts,
        deadline: Option<Instant>,
        symmetry_engaged: bool,
        advice: RetryAdvice<'a>,
    ) -> Self {
        let eligible = symmetry_engaged
            && opts.tree_cert_leaves > 0
            && mode.depth == 0
            && !mode.cheap
            && !mode.projected
            && !mode.no_sym;
        if eligible {
            Self(SymmetryRetryKind::Eligible {
                base_mode: mode,
                deadline,
                advice,
            })
        } else {
            Self(SymmetryRetryKind::Ineligible)
        }
    }
}

/// Search state whose coverage determines the strongest terminal claim.
pub(super) struct FrontierConclusion<'a> {
    pub(super) dive: &'a [Node],
    pub(super) heap: &'a BinaryHeap<Node>,
    pub(super) incumbent: Option<(Vec<BigRational>, BigRational)>,
    pub(super) lost_subtree: bool,
    pub(super) lost_bank: Option<&'a BigRational>,
    pub(super) restart_bank: Option<&'a BigRational>,
    pub(super) root_floor: Option<&'a BigRational>,
    pub(super) floor_policy: TreeFloorPolicy,
    pub(super) objective: ObjectiveClass,
    pub(super) termination: SearchTermination,
    pub(super) relaxation: RelaxationConclusion,
}

#[derive(Clone, Copy)]
pub(super) enum TreeFloorPolicy {
    Apply,
    Ignore,
}

#[derive(Clone, Copy)]
pub(super) enum ObjectiveClass {
    Costed,
    Feasibility,
}

#[derive(Clone, Copy)]
enum InterruptedBoundPolicy {
    Report,
    Suppress,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum SearchTermination {
    Exhausted,
    TimedOut,
    Incomplete,
}

#[derive(Clone, Copy)]
pub(super) enum RelaxationConclusion {
    Bounded,
    Unbounded,
}

/// Diagnostic counters plus the optional caller-frame replay target.
pub(super) struct MarginFinalization<'a> {
    pub(super) target: Option<&'a crate::margin::MarginProofTarget<'a>>,
    pub(super) live_preview_enabled: bool,
    pub(super) live_preview_attempted: bool,
    pub(super) bound_checks: usize,
    pub(super) bound_crossings: usize,
    pub(super) replay_failures: usize,
}

pub(super) struct CertificateFinalization {
    pub(super) capture: crate::tree_cert::TreeCapture,
    pub(super) full_deadline: Option<Instant>,
    pub(super) finalize_reserve: Option<Duration>,
}

#[derive(Clone, Copy)]
pub(super) enum FinalizeTrace {
    Disabled,
    Enabled { nodes: usize, started: Instant },
}

impl FinalizeTrace {
    fn enabled(self) -> bool {
        matches!(self, Self::Enabled { .. })
    }

    fn nodes(self) -> usize {
        match self {
            Self::Disabled => 0,
            Self::Enabled { nodes, .. } => nodes,
        }
    }
}

pub(super) struct FinalizationRequest<'a> {
    pub(super) frame: FinalizationFrame<'a>,
    pub(super) frontier: FrontierConclusion<'a>,
    pub(super) margin: MarginFinalization<'a>,
    pub(super) certificate: CertificateFinalization,
    pub(super) trace: FinalizeTrace,
}

/// Consume terminal search state and emit the strongest licensed outcome.
pub(super) fn finalize_search(mut request: FinalizationRequest<'_>) -> Outcome {
    if matches!(request.frontier.relaxation, RelaxationConclusion::Unbounded) {
        return probe_integer_feasibility(&request.frame);
    }
    let exact_bound = aggregate_frontier_bound(&request);
    trace_tree_bound(&request, exact_bound.as_ref());
    let framed_bound = exact_bound.map(|bound| bound.framed);
    let interrupted_bound_policy = if matches!(request.frontier.objective, ObjectiveClass::Costed)
        && crate::tune::caller_flag(crate::tune::Knob::NoTreeBoundOutcome) != Some(true)
    {
        InterruptedBoundPolicy::Report
    } else {
        InterruptedBoundPolicy::Suppress
    };
    if let Some(outcome) = finalize_margin(&mut request, framed_bound.as_ref()) {
        return outcome;
    }
    trace_margin_fallthrough(&request);
    build_outcome(request, framed_bound, interrupted_bound_policy)
}

fn probe_integer_feasibility(frame: &FinalizationFrame<'_>) -> Outcome {
    let mut probe = frame.search_model.clone();
    probe.set_objective(&[], Sense::Minimize);
    let opts = frame.opts.clone().with_tree_cert_leaves(0);
    map_integer_feasibility_probe(solve_milp(&probe, &opts))
}

/// Map only the probe's feasibility fact; its evidence names the search frame.
fn map_integer_feasibility_probe(outcome: Outcome) -> Outcome {
    match outcome {
        Outcome::Optimal { .. } | Outcome::Feasible { .. } => Outcome::Unbounded,
        Outcome::Infeasible { .. } => Outcome::Infeasible {
            cert: None,
            tree_cert: None,
        },
        _ => Outcome::Unknown {
            reason: UnknownReason::SolverIncomplete {
                detail: "unbounded relaxation, but integer feasibility undecided".to_owned(),
            },
        },
    }
}

fn aggregate_frontier_bound(request: &FinalizationRequest<'_>) -> Option<ExactFrontierBound> {
    exact_frontier_bound(
        None,
        request.frontier.dive,
        request.frontier.heap,
        request.frontier.incumbent.as_ref().map(|(_, value)| value),
        request.frontier.lost_subtree,
        request.frontier.lost_bank,
        request.frontier.restart_bank,
        request.frontier.root_floor,
        matches!(request.frontier.floor_policy, TreeFloorPolicy::Apply),
        matches!(request.frontier.objective, ObjectiveClass::Feasibility),
        request.frame.sense,
        &request.frame.model_offset,
    )
}

fn trace_tree_bound(request: &FinalizationRequest<'_>, bound: Option<&ExactFrontierBound>) {
    if !request.trace.enabled() {
        return;
    }
    let Some(bound) = bound else {
        return;
    };
    eprintln!(
        "--trace tree bound (minimize frame) = {:.6} (root floor {})",
        to_f64(&bound.internal),
        request.frontier.root_floor.map_or_else(
            || "none".to_owned(),
            |floor| format!("{:.6}", to_f64(floor))
        )
    );
}

fn finalize_margin(
    request: &mut FinalizationRequest<'_>,
    framed_bound: Option<&BigRational>,
) -> Option<Outcome> {
    let target = request.margin.target?;
    let bound = framed_bound?;
    if !request.certificate.capture.is_armed() {
        return None;
    }
    request.margin.bound_checks += 1;
    if !target.strictly_excludes(bound) {
        return None;
    }
    request.margin.bound_crossings += 1;
    trace_margin_replay(request, bound, "finalize-begin");
    let certificate = request.certificate.capture.finalize_margin_cover(
        target.proof_model(),
        finalize_deadline(
            request.certificate.full_deadline,
            request.certificate.finalize_reserve,
            Instant::now(),
        ),
    );
    let Some(certificate) = certificate else {
        request.margin.replay_failures += 1;
        trace_margin_replay(request, bound, "finalize-failed-fallthrough");
        return None;
    };
    debug_assert!(certificate.verify(target.proof_model()).is_ok());
    if request.trace.enabled() {
        eprintln!(
            "--trace marked-margin-bound-stop phase=terminal replay=finalize-verified \
             checks={} crossings={} failures={}",
            request.margin.bound_checks,
            request.margin.bound_crossings,
            request.margin.replay_failures
        );
    }
    Some(Outcome::Infeasible {
        cert: None,
        tree_cert: Some(certificate),
    })
}

fn trace_margin_replay(request: &FinalizationRequest<'_>, bound: &BigRational, replay: &str) {
    if request.trace.enabled() {
        eprintln!(
            "--trace marked-margin-bound-stop phase=terminal bound={:.12} nodes={} \
             frontier={} replay={replay}",
            to_f64(bound),
            request.trace.nodes(),
            request.frontier.dive.len() + request.frontier.heap.len(),
        );
    }
}

fn trace_margin_fallthrough(request: &FinalizationRequest<'_>) {
    if request.trace.enabled() && request.margin.target.is_some() {
        eprintln!(
            "--trace marked-margin-bound-stop phase=fallthrough checks={} crossings={} \
             failures={} live_preview_enabled={} live_preview_attempted={} capture_armed={}",
            request.margin.bound_checks,
            request.margin.bound_crossings,
            request.margin.replay_failures,
            request.margin.live_preview_enabled,
            request.margin.live_preview_attempted,
            request.certificate.capture.is_armed()
        );
    }
}

fn build_outcome(
    mut request: FinalizationRequest<'_>,
    framed_bound: Option<BigRational>,
    interrupted_bound_policy: InterruptedBoundPolicy,
) -> Outcome {
    match request.frontier.incumbent.take() {
        Some((values, minimized)) => {
            outcome_with_incumbent(&request, values, minimized, framed_bound)
        }
        None => outcome_without_incumbent(request, framed_bound, interrupted_bound_policy),
    }
}

fn outcome_with_incumbent(
    request: &FinalizationRequest<'_>,
    values: Vec<BigRational>,
    minimized: BigRational,
    framed_bound: Option<BigRational>,
) -> Outcome {
    let value = match request.frame.sense {
        Sense::Minimize => minimized,
        Sense::Maximize => -minimized,
    };
    if request.frontier.termination != SearchTermination::Exhausted {
        if request.trace.enabled() {
            if let Some(bound) = &framed_bound {
                eprintln!("--trace interrupted: dual bound = {bound}");
            }
        }
        return Outcome::Feasible {
            model_values: values,
            incumbent_only: true,
            dual_bound: framed_bound,
        };
    }
    let cert = zero_objective_certificate(request);
    Outcome::Optimal {
        value: value + &request.frame.model_offset,
        model_values: values,
        cert,
    }
}

fn zero_objective_certificate(
    request: &FinalizationRequest<'_>,
) -> Option<crate::cert::OptimalityCertificate> {
    let zero = matches!(request.frontier.objective, ObjectiveClass::Feasibility)
        && (0..request.frame.caller_model.num_cols())
            .all(|column| request.frame.caller_model.obj_coeff(Col(column as u32)) == 0.0);
    zero.then(|| crate::cert::OptimalityCertificate {
        sense: request.frame.sense,
        objective: Vec::new(),
        bound: BigRational::zero(),
        multipliers: Vec::new(),
    })
}

fn outcome_without_incumbent(
    request: FinalizationRequest<'_>,
    framed_bound: Option<BigRational>,
    interrupted_bound_policy: InterruptedBoundPolicy,
) -> Outcome {
    if request.frontier.termination != SearchTermination::Exhausted {
        if let (InterruptedBoundPolicy::Report, Some(bound)) =
            (interrupted_bound_policy, framed_bound)
        {
            return Outcome::Bound {
                dual_bound: bound,
                rigorous: true,
            };
        }
        return interrupted_without_incumbent(request.frontier.termination);
    }
    finalize_infeasible(request)
}

fn interrupted_without_incumbent(termination: SearchTermination) -> Outcome {
    let reason = match termination {
        SearchTermination::TimedOut => UnknownReason::Timeout,
        SearchTermination::Incomplete => UnknownReason::SolverIncomplete {
            detail: "branch-and-bound could not settle every node".to_owned(),
        },
        SearchTermination::Exhausted => unreachable!("exhausted search is handled separately"),
    };
    Outcome::Unknown { reason }
}

fn finalize_infeasible(request: FinalizationRequest<'_>) -> Outcome {
    let mut tree_cert = request.certificate.capture.finalize(
        request.frame.caller_model,
        terminal_finalize_deadline(request.certificate.full_deadline),
        request.certificate.finalize_reserve,
    );
    if tree_cert.is_none() && symmetry_retry_allowed(&request.frame.symmetry_retry) {
        tree_cert = retry_without_symmetry(&request.frame);
    }
    if let FinalizeTrace::Enabled { started, .. } = request.trace {
        eprintln!(
            "--trace finalize: outcome built at +{:.2}s",
            started.elapsed().as_secs_f64()
        );
    }
    Outcome::Infeasible {
        cert: None,
        tree_cert,
    }
}

fn symmetry_retry_allowed(retry: &SymmetryRetry<'_>) -> bool {
    match &retry.0 {
        SymmetryRetryKind::Ineligible => false,
        SymmetryRetryKind::Eligible { deadline, .. } => {
            deadline.is_none_or(|deadline| Instant::now() < deadline)
        }
    }
}

fn retry_without_symmetry(
    frame: &FinalizationFrame<'_>,
) -> Option<crate::tree_cert::MilpInfeasibilityCertificate> {
    let SymmetryRetryKind::Eligible {
        base_mode, advice, ..
    } = &frame.symmetry_retry.0
    else {
        return None;
    };
    let mode = SearchMode {
        no_sym: true,
        ..*base_mode
    };
    match solve_milp_in(
        frame.caller_model,
        frame.opts,
        mode,
        None,
        advice.branch_hints,
        advice.root_probe_shortlist,
        advice.shared_binary_prefix,
    ) {
        Outcome::Infeasible { tree_cert, .. } => tree_cert,
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unbounded_probe_strips_search_frame_evidence() {
        let farkas = crate::cert::FarkasCertificate {
            multipliers: Vec::new(),
        };
        let tree = crate::tree_cert::MilpInfeasibilityCertificate {
            root: crate::tree_cert::TreeNode::Leaf {
                farkas: farkas.clone(),
            },
        };
        let mapped = map_integer_feasibility_probe(Outcome::Infeasible {
            cert: Some(farkas),
            tree_cert: Some(tree),
        });
        assert!(matches!(
            mapped,
            Outcome::Infeasible {
                cert: None,
                tree_cert: None
            }
        ));
    }
}
