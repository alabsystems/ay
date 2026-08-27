// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Canonical root frontier construction.
//!
//! Prefix scoring is advice only. Every returned region remains one member of
//! a complete canonical partition, and every floor comes from the same exact
//! safe-bound conversion used by ordinary nodes.

use std::collections::BinaryHeap;
use std::num::NonZeroUsize;
use std::sync::Arc;

use super::*;
use crate::simplex::Candidate;

pub(super) struct RootFrame<'a> {
    pub(super) caller_model: &'a Model,
    pub(super) lp: &'a FloatLp,
    pub(super) candidate: &'a Candidate,
    pub(super) lower: &'a [f64],
    pub(super) upper: &'a [f64],
    pub(super) objective_granularity: Option<&'a BigRational>,
}

pub(super) struct FrontierStorage<'a> {
    pub(super) heap: &'a mut BinaryHeap<Node>,
    pub(super) dive: &'a mut Vec<Node>,
    pub(super) capture: &'a mut crate::tree_cert::TreeCapture,
    pub(super) open_bytes: &'a mut usize,
    pub(super) node_basis_width: usize,
    pub(super) memory_budget: Option<usize>,
}

pub(super) struct PrefixRequest<'a> {
    pub(super) fallback: &'a [Col],
    pub(super) target: Option<TargetFsbPrefixRequest<'a>>,
    pub(super) preparation: PrefixPreparation,
}

#[derive(Clone, Copy)]
pub(super) enum PrefixPreparation {
    Canonical,
    ProofFirst(NonZeroUsize),
}

impl PrefixPreparation {
    fn requested_workers(self) -> Option<usize> {
        match self {
            Self::Canonical => None,
            Self::ProofFirst(workers) => Some(workers.get()),
        }
    }
}

pub(super) struct RootFrontierRequest<'frame, 'storage, 'prefix> {
    pub(super) frame: RootFrame<'frame>,
    pub(super) storage: FrontierStorage<'storage>,
    pub(super) prefix: PrefixRequest<'prefix>,
    pub(super) deadline: Option<Instant>,
    pub(super) trace: root_search::RootTrace,
}

enum SelectedPrefix<'a> {
    Fallback(&'a [Col]),
    Target([Col; TARGET_FSB_PREFIX_WIDTH]),
}

pub(super) struct PreparedRootFrontier<'a> {
    prefix: SelectedPrefix<'a>,
    global_floor: Option<Arc<BigRational>>,
}

impl PreparedRootFrontier<'_> {
    pub(super) fn prefix(&self) -> &[Col] {
        match &self.prefix {
            SelectedPrefix::Fallback(prefix) => prefix,
            SelectedPrefix::Target(prefix) => prefix,
        }
    }

    pub(super) fn global_floor(&self) -> Option<&BigRational> {
        self.global_floor.as_deref()
    }
}

pub(super) fn prepare_root_frontier<'prefix>(
    mut request: RootFrontierRequest<'_, '_, 'prefix>,
) -> PreparedRootFrontier<'prefix> {
    let selected = target_fsb_prefix_or_fallback(
        request.frame.caller_model,
        request.frame.lp,
        request.frame.candidate,
        request.frame.lower,
        request.frame.upper,
        request.prefix.fallback,
        request.prefix.target,
        request.deadline,
        request.trace.enabled(),
    );
    let prefix = match selected {
        Some(prefix) => SelectedPrefix::Target(prefix),
        None => SelectedPrefix::Fallback(request.prefix.fallback),
    };
    let global_floor = if prefix_slice(&prefix).is_empty() {
        seed_unpartitioned_root(&mut request)
    } else {
        seed_prefix_frontier(&mut request, prefix_slice(&prefix))
    };
    PreparedRootFrontier {
        prefix,
        global_floor,
    }
}

fn prefix_slice<'borrow>(prefix: &'borrow SelectedPrefix<'_>) -> &'borrow [Col] {
    match prefix {
        SelectedPrefix::Fallback(prefix) => prefix,
        SelectedPrefix::Target(prefix) => prefix,
    }
}

fn seed_unpartitioned_root(
    request: &mut RootFrontierRequest<'_, '_, '_>,
) -> Option<Arc<BigRational>> {
    let floor = root_floor(request).map(Arc::new);
    let global = floor.clone();
    let prepared = prepare_root_relaxation(
        request.frame.lp,
        request.frame.candidate,
        request.frame.lower,
        request.frame.upper,
    );
    request
        .storage
        .heap
        .push(root_node(floor, prepared, request.storage.capture.root()));
    global
}

fn root_floor(request: &RootFrontierRequest<'_, '_, '_>) -> Option<BigRational> {
    if crate::tune::caller_flag(crate::tune::Knob::NoRootFloor) == Some(true) {
        return None;
    }
    let mut scratch = vec![(0.0, 0.0); request.frame.lp.n];
    let raw = safe_bound_reason(
        request.frame.lp,
        &request.frame.candidate.duals,
        request.frame.lower,
        request.frame.upper,
        &mut scratch,
    );
    let floor = raw.ok().and_then(exact).map(|bound| {
        request
            .frame
            .objective_granularity
            .map_or_else(|| bound.clone(), |step| round_up_to(&bound, step))
    });
    if request.trace.enabled() {
        trace_root_floor(request.frame.candidate, &raw, floor.as_ref());
    }
    floor
}

fn trace_root_floor(
    candidate: &Candidate,
    raw: &Result<f64, SafeBoundDecline>,
    floor: Option<&BigRational>,
) {
    let shown = match (floor, raw) {
        (Some(value), _) => format!("{}", to_f64(value)),
        (None, Err(error)) => format!("{error}"),
        (None, Ok(_)) => "declined(inexact conversion)".to_owned(),
    };
    let tried = IMPLIED_CORNER_TRIED.load(std::sync::atomic::Ordering::Relaxed);
    let census = if tried == 0 {
        String::new()
    } else {
        format!(
            "; implied-corner tried={tried} closed={}",
            IMPLIED_CORNER_FOUND.load(std::sync::atomic::Ordering::Relaxed)
        )
    };
    eprintln!(
        "--trace root node floor = {shown} (root status {:?}){census}",
        candidate.status
    );
}

fn seed_prefix_frontier(
    request: &mut RootFrontierRequest<'_, '_, '_>,
    prefix: &[Col],
) -> Option<Arc<BigRational>> {
    let (frontier, raw_floor) = shared_binary_prefix_frontier(
        prefix,
        request.frame.lp,
        request.frame.candidate,
        request.frame.lower,
        request.frame.upper,
        request.frame.objective_granularity,
        request.storage.capture,
    );
    let global_floor = raw_floor
        .and_then(exact)
        .map(|bound| {
            request
                .frame
                .objective_granularity
                .map_or_else(|| bound.clone(), |step| round_up_to(&bound, step))
        })
        .map(Arc::new);
    let frontier = prepare_prefix_relaxations(request, frontier);
    let seeded = frontier.len();
    for node in frontier.into_iter().rev() {
        *request.storage.open_bytes += node_bytes(&node, request.storage.node_basis_width);
        request.storage.dive.push(node);
    }
    if request.trace.enabled() {
        trace_prefix_frontier(prefix, seeded, raw_floor);
    }
    global_floor
}

fn prepare_prefix_relaxations(
    request: &mut RootFrontierRequest<'_, '_, '_>,
    frontier: Vec<Node>,
) -> Vec<Node> {
    let Some(requested_workers) = request.prefix.preparation.requested_workers() else {
        return frontier;
    };
    prepare_shared_binary_prefix_relaxations(
        request.frame.lp,
        request.frame.candidate,
        request.frame.lower,
        request.frame.upper,
        frontier,
        requested_workers,
        request.deadline,
        request.storage.memory_budget,
        request.storage.capture,
        request.trace.enabled(),
    )
}

fn trace_prefix_frontier(prefix: &[Col], seeded: usize, raw_floor: Option<f64>) {
    let columns = prefix
        .iter()
        .map(|column| column.index())
        .collect::<Vec<_>>();
    eprintln!(
        "--trace shared-prefix frontier: cols={columns:?} \
         complete_leaves={} live_leaves={seeded} root_preparations=1 \
         shared_root_bound={}",
        1usize << prefix.len(),
        raw_floor.map_or_else(|| "none".to_owned(), |value| format!("{value:.6}")),
    );
}
