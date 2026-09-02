// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Deterministic bounded closure for scalar-support seeds.

use std::collections::VecDeque;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use super::super::candidate_flow::{CandidateControl, MAX_PROPAGATED_CANDIDATES};
use super::{SupportKey, MAX_SUPPORT_GRAPH_NODES};

const MAX_SUPPORT_TRAVERSALS: usize = 131_072;

pub(super) fn ordered_bounded_closure(
    direct: FxHashSet<SupportKey>,
    store_seeds: FxHashSet<SupportKey>,
    graph: &FxHashMap<SupportKey, Vec<SupportKey>>,
    control: Option<CandidateControl<'_>>,
) -> Option<Vec<SupportKey>> {
    poll(control)?;
    let mut direct: Vec<_> = direct.into_iter().collect();
    direct.sort_unstable();
    poll(control)?;
    let direct_set: FxHashSet<_> = direct.iter().copied().collect();
    let mut stores: Vec<_> = store_seeds
        .into_iter()
        .filter(|support| !direct_set.contains(support))
        .collect();
    stores.sort_unstable();
    poll(control)?;

    let mut ordered = Vec::new();
    let mut seen = FxHashSet::default();
    let mut queue = VecDeque::new();
    for support in direct.into_iter().chain(stores) {
        poll(control)?;
        if seen.insert(support) {
            if seen.len() > MAX_SUPPORT_GRAPH_NODES {
                return None;
            }
            ordered.push(support);
            if ordered.len() == MAX_PROPAGATED_CANDIDATES {
                poll(control)?;
                return Some(ordered);
            }
            queue.push_back(support);
        }
    }

    let mut traversals = 0usize;
    while let Some(support) = queue.pop_front() {
        poll(control)?;
        let Some(neighbors) = graph.get(&support) else {
            continue;
        };
        for neighbor in neighbors {
            poll(control)?;
            traversals = traversals.checked_add(1)?;
            if traversals > MAX_SUPPORT_TRAVERSALS {
                return None;
            }
            if seen.insert(*neighbor) {
                if seen.len() > MAX_SUPPORT_GRAPH_NODES {
                    return None;
                }
                ordered.push(*neighbor);
                if ordered.len() == MAX_PROPAGATED_CANDIDATES {
                    poll(control)?;
                    return Some(ordered);
                }
                queue.push_back(*neighbor);
            }
        }
    }
    poll(control)?;
    Some(ordered)
}

fn poll(control: Option<CandidateControl<'_>>) -> Option<()> {
    (!control.is_some_and(CandidateControl::stopped)).then_some(())
}
