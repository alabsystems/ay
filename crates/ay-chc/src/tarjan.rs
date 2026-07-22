// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Generic Tarjan's SCC algorithm (dense variant).
//!
//! Nodes are `usize` indices `0..n`. Uses pre-allocated slices.
//! Best for predicate-level graphs where nodes are mapped to contiguous indices.

/// Result of Tarjan's SCC computation: a list of components.
///
/// Each component is a `Vec<N>` of nodes in that SCC. Components are returned
/// in reverse topological order (deepest SCCs first).
pub(crate) type SccResult<N> = Vec<Vec<N>>;

/// Compute SCCs over a dense graph with `usize` node indices `0..n`.
///
/// `neighbors(v)` must return an iterator over the successors of node `v`.
/// All returned node indices must be in `0..n`.
///
/// Returns SCCs in reverse topological order.
pub(crate) fn tarjan_scc_dense(
    n: usize,
    mut neighbors: impl FnMut(usize) -> Vec<usize>,
) -> SccResult<usize> {
    if n == 0 {
        return Vec::new();
    }

    let mut state = DenseTarjanState::new(n);

    for v in 0..n {
        if state.indices[v] == usize::MAX {
            strongconnect_dense(v, &mut state, &mut neighbors);
        }
    }

    state.sccs
}

struct DenseTarjanState {
    index: usize,
    stack: Vec<usize>,
    on_stack: Vec<bool>,
    indices: Vec<usize>,
    lowlink: Vec<usize>,
    sccs: Vec<Vec<usize>>,
}

impl DenseTarjanState {
    fn new(n: usize) -> Self {
        Self {
            index: 0,
            stack: Vec::new(),
            on_stack: vec![false; n],
            indices: vec![usize::MAX; n],
            lowlink: vec![0; n],
            sccs: Vec::new(),
        }
    }
}

fn strongconnect_dense(
    v: usize,
    state: &mut DenseTarjanState,
    neighbors: &mut impl FnMut(usize) -> Vec<usize>,
) {
    state.indices[v] = state.index;
    state.lowlink[v] = state.index;
    state.index += 1;
    state.stack.push(v);
    state.on_stack[v] = true;

    for w in neighbors(v) {
        if state.indices[w] == usize::MAX {
            strongconnect_dense(w, state, neighbors);
            state.lowlink[v] = state.lowlink[v].min(state.lowlink[w]);
        } else if state.on_stack[w] {
            state.lowlink[v] = state.lowlink[v].min(state.indices[w]);
        }
    }

    if state.lowlink[v] == state.indices[v] {
        let mut scc = Vec::new();
        loop {
            let w = state
                .stack
                .pop()
                .expect("Tarjan stack must contain SCC root during unwind");
            state.on_stack[w] = false;
            scc.push(w);
            if w == v {
                break;
            }
        }
        state.sccs.push(scc);
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "tarjan_tests.rs"]
mod tests;
