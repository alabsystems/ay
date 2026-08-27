// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;
use super::exact::{ExactOutcome, ExactState};
use super::points::coordinate_candidates;
use super::probe::GridProbe;

/// Immutable inputs shared by every node of one grid traversal.
pub(super) struct GridSearch<'a> {
    pub(super) constraints: &'a [MultiConstraint],
    pub(super) vars: &'a [TermId],
    pub(super) order: &'a [TermId],
    pub(super) grid: &'a [BigRational],
    pub(super) exact: &'a ExactState,
    pub(super) probe: Option<&'a GridProbe>,
}

fn complete_model(vars: &[TermId], bx: &VarBox) -> Option<Vec<(TermId, BigRational)>> {
    vars.iter()
        .copied()
        .map(|var| Some((var, bx.get(&var).and_then(interval_point)?.clone())))
        .collect()
}

impl NraSolver<'_> {
    fn solve_exact_prefix(
        &self,
        search: &GridSearch<'_>,
        depth: usize,
        var: TermId,
        interval: &Interval,
        bx: &VarBox,
        budget: &mut usize,
    ) -> Option<UniResult> {
        if !search.exact.available() || *budget < GRID_EXACT_NODE_COST {
            return None;
        }
        *budget -= GRID_EXACT_NODE_COST;
        diag!("NRA-LAST enter depth={depth}");
        let outcome =
            self.solve_last_coordinate(search.constraints, search.vars, var, interval, bx);
        search.exact.charge(&outcome);
        match outcome {
            ExactOutcome::Model(model) => Some(model),
            ExactOutcome::Empty | ExactOutcome::Declined => None,
        }
    }

    /// Pin one coordinate, contract, and recurse. Exact-prefix failures never
    /// prune a larger region; only interval contraction cuts a subtree.
    pub(super) fn grid_dfs(
        &self,
        search: &GridSearch<'_>,
        depth: usize,
        bx: VarBox,
        budget: &mut usize,
    ) -> Option<UniResult> {
        if search.exact.spent() {
            return None;
        }
        if depth == search.order.len() {
            let model = complete_model(search.vars, &bx)?;
            return self.verify_model(&model).then_some(UniResult::Sat(model));
        }

        let var = search.order[depth];
        let interval = bx.get(&var)?.clone();
        if let Some(value) = interval_point(&interval) {
            if let Some(probe) = search.probe {
                probe.pin(depth, value);
            }
            return self.grid_dfs(search, depth + 1, bx, budget);
        }
        if search.exact.solves_last_coordinate() && depth + 1 == search.order.len() {
            return self.solve_exact_prefix(search, depth, var, &interval, &bx, budget);
        }

        let candidates = coordinate_candidates(&interval, search.grid);
        diag!(
            "NRA-CAND depth={depth} iv=[{:?},{:?}] cands={:?}",
            &interval.lo,
            &interval.hi,
            candidates
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
        );
        if let Some(probe) = search.probe {
            probe.note_candidates(depth, &candidates, &interval);
        }
        for candidate in candidates {
            if *budget == 0 {
                if let Some(probe) = search.probe {
                    probe.starved();
                }
                return None;
            }
            *budget -= 1;
            if let Some(probe) = search.probe {
                probe.pick(depth, &candidate);
            }
            let mut next = bx.clone();
            next.insert(var, Interval::point(candidate));
            if matches!(
                contract_box(search.constraints, search.vars, &mut next),
                Contraction::Refuted
            ) {
                if let Some(probe) = search.probe {
                    probe.note_refuted(depth);
                }
                continue;
            }
            if let Some(model) = self.grid_dfs(search, depth + 1, next, budget) {
                return Some(model);
            }
        }
        None
    }
}
