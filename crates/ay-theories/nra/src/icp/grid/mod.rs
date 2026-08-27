// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-only exact-grid fallback for ICP.
//!
//! The first pass preserves the established candidate order and spends only
//! the ordinary grid budget. Only after that pass fails does a separately
//! budgeted traversal solve the final free coordinate as a univariate system.
//! Every returned rational model passes exact substitution, and every returned
//! algebraic model passes exact sign checks. Neither pass can return UNSAT.

mod exact;
mod points;
mod probe;
mod search;

#[cfg(test)]
pub(super) use exact::ExactOutcome;
pub(super) use exact::ExactState;
pub(super) use points::dyadic_grid;
#[cfg(test)]
pub(super) use points::interval_scale_points;
use probe::GridProbe;
use search::GridSearch;

use super::*;

/// Immutable inputs for one candidate-grid pass.
///
/// The ordinary and exact passes traverse the same problem but carry distinct
/// [`ExactState`] and diagnostic level ranges. Keeping those inputs together
/// prevents a call site from accidentally pairing one pass's state with the
/// other's level numbering.
struct GridTraversal<'a> {
    constraints: &'a [MultiConstraint],
    vars: &'a [TermId],
    order: &'a [TermId],
    root: &'a VarBox,
    exact: &'a ExactState,
    probe: Option<&'a GridProbe>,
    probe_level_base: usize,
}

fn ordered_variables(vars: &[TermId], root: &VarBox) -> Vec<TermId> {
    let mut order = vars.to_vec();
    order.sort_by(|a, b| {
        let width_a = root.get(a).and_then(interval_width);
        let width_b = root.get(b).and_then(interval_width);
        match (width_a, width_b) {
            (Some(a), Some(b)) => a.cmp(&b),
            (Some(_), None) => std::cmp::Ordering::Less,
            (None, Some(_)) => std::cmp::Ordering::Greater,
            (None, None) => std::cmp::Ordering::Equal,
        }
    });
    order
}

impl NraSolver<'_> {
    fn run_grid_levels(
        &self,
        traversal: &GridTraversal<'_>,
        budget: &mut usize,
    ) -> Option<UniResult> {
        for level in 0..=GRID_MAX_LEVEL {
            if traversal.exact.solves_last_coordinate()
                && (*budget < GRID_EXACT_NODE_COST || !traversal.exact.available())
            {
                break;
            }
            if let Some(probe) = traversal.probe {
                probe.level_reset(traversal.probe_level_base + level);
            }
            let search = GridSearch {
                constraints: traversal.constraints,
                vars: traversal.vars,
                order: traversal.order,
                grid: dyadic_grid(level),
                exact: traversal.exact,
                probe: traversal.probe,
            };
            let result = self.grid_dfs(&search, 0, traversal.root.clone(), budget);
            if result.is_some() || *budget == 0 {
                return result;
            }
        }
        None
    }

    /// Try independently chosen dyadic values after branch-and-prune returns
    /// `Unknown`. This method can produce SAT only; failure is `None`.
    pub(super) fn dyadic_grid_search(
        &self,
        constraints: &[MultiConstraint],
        vars: &[TermId],
        root: &VarBox,
    ) -> Option<UniResult> {
        if vars.len() > GRID_MAX_VARS {
            diag!("NRA-GRID declined vars={} > {}", vars.len(), GRID_MAX_VARS);
            return None;
        }
        diag!(
            "NRA-GRID enter vars={} budget={} box: {}",
            vars.len(),
            self.grid_budget.get(),
            diagnostics::render_box(self, vars, root)
        );
        let order = ordered_variables(vars, root);
        let probe = GridProbe::install(self, &order);

        let mut budget = GRID_MAX_NODES.min(self.grid_budget.get());
        let start = budget;
        let enumerate = ExactState::disabled();
        let mut result = self.run_grid_levels(
            &GridTraversal {
                constraints,
                vars,
                order: &order,
                root,
                exact: &enumerate,
                probe: probe.as_ref(),
                probe_level_base: 0,
            },
            &mut budget,
        );
        self.grid_budget
            .set(self.grid_budget.get() - (start - budget));

        if result.is_none() {
            let mut exact_budget = GRID_EXACT_MAX_NODES.min(self.grid_exact_budget.get());
            let exact_start = exact_budget;
            let exact = ExactState::with(GRID_EXACT_SOLVES);
            result = self.run_grid_levels(
                &GridTraversal {
                    constraints,
                    vars,
                    order: &order,
                    root,
                    exact: &exact,
                    probe: probe.as_ref(),
                    probe_level_base: GRID_MAX_LEVEL + 1,
                },
                &mut exact_budget,
            );
            self.grid_exact_budget
                .set(self.grid_exact_budget.get() - (exact_start - exact_budget));
            diag!(
                "NRA-GRID pass2 found={} exact_nodes={} exact_left={}",
                result.is_some(),
                exact_start - exact_budget,
                self.grid_exact_budget.get()
            );
        }
        diag!(
            "NRA-GRID exit found={} nodes_used={} budget_left={}",
            result.is_some(),
            start - budget,
            budget
        );
        if let Some(probe) = &probe {
            probe.report(result.is_some(), start - budget, budget);
        }
        result
    }
}
