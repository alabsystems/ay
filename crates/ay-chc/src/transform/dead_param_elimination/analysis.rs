// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::DeadParamEliminator;
use crate::{ChcExpr, ChcOp, ChcProblem, ChcVar, ClauseHead, HornClause, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

type PositionKey = (PredicateId, usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ClausePositionKind {
    Body,
    Head,
}

struct ClausePosition<'a> {
    pred_id: PredicateId,
    pos: usize,
    arg: &'a ChcExpr,
    vars: FxHashSet<ChcVar>,
    kind: ClausePositionKind,
}

impl ClausePosition<'_> {
    fn key(&self) -> PositionKey {
        (self.pred_id, self.pos)
    }

    fn is_body(&self) -> bool {
        matches!(self.kind, ClausePositionKind::Body)
    }
}

impl DeadParamEliminator {
    /// Compute the set of live argument positions for each predicate.
    ///
    /// Positions are live if they're referenced by constraints, contain
    /// constants, or connect to other live positions through predicate
    /// applications.
    ///
    /// The liveness system is a monotone reachability closure: per-clause
    /// SEEDS (non-variable args, constraint-referenced positions, body-join
    /// positions) and per-clause var-sharing FLOW EDGES are both invariant in
    /// `live`, so they are computed ONCE per clause and closed with a single
    /// global worklist pass. The previous per-round re-scan rebuilt every
    /// clause's quadratic edge set each round and needed one round per DAG
    /// level to propagate — ~110s on the 377-relation/full-arity-63k
    /// coroutine instances; the identical least fixpoint now lands in
    /// seconds.
    pub(super) fn compute_live_positions(
        &self,
        problem: &ChcProblem,
    ) -> FxHashMap<PredicateId, FxHashSet<usize>> {
        let mut live: FxHashMap<PredicateId, FxHashSet<usize>> = FxHashMap::default();

        for pred in problem.predicates() {
            live.insert(pred.id, FxHashSet::default());
        }

        let mut flow_edges: FxHashMap<PositionKey, FxHashSet<PositionKey>> = FxHashMap::default();
        for clause in problem.clauses() {
            let positions = self.collect_clause_positions(clause);
            self.seed_live_positions_from_constants(&positions, &mut live);
            self.seed_live_positions_from_constraints(
                clause.body.constraint.as_ref(),
                &positions,
                &mut live,
            );
            self.seed_body_join_positions(&positions, &mut live);
            for (key, neighbors) in self.build_clause_flow_edges(&positions) {
                flow_edges.entry(key).or_default().extend(neighbors);
            }
        }

        self.propagate_live_positions(&flow_edges, &mut live);
        live
    }

    fn collect_clause_positions<'a>(&self, clause: &'a HornClause) -> Vec<ClausePosition<'a>> {
        let mut positions = Vec::new();

        for (pred_id, args) in &clause.body.predicates {
            for (pos, arg) in args.iter().enumerate() {
                positions.push(ClausePosition {
                    pred_id: *pred_id,
                    pos,
                    arg,
                    vars: arg.vars().into_iter().collect(),
                    kind: ClausePositionKind::Body,
                });
            }
        }

        if let ClauseHead::Predicate(pred_id, args) = &clause.head {
            for (pos, arg) in args.iter().enumerate() {
                positions.push(ClausePosition {
                    pred_id: *pred_id,
                    pos,
                    arg,
                    vars: arg.vars().into_iter().collect(),
                    kind: ClausePositionKind::Head,
                });
            }
        }

        positions
    }

    fn seed_live_positions_from_constants(
        &self,
        positions: &[ClausePosition<'_>],
        live: &mut FxHashMap<PredicateId, FxHashSet<usize>>,
    ) -> bool {
        let mut changed = false;

        for position in positions {
            if !is_single_variable(position.arg) {
                changed |= Self::mark_position_live(live, position.key());
            }
        }

        changed
    }

    fn seed_live_positions_from_constraints(
        &self,
        constraint: Option<&ChcExpr>,
        positions: &[ClausePosition<'_>],
        live: &mut FxHashMap<PredicateId, FxHashSet<usize>>,
    ) -> bool {
        let seed_vars = Self::collect_constraint_seed_vars(constraint);
        if seed_vars.is_empty() {
            return false;
        }

        let mut changed = false;
        for position in positions {
            if position.vars.iter().any(|var| seed_vars.contains(var)) {
                changed |= Self::mark_position_live(live, position.key());
            }
        }
        changed
    }

    fn seed_body_join_positions(
        &self,
        positions: &[ClausePosition<'_>],
        live: &mut FxHashMap<PredicateId, FxHashSet<usize>>,
    ) -> bool {
        let mut body_var_positions: FxHashMap<ChcVar, FxHashSet<PositionKey>> =
            FxHashMap::default();

        for position in positions.iter().filter(|position| position.is_body()) {
            for var in &position.vars {
                body_var_positions
                    .entry(var.clone())
                    .or_default()
                    .insert(position.key());
            }
        }

        let mut changed = false;
        for body_positions in body_var_positions.values() {
            if body_positions.len() <= 1 {
                continue;
            }

            for &position in body_positions {
                changed |= Self::mark_position_live(live, position);
            }
        }

        changed
    }

    fn build_clause_flow_edges(
        &self,
        positions: &[ClausePosition<'_>],
    ) -> FxHashMap<PositionKey, FxHashSet<PositionKey>> {
        let mut flow_edges: FxHashMap<PositionKey, FxHashSet<PositionKey>> = FxHashMap::default();

        for (idx, lhs) in positions.iter().enumerate() {
            if lhs.vars.is_empty() {
                continue;
            }

            for rhs in positions.iter().skip(idx + 1) {
                if rhs.vars.is_empty() || !lhs.vars.iter().any(|var| rhs.vars.contains(var)) {
                    continue;
                }

                flow_edges.entry(lhs.key()).or_default().insert(rhs.key());
                flow_edges.entry(rhs.key()).or_default().insert(lhs.key());
            }
        }

        flow_edges
    }

    fn propagate_live_positions(
        &self,
        flow_edges: &FxHashMap<PositionKey, FxHashSet<PositionKey>>,
        live: &mut FxHashMap<PredicateId, FxHashSet<usize>>,
    ) -> bool {
        let mut reachable: FxHashSet<PositionKey> = FxHashSet::default();
        let mut worklist = Vec::new();

        for &position in flow_edges.keys() {
            if Self::position_is_live(live, position) && reachable.insert(position) {
                worklist.push(position);
            }
        }

        while let Some(position) = worklist.pop() {
            let Some(neighbors) = flow_edges.get(&position) else {
                continue;
            };
            for &neighbor in neighbors {
                if reachable.insert(neighbor) {
                    worklist.push(neighbor);
                }
            }
        }

        let mut changed = false;
        for position in reachable {
            changed |= Self::mark_position_live(live, position);
        }
        changed
    }

    fn collect_constraint_seed_vars(constraint: Option<&ChcExpr>) -> FxHashSet<ChcVar> {
        let Some(constraint) = constraint else {
            return FxHashSet::default();
        };

        let mut seed_vars: FxHashSet<ChcVar> = constraint.vars().into_iter().collect();
        for conjunct in constraint.collect_conjuncts() {
            if let Some((solved_var, parameter_vars)) =
                extract_solved_equality_parameter_vars(&conjunct)
            {
                seed_vars.insert(solved_var);
                seed_vars.extend(parameter_vars);
            }
        }
        seed_vars
    }

    fn mark_position_live(
        live: &mut FxHashMap<PredicateId, FxHashSet<usize>>,
        position: PositionKey,
    ) -> bool {
        live.get_mut(&position.0)
            .is_some_and(|live_set| live_set.insert(position.1))
    }

    fn position_is_live(
        live: &FxHashMap<PredicateId, FxHashSet<usize>>,
        position: PositionKey,
    ) -> bool {
        live.get(&position.0)
            .is_some_and(|live_set| live_set.contains(&position.1))
    }
}

fn is_single_variable(expr: &ChcExpr) -> bool {
    matches!(expr, ChcExpr::Var(_))
}

fn extract_solved_equality_parameter_vars(expr: &ChcExpr) -> Option<(ChcVar, Vec<ChcVar>)> {
    match expr {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(var), rhs) => {
                    let parameter_vars = rhs.vars();
                    (!parameter_vars.is_empty()).then(|| (var.clone(), parameter_vars))
                }
                (lhs, ChcExpr::Var(var)) => {
                    let parameter_vars = lhs.vars();
                    (!parameter_vars.is_empty()).then(|| (var.clone(), parameter_vars))
                }
                _ => None,
            }
        }
        _ => None,
    }
}
