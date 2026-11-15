// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause case splitting on `ite` and `or`: the one-step splits and their
//! helpers. The drivers that apply them to a whole problem, recording where
//! each output clause came from, are in [`recorded`].

use super::simplified_conjunction::SimplifiedConjunction;
use super::*;

mod recorded;

impl ChcProblem {
    /// The `verbose` summary of one splitting pass (`kind`: `ite` or `or`).
    fn report_case_splits(
        kind: &str,
        total_splits: usize,
        clauses_with_splits: usize,
        old_len: usize,
        new_len: usize,
    ) {
        safe_eprintln!(
            "CHC: {kind}-splitting: {total_splits} splits across {clauses_with_splits} clauses \
             ({old_len} -> {new_len})"
        );
    }

    fn clause_is_trivially_false(clause: &HornClause) -> bool {
        matches!(clause.body.constraint, Some(ChcExpr::Bool(false)))
    }

    fn split_clause_once_on_or(
        clause: &HornClause,
        max_or_branches: usize,
    ) -> Option<Vec<HornClause>> {
        let constraint = clause.body.constraint.as_ref()?;

        // Cases:
        // 1) constraint is (or a b ...)
        // 2) constraint is a conjunction with one conjunct containing an (or ...)
        let (guard_conjuncts, branches) = match constraint {
            ChcExpr::Op(ChcOp::Or, args) => {
                let mut branches = Vec::new();
                Self::collect_or_branches(args, &mut branches);
                (Vec::new(), branches)
            }
            _ => {
                let mut conjuncts = Vec::new();
                constraint.collect_conjuncts_into(&mut conjuncts);

                let mut or_index = None;
                let mut branches = Vec::new();
                for (i, c) in conjuncts.iter().enumerate() {
                    if let ChcExpr::Op(ChcOp::Or, args) = c {
                        or_index = Some(i);
                        Self::collect_or_branches(args, &mut branches);
                        break;
                    }
                }
                let idx = or_index?;
                let guards = conjuncts
                    .into_iter()
                    .enumerate()
                    .filter(|(i, _)| *i != idx)
                    .map(|(_, c)| c)
                    .collect::<Vec<_>>();
                (guards, branches)
            }
        };

        if branches.len() <= 1 || branches.len() > max_or_branches {
            return None;
        }

        // Simplify the shared guard once per split; each branch then only
        // simplifies its own disjunct. Folding the guards in one by one
        // re-simplified the whole growing constraint per guard and per branch
        // (O(guards x size)): 91-96 % of PdrSolver::new on wide sally systems
        // (PERF_vs_winners_2026-09-25, row 6).
        let guard = SimplifiedConjunction::from_conjuncts(guard_conjuncts);
        let mut split_clauses = Vec::with_capacity(branches.len());
        for branch in branches {
            let new_constraint = guard.conjoin(branch);

            split_clauses.push(
                HornClause::new(
                    ClauseBody::new(clause.body.predicates.clone(), new_constraint),
                    clause.head.clone(),
                )
                .with_inherited_provenance(clause),
            );
        }

        Some(split_clauses)
    }

    fn collect_or_branches(args: &[Arc<ChcExpr>], out: &mut Vec<ChcExpr>) {
        crate::expr::maybe_grow_expr_stack(|| {
            for a in args {
                match a.as_ref() {
                    ChcExpr::Op(ChcOp::Or, nested) => Self::collect_or_branches(nested, out),
                    _ => out.push(a.as_ref().clone()),
                }
            }
        });
    }

    fn split_clause_once_on_ite(clause: &HornClause) -> Option<(HornClause, HornClause)> {
        // 1) Split on ite inside background constraint.
        if let Some(constraint) = &clause.body.constraint {
            if let Some((cond, then_c, else_c)) = Self::split_expr_once_on_ite(constraint) {
                let a = HornClause::new(
                    ClauseBody::new(
                        clause.body.predicates.clone(),
                        Self::conjoin_constraint(Some(then_c), cond.clone()),
                    ),
                    clause.head.clone(),
                )
                .with_inherited_provenance(clause);
                let b = HornClause::new(
                    ClauseBody::new(
                        clause.body.predicates.clone(),
                        Self::conjoin_constraint(Some(else_c), ChcExpr::not(cond)),
                    ),
                    clause.head.clone(),
                )
                .with_inherited_provenance(clause);
                return Some((a, b));
            }
        }

        // 2) Split on ite inside any body predicate argument.
        for (pred_i, (_pred, args)) in clause.body.predicates.iter().enumerate() {
            for (arg_i, arg) in args.iter().enumerate() {
                if let Some((cond, then_arg, else_arg)) = Self::split_expr_once_on_ite(arg) {
                    let mut preds_then = clause.body.predicates.clone();
                    preds_then[pred_i].1[arg_i] = then_arg;

                    let mut preds_else = clause.body.predicates.clone();
                    preds_else[pred_i].1[arg_i] = else_arg;

                    let then_constraint =
                        Self::conjoin_constraint(clause.body.constraint.clone(), cond.clone());
                    let else_constraint = Self::conjoin_constraint(
                        clause.body.constraint.clone(),
                        ChcExpr::not(cond),
                    );

                    let a = HornClause::new(
                        ClauseBody::new(preds_then, then_constraint),
                        clause.head.clone(),
                    )
                    .with_inherited_provenance(clause);
                    let b = HornClause::new(
                        ClauseBody::new(preds_else, else_constraint),
                        clause.head.clone(),
                    )
                    .with_inherited_provenance(clause);
                    return Some((a, b));
                }
            }
        }

        // 3) Split on ite inside head predicate arguments.
        let ClauseHead::Predicate(head_pred, head_args) = &clause.head else {
            return None;
        };
        for (arg_i, arg) in head_args.iter().enumerate() {
            if let Some((cond, then_arg, else_arg)) = Self::split_expr_once_on_ite(arg) {
                let mut head_then_args = head_args.clone();
                head_then_args[arg_i] = then_arg;
                let mut head_else_args = head_args.clone();
                head_else_args[arg_i] = else_arg;

                let then_constraint =
                    Self::conjoin_constraint(clause.body.constraint.clone(), cond.clone());
                let else_constraint =
                    Self::conjoin_constraint(clause.body.constraint.clone(), ChcExpr::not(cond));

                let a = HornClause::new(
                    ClauseBody::new(clause.body.predicates.clone(), then_constraint),
                    ClauseHead::Predicate(*head_pred, head_then_args),
                )
                .with_inherited_provenance(clause);
                let b = HornClause::new(
                    ClauseBody::new(clause.body.predicates.clone(), else_constraint),
                    ClauseHead::Predicate(*head_pred, head_else_args),
                )
                .with_inherited_provenance(clause);
                return Some((a, b));
            }
        }

        None
    }

    fn normalize_constraint_opt(constraint: Option<ChcExpr>) -> Option<ChcExpr> {
        let c = constraint?;
        let simplified = c.simplify_constants();
        match simplified {
            ChcExpr::Bool(true) => None,
            other => Some(other),
        }
    }

    fn conjoin_constraint(existing: Option<ChcExpr>, extra: ChcExpr) -> Option<ChcExpr> {
        let extra = extra.simplify_constants();
        match extra {
            ChcExpr::Bool(true) => Self::normalize_constraint_opt(existing),
            ChcExpr::Bool(false) => Some(ChcExpr::Bool(false)),
            _ => {
                let combined = match existing {
                    None => extra,
                    Some(c) => ChcExpr::and(c, extra),
                };
                Self::normalize_constraint_opt(Some(combined))
            }
        }
    }

    fn split_expr_once_on_ite(expr: &ChcExpr) -> Option<(ChcExpr, ChcExpr, ChcExpr)> {
        let path = Self::find_ite_path(expr)?;
        let ite = Self::get_subexpr(expr, &path)?;
        let ChcExpr::Op(ChcOp::Ite, args) = ite else {
            return None;
        };
        if args.len() != 3 {
            return None;
        }
        let cond = args[0].as_ref().clone();
        let then_ = args[1].as_ref().clone();
        let else_ = args[2].as_ref().clone();

        let then_expr = Self::replace_subexpr(expr, &path, &then_);
        let else_expr = Self::replace_subexpr(expr, &path, &else_);
        Some((cond, then_expr, else_expr))
    }

    fn find_ite_path(expr: &ChcExpr) -> Option<Vec<usize>> {
        // Shared DAGs (WP-F F0b): the leftmost path to the first `ite` in
        // preorder, found by following the first child whose subtree holds an
        // `ite` (memoised per distinct node) — the same path the tree walk
        // below returns.
        if crate::expr::dag::tree_size_at_least(expr, crate::expr::dag::DAG_WALK_MIN_TREE) {
            let mut has_ite = crate::expr::dag::SubtreeAnyVia::new(
                |e| matches!(e, ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3),
                |e| matches!(e, ChcExpr::Op(..) | ChcExpr::PredicateApp(..)),
            );
            if !has_ite.holds(expr) {
                return None;
            }
            let mut path = Vec::new();
            let mut current = expr;
            loop {
                if matches!(current, ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3) {
                    return Some(path);
                }
                let (ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args)) = current else {
                    return None;
                };
                let (index, child) = args.iter().enumerate().find(|(_, a)| has_ite.holds(a))?;
                path.push(index);
                current = child;
            }
        }
        crate::expr::maybe_grow_expr_stack(|| match expr {
            // Match any ITE regardless of return sort (boolean or arithmetic)
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => Some(Vec::new()),
            ChcExpr::Op(_, args) => {
                for (i, a) in args.iter().enumerate() {
                    if let Some(mut sub) = Self::find_ite_path(a.as_ref()) {
                        sub.insert(0, i);
                        return Some(sub);
                    }
                }
                None
            }
            ChcExpr::PredicateApp(_, _, args) => {
                for (i, a) in args.iter().enumerate() {
                    if let Some(mut sub) = Self::find_ite_path(a.as_ref()) {
                        sub.insert(0, i);
                        return Some(sub);
                    }
                }
                None
            }
            _ => None,
        })
    }

    fn get_subexpr<'a>(expr: &'a ChcExpr, path: &[usize]) -> Option<&'a ChcExpr> {
        let mut current = expr;
        for &idx in path {
            current = match current {
                ChcExpr::Op(_, args) => args.get(idx)?.as_ref(),
                ChcExpr::PredicateApp(_, _, args) => args.get(idx)?.as_ref(),
                _ => return None,
            };
        }
        Some(current)
    }

    fn replace_subexpr(expr: &ChcExpr, path: &[usize], replacement: &ChcExpr) -> ChcExpr {
        if path.is_empty() {
            return replacement.clone();
        }
        let first = path[0];
        let rest = &path[1..];

        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(op, args) => {
                let mut new_args: Vec<Arc<ChcExpr>> = Vec::with_capacity(args.len());
                for (i, a) in args.iter().enumerate() {
                    if i == first {
                        new_args.push(Arc::new(Self::replace_subexpr(
                            a.as_ref(),
                            rest,
                            replacement,
                        )));
                    } else {
                        new_args.push(Arc::new(a.as_ref().clone()));
                    }
                }
                ChcExpr::Op(*op, new_args)
            }
            ChcExpr::PredicateApp(name, id, args) => {
                let mut new_args: Vec<Arc<ChcExpr>> = Vec::with_capacity(args.len());
                for (i, a) in args.iter().enumerate() {
                    if i == first {
                        new_args.push(Arc::new(Self::replace_subexpr(
                            a.as_ref(),
                            rest,
                            replacement,
                        )));
                    } else {
                        new_args.push(Arc::new(a.as_ref().clone()));
                    }
                }
                ChcExpr::PredicateApp(name.clone(), *id, new_args)
            }
            _ => expr.clone(),
        })
    }
}
