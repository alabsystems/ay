// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded discovery of scalar variables used as relevant Store indices.

use ay_core::kani_compat::DetHashSet as FxHashSet;

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};

use super::super::candidate_flow::CandidateControl;
use super::{ScanBudget, MAX_NONZERO_BV_WIDTH};

pub(super) fn collect_relevant_store_index_vars(
    root: &ChcExpr,
    tracked_bases: &FxHashSet<ChcVar>,
    tracked_results: &FxHashSet<ChcVar>,
    force_root: bool,
    out: &mut FxHashSet<ChcVar>,
    budget: &mut ScanBudget,
    control: Option<CandidateControl<'_>>,
) -> Option<()> {
    let mut stack = vec![(root, 0usize, force_root)];
    while let Some((expression, depth, forced)) = stack.pop() {
        if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
            return None;
        }
        budget.charge(control)?;
        match expression {
            ChcExpr::Op(ChcOp::Store, args) => {
                let [base, index, value] = args.as_slice() else {
                    continue;
                };
                if forced || store_base_reaches(base, tracked_bases, budget, control)? {
                    collect_index_variables(index, out, budget, control)?;
                }
                stack.push((value, depth + 1, forced));
                stack.push((index, depth + 1, forced));
                stack.push((base, depth + 1, forced));
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let left = args[0].as_ref();
                let right = args[1].as_ref();
                if !forced {
                    if exact_tracked_variable(left, tracked_results) {
                        stack.push((right, depth + 1, true));
                    }
                    if exact_tracked_variable(right, tracked_results) {
                        stack.push((left, depth + 1, true));
                    }
                }
                stack.push((right, depth + 1, forced));
                stack.push((left, depth + 1, forced));
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                for argument in args.iter().rev() {
                    stack.push((argument, depth + 1, forced));
                }
            }
            ChcExpr::ConstArray(_, value) => stack.push((value, depth + 1, forced)),
            _ => {}
        }
    }
    Some(())
}

fn exact_tracked_variable(expression: &ChcExpr, tracked: &FxHashSet<ChcVar>) -> bool {
    matches!(expression, ChcExpr::Var(variable) if tracked.contains(variable))
}

fn store_base_reaches(
    root: &ChcExpr,
    tracked: &FxHashSet<ChcVar>,
    budget: &mut ScanBudget,
    control: Option<CandidateControl<'_>>,
) -> Option<bool> {
    let mut stack = vec![(root, 0usize)];
    while let Some((expression, depth)) = stack.pop() {
        if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
            return None;
        }
        budget.charge(control)?;
        match expression {
            ChcExpr::Var(variable) => {
                if tracked.contains(variable) {
                    return Some(true);
                }
            }
            ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
                stack.push((&args[0], depth + 1));
            }
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                stack.push((&args[2], depth + 1));
                stack.push((&args[1], depth + 1));
            }
            _ => {}
        }
    }
    Some(false)
}

fn collect_index_variables(
    root: &ChcExpr,
    out: &mut FxHashSet<ChcVar>,
    budget: &mut ScanBudget,
    control: Option<CandidateControl<'_>>,
) -> Option<()> {
    let mut stack = vec![(root, 0usize)];
    while let Some((expression, depth)) = stack.pop() {
        if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
            return None;
        }
        budget.charge(control)?;
        match expression {
            ChcExpr::Var(variable)
                if matches!(&variable.sort, ChcSort::BitVec(1..=MAX_NONZERO_BV_WIDTH)) =>
            {
                out.insert(variable.clone());
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                for argument in args.iter().rev() {
                    stack.push((argument, depth + 1));
                }
            }
            ChcExpr::ConstArray(_, value) => stack.push((value, depth + 1)),
            _ => {}
        }
    }
    Some(())
}
