// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Admission for finite observations of scalar-valued array lambdas.
//!
//! The virtual substitution walk prices the expanded expression *before*
//! `instantiate` allocates it. Private variables resolve only in the template;
//! captured values are visited in their original outer scope.

use super::*;
use crate::expr::ChcArrayLambda;

struct ObservationBudget<'a> {
    remaining: usize,
    remaining_names: usize,
    max_depth: usize,
    should_stop: &'a mut dyn FnMut() -> bool,
}

fn simple_sort(sort: &ChcSort) -> bool {
    matches!(
        sort,
        ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_)
    )
}

fn flat_sort(sort: &ChcSort) -> bool {
    simple_sort(sort)
        || matches!(sort, ChcSort::Array(key, value)
        if matches!(key.as_ref(), ChcSort::Int | ChcSort::BitVec(_)) && simple_sort(value))
}

impl ObservationBudget<'_> {
    fn charge(&mut self, depth: usize) -> Option<()> {
        if depth > self.max_depth || (self.should_stop)() {
            return None;
        }
        self.remaining = self.remaining.checked_sub(1)?;
        Some(())
    }

    fn matrix(&mut self, lambda: &ChcArrayLambda, depth: usize) -> Option<()> {
        self.remaining = self
            .remaining
            .checked_sub(lambda.formals().len().checked_mul(2)?)?;
        self.remaining_names = self
            .remaining_names
            .checked_sub(lambda.binder().name.len())?;
        for formal in lambda.formals() {
            self.charge(depth)?;
            self.remaining_names = self.remaining_names.checked_sub(formal.name.len())?;
            if !flat_sort(&formal.sort) {
                return None;
            }
        }
        if lambda.formals().len() != lambda.captures().len()
            || !matches!(lambda.binder().sort, ChcSort::Int | ChcSort::BitVec(_))
            || !simple_sort(lambda.value_sort())
        {
            return None;
        }
        let mut pending = vec![(lambda.body().as_ref(), true, depth)];
        if pending.len().checked_add(lambda.captures().len())? > self.remaining {
            return None;
        }
        pending.extend(
            lambda
                .captures()
                .iter()
                .map(|capture| (capture.as_ref(), false, depth)),
        );
        while let Some((node, scoped, depth)) = pending.pop() {
            self.charge(depth)?;
            match node {
                ChcExpr::Var(variable) => {
                    if !flat_sort(&variable.sort) {
                        return None;
                    }
                    self.remaining_names = self.remaining_names.checked_sub(variable.name.len())?;
                }
                ChcExpr::FuncApp(name, sort, _) => {
                    if !flat_sort(sort) {
                        return None;
                    }
                    self.remaining_names = self.remaining_names.checked_sub(name.len())?;
                }
                ChcExpr::PredicateApp(..)
                | ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_) => return None,
                _ => {}
            }
            if let ChcExpr::Var(variable) = node {
                if scoped {
                    if variable == lambda.binder() {
                        // Every tracked index is one typed literal node.
                        self.charge(depth)?;
                    } else {
                        let mut slot = None;
                        for (index, formal) in lambda.formals().iter().enumerate() {
                            self.charge(depth)?;
                            if formal == variable {
                                slot = Some(index);
                                break;
                            }
                        }
                        let slot = slot?;
                        pending.push((lambda.captures()[slot].as_ref(), false, depth));
                    }
                }
                continue;
            }
            if matches!(node, ChcExpr::ArrayLambda(_)) {
                // Higher-order or nested functional values need separate
                // admission; do not treat their closed body as a leaf.
                return None;
            }
            let children = crate::expr::dag::children(node);
            if pending
                .len()
                .checked_add(children.len())
                .is_none_or(|count| count > self.remaining)
            {
                return None;
            }
            pending.extend(
                children
                    .iter()
                    .map(|child| (child.as_ref(), scoped, depth + 1)),
            );
        }
        // All capture ASTs (including unused slots), their expansion and
        // their sorts were bounded before this exact sort computation.
        lambda.captures_are_well_typed().then_some(())
    }

    fn root(
        &mut self,
        root: &ChcExpr,
        observed_array: bool,
        positive_conjunct: bool,
        indices: &FxHashMap<ChcSort, FxHashSet<ConstIndex>>,
    ) -> Option<()> {
        let mut pending = vec![(root, observed_array, positive_conjunct, 1usize)];
        while let Some((node, observed, positive_conjunct, depth)) = pending.pop() {
            self.charge(depth)?;
            if let ChcExpr::ArrayLambda(lambda) = node {
                if !observed {
                    return None;
                }
                let keys = indices.get(&lambda.binder().sort)?;
                if keys.is_empty() {
                    return None;
                }
                for key in keys {
                    if key.to_expr().sort() != lambda.binder().sort {
                        return None;
                    }
                    self.matrix(lambda, depth + 1)?;
                }
                continue;
            }
            if let ChcExpr::Op(ChcOp::Select, arguments) = node {
                if arguments.len() != 2
                    || ChcProblem::array_key_sort(&arguments[0].sort())
                        != Some(&arguments[1].sort())
                {
                    return None;
                }
            }
            let children = crate::expr::dag::children(node);
            if pending
                .len()
                .checked_add(children.len())
                .is_none_or(|count| count > self.remaining)
            {
                return None;
            }
            for (position, child) in children.iter().enumerate() {
                let allowed = match node {
                    ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 && position == 0 => {
                        ChcProblem::is_scalarizable_array_sort(&args[0].sort())
                            && ChcProblem::try_eval_const_index(&args[1]).is_some()
                            && ChcProblem::array_key_sort(&args[0].sort()) == Some(&args[1].sort())
                    }
                    ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => observed && position == 0,
                    ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => observed && position > 0,
                    ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 && positive_conjunct => {
                        matches!(
                            child.as_ref(),
                            ChcExpr::ArrayLambda(_) | ChcExpr::Op(ChcOp::Store, _)
                        ) && matches!(args[1 - position].as_ref(), ChcExpr::Var(variable)
                                if ChcProblem::is_scalarizable_array_sort(&variable.sort)
                                    && variable.sort == child.sort())
                    }
                    _ => false,
                };
                let conjunct = positive_conjunct && matches!(node, ChcExpr::Op(ChcOp::And, _));
                pending.push((child.as_ref(), allowed, conjunct, depth + 1));
            }
        }
        Some(())
    }
}

impl ChcProblem {
    /// Conservative expanded work for one literal-index beta observation.
    /// Nodes, repeated captures, formal lookups and copied symbol bytes all
    /// consume the existing work envelope before allocating the instance.
    pub(crate) fn lambda_observation_work(
        lambda: &ChcArrayLambda,
        max_nodes: usize,
        max_name_bytes: usize,
        max_depth: usize,
        mut should_stop: impl FnMut() -> bool,
    ) -> Option<(usize, usize)> {
        let mut budget = ObservationBudget {
            remaining: max_nodes,
            remaining_names: max_name_bytes,
            max_depth,
            should_stop: &mut should_stop,
        };
        budget.matrix(lambda, 1)?;
        Some((
            max_nodes - budget.remaining,
            max_name_bytes - budget.remaining_names,
        ))
    }

    pub(super) fn admit_lambda_observations(
        &self,
        indices: &FxHashMap<ChcSort, FxHashSet<ConstIndex>>,
        max_nodes: usize,
        mut should_stop: impl FnMut() -> bool,
    ) -> Option<usize> {
        let mut budget = ObservationBudget {
            remaining: max_nodes,
            remaining_names: 8 * crate::expr::MAX_PREPROCESSING_NODES,
            max_depth: 256,
            should_stop: &mut should_stop,
        };
        for clause in &self.clauses {
            if let Some(constraint) = &clause.body.constraint {
                budget.root(constraint, false, true, indices)?;
            }
            for (predicate, args) in &clause.body.predicates {
                let sorts = &self.predicates.get(predicate.index())?.arg_sorts;
                if sorts.len() != args.len() {
                    return None;
                }
                for (arg, sort) in args.iter().zip(sorts) {
                    budget.root(arg, Self::is_scalarizable_array_sort(sort), false, indices)?;
                }
            }
            if let ClauseHead::Predicate(predicate, args) = &clause.head {
                let sorts = &self.predicates.get(predicate.index())?.arg_sorts;
                if sorts.len() != args.len() {
                    return None;
                }
                for (arg, sort) in args.iter().zip(sorts) {
                    budget.root(arg, Self::is_scalarizable_array_sort(sort), false, indices)?;
                }
            }
        }
        Some(max_nodes - budget.remaining)
    }
}
