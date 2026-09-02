// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact, resource-bounded substitution for query-anchored ghost candidates.
//!
//! General-purpose [`ChcExpr::substitute`] is intentionally best-effort: at
//! its traversal cap it leaves the unreached subtree unchanged. That behavior
//! is useful in preprocessing, but a Houdini obligation must never retain a
//! formal candidate binder. This module instead substitutes every formal or
//! rejects the whole rewrite.

use std::sync::Arc;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::time::Instant;
use ay_core::TermStore;

use crate::{CancellationToken, ChcExpr, ChcOp, ChcSort, ChcVar};

/// Avoid an RSS/clock query at every AST node while keeping cancellation
/// responsive. Cancellation itself remains a cheap per-node atomic read.
const CONTROL_POLL_STRIDE: u16 = 256;

/// Result of one exact candidate substitution.
#[derive(Debug)]
pub(super) struct ExactCandidateSubstitution {
    /// Fully rebound formula. No formal in `formals` remains in this tree.
    pub(super) formula: ChcExpr,
    /// Exact expanded node count of `formula`.
    ///
    /// Shared replacement DAGs are counted once per occurrence, matching the
    /// work of a downstream structural traversal even though their storage is
    /// shared. Callers can charge this directly to a Houdini work meter.
    pub(super) expanded_nodes: usize,
}

/// Substitute every scalar candidate formal with its corresponding actual.
///
/// The rewrite is parallel: variables inside an actual are clause variables,
/// not candidates for a second substitution. Every formal name must be unique,
/// arity and sorts must match, and every variable reached in `formula` must be
/// mapped. Candidate templates are restricted to the scalar QF grammar used by
/// query-anchored synthesis; unused formals may have any declared sort because
/// the full raw predicate signature includes original array parameters. An
/// actual inserted for a used scalar formal may contain QF array/UF terms
/// because a scalar predicate argument can itself be a `select` or function
/// application. Predicate applications and parser-only markers are rejected in
/// every inserted expression.
///
/// `node_budget` bounds the exact expanded result, not merely the template.
/// Reusing a large actual at ten formal occurrences therefore spends ten times
/// its expanded size, while the returned AST stores one shared `Arc` root.
pub(super) fn exact_substitute_scalar_candidate(
    formula: &ChcExpr,
    formals: &[ChcVar],
    actuals: &[ChcExpr],
    cancellation: &CancellationToken,
    deadline: Instant,
    node_budget: usize,
) -> Option<ExactCandidateSubstitution> {
    if node_budget == 0 || formals.len() != actuals.len() {
        return None;
    }

    let mut control = SubstitutionControl::new(cancellation, deadline);
    control.boundary()?;
    if formula.sort() != ChcSort::Bool {
        return None;
    }
    control.boundary()?;

    let mut formal_positions = FxHashMap::default();
    let mut formal_names = FxHashSet::default();
    for (position, (formal, actual)) in formals.iter().zip(actuals).enumerate() {
        control.checkpoint()?;
        let actual_sort = actual.sort();
        if actual_sort != formal.sort
            || !formal_names.insert(formal.name.as_str())
            || formal_positions.insert(formal, position).is_some()
        {
            return None;
        }
        control.boundary()?;
    }

    let mut substituter = ExactSubstituter {
        formals,
        actuals,
        formal_positions,
        replacements: (0..formals.len()).map(|_| None).collect(),
        replacement_memo: FxHashMap::default(),
        template_memo: FxHashMap::default(),
        output_budget: NodeBudget::new(node_budget),
        control,
    };
    let root_key = formula as *const ChcExpr;
    let built = substituter.rewrite(formula, 0)?;
    substituter.control.boundary()?;
    if built.expanded_nodes != substituter.output_budget.used {
        return None;
    }

    // The root memo entry is not needed after the rewrite. Removing it lets
    // the common non-variable-root case unwrap without cloning its child Vec.
    substituter.template_memo.remove(&root_key);
    let formula =
        Arc::try_unwrap(built.expression).unwrap_or_else(|shared| shared.as_ref().clone());
    substituter.control.boundary()?;
    Some(ExactCandidateSubstitution {
        formula,
        expanded_nodes: built.expanded_nodes,
    })
}

struct SubstitutionControl<'a> {
    cancellation: &'a CancellationToken,
    deadline: Instant,
    since_full_poll: u16,
}

impl<'a> SubstitutionControl<'a> {
    fn new(cancellation: &'a CancellationToken, deadline: Instant) -> Self {
        Self {
            cancellation,
            deadline,
            since_full_poll: 0,
        }
    }

    fn boundary(&self) -> Option<()> {
        (!self.cancellation.is_cancelled()
            && Instant::now() < self.deadline
            && !TermStore::global_memory_exceeded())
        .then_some(())
    }

    fn checkpoint(&mut self) -> Option<()> {
        if self.cancellation.is_cancelled() {
            return None;
        }
        self.since_full_poll = self.since_full_poll.saturating_add(1);
        if self.since_full_poll >= CONTROL_POLL_STRIDE {
            self.since_full_poll = 0;
            self.boundary()?;
        }
        Some(())
    }
}

#[derive(Clone, Copy)]
struct Counted {
    expanded_nodes: usize,
    height: usize,
}

#[derive(Clone)]
struct Built {
    expression: Arc<ChcExpr>,
    expanded_nodes: usize,
    height: usize,
}

#[derive(Clone)]
struct Replacement {
    expression: Arc<ChcExpr>,
    expanded_nodes: usize,
    height: usize,
}

struct NodeBudget {
    remaining: usize,
    used: usize,
}

impl NodeBudget {
    const fn new(limit: usize) -> Self {
        Self {
            remaining: limit,
            used: 0,
        }
    }

    fn charge(&mut self, nodes: usize) -> Option<()> {
        self.remaining = self.remaining.checked_sub(nodes)?;
        self.used = self.used.checked_add(nodes)?;
        Some(())
    }
}

struct ExactSubstituter<'a> {
    formals: &'a [ChcVar],
    actuals: &'a [ChcExpr],
    formal_positions: FxHashMap<&'a ChcVar, usize>,
    replacements: Vec<Option<Replacement>>,
    /// Expanded counts for actual sub-DAGs. Raw pointers are lookup identities
    /// only; all pointed-to expressions remain borrowed for this call.
    replacement_memo: FxHashMap<*const ChcExpr, Counted>,
    /// Rewritten candidate sub-DAGs, preserving sharing in the output.
    template_memo: FxHashMap<*const ChcExpr, Built>,
    output_budget: NodeBudget,
    control: SubstitutionControl<'a>,
}

impl ExactSubstituter<'_> {
    fn rewrite(&mut self, expression: &ChcExpr, depth: usize) -> Option<Built> {
        self.control.checkpoint()?;
        if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
            return None;
        }

        let key = expression as *const ChcExpr;
        if let Some(cached) = self.template_memo.get(&key).cloned() {
            depth
                .checked_add(cached.height)
                .filter(|end| *end <= crate::expr::MAX_EXPR_RECURSION_DEPTH)?;
            self.output_budget.charge(cached.expanded_nodes)?;
            return Some(cached);
        }

        let built = match expression {
            ChcExpr::Var(variable) => {
                let position = *self.formal_positions.get(variable)?;
                if matches!(
                    &self.formals.get(position)?.sort,
                    ChcSort::Array(_, _) | ChcSort::Datatype { .. }
                ) {
                    return None;
                }
                let replacement = self.replacement(position)?;
                depth
                    .checked_add(replacement.height)
                    .filter(|end| *end <= crate::expr::MAX_EXPR_RECURSION_DEPTH)?;
                self.output_budget.charge(replacement.expanded_nodes)?;
                Built {
                    expression: replacement.expression,
                    expanded_nodes: replacement.expanded_nodes,
                    height: replacement.height,
                }
            }
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::BitVec(_, _) | ChcExpr::Real(_, 1..) => {
                self.output_budget.charge(1)?;
                Built {
                    expression: Arc::new(expression.clone()),
                    expanded_nodes: 1,
                    height: 1,
                }
            }
            ChcExpr::Op(ChcOp::Select | ChcOp::Store, _)
            | ChcExpr::FuncApp(_, _, _)
            | ChcExpr::PredicateApp(_, _, _)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_)
            | ChcExpr::ConstArray(_, _)
            | ChcExpr::Real(_, _) => return None,
            ChcExpr::Op(operation, arguments) => {
                self.output_budget.charge(1)?;
                if arguments.len() > self.output_budget.remaining {
                    return None;
                }
                let mut expanded_nodes = 1usize;
                let mut height = 1usize;
                let mut rewritten = Vec::new();
                rewritten
                    .try_reserve(arguments.len().min(usize::from(CONTROL_POLL_STRIDE)))
                    .ok()?;
                for argument in arguments {
                    if rewritten.len() == rewritten.capacity() {
                        self.control.boundary()?;
                        rewritten
                            .try_reserve(
                                arguments
                                    .len()
                                    .saturating_sub(rewritten.len())
                                    .min(usize::from(CONTROL_POLL_STRIDE)),
                            )
                            .ok()?;
                    }
                    let child = self.rewrite(argument, depth + 1)?;
                    expanded_nodes = expanded_nodes.checked_add(child.expanded_nodes)?;
                    height = height.max(child.height.checked_add(1)?);
                    rewritten.push(child.expression);
                }
                Built {
                    expression: Arc::new(ChcExpr::Op(*operation, rewritten)),
                    expanded_nodes,
                    height,
                }
            }
        };
        self.template_memo.insert(key, built.clone());
        Some(built)
    }

    fn replacement(&mut self, position: usize) -> Option<Replacement> {
        if let Some(cached) = self.replacements.get(position)?.clone() {
            return Some(cached);
        }
        self.control.boundary()?;
        let actual = self.actuals.get(position)?;
        let mut validation_budget = NodeBudget::new(self.output_budget.remaining);
        let counted = count_supported_actual(
            actual,
            0,
            &mut validation_budget,
            &mut self.replacement_memo,
            &mut self.control,
        )?;
        if counted.expanded_nodes != validation_budget.used {
            return None;
        }
        self.control.boundary()?;
        let replacement = Replacement {
            // Clone the actual root once. Children remain shared `Arc`s, and
            // every occurrence below reuses this root through `Arc::clone`.
            expression: Arc::new(actual.clone()),
            expanded_nodes: counted.expanded_nodes,
            height: counted.height,
        };
        *self.replacements.get_mut(position)? = Some(replacement.clone());
        Some(replacement)
    }
}

fn count_supported_actual(
    expression: &ChcExpr,
    depth: usize,
    budget: &mut NodeBudget,
    memo: &mut FxHashMap<*const ChcExpr, Counted>,
    control: &mut SubstitutionControl<'_>,
) -> Option<Counted> {
    control.checkpoint()?;
    if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
        return None;
    }
    let key = expression as *const ChcExpr;
    if let Some(cached) = memo.get(&key).copied() {
        depth
            .checked_add(cached.height)
            .filter(|end| *end <= crate::expr::MAX_EXPR_RECURSION_DEPTH)?;
        budget.charge(cached.expanded_nodes)?;
        return Some(cached);
    }

    budget.charge(1)?;
    let mut counted = Counted {
        expanded_nodes: 1,
        height: 1,
    };
    let children: &[Arc<ChcExpr>] = match expression {
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Var(_)
        | ChcExpr::Real(_, 1..) => &[],
        ChcExpr::Op(_, arguments) | ChcExpr::FuncApp(_, _, arguments) => arguments,
        ChcExpr::ConstArray(_, value) => std::slice::from_ref(value),
        ChcExpr::PredicateApp(_, _, _)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_)
        | ChcExpr::Real(_, _) => return None,
    };
    for child in children {
        let child_count = count_supported_actual(child, depth + 1, budget, memo, control)?;
        counted.expanded_nodes = counted
            .expanded_nodes
            .checked_add(child_count.expanded_nodes)?;
        counted.height = counted.height.max(child_count.height.checked_add(1)?);
    }
    memo.insert(key, counted);
    Some(counted)
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "candidate_substitute_tests.rs"]
mod tests;
