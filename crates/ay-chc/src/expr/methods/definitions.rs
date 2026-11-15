// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Elimination of the variables that top-level equalities define.

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use super::{ChcExpr, ChcOp, ChcVar, MAX_PREPROCESSING_NODES};
use crate::smt::SmtValue;

/// A substitution round whose result has more than this many times the nodes
/// of the formula the elimination started from is discarded, and the
/// elimination stops there. Substituting a compound right-hand side into
/// several occurrences grows the formula, and a chain of such definitions
/// grows it geometrically.
const DEFINITION_GROWTH_FACTOR: usize = 4;

/// Floor of the node cap, so a small formula may still take a few substituted
/// right-hand sides.
const DEFINITION_NODE_FLOOR: usize = 4096;

/// Rounds stop once the node counts of the accepted rounds sum past this many
/// times the node cap. The variable count alone bounds the work only by
/// `|vars| × cap`: when every definition mentions all the later variables, a
/// round takes a single definition, and each round walks a formula as large
/// as the cap.
const DEFINITION_WORK_FACTOR: usize = 2;

impl ChcExpr {
    /// Substitute away every variable that a top-level conjunct `x = t`
    /// (`x ∉ vars(t)`) defines, folding constants and array reads after each
    /// round, until no such definition is left or a bound below is reached.
    ///
    /// A round substitutes a batch of definitions at once: the first
    /// definition of each variable that no other definition of the batch
    /// mentions, so the substitution is idempotent and removes every variable
    /// of the batch from the formula (its own conjunct becomes `t = t`, which
    /// folds to `true`). The number of variables therefore bounds the rounds.
    /// A round that would grow the formula past [`DEFINITION_GROWTH_FACTOR`]
    /// times its starting size (and past [`DEFINITION_NODE_FLOOR`] nodes) is
    /// discarded, and the formula of the previous round is returned. The
    /// elimination also stops after the round that takes the accumulated
    /// round sizes past [`DEFINITION_WORK_FACTOR`] times that cap, and before
    /// a round once the thread's SMT deadline has expired; stopping early
    /// only leaves definitions in place.
    ///
    /// Every model of `self` is a model of the result, because each
    /// substituted variable equals its right-hand side there; so `unsat` for
    /// the result is `unsat` for `self`. When every substitution completes,
    /// a model of the result also extends to one of `self` by evaluating the
    /// definitions in reverse order, and the two are equisatisfiable; but
    /// `substitute` may leave occurrences in place in a formula past its node
    /// or depth budget, and the result is then only implied by `self`. A
    /// caller may therefore trust an `unsat` answer, and must re-derive or
    /// re-check on `self` whatever a `sat` answer is used for.
    pub(crate) fn eliminate_top_level_definitions(&self) -> Self {
        self.eliminate_top_level_definitions_with_trail().0
    }

    /// [`Self::eliminate_top_level_definitions`], also returning the
    /// definitions it substituted, in substitution order, for
    /// [`Self::extend_model_by_definitions`].
    pub(crate) fn eliminate_top_level_definitions_with_trail(&self) -> (Self, Vec<(ChcVar, Self)>) {
        let mut trail = Vec::new();
        let mut current = self.simplify_array_ops().simplify_constants();
        let node_cap = current
            .node_count(MAX_PREPROCESSING_NODES)
            .saturating_mul(DEFINITION_GROWTH_FACTOR)
            .max(DEFINITION_NODE_FLOOR);
        let work_cap = node_cap.saturating_mul(DEFINITION_WORK_FACTOR);
        let mut work = 0usize;
        for _ in 0..current.vars().len() {
            if crate::smt::smt_deadline_expired() {
                break;
            }
            let batch = current.independent_top_level_definitions();
            if batch.is_empty() {
                break;
            }
            // Constants first, so an index such as `extract(concat(66, 0))`
            // is the literal the read-over-write folding compares.
            let next = current
                .substitute(&batch)
                .simplify_constants()
                .simplify_array_ops()
                .simplify_constants();
            let next_nodes = next.node_count(node_cap.saturating_add(1));
            if next == current || next_nodes > node_cap {
                break;
            }
            current = next;
            trail.extend(batch);
            work = work.saturating_add(next_nodes);
            if work > work_cap {
                break;
            }
        }
        (current, trail)
    }

    /// Extend `model`, a model of a formula
    /// [`Self::eliminate_top_level_definitions_with_trail`] returned, to the
    /// variables its trail `definitions` substituted away: each right-hand
    /// side is evaluated in reverse substitution order, after the definitions
    /// of the variables it mentions. A variable the model already assigns
    /// keeps its value, and one whose right-hand side does not evaluate stays
    /// unassigned. A `sat` model of the eliminated formula thus names the
    /// eliminated variables again in a single pass, whatever order their
    /// definitions are listed in.
    pub(crate) fn extend_model_by_definitions(
        definitions: &[(ChcVar, Self)],
        model: &mut FxHashMap<String, SmtValue>,
    ) {
        for (var, value) in definitions.iter().rev() {
            if model.contains_key(&var.name) {
                continue;
            }
            if let Some(assigned) = crate::expr::evaluate_expr(value, model) {
                model.insert(var.name.clone(), assigned);
            }
        }
    }

    /// [`Self::eliminate_top_level_definitions`] applied to each disjunct of a
    /// top-level disjunction, or to `self` when it is not one. A disjunction
    /// is satisfiable exactly when one of its disjuncts is, so the result
    /// relates to `self` as each eliminated disjunct relates to its source:
    /// implied by it, and equisatisfiable when the substitutions complete.
    pub(crate) fn eliminate_definitions_per_disjunct(&self) -> Self {
        match self {
            Self::Op(ChcOp::Or, disjuncts) => Self::or_all(
                disjuncts
                    .iter()
                    .map(|disjunct| disjunct.eliminate_top_level_definitions()),
            ),
            _ => self.eliminate_top_level_definitions(),
        }
    }

    /// The definitions [`Self::eliminate_top_level_definitions`] substitutes in
    /// one round: for each top-level conjunct `x = t` in order, unless `x` is
    /// already defined or mentioned by an earlier definition of the batch, or
    /// `t` mentions a variable the batch defines.
    fn independent_top_level_definitions(&self) -> Vec<(ChcVar, Self)> {
        let mut defined: FxHashSet<ChcVar> = FxHashSet::default();
        let mut mentioned: FxHashSet<ChcVar> = FxHashSet::default();
        let mut batch = Vec::new();
        for conjunct in self.collect_conjuncts() {
            let Some((var, value)) = conjunct.top_level_definition() else {
                continue;
            };
            if defined.contains(&var) || mentioned.contains(&var) {
                continue;
            }
            let value_vars = value.vars();
            if value_vars.iter().any(|v| defined.contains(v)) {
                continue;
            }
            mentioned.extend(value_vars);
            defined.insert(var.clone());
            batch.push((var, value));
        }
        batch
    }

    /// `(x, t)` when `self` is `x = t` or `t = x` with `x ∉ vars(t)`; the left
    /// variable wins when both sides qualify.
    fn top_level_definition(&self) -> Option<(ChcVar, Self)> {
        let Self::Op(ChcOp::Eq, args) = self else {
            return None;
        };
        let [lhs, rhs] = args.as_slice() else {
            return None;
        };
        Self::oriented_definition(lhs, rhs).or_else(|| Self::oriented_definition(rhs, lhs))
    }

    fn oriented_definition(lhs: &Self, rhs: &Self) -> Option<(ChcVar, Self)> {
        let Self::Var(var) = lhs else {
            return None;
        };
        if rhs.vars().contains(var) {
            return None;
        }
        Some((var.clone(), rhs.clone()))
    }
}
