// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source-bound UNSAT certificate for exact quantified integer theorems.
//!
//! The general quantified solver proves these formulas after Skolemization, but
//! its isolated ground refutation is not an authored-scope proof.  This module
//! supplies the missing publication authority without trusting that producer:
//! it independently reparses the exact authored root and accepts only one of
//!
//! ```text
//! forall x:Int. exists y:Int. y * y = x
//! forall x:Int. exists y:Int. y <= x and x + 1 <= y
//! not (forall x:Int. exists y:Int. x < y and C < y)
//! ```
//!
//! All three roots are false. The first is refuted by `x = 2`, since an integer
//! square is `0` or `1` modulo `4`; the second has no witness for any `x`,
//! because its two bounds imply `x + 1 <= x`. The third is false because the
//! unnegated sentence is valid: `y = max(x, C) + 1` satisfies both strict lower
//! bounds. A sibling checker also covers contradictory bounded existentials and
//! the exact duality between a pointwise Boolean-UF definition and a bounded
//! existential over that UF. Every other shape declines. Successful evidence
//! is bound to the exact public query, source scope, ordered root vector, and
//! term-store snapshot; publication re-runs these small checkers.

mod bounded_bool_uf;

use std::collections::HashSet;

use ay_core::term::{Constant, Symbol, TermData, TermStoreSnapshotStamp};
use ay_core::{Sort, TermId, TermStore};
use ay_frontend::{Context, SourceContextStamp};
use num_bigint::BigInt;

use super::{Executor, QueryAuthorityEpoch};

/// Canonical identities interpreted by this checker.
///
/// A legal colliding declaration receives a private identity.  Observing a
/// declaration that still owns one of these canonical identities means the
/// frontend identity invariant was bypassed, so authority is refused.
const CHECKED_CORE_OPERATORS: [&str; 9] = ["and", "=", "*", "<=", "+", "-", "<", ">=", ">"];

/// Bound malformed low-level DAGs independently of the ordinary parser.
const MAX_REACHABLE_NODES: usize = 64;

#[derive(Debug)]
pub(in crate::executor) struct CheckedExactForallExistsUnsat {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    roots: Box<[TermId]>,
    term_snapshot: TermStoreSnapshotStamp,
}

impl CheckedExactForallExistsUnsat {
    pub(in crate::executor) fn is_current(&self, executor: &Executor) -> bool {
        self.is_current_for_roots(executor, &executor.ctx.assertions)
    }

    fn is_current_for_roots(&self, executor: &Executor, roots: &[TermId]) -> bool {
        self.query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.roots.as_ref() == roots
            && self.term_snapshot == executor.ctx.terms.snapshot_stamp()
            && exact_root_is_unsat(&executor.ctx, roots)
    }
}

impl Executor {
    /// Independently authenticate an explicit immutable authored-root window.
    /// The caller in `unsat_cert` owns the public epoch/scope checks; accepting
    /// an explicit slice here prevents a transformed working assertion vector
    /// from silently replacing the source obligation.
    pub(in crate::executor) fn try_authorize_exact_forall_exists_roots(
        &self,
        roots: &[TermId],
    ) -> Option<CheckedExactForallExistsUnsat> {
        let term_snapshot = self.ctx.terms.snapshot_stamp();
        if !exact_root_is_unsat(&self.ctx, roots)
            || term_snapshot != self.ctx.terms.snapshot_stamp()
        {
            return None;
        }
        Some(self.bind_exact_forall_exists(roots, term_snapshot))
    }

    fn bind_exact_forall_exists(
        &self,
        roots: &[TermId],
        term_snapshot: TermStoreSnapshotStamp,
    ) -> CheckedExactForallExistsUnsat {
        CheckedExactForallExistsUnsat {
            query_epoch: self.query_authority_epoch.clone(),
            source_context_stamp: self.ctx.source_context_stamp(),
            roots: roots.into(),
            term_snapshot,
        }
    }
}

fn exact_root_is_unsat(ctx: &Context, roots: &[TermId]) -> bool {
    if roots.is_empty()
        || !core_operators_are_unshadowed(ctx)
        || roots
            .iter()
            .any(|&root| require_sort(&ctx.terms, root, &Sort::Bool).is_none())
    {
        return false;
    }
    if bounded_bool_uf::exact_bounded_bool_uf_is_unsat(ctx, roots) {
        return true;
    }
    let [root] = roots else {
        return false;
    };

    let terms = &ctx.terms;
    is_false_forall_exists(terms, *root) || is_negated_unbounded_above_forall_exists(terms, *root)
}

fn is_false_forall_exists(terms: &TermStore, root: TermId) -> bool {
    let Some((matrix, x, y)) = exact_int_forall_exists_matrix(terms, root) else {
        return false;
    };
    is_perfect_square_surjectivity(terms, matrix, x, y)
        || is_empty_successor_interval(terms, matrix, x, y)
}

/// `not (forall x. exists y. x < y and C < y)` is false for every integer
/// constant `C`: choose `y = max(x, C) + 1`.
fn is_negated_unbounded_above_forall_exists(terms: &TermStore, root: TermId) -> bool {
    let Some(TermData::Not(sentence)) = live_term(terms, root) else {
        return false;
    };
    let Some((matrix, x, y)) = exact_int_forall_exists_matrix(terms, *sentence) else {
        return false;
    };
    let Some((first, second)) = binary_app(terms, matrix, "and", &Sort::Bool) else {
        return false;
    };
    (is_strict_lower_bound(terms, first, x, y) && is_constant_strict_lower_bound(terms, second, y))
        || (is_strict_lower_bound(terms, second, x, y)
            && is_constant_strict_lower_bound(terms, first, y))
}

fn exact_int_forall_exists_matrix(
    terms: &TermStore,
    root: TermId,
) -> Option<(TermId, TermId, TermId)> {
    require_sort(terms, root, &Sort::Bool)?;
    let TermData::Forall(outer, outer_body, outer_triggers) = live_term(terms, root)? else {
        return None;
    };
    let [(outer_name, Sort::Int)] = outer.as_slice() else {
        return None;
    };
    if !outer_triggers.is_empty() {
        return None;
    }
    require_sort(terms, *outer_body, &Sort::Bool)?;

    let TermData::Exists(inner, matrix, inner_triggers) = live_term(terms, *outer_body)? else {
        return None;
    };
    let [(inner_name, Sort::Int)] = inner.as_slice() else {
        return None;
    };
    if outer_name == inner_name || !inner_triggers.is_empty() {
        return None;
    }
    require_sort(terms, *matrix, &Sort::Bool)?;

    let x = unique_named_var(terms, *matrix, outer_name)?;
    let y = unique_named_var(terms, *matrix, inner_name)?;
    if x == y {
        return None;
    }
    require_sort(terms, x, &Sort::Int)?;
    require_sort(terms, y, &Sort::Int)?;
    Some((*matrix, x, y))
}

fn is_strict_lower_bound(terms: &TermStore, atom: TermId, lower: TermId, y: TermId) -> bool {
    matches!(binary_app(terms, atom, "<", &Sort::Bool), Some((left, right)) if left == lower && right == y)
}

fn is_constant_strict_lower_bound(terms: &TermStore, atom: TermId, y: TermId) -> bool {
    let Some((left, right)) = binary_app(terms, atom, "<", &Sort::Bool) else {
        return false;
    };
    right == y
        && require_sort(terms, left, &Sort::Int).is_some()
        && matches!(
            live_term(terms, left),
            Some(TermData::Const(Constant::Int(_)))
        )
}

fn is_perfect_square_surjectivity(terms: &TermStore, matrix: TermId, x: TermId, y: TermId) -> bool {
    let Some((left, right)) = binary_app(terms, matrix, "=", &Sort::Bool) else {
        return false;
    };
    [(left, right), (right, left)]
        .into_iter()
        .any(|(square, target)| target == x && is_square_of(terms, square, y))
}

fn is_square_of(terms: &TermStore, term: TermId, y: TermId) -> bool {
    let Some((left, right)) = binary_app(terms, term, "*", &Sort::Int) else {
        return false;
    };
    left == y && right == y
}

fn is_empty_successor_interval(terms: &TermStore, matrix: TermId, x: TermId, y: TermId) -> bool {
    let Some((first, second)) = binary_app(terms, matrix, "and", &Sort::Bool) else {
        return false;
    };
    (is_upper_bound(terms, first, x, y) && is_successor_lower_bound(terms, second, x, y))
        || (is_upper_bound(terms, second, x, y) && is_successor_lower_bound(terms, first, x, y))
}

fn is_upper_bound(terms: &TermStore, atom: TermId, x: TermId, y: TermId) -> bool {
    matches!(binary_app(terms, atom, "<=", &Sort::Bool), Some((left, right)) if left == y && right == x)
}

fn is_successor_lower_bound(terms: &TermStore, atom: TermId, x: TermId, y: TermId) -> bool {
    let Some((left, right)) = binary_app(terms, atom, "<=", &Sort::Bool) else {
        return false;
    };
    right == y && is_x_plus_one(terms, left, x)
}

fn is_x_plus_one(terms: &TermStore, term: TermId, x: TermId) -> bool {
    let Some((left, right)) = binary_app(terms, term, "+", &Sort::Int) else {
        return false;
    };
    (left == x && is_int_one(terms, right)) || (right == x && is_int_one(terms, left))
}

fn is_int_one(terms: &TermStore, term: TermId) -> bool {
    require_sort(terms, term, &Sort::Int).is_some()
        && matches!(live_term(terms, term), Some(TermData::Const(Constant::Int(value))) if value == &BigInt::from(1u8))
}

fn binary_app(
    terms: &TermStore,
    term: TermId,
    expected_operator: &str,
    expected_sort: &Sort,
) -> Option<(TermId, TermId)> {
    require_sort(terms, term, expected_sort)?;
    let TermData::App(Symbol::Named(operator), args) = live_term(terms, term)? else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    (operator == expected_operator).then_some((*left, *right))
}

fn core_operators_are_unshadowed(ctx: &Context) -> bool {
    ctx.symbol_iter().all(|(surface, info)| {
        !CHECKED_CORE_OPERATORS.contains(&ctx.symbol_identity_name(surface, info))
    })
}

fn live_term(terms: &TermStore, term: TermId) -> Option<&TermData> {
    terms.entry_stamp(term)?;
    Some(terms.get(term))
}

fn require_sort(terms: &TermStore, term: TermId, expected: &Sort) -> Option<()> {
    terms.entry_stamp(term)?;
    (terms.sort(term) == expected).then_some(())
}

/// Recover one binder's exact term identity and reject same-name ambiguity.
fn unique_named_var(terms: &TermStore, root: TermId, name: &str) -> Option<TermId> {
    let mut stack = vec![root];
    let mut seen = HashSet::new();
    let mut found = None;
    let mut remaining = MAX_REACHABLE_NODES;
    while let Some(term) = stack.pop() {
        if remaining == 0 {
            return None;
        }
        remaining -= 1;
        if !seen.insert(term) {
            continue;
        }
        match live_term(terms, term)? {
            TermData::Var(candidate, _) if candidate == name => match found {
                Some(previous) if previous != term => return None,
                _ => found = Some(term),
            },
            TermData::Var(_, _) | TermData::Const(_) => {}
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                stack.extend([*condition, *then_term, *else_term]);
            }
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, value)| *value));
                stack.push(*body);
            }
            TermData::Forall(_, body, patterns) | TermData::Exists(_, body, patterns) => {
                stack.push(*body);
                stack.extend(patterns.iter().flatten().copied());
            }
            _ => return None,
        }
    }
    found
}

#[cfg(test)]
mod tests;
